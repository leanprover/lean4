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
v___x_407_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_407_, 0, v___x_402_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
lean_ctor_set(v___x_407_, 2, v___x_383_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*3, v___x_404_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*3 + 1, v___x_405_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*3 + 2, v___x_405_);
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
v___x_857_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_857_, 0, v___x_852_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
lean_ctor_set(v___x_857_, 2, v___x_833_);
lean_ctor_set_uint8(v___x_857_, sizeof(void*)*3, v___x_854_);
lean_ctor_set_uint8(v___x_857_, sizeof(void*)*3 + 1, v___x_855_);
lean_ctor_set_uint8(v___x_857_, sizeof(void*)*3 + 2, v___x_855_);
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
size_t v_sz_boxed_892_; size_t v___x_15377__boxed_893_; lean_object* v_res_894_; 
v_sz_boxed_892_ = lean_unbox_usize(v_sz_880_);
lean_dec(v_sz_880_);
v___x_15377__boxed_893_ = lean_unbox_usize(v___x_881_);
lean_dec(v___x_881_);
v_res_894_ = l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___lam__0(v_self_878_, v_defaultTargets_879_, v_sz_boxed_892_, v___x_15377__boxed_893_, v___x_882_, v___x_883_, v___x_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
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
lean_object* v___y_1146_; uint8_t v___y_1147_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1170_; lean_object* v___y_1171_; uint8_t v___y_1172_; lean_object* v___y_1173_; lean_object* v_toContext_1177_; lean_object* v_lakeEnv_1178_; uint8_t v_noCache_1179_; lean_object* v_toolchain_1180_; uint8_t v_a_1182_; lean_object* v_a_1183_; 
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
v___x_1155_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1155_, 0, v___x_1151_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
lean_ctor_set(v___x_1155_, 2, v___x_1150_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*3, v___x_1153_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*3 + 1, v___y_1147_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*3 + 2, v___y_1147_);
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
v___x_1174_ = lean_string_utf8_byte_size(v___y_1171_);
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
v___y_1147_ = v___y_1172_;
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
v___y_1171_ = v_toolchain_1180_;
v___y_1172_ = v_preferReleaseBuild_1189_;
v___y_1173_ = v_keyName_1185_;
goto v___jp_1169_;
}
}
else
{
lean_inc(v_keyName_1185_);
v___y_1170_ = v_a_1183_;
v___y_1171_ = v_toolchain_1180_;
v___y_1172_ = v_preferReleaseBuild_1189_;
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(lean_object* v_self_1213_, lean_object* v_facet_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v_toBuildConfig_1218_; uint8_t v_verbosity_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
v_toBuildConfig_1218_ = lean_ctor_get(v_a_1215_, 0);
v_verbosity_1219_ = lean_ctor_get_uint8(v_toBuildConfig_1218_, sizeof(void*)*5 + 4);
v___x_1220_ = lean_box(v_verbosity_1219_);
v___x_1221_ = lean_obj_tag_nat(v___x_1220_);
lean_dec(v___x_1220_);
v___x_1222_ = lean_unsigned_to_nat(2u);
v___x_1223_ = lean_nat_dec_eq(v___x_1221_, v___x_1222_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
lean_dec(v_facet_1214_);
lean_dec_ref(v_self_1213_);
v___x_1224_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
lean_ctor_set(v___x_1225_, 1, v_a_1216_);
return v___x_1225_;
}
else
{
lean_object* v_baseName_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v_baseName_1226_ = lean_ctor_get(v_self_1213_, 1);
lean_inc(v_baseName_1226_);
lean_dec_ref(v_self_1213_);
v___x_1227_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_1228_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1226_, v___x_1223_);
v___x_1229_ = lean_string_append(v___x_1227_, v___x_1228_);
lean_dec_ref(v___x_1228_);
v___x_1230_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1231_ = lean_string_append(v___x_1229_, v___x_1230_);
v___x_1232_ = l_Lake_Name_eraseHead(v_facet_1214_);
v___x_1233_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1232_, v___x_1223_);
v___x_1234_ = lean_string_append(v___x_1231_, v___x_1233_);
lean_dec_ref(v___x_1233_);
v___x_1235_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1236_ = lean_string_append(v___x_1234_, v___x_1235_);
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
lean_ctor_set(v___x_1237_, 1, v_a_1216_);
return v___x_1237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___boxed(lean_object* v_self_1238_, lean_object* v_facet_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(v_self_1238_, v_facet_1239_, v_a_1240_, v_a_1241_);
lean_dec_ref(v_a_1240_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(lean_object* v_self_1244_, lean_object* v_facet_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_){
_start:
{
lean_object* v_toBuildConfig_1253_; uint8_t v_verbosity_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v_toBuildConfig_1253_ = lean_ctor_get(v_a_1250_, 0);
v_verbosity_1254_ = lean_ctor_get_uint8(v_toBuildConfig_1253_, sizeof(void*)*5 + 4);
v___x_1255_ = lean_box(v_verbosity_1254_);
v___x_1256_ = lean_obj_tag_nat(v___x_1255_);
lean_dec(v___x_1255_);
v___x_1257_ = lean_unsigned_to_nat(2u);
v___x_1258_ = lean_nat_dec_eq(v___x_1256_, v___x_1257_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec(v_facet_1245_);
lean_dec_ref(v_self_1244_);
v___x_1259_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
lean_ctor_set(v___x_1260_, 1, v_a_1251_);
return v___x_1260_;
}
else
{
lean_object* v_baseName_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v_baseName_1261_ = lean_ctor_get(v_self_1244_, 1);
lean_inc(v_baseName_1261_);
lean_dec_ref(v_self_1244_);
v___x_1262_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_1263_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1261_, v___x_1258_);
v___x_1264_ = lean_string_append(v___x_1262_, v___x_1263_);
lean_dec_ref(v___x_1263_);
v___x_1265_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1266_ = lean_string_append(v___x_1264_, v___x_1265_);
v___x_1267_ = l_Lake_Name_eraseHead(v_facet_1245_);
v___x_1268_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1267_, v___x_1258_);
v___x_1269_ = lean_string_append(v___x_1266_, v___x_1268_);
lean_dec_ref(v___x_1268_);
v___x_1270_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1271_ = lean_string_append(v___x_1269_, v___x_1270_);
v___x_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
lean_ctor_set(v___x_1272_, 1, v_a_1251_);
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
lean_object* v_a_1299_; lean_object* v_a_1300_; lean_object* v_a_1322_; lean_object* v_a_1323_; 
if (v_success_1290_ == 0)
{
lean_object* v_config_1344_; uint8_t v_preferReleaseBuild_1345_; 
v_config_1344_ = lean_ctor_get(v_self_1289_, 6);
v_preferReleaseBuild_1345_ = lean_ctor_get_uint8(v_config_1344_, sizeof(void*)*28 + 2);
if (v_preferReleaseBuild_1345_ == 0)
{
lean_object* v_toBuildConfig_1346_; lean_object* v_baseName_1347_; uint8_t v_verbosity_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v_toBuildConfig_1346_ = lean_ctor_get(v___y_1295_, 0);
v_baseName_1347_ = lean_ctor_get(v_self_1289_, 1);
lean_inc(v_baseName_1347_);
lean_dec_ref(v_self_1289_);
v_verbosity_1348_ = lean_ctor_get_uint8(v_toBuildConfig_1346_, sizeof(void*)*5 + 4);
v___x_1349_ = lean_box(v_verbosity_1348_);
v___x_1350_ = lean_obj_tag_nat(v___x_1349_);
lean_dec(v___x_1349_);
v___x_1351_ = lean_unsigned_to_nat(2u);
v___x_1352_ = lean_nat_dec_eq(v___x_1350_, v___x_1351_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; 
lean_dec(v_baseName_1347_);
v___x_1353_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_1299_ = v___x_1353_;
v_a_1300_ = v___y_1296_;
goto v___jp_1298_;
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1354_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_1355_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1347_, v___x_1352_);
v___x_1356_ = lean_string_append(v___x_1354_, v___x_1355_);
lean_dec_ref(v___x_1355_);
v___x_1357_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1358_ = lean_string_append(v___x_1356_, v___x_1357_);
v___x_1359_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2);
v___x_1360_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1359_, v___x_1352_);
v___x_1361_ = lean_string_append(v___x_1358_, v___x_1360_);
lean_dec_ref(v___x_1360_);
v___x_1362_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1363_ = lean_string_append(v___x_1361_, v___x_1362_);
v_a_1299_ = v___x_1363_;
v_a_1300_ = v___y_1296_;
goto v___jp_1298_;
}
}
else
{
lean_object* v_toBuildConfig_1364_; lean_object* v_baseName_1365_; uint8_t v_verbosity_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v_toBuildConfig_1364_ = lean_ctor_get(v___y_1295_, 0);
v_baseName_1365_ = lean_ctor_get(v_self_1289_, 1);
lean_inc(v_baseName_1365_);
lean_dec_ref(v_self_1289_);
v_verbosity_1366_ = lean_ctor_get_uint8(v_toBuildConfig_1364_, sizeof(void*)*5 + 4);
v___x_1367_ = lean_box(v_verbosity_1366_);
v___x_1368_ = lean_obj_tag_nat(v___x_1367_);
lean_dec(v___x_1367_);
v___x_1369_ = lean_unsigned_to_nat(2u);
v___x_1370_ = lean_nat_dec_eq(v___x_1368_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; 
lean_dec(v_baseName_1365_);
v___x_1371_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_1322_ = v___x_1371_;
v_a_1323_ = v___y_1296_;
goto v___jp_1321_;
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1372_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_1373_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1365_, v___x_1370_);
v___x_1374_ = lean_string_append(v___x_1372_, v___x_1373_);
lean_dec_ref(v___x_1373_);
v___x_1375_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1376_ = lean_string_append(v___x_1374_, v___x_1375_);
v___x_1377_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3);
v___x_1378_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1377_, v___x_1370_);
v___x_1379_ = lean_string_append(v___x_1376_, v___x_1378_);
lean_dec_ref(v___x_1378_);
v___x_1380_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1381_ = lean_string_append(v___x_1379_, v___x_1380_);
v_a_1322_ = v___x_1381_;
v_a_1323_ = v___y_1296_;
goto v___jp_1321_;
}
}
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_dec_ref(v_self_1289_);
v___x_1382_ = lean_box(0);
v___x_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
lean_ctor_set(v___x_1383_, 1, v___y_1296_);
return v___x_1383_;
}
v___jp_1298_:
{
lean_object* v_log_1301_; uint8_t v_action_1302_; uint8_t v_wantsRebuild_1303_; uint8_t v_canceled_1304_; lean_object* v_trace_1305_; lean_object* v_buildTime_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1320_; 
v_log_1301_ = lean_ctor_get(v_a_1300_, 0);
v_action_1302_ = lean_ctor_get_uint8(v_a_1300_, sizeof(void*)*3);
v_wantsRebuild_1303_ = lean_ctor_get_uint8(v_a_1300_, sizeof(void*)*3 + 1);
v_canceled_1304_ = lean_ctor_get_uint8(v_a_1300_, sizeof(void*)*3 + 2);
v_trace_1305_ = lean_ctor_get(v_a_1300_, 1);
v_buildTime_1306_ = lean_ctor_get(v_a_1300_, 2);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_a_1300_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1308_ = v_a_1300_;
v_isShared_1309_ = v_isSharedCheck_1320_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_buildTime_1306_);
lean_inc(v_trace_1305_);
lean_inc(v_log_1301_);
lean_dec(v_a_1300_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1320_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1317_; 
v___x_1310_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0));
v___x_1311_ = lean_string_append(v___x_1310_, v_a_1299_);
lean_dec_ref(v_a_1299_);
v___x_1312_ = 0;
v___x_1313_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1313_, 0, v___x_1311_);
lean_ctor_set_uint8(v___x_1313_, sizeof(void*)*1, v___x_1312_);
v___x_1314_ = lean_box(0);
v___x_1315_ = lean_array_push(v_log_1301_, v___x_1313_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v___x_1315_);
v___x_1317_ = v___x_1308_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1315_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_trace_1305_);
lean_ctor_set(v_reuseFailAlloc_1319_, 2, v_buildTime_1306_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*3, v_action_1302_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*3 + 1, v_wantsRebuild_1303_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*3 + 2, v_canceled_1304_);
v___x_1317_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1318_; 
v___x_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1314_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
return v___x_1318_;
}
}
}
v___jp_1321_:
{
lean_object* v_log_1324_; uint8_t v_action_1325_; uint8_t v_wantsRebuild_1326_; uint8_t v_canceled_1327_; lean_object* v_trace_1328_; lean_object* v_buildTime_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1343_; 
v_log_1324_ = lean_ctor_get(v_a_1323_, 0);
v_action_1325_ = lean_ctor_get_uint8(v_a_1323_, sizeof(void*)*3);
v_wantsRebuild_1326_ = lean_ctor_get_uint8(v_a_1323_, sizeof(void*)*3 + 1);
v_canceled_1327_ = lean_ctor_get_uint8(v_a_1323_, sizeof(void*)*3 + 2);
v_trace_1328_ = lean_ctor_get(v_a_1323_, 1);
v_buildTime_1329_ = lean_ctor_get(v_a_1323_, 2);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_a_1323_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1331_ = v_a_1323_;
v_isShared_1332_ = v_isSharedCheck_1343_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_buildTime_1329_);
lean_inc(v_trace_1328_);
lean_inc(v_log_1324_);
lean_dec(v_a_1323_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1343_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1333_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1));
v___x_1334_ = lean_string_append(v___x_1333_, v_a_1322_);
lean_dec_ref(v_a_1322_);
v___x_1335_ = 2;
v___x_1336_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1336_, 0, v___x_1334_);
lean_ctor_set_uint8(v___x_1336_, sizeof(void*)*1, v___x_1335_);
v___x_1337_ = lean_box(0);
v___x_1338_ = lean_array_push(v_log_1324_, v___x_1336_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1338_);
v___x_1340_ = v___x_1331_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1338_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_trace_1328_);
lean_ctor_set(v_reuseFailAlloc_1342_, 2, v_buildTime_1329_);
lean_ctor_set_uint8(v_reuseFailAlloc_1342_, sizeof(void*)*3, v_action_1325_);
lean_ctor_set_uint8(v_reuseFailAlloc_1342_, sizeof(void*)*3 + 1, v_wantsRebuild_1326_);
lean_ctor_set_uint8(v_reuseFailAlloc_1342_, sizeof(void*)*3 + 2, v_canceled_1327_);
v___x_1340_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1337_);
lean_ctor_set(v___x_1341_, 1, v___x_1340_);
return v___x_1341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed(lean_object* v_self_1384_, lean_object* v_success_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
uint8_t v_success_boxed_1393_; lean_object* v_res_1394_; 
v_success_boxed_1393_ = lean_unbox(v_success_1385_);
v_res_1394_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(v_self_1384_, v_success_boxed_1393_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(lean_object* v_self_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v___f_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_inc_ref(v_self_1395_);
v___f_1403_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed), 9, 1);
lean_closure_set(v___f_1403_, 0, v_self_1395_);
v___x_1404_ = l_Lake_instDataKindUnit;
lean_inc_ref(v_a_1396_);
v___x_1405_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1418_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_a_1407_ = lean_ctor_get(v___x_1405_, 1);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1409_ = v___x_1405_;
v_isShared_1410_ = v_isSharedCheck_1418_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1418_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; uint8_t v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1411_ = lean_unsigned_to_nat(0u);
v___x_1412_ = 0;
v___x_1413_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_1414_ = l_Lake_Job_mapM___redArg(v___x_1404_, v_a_1406_, v___f_1403_, v___x_1411_, v___x_1412_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v___x_1413_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1414_);
v___x_1416_ = v___x_1409_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1414_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_a_1407_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_dec_ref(v___f_1403_);
lean_dec_ref(v_a_1396_);
v_a_1419_ = lean_ctor_get(v___x_1405_, 0);
v_a_1420_ = lean_ctor_get(v___x_1405_, 1);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1405_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_inc(v_a_1419_);
lean_dec(v___x_1405_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1419_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___boxed(lean_object* v_self_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec(v_a_1431_);
lean_dec(v_a_1430_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(lean_object* v_self_1437_, lean_object* v_as_1438_, size_t v_sz_1439_, size_t v_i_1440_, lean_object* v_b_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
uint8_t v___x_1449_; 
v___x_1449_ = lean_usize_dec_lt(v_i_1440_, v_sz_1439_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; 
lean_dec_ref(v___y_1442_);
lean_dec_ref(v_self_1437_);
v___x_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1450_, 0, v_b_1441_);
lean_ctor_set(v___x_1450_, 1, v___y_1447_);
return v___x_1450_;
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1452_; 
v_a_1451_ = lean_array_uget_borrowed(v_as_1438_, v_i_1440_);
lean_inc_ref(v___y_1442_);
lean_inc(v_a_1451_);
lean_inc_ref(v_self_1437_);
v___x_1452_ = l_Lake_Package_fetchTargetJob(v_self_1437_, v_a_1451_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v_a_1454_; lean_object* v___x_1455_; size_t v___x_1456_; size_t v___x_1457_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_a_1453_);
v_a_1454_ = lean_ctor_get(v___x_1452_, 1);
lean_inc(v_a_1454_);
lean_dec_ref_known(v___x_1452_, 2);
v___x_1455_ = l_Lake_Job_mix___redArg(v_b_1441_, v_a_1453_);
v___x_1456_ = ((size_t)1ULL);
v___x_1457_ = lean_usize_add(v_i_1440_, v___x_1456_);
v_i_1440_ = v___x_1457_;
v_b_1441_ = v___x_1455_;
v___y_1447_ = v_a_1454_;
goto _start;
}
else
{
lean_object* v_a_1459_; lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec_ref(v___y_1442_);
lean_dec_ref(v_b_1441_);
lean_dec_ref(v_self_1437_);
v_a_1459_ = lean_ctor_get(v___x_1452_, 0);
v_a_1460_ = lean_ctor_get(v___x_1452_, 1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1452_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_inc(v_a_1459_);
lean_dec(v___x_1452_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1459_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0___boxed(lean_object* v_self_1468_, lean_object* v_as_1469_, lean_object* v_sz_1470_, lean_object* v_i_1471_, lean_object* v_b_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
size_t v_sz_boxed_1480_; size_t v_i_boxed_1481_; lean_object* v_res_1482_; 
v_sz_boxed_1480_ = lean_unbox_usize(v_sz_1470_);
lean_dec(v_sz_1470_);
v_i_boxed_1481_ = lean_unbox_usize(v_i_1471_);
lean_dec(v_i_1471_);
v_res_1482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_1468_, v_as_1469_, v_sz_boxed_1480_, v_i_boxed_1481_, v_b_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v_as_1469_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(lean_object* v_config_1483_, lean_object* v_self_1484_, lean_object* v_____r_1485_, lean_object* v_job_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_extraDepTargets_1494_; size_t v_sz_1495_; size_t v___x_1496_; lean_object* v___x_1497_; 
v_extraDepTargets_1494_ = lean_ctor_get(v_config_1483_, 2);
v_sz_1495_ = lean_array_size(v_extraDepTargets_1494_);
v___x_1496_ = ((size_t)0ULL);
v___x_1497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_1484_, v_extraDepTargets_1494_, v_sz_1495_, v___x_1496_, v_job_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed(lean_object* v_config_1498_, lean_object* v_self_1499_, lean_object* v_____r_1500_, lean_object* v_job_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(v_config_1498_, v_self_1499_, v_____r_1500_, v_job_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v_config_1498_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(uint8_t v___x_1510_, lean_object* v_self_1511_, lean_object* v_job_1512_, lean_object* v___f_1513_, lean_object* v___x_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
if (v___x_1510_ == 0)
{
lean_object* v___x_1522_; 
lean_inc_ref(v___y_1515_);
v___x_1522_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_1511_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v_a_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
v_a_1524_ = lean_ctor_get(v___x_1522_, 1);
lean_inc(v_a_1524_);
lean_dec_ref_known(v___x_1522_, 2);
v___x_1525_ = l_Lake_Job_add___redArg(v_job_1512_, v_a_1523_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc(v___y_1517_);
lean_inc(v___y_1516_);
v___x_1526_ = lean_apply_9(v___f_1513_, v___x_1514_, v___x_1525_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v_a_1524_, lean_box(0));
return v___x_1526_;
}
else
{
lean_dec_ref(v___y_1515_);
lean_dec_ref(v___f_1513_);
lean_dec_ref(v_job_1512_);
return v___x_1522_;
}
}
else
{
lean_object* v___x_1527_; 
lean_dec_ref(v_self_1511_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc(v___y_1517_);
lean_inc(v___y_1516_);
v___x_1527_ = lean_apply_9(v___f_1513_, v___x_1514_, v_job_1512_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, lean_box(0));
return v___x_1527_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed(lean_object* v___x_1528_, lean_object* v_self_1529_, lean_object* v_job_1530_, lean_object* v___f_1531_, lean_object* v___x_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
uint8_t v___x_4126__boxed_1540_; lean_object* v_res_1541_; 
v___x_4126__boxed_1540_ = lean_unbox(v___x_1528_);
v_res_1541_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(v___x_4126__boxed_1540_, v_self_1529_, v_job_1530_, v___f_1531_, v___x_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec(v___y_1534_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(lean_object* v_self_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v_wsIdx_1552_; lean_object* v_baseName_1553_; lean_object* v_config_1554_; lean_object* v___f_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; uint8_t v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v_job_1575_; uint8_t v___x_1576_; lean_object* v___x_1577_; lean_object* v___y_1578_; lean_object* v___x_1579_; 
v_wsIdx_1552_ = lean_ctor_get(v_self_1544_, 0);
v_baseName_1553_ = lean_ctor_get(v_self_1544_, 1);
v_config_1554_ = lean_ctor_get(v_self_1544_, 6);
lean_inc_ref(v_self_1544_);
lean_inc_ref(v_config_1554_);
v___f_1555_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1555_, 0, v_config_1554_);
lean_closure_set(v___f_1555_, 1, v_self_1544_);
v___x_1556_ = l_Lake_instDataKindUnit;
v___x_1557_ = 1;
lean_inc(v_baseName_1553_);
v___x_1558_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1553_, v___x_1557_);
v___x_1559_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0));
lean_inc_ref(v___x_1558_);
v___x_1560_ = lean_string_append(v___x_1558_, v___x_1559_);
v___x_1561_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1));
v___x_1562_ = lean_string_append(v___x_1561_, v___x_1558_);
lean_dec_ref(v___x_1558_);
v___x_1563_ = lean_string_append(v___x_1562_, v___x_1559_);
v___x_1564_ = lean_box(0);
v___x_1565_ = lean_box(0);
v___x_1566_ = lean_unsigned_to_nat(0u);
v___x_1567_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_1568_ = 0;
v___x_1569_ = 0;
v___x_1570_ = l_Lake_BuildTrace_nil(v___x_1563_);
v___x_1571_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1571_, 0, v___x_1567_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
lean_ctor_set(v___x_1571_, 2, v___x_1566_);
lean_ctor_set_uint8(v___x_1571_, sizeof(void*)*3, v___x_1568_);
lean_ctor_set_uint8(v___x_1571_, sizeof(void*)*3 + 1, v___x_1569_);
lean_ctor_set_uint8(v___x_1571_, sizeof(void*)*3 + 2, v___x_1569_);
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1564_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v___x_1573_ = lean_task_pure(v___x_1572_);
v___x_1574_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v_job_1575_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_1575_, 0, v___x_1573_);
lean_ctor_set(v_job_1575_, 1, v___x_1565_);
lean_ctor_set(v_job_1575_, 2, v___x_1574_);
lean_ctor_set_uint8(v_job_1575_, sizeof(void*)*3, v___x_1569_);
v___x_1576_ = lean_nat_dec_eq(v_wsIdx_1552_, v___x_1566_);
v___x_1577_ = lean_box(v___x_1576_);
v___y_1578_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed), 12, 5);
lean_closure_set(v___y_1578_, 0, v___x_1577_);
lean_closure_set(v___y_1578_, 1, v_self_1544_);
lean_closure_set(v___y_1578_, 2, v_job_1575_);
lean_closure_set(v___y_1578_, 3, v___f_1555_);
lean_closure_set(v___y_1578_, 4, v___x_1564_);
v___x_1579_ = l_Lake_ensureJob___redArg(v___x_1556_, v___y_1578_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1604_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_a_1581_ = lean_ctor_get(v___x_1579_, 1);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1583_ = v___x_1579_;
v_isShared_1584_ = v_isSharedCheck_1604_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1604_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v_task_1585_; lean_object* v_kind_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1602_; 
v_task_1585_ = lean_ctor_get(v_a_1580_, 0);
v_kind_1586_ = lean_ctor_get(v_a_1580_, 1);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_a_1580_);
if (v_isSharedCheck_1602_ == 0)
{
lean_object* v_unused_1603_; 
v_unused_1603_ = lean_ctor_get(v_a_1580_, 2);
lean_dec(v_unused_1603_);
v___x_1588_ = v_a_1580_;
v_isShared_1589_ = v_isSharedCheck_1602_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_kind_1586_);
lean_inc(v_task_1585_);
lean_dec(v_a_1580_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1602_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v_registeredJobs_1590_; lean_object* v_job_1592_; 
v_registeredJobs_1590_ = lean_ctor_get(v_a_1549_, 4);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 2, v___x_1560_);
v_job_1592_ = v___x_1588_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_task_1585_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_kind_1586_);
lean_ctor_set(v_reuseFailAlloc_1601_, 2, v___x_1560_);
v_job_1592_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1599_; 
lean_ctor_set_uint8(v_job_1592_, sizeof(void*)*3, v___x_1569_);
v___x_1593_ = lean_st_ref_take(v_registeredJobs_1590_);
lean_inc_ref(v_job_1592_);
v___x_1594_ = l_Lake_Job_toOpaque___redArg(v_job_1592_);
v___x_1595_ = lean_array_push(v___x_1593_, v___x_1594_);
v___x_1596_ = lean_st_ref_put(v_registeredJobs_1590_, v___x_1595_);
v___x_1597_ = l_Lake_Job_renew___redArg(v_job_1592_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 0, v___x_1597_);
v___x_1599_ = v___x_1583_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_a_1581_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1560_);
return v___x_1579_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___boxed(lean_object* v_self_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(v_self_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_);
lean_dec_ref(v_a_1610_);
lean_dec(v_a_1609_);
lean_dec(v_a_1608_);
lean_dec(v_a_1607_);
return v_res_1613_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = lean_box(0);
v___x_1615_ = l_Lean_Json_compress(v___x_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(uint8_t v_fmt_1616_){
_start:
{
if (v_fmt_1616_ == 0)
{
lean_object* v___x_1617_; 
v___x_1617_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
return v___x_1617_;
}
else
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0);
return v___x_1618_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_1619_){
_start:
{
uint8_t v_fmt_boxed_1620_; lean_object* v_res_1621_; 
v_fmt_boxed_1620_ = lean_unbox(v_fmt_1619_);
v_res_1621_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_boxed_1620_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(uint8_t v_fmt_1622_, lean_object* v_a_1623_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_1622_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___boxed(lean_object* v_fmt_1625_, lean_object* v_a_1626_){
_start:
{
uint8_t v_fmt_boxed_1627_; lean_object* v_res_1628_; 
v_fmt_boxed_1627_ = lean_unbox(v_fmt_1625_);
v_res_1628_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(v_fmt_boxed_1627_, v_a_1626_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0(uint8_t v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v___y_1629_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0___boxed(lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
uint8_t v___y_67__boxed_1634_; lean_object* v_res_1635_; 
v___y_67__boxed_1634_ = lean_unbox(v___y_1632_);
v_res_1635_ = l_Lake_Package_extraDepFacetConfig___lam__0(v___y_67__boxed_1634_, v___y_1633_);
return v_res_1635_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_1638_; uint8_t v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___f_1638_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_1639_ = 1;
v___x_1640_ = l_Lake_instDataKindUnit;
v___x_1641_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__1));
v___x_1642_ = l_Lake_Package_keyword;
v___x_1643_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
lean_ctor_set(v___x_1643_, 1, v___x_1641_);
lean_ctor_set(v___x_1643_, 2, v___x_1640_);
lean_ctor_set(v___x_1643_, 3, v___f_1638_);
lean_ctor_set_uint8(v___x_1643_, sizeof(void*)*4, v___x_1639_);
lean_ctor_set_uint8(v___x_1643_, sizeof(void*)*4 + 1, v___x_1639_);
return v___x_1643_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = lean_obj_once(&l_Lake_Package_extraDepFacetConfig___closed__2, &l_Lake_Package_extraDepFacetConfig___closed__2_once, _init_l_Lake_Package_extraDepFacetConfig___closed__2);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(lean_object* v_self_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v_origName_1664_; lean_object* v_dir_1665_; lean_object* v_scope_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; 
v_origName_1664_ = lean_ctor_get(v_self_1660_, 3);
lean_inc(v_origName_1664_);
v_dir_1665_ = lean_ctor_get(v_self_1660_, 4);
lean_inc_ref(v_dir_1665_);
v_scope_1666_ = lean_ctor_get(v_self_1660_, 10);
lean_inc_ref(v_scope_1666_);
lean_dec_ref(v_self_1660_);
v___x_1667_ = lean_string_utf8_byte_size(v_scope_1666_);
v___x_1668_ = lean_unsigned_to_nat(0u);
v___x_1669_ = lean_nat_dec_eq(v___x_1667_, v___x_1668_);
if (v___x_1669_ == 0)
{
lean_object* v_log_1670_; uint8_t v_action_1671_; uint8_t v_wantsRebuild_1672_; uint8_t v_canceled_1673_; lean_object* v_trace_1674_; lean_object* v_buildTime_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v_log_1670_ = lean_ctor_get(v_a_1662_, 0);
v_action_1671_ = lean_ctor_get_uint8(v_a_1662_, sizeof(void*)*3);
v_wantsRebuild_1672_ = lean_ctor_get_uint8(v_a_1662_, sizeof(void*)*3 + 1);
v_canceled_1673_ = lean_ctor_get_uint8(v_a_1662_, sizeof(void*)*3 + 2);
v_trace_1674_ = lean_ctor_get(v_a_1662_, 1);
v_buildTime_1675_ = lean_ctor_get(v_a_1662_, 2);
v___x_1676_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
v___x_1677_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1676_, v_dir_1665_);
if (lean_obj_tag(v___x_1677_) == 1)
{
lean_object* v_toContext_1678_; lean_object* v_lakeEnv_1679_; lean_object* v_val_1680_; lean_object* v_toolchain_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; 
v_toContext_1678_ = lean_ctor_get(v_a_1661_, 1);
v_lakeEnv_1679_ = lean_ctor_get(v_toContext_1678_, 0);
v_val_1680_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_val_1680_);
lean_dec_ref_known(v___x_1677_, 1);
v_toolchain_1681_ = lean_ctor_get(v_lakeEnv_1679_, 19);
v___x_1682_ = lean_string_utf8_byte_size(v_toolchain_1681_);
v___x_1683_ = lean_nat_dec_eq(v___x_1682_, v___x_1668_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1684_ = l_Lean_Name_toString(v_origName_1664_, v___x_1669_);
lean_inc_ref(v_lakeEnv_1679_);
v___x_1685_ = l_Lake_Reservoir_pkgApiUrl(v_lakeEnv_1679_, v_scope_1666_, v___x_1684_);
lean_dec_ref(v___x_1684_);
lean_dec_ref(v_scope_1666_);
v___x_1686_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1));
v___x_1687_ = lean_string_append(v___x_1685_, v___x_1686_);
v___x_1688_ = lean_string_append(v___x_1687_, v_val_1680_);
lean_dec(v_val_1680_);
v___x_1689_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2));
v___x_1690_ = lean_string_append(v___x_1688_, v___x_1689_);
v___x_1691_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_1692_ = l_Lake_uriEncode(v_toolchain_1681_, v___x_1691_);
v___x_1693_ = lean_string_append(v___x_1690_, v___x_1692_);
lean_dec_ref(v___x_1692_);
v___x_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
lean_ctor_set(v___x_1694_, 1, v_a_1662_);
return v___x_1694_;
}
else
{
lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1705_; 
lean_inc(v_buildTime_1675_);
lean_inc_ref(v_trace_1674_);
lean_inc_ref(v_log_1670_);
lean_dec(v_val_1680_);
lean_dec_ref(v_scope_1666_);
lean_dec(v_origName_1664_);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_a_1662_);
if (v_isSharedCheck_1705_ == 0)
{
lean_object* v_unused_1706_; lean_object* v_unused_1707_; lean_object* v_unused_1708_; 
v_unused_1706_ = lean_ctor_get(v_a_1662_, 2);
lean_dec(v_unused_1706_);
v_unused_1707_ = lean_ctor_get(v_a_1662_, 1);
lean_dec(v_unused_1707_);
v_unused_1708_ = lean_ctor_get(v_a_1662_, 0);
lean_dec(v_unused_1708_);
v___x_1696_ = v_a_1662_;
v_isShared_1697_ = v_isSharedCheck_1705_;
goto v_resetjp_1695_;
}
else
{
lean_dec(v_a_1662_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1705_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1702_; 
v___x_1698_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4));
v___x_1699_ = lean_array_get_size(v_log_1670_);
v___x_1700_ = lean_array_push(v_log_1670_, v___x_1698_);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v___x_1700_);
v___x_1702_ = v___x_1696_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1700_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v_trace_1674_);
lean_ctor_set(v_reuseFailAlloc_1704_, 2, v_buildTime_1675_);
lean_ctor_set_uint8(v_reuseFailAlloc_1704_, sizeof(void*)*3, v_action_1671_);
lean_ctor_set_uint8(v_reuseFailAlloc_1704_, sizeof(void*)*3 + 1, v_wantsRebuild_1672_);
lean_ctor_set_uint8(v_reuseFailAlloc_1704_, sizeof(void*)*3 + 2, v_canceled_1673_);
v___x_1702_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
lean_object* v___x_1703_; 
v___x_1703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1699_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
return v___x_1703_;
}
}
}
}
else
{
lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1719_; 
lean_inc(v_buildTime_1675_);
lean_inc_ref(v_trace_1674_);
lean_inc_ref(v_log_1670_);
lean_dec(v___x_1677_);
lean_dec_ref(v_scope_1666_);
lean_dec(v_origName_1664_);
v_isSharedCheck_1719_ = !lean_is_exclusive(v_a_1662_);
if (v_isSharedCheck_1719_ == 0)
{
lean_object* v_unused_1720_; lean_object* v_unused_1721_; lean_object* v_unused_1722_; 
v_unused_1720_ = lean_ctor_get(v_a_1662_, 2);
lean_dec(v_unused_1720_);
v_unused_1721_ = lean_ctor_get(v_a_1662_, 1);
lean_dec(v_unused_1721_);
v_unused_1722_ = lean_ctor_get(v_a_1662_, 0);
lean_dec(v_unused_1722_);
v___x_1710_ = v_a_1662_;
v_isShared_1711_ = v_isSharedCheck_1719_;
goto v_resetjp_1709_;
}
else
{
lean_dec(v_a_1662_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1719_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1716_; 
v___x_1712_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6));
v___x_1713_ = lean_array_get_size(v_log_1670_);
v___x_1714_ = lean_array_push(v_log_1670_, v___x_1712_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 0, v___x_1714_);
v___x_1716_ = v___x_1710_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1714_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_trace_1674_);
lean_ctor_set(v_reuseFailAlloc_1718_, 2, v_buildTime_1675_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, sizeof(void*)*3, v_action_1671_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, sizeof(void*)*3 + 1, v_wantsRebuild_1672_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, sizeof(void*)*3 + 2, v_canceled_1673_);
v___x_1716_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v___x_1717_; 
v___x_1717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1713_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
return v___x_1717_;
}
}
}
}
else
{
lean_object* v_log_1723_; uint8_t v_action_1724_; uint8_t v_wantsRebuild_1725_; uint8_t v_canceled_1726_; lean_object* v_trace_1727_; lean_object* v_buildTime_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1739_; 
lean_dec_ref(v_scope_1666_);
lean_dec_ref(v_dir_1665_);
lean_dec(v_origName_1664_);
v_log_1723_ = lean_ctor_get(v_a_1662_, 0);
v_action_1724_ = lean_ctor_get_uint8(v_a_1662_, sizeof(void*)*3);
v_wantsRebuild_1725_ = lean_ctor_get_uint8(v_a_1662_, sizeof(void*)*3 + 1);
v_canceled_1726_ = lean_ctor_get_uint8(v_a_1662_, sizeof(void*)*3 + 2);
v_trace_1727_ = lean_ctor_get(v_a_1662_, 1);
v_buildTime_1728_ = lean_ctor_get(v_a_1662_, 2);
v_isSharedCheck_1739_ = !lean_is_exclusive(v_a_1662_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1730_ = v_a_1662_;
v_isShared_1731_ = v_isSharedCheck_1739_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_buildTime_1728_);
lean_inc(v_trace_1727_);
lean_inc(v_log_1723_);
lean_dec(v_a_1662_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1739_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1736_; 
v___x_1732_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8));
v___x_1733_ = lean_array_get_size(v_log_1723_);
v___x_1734_ = lean_array_push(v_log_1723_, v___x_1732_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1734_);
v___x_1736_ = v___x_1730_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1734_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v_trace_1727_);
lean_ctor_set(v_reuseFailAlloc_1738_, 2, v_buildTime_1728_);
lean_ctor_set_uint8(v_reuseFailAlloc_1738_, sizeof(void*)*3, v_action_1724_);
lean_ctor_set_uint8(v_reuseFailAlloc_1738_, sizeof(void*)*3 + 1, v_wantsRebuild_1725_);
lean_ctor_set_uint8(v_reuseFailAlloc_1738_, sizeof(void*)*3 + 2, v_canceled_1726_);
v___x_1736_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1733_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
return v___x_1737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___boxed(lean_object* v_self_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1740_, v_a_1741_, v_a_1742_);
lean_dec_ref(v_a_1741_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(lean_object* v_self_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1745_, v_a_1750_, v_a_1751_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___boxed(lean_object* v_self_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(v_self_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
lean_dec_ref(v_a_1759_);
lean_dec(v_a_1758_);
lean_dec(v_a_1757_);
lean_dec(v_a_1756_);
lean_dec_ref(v_a_1755_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(lean_object* v_self_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v_rev_1776_; lean_object* v_log_1777_; uint8_t v_action_1778_; uint8_t v_wantsRebuild_1779_; uint8_t v_canceled_1780_; lean_object* v_trace_1781_; lean_object* v_buildTime_1782_; lean_object* v_dir_1791_; lean_object* v_config_1792_; lean_object* v_remoteUrl_1793_; lean_object* v_buildArchive_1794_; lean_object* v___y_1796_; lean_object* v___y_1797_; uint8_t v___y_1798_; uint8_t v___y_1799_; uint8_t v___y_1800_; lean_object* v___y_1801_; lean_object* v_val_1802_; lean_object* v___y_1822_; lean_object* v_releaseRepo_1844_; 
v_dir_1791_ = lean_ctor_get(v_self_1772_, 4);
lean_inc_ref(v_dir_1791_);
v_config_1792_ = lean_ctor_get(v_self_1772_, 6);
lean_inc_ref(v_config_1792_);
v_remoteUrl_1793_ = lean_ctor_get(v_self_1772_, 11);
lean_inc_ref(v_remoteUrl_1793_);
v_buildArchive_1794_ = lean_ctor_get(v_self_1772_, 21);
lean_inc_ref(v_buildArchive_1794_);
lean_dec_ref(v_self_1772_);
v_releaseRepo_1844_ = lean_ctor_get(v_config_1792_, 10);
lean_inc(v_releaseRepo_1844_);
lean_dec_ref(v_config_1792_);
if (lean_obj_tag(v_releaseRepo_1844_) == 0)
{
lean_object* v___x_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1845_ = lean_string_utf8_byte_size(v_remoteUrl_1793_);
v___x_1846_ = lean_unsigned_to_nat(0u);
v___x_1847_ = lean_nat_dec_eq(v___x_1845_, v___x_1846_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; 
v___x_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1848_, 0, v_remoteUrl_1793_);
v___y_1822_ = v___x_1848_;
goto v___jp_1821_;
}
else
{
lean_dec_ref(v_remoteUrl_1793_);
v___y_1822_ = v_releaseRepo_1844_;
goto v___jp_1821_;
}
}
else
{
lean_dec_ref(v_remoteUrl_1793_);
v___y_1822_ = v_releaseRepo_1844_;
goto v___jp_1821_;
}
v___jp_1775_:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1783_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0));
v___x_1784_ = lean_string_append(v___x_1783_, v_rev_1776_);
lean_dec_ref(v_rev_1776_);
v___x_1785_ = 3;
v___x_1786_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1786_, 0, v___x_1784_);
lean_ctor_set_uint8(v___x_1786_, sizeof(void*)*1, v___x_1785_);
v___x_1787_ = lean_array_get_size(v_log_1777_);
v___x_1788_ = lean_array_push(v_log_1777_, v___x_1786_);
v___x_1789_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
lean_ctor_set(v___x_1789_, 1, v_trace_1781_);
lean_ctor_set(v___x_1789_, 2, v_buildTime_1782_);
lean_ctor_set_uint8(v___x_1789_, sizeof(void*)*3, v_action_1778_);
lean_ctor_set_uint8(v___x_1789_, sizeof(void*)*3 + 1, v_wantsRebuild_1779_);
lean_ctor_set_uint8(v___x_1789_, sizeof(void*)*3 + 2, v_canceled_1780_);
v___x_1790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1787_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
return v___x_1790_;
}
v___jp_1795_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
lean_inc_ref(v_dir_1791_);
v___x_1804_ = l_Lake_GitRepo_findTag_x3f(v___x_1803_, v_dir_1791_);
if (lean_obj_tag(v___x_1804_) == 1)
{
lean_object* v_val_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
lean_dec_ref(v_dir_1791_);
v_val_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_val_1805_);
lean_dec_ref_known(v___x_1804_, 1);
v___x_1806_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1806_, 0, v___y_1796_);
lean_ctor_set(v___x_1806_, 1, v___y_1797_);
lean_ctor_set(v___x_1806_, 2, v___y_1801_);
lean_ctor_set_uint8(v___x_1806_, sizeof(void*)*3, v___y_1798_);
lean_ctor_set_uint8(v___x_1806_, sizeof(void*)*3 + 1, v___y_1799_);
lean_ctor_set_uint8(v___x_1806_, sizeof(void*)*3 + 2, v___y_1800_);
v___x_1807_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1));
v___x_1808_ = lean_string_append(v_val_1802_, v___x_1807_);
v___x_1809_ = lean_string_append(v___x_1808_, v_val_1805_);
lean_dec(v_val_1805_);
v___x_1810_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2));
v___x_1811_ = lean_string_append(v___x_1809_, v___x_1810_);
v___x_1812_ = lean_string_append(v___x_1811_, v_buildArchive_1794_);
lean_dec_ref(v_buildArchive_1794_);
v___x_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
lean_ctor_set(v___x_1813_, 1, v___x_1806_);
return v___x_1813_;
}
else
{
lean_object* v___x_1814_; 
lean_dec(v___x_1804_);
lean_dec_ref(v_val_1802_);
lean_dec_ref(v_buildArchive_1794_);
v___x_1814_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1803_, v_dir_1791_);
if (lean_obj_tag(v___x_1814_) == 1)
{
lean_object* v_val_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v_val_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_val_1815_);
lean_dec_ref_known(v___x_1814_, 1);
v___x_1816_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3));
v___x_1817_ = lean_string_append(v___x_1816_, v_val_1815_);
lean_dec(v_val_1815_);
v___x_1818_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4));
v___x_1819_ = lean_string_append(v___x_1817_, v___x_1818_);
v_rev_1776_ = v___x_1819_;
v_log_1777_ = v___y_1796_;
v_action_1778_ = v___y_1798_;
v_wantsRebuild_1779_ = v___y_1799_;
v_canceled_1780_ = v___y_1800_;
v_trace_1781_ = v___y_1797_;
v_buildTime_1782_ = v___y_1801_;
goto v___jp_1775_;
}
else
{
lean_object* v___x_1820_; 
lean_dec(v___x_1814_);
v___x_1820_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v_rev_1776_ = v___x_1820_;
v_log_1777_ = v___y_1796_;
v_action_1778_ = v___y_1798_;
v_wantsRebuild_1779_ = v___y_1799_;
v_canceled_1780_ = v___y_1800_;
v_trace_1781_ = v___y_1797_;
v_buildTime_1782_ = v___y_1801_;
goto v___jp_1775_;
}
}
}
v___jp_1821_:
{
lean_object* v_log_1823_; uint8_t v_action_1824_; uint8_t v_wantsRebuild_1825_; uint8_t v_canceled_1826_; lean_object* v_trace_1827_; lean_object* v_buildTime_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1843_; 
v_log_1823_ = lean_ctor_get(v_a_1773_, 0);
v_action_1824_ = lean_ctor_get_uint8(v_a_1773_, sizeof(void*)*3);
v_wantsRebuild_1825_ = lean_ctor_get_uint8(v_a_1773_, sizeof(void*)*3 + 1);
v_canceled_1826_ = lean_ctor_get_uint8(v_a_1773_, sizeof(void*)*3 + 2);
v_trace_1827_ = lean_ctor_get(v_a_1773_, 1);
v_buildTime_1828_ = lean_ctor_get(v_a_1773_, 2);
v_isSharedCheck_1843_ = !lean_is_exclusive(v_a_1773_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1830_ = v_a_1773_;
v_isShared_1831_ = v_isSharedCheck_1843_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_buildTime_1828_);
lean_inc(v_trace_1827_);
lean_inc(v_log_1823_);
lean_dec(v_a_1773_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1843_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = l_Lake_Git_defaultRemote;
lean_inc_ref(v_dir_1791_);
v___x_1833_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v___x_1832_, v_dir_1791_);
if (lean_obj_tag(v___y_1822_) == 0)
{
if (lean_obj_tag(v___x_1833_) == 1)
{
lean_object* v_val_1834_; 
lean_del_object(v___x_1830_);
v_val_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_val_1834_);
lean_dec_ref_known(v___x_1833_, 1);
v___y_1796_ = v_log_1823_;
v___y_1797_ = v_trace_1827_;
v___y_1798_ = v_action_1824_;
v___y_1799_ = v_wantsRebuild_1825_;
v___y_1800_ = v_canceled_1826_;
v___y_1801_ = v_buildTime_1828_;
v_val_1802_ = v_val_1834_;
goto v___jp_1795_;
}
else
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1839_; 
lean_dec(v___x_1833_);
lean_dec_ref(v_buildArchive_1794_);
lean_dec_ref(v_dir_1791_);
v___x_1835_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6));
v___x_1836_ = lean_array_get_size(v_log_1823_);
v___x_1837_ = lean_array_push(v_log_1823_, v___x_1835_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v___x_1837_);
v___x_1839_ = v___x_1830_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1837_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_trace_1827_);
lean_ctor_set(v_reuseFailAlloc_1841_, 2, v_buildTime_1828_);
lean_ctor_set_uint8(v_reuseFailAlloc_1841_, sizeof(void*)*3, v_action_1824_);
lean_ctor_set_uint8(v_reuseFailAlloc_1841_, sizeof(void*)*3 + 1, v_wantsRebuild_1825_);
lean_ctor_set_uint8(v_reuseFailAlloc_1841_, sizeof(void*)*3 + 2, v_canceled_1826_);
v___x_1839_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1840_; 
v___x_1840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1836_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
return v___x_1840_;
}
}
}
else
{
lean_object* v_val_1842_; 
lean_dec(v___x_1833_);
lean_del_object(v___x_1830_);
v_val_1842_ = lean_ctor_get(v___y_1822_, 0);
lean_inc(v_val_1842_);
lean_dec_ref_known(v___y_1822_, 1);
v___y_1796_ = v_log_1823_;
v___y_1797_ = v_trace_1827_;
v___y_1798_ = v_action_1824_;
v___y_1799_ = v_wantsRebuild_1825_;
v___y_1800_ = v_canceled_1826_;
v___y_1801_ = v_buildTime_1828_;
v_val_1802_ = v_val_1842_;
goto v___jp_1795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___boxed(lean_object* v_self_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1849_, v_a_1850_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(lean_object* v_self_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1853_, v_a_1859_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___boxed(lean_object* v_self_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(v_self_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_);
lean_dec_ref(v_a_1867_);
lean_dec(v_a_1866_);
lean_dec(v_a_1865_);
lean_dec(v_a_1864_);
lean_dec_ref(v_a_1863_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(lean_object* v_val_1871_, lean_object* v_a_x3f_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_log_1875_; uint8_t v_action_1876_; uint8_t v_wantsRebuild_1877_; uint8_t v_canceled_1878_; lean_object* v_trace_1879_; lean_object* v_buildTime_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1892_; 
v_log_1875_ = lean_ctor_get(v___y_1873_, 0);
v_action_1876_ = lean_ctor_get_uint8(v___y_1873_, sizeof(void*)*3);
v_wantsRebuild_1877_ = lean_ctor_get_uint8(v___y_1873_, sizeof(void*)*3 + 1);
v_canceled_1878_ = lean_ctor_get_uint8(v___y_1873_, sizeof(void*)*3 + 2);
v_trace_1879_ = lean_ctor_get(v___y_1873_, 1);
v_buildTime_1880_ = lean_ctor_get(v___y_1873_, 2);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___y_1873_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1882_ = v___y_1873_;
v_isShared_1883_ = v_isSharedCheck_1892_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_buildTime_1880_);
lean_inc(v_trace_1879_);
lean_inc(v_log_1875_);
lean_dec(v___y_1873_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1892_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1884_ = lean_io_mono_ms_now();
v___x_1885_ = lean_nat_sub(v___x_1884_, v_val_1871_);
lean_dec(v___x_1884_);
v___x_1886_ = lean_box(0);
v___x_1887_ = lean_nat_add(v_buildTime_1880_, v___x_1885_);
lean_dec(v___x_1885_);
lean_dec(v_buildTime_1880_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 2, v___x_1887_);
v___x_1889_ = v___x_1882_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_log_1875_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_trace_1879_);
lean_ctor_set(v_reuseFailAlloc_1891_, 2, v___x_1887_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*3, v_action_1876_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*3 + 1, v_wantsRebuild_1877_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*3 + 2, v_canceled_1878_);
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
lean_object* v_a_1913_; lean_object* v_a_1914_; lean_object* v_log_1917_; uint8_t v_action_1918_; uint8_t v_wantsRebuild_1919_; uint8_t v_canceled_1920_; lean_object* v_trace_1921_; lean_object* v_buildTime_1922_; lean_object* v_toBuildConfig_1928_; lean_object* v_log_1929_; uint8_t v_action_1930_; uint8_t v_wantsRebuild_1931_; uint8_t v_canceled_1932_; lean_object* v_trace_1933_; lean_object* v_buildTime_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_2024_; 
v_toBuildConfig_1928_ = lean_ctor_get(v_a_1909_, 0);
v_log_1929_ = lean_ctor_get(v_a_1910_, 0);
v_action_1930_ = lean_ctor_get_uint8(v_a_1910_, sizeof(void*)*3);
v_wantsRebuild_1931_ = lean_ctor_get_uint8(v_a_1910_, sizeof(void*)*3 + 1);
v_canceled_1932_ = lean_ctor_get_uint8(v_a_1910_, sizeof(void*)*3 + 2);
v_trace_1933_ = lean_ctor_get(v_a_1910_, 1);
v_buildTime_1934_ = lean_ctor_get(v_a_1910_, 2);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_a_1910_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_1936_ = v_a_1910_;
v_isShared_1937_ = v_isSharedCheck_2024_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_buildTime_1934_);
lean_inc(v_trace_1933_);
lean_inc(v_log_1929_);
lean_dec(v_a_1910_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_2024_;
goto v_resetjp_1935_;
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
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1923_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__1));
v___x_1924_ = lean_array_get_size(v_log_1917_);
v___x_1925_ = lean_array_push(v_log_1917_, v___x_1923_);
v___x_1926_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
lean_ctor_set(v___x_1926_, 1, v_trace_1921_);
lean_ctor_set(v___x_1926_, 2, v_buildTime_1922_);
lean_ctor_set_uint8(v___x_1926_, sizeof(void*)*3, v_action_1918_);
lean_ctor_set_uint8(v___x_1926_, sizeof(void*)*3 + 1, v_wantsRebuild_1919_);
lean_ctor_set_uint8(v___x_1926_, sizeof(void*)*3 + 2, v_canceled_1920_);
v___x_1927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1924_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
return v___x_1927_;
}
v_resetjp_1935_:
{
uint8_t v_noBuild_1938_; uint8_t v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v_noBuild_1938_ = lean_ctor_get_uint8(v_toBuildConfig_1928_, sizeof(void*)*5 + 2);
v___x_1939_ = l_Lake_JobAction_merge(v_action_1930_, v_action_1908_);
v___x_1940_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__2));
lean_inc_ref(v_traceFile_1907_);
v___x_1941_ = l_System_FilePath_addExtension(v_traceFile_1907_, v___x_1940_);
if (v_noBuild_1938_ == 0)
{
lean_object* v___x_1942_; lean_object* v_a_1944_; lean_object* v_a_1945_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1942_ = lean_io_mono_ms_now();
v___x_1949_ = lean_array_get_size(v_log_1929_);
v___x_1950_ = l_Lake_download(v_url_1903_, v_archiveFile_1904_, v_headers_1905_, v_log_1929_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v_a_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1951_);
v_a_1952_ = lean_ctor_get(v___x_1950_, 1);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___x_1950_, 2);
v___x_1953_ = lean_array_get_size(v_a_1952_);
v___x_1954_ = l_Array_extract___redArg(v_a_1952_, v___x_1949_, v___x_1953_);
v___x_1955_ = lean_box(0);
v___x_1956_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1906_, v___x_1955_, v___x_1954_);
v___x_1957_ = l_Lake_BuildMetadata_writeFile(v_traceFile_1907_, v___x_1956_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1994_; 
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1994_ == 0)
{
lean_object* v_unused_1995_; 
v_unused_1995_ = lean_ctor_get(v___x_1957_, 0);
lean_dec(v_unused_1995_);
v___x_1959_ = v___x_1957_;
v_isShared_1960_ = v_isSharedCheck_1994_;
goto v_resetjp_1958_;
}
else
{
lean_dec(v___x_1957_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1994_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; 
v___x_1961_ = l_Lake_removeFileIfExists(v___x_1941_);
lean_dec_ref(v___x_1941_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1984_; 
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1984_ == 0)
{
lean_object* v_unused_1985_; 
v_unused_1985_ = lean_ctor_get(v___x_1961_, 0);
lean_dec(v_unused_1985_);
v___x_1963_ = v___x_1961_;
v_isShared_1964_ = v_isSharedCheck_1984_;
goto v_resetjp_1962_;
}
else
{
lean_dec(v___x_1961_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1984_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v_a_1952_);
v___x_1966_ = v___x_1936_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1952_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_trace_1933_);
lean_ctor_set(v_reuseFailAlloc_1983_, 2, v_buildTime_1934_);
lean_ctor_set_uint8(v_reuseFailAlloc_1983_, sizeof(void*)*3 + 1, v_wantsRebuild_1931_);
lean_ctor_set_uint8(v_reuseFailAlloc_1983_, sizeof(void*)*3 + 2, v_canceled_1932_);
v___x_1966_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_object* v___x_1968_; 
lean_ctor_set_uint8(v___x_1966_, sizeof(void*)*3, v___x_1939_);
lean_inc(v_a_1951_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v_a_1951_);
v___x_1968_ = v___x_1963_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1951_);
v___x_1968_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1970_; 
if (v_isShared_1960_ == 0)
{
lean_ctor_set_tag(v___x_1959_, 1);
lean_ctor_set(v___x_1959_, 0, v___x_1968_);
v___x_1970_ = v___x_1959_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
lean_object* v___x_1971_; lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
v___x_1971_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_1942_, v___x_1970_, v___x_1966_);
lean_dec_ref(v___x_1970_);
lean_dec(v___x_1942_);
v_a_1972_ = lean_ctor_get(v___x_1971_, 1);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1979_ == 0)
{
lean_object* v_unused_1980_; 
v_unused_1980_ = lean_ctor_get(v___x_1971_, 0);
lean_dec(v_unused_1980_);
v___x_1974_ = v___x_1971_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1971_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 0, v_a_1951_);
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1951_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1992_; 
lean_del_object(v___x_1959_);
lean_dec(v_a_1951_);
v_a_1986_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_a_1986_);
lean_dec_ref_known(v___x_1961_, 1);
v___x_1987_ = lean_io_error_to_string(v_a_1986_);
v___x_1988_ = 3;
v___x_1989_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1989_, 0, v___x_1987_);
lean_ctor_set_uint8(v___x_1989_, sizeof(void*)*1, v___x_1988_);
v___x_1990_ = lean_array_push(v_a_1952_, v___x_1989_);
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v___x_1990_);
v___x_1992_ = v___x_1936_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_trace_1933_);
lean_ctor_set(v_reuseFailAlloc_1993_, 2, v_buildTime_1934_);
lean_ctor_set_uint8(v_reuseFailAlloc_1993_, sizeof(void*)*3 + 1, v_wantsRebuild_1931_);
lean_ctor_set_uint8(v_reuseFailAlloc_1993_, sizeof(void*)*3 + 2, v_canceled_1932_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_ctor_set_uint8(v___x_1992_, sizeof(void*)*3, v___x_1939_);
v_a_1944_ = v___x_1953_;
v_a_1945_ = v___x_1992_;
goto v___jp_1943_;
}
}
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2002_; 
lean_dec(v_a_1951_);
lean_dec_ref(v___x_1941_);
v_a_1996_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1996_);
lean_dec_ref_known(v___x_1957_, 1);
v___x_1997_ = lean_io_error_to_string(v_a_1996_);
v___x_1998_ = 3;
v___x_1999_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1999_, 0, v___x_1997_);
lean_ctor_set_uint8(v___x_1999_, sizeof(void*)*1, v___x_1998_);
v___x_2000_ = lean_array_push(v_a_1952_, v___x_1999_);
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v___x_2000_);
v___x_2002_ = v___x_1936_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_trace_1933_);
lean_ctor_set(v_reuseFailAlloc_2003_, 2, v_buildTime_1934_);
lean_ctor_set_uint8(v_reuseFailAlloc_2003_, sizeof(void*)*3 + 1, v_wantsRebuild_1931_);
lean_ctor_set_uint8(v_reuseFailAlloc_2003_, sizeof(void*)*3 + 2, v_canceled_1932_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
lean_ctor_set_uint8(v___x_2002_, sizeof(void*)*3, v___x_1939_);
v_a_1944_ = v___x_1953_;
v_a_1945_ = v___x_2002_;
goto v___jp_1943_;
}
}
}
else
{
lean_object* v_a_2004_; lean_object* v_a_2005_; lean_object* v___x_2007_; 
lean_dec_ref(v___x_1941_);
lean_dec_ref(v_traceFile_1907_);
v_a_2004_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_2004_);
v_a_2005_ = lean_ctor_get(v___x_1950_, 1);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_1950_, 2);
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v_a_2005_);
v___x_2007_ = v___x_1936_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2005_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_trace_1933_);
lean_ctor_set(v_reuseFailAlloc_2008_, 2, v_buildTime_1934_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*3 + 1, v_wantsRebuild_1931_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*3 + 2, v_canceled_1932_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*3, v___x_1939_);
v_a_1944_ = v_a_2004_;
v_a_1945_ = v___x_2007_;
goto v___jp_1943_;
}
}
v___jp_1943_:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v_a_1948_; 
v___x_1946_ = lean_box(0);
v___x_1947_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_1942_, v___x_1946_, v_a_1945_);
lean_dec(v___x_1942_);
v_a_1948_ = lean_ctor_get(v___x_1947_, 1);
lean_inc(v_a_1948_);
lean_dec_ref(v___x_1947_);
v_a_1913_ = v_a_1944_;
v_a_1914_ = v_a_1948_;
goto v___jp_1912_;
}
}
else
{
uint8_t v___x_2009_; 
lean_dec_ref(v_archiveFile_1904_);
lean_dec_ref(v_url_1903_);
v___x_2009_ = l_System_FilePath_pathExists(v_traceFile_1907_);
lean_dec_ref(v_traceFile_1907_);
if (v___x_2009_ == 0)
{
lean_dec_ref(v___x_1941_);
lean_del_object(v___x_1936_);
v_log_1917_ = v_log_1929_;
v_action_1918_ = v___x_1939_;
v_wantsRebuild_1919_ = v_noBuild_1938_;
v_canceled_1920_ = v_canceled_1932_;
v_trace_1921_ = v_trace_1933_;
v_buildTime_1922_ = v_buildTime_1934_;
goto v___jp_1916_;
}
else
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2010_ = lean_box(0);
v___x_2011_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_2012_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1906_, v___x_2010_, v___x_2011_);
v___x_2013_ = l_Lake_BuildMetadata_writeFile(v___x_1941_, v___x_2012_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_dec_ref_known(v___x_2013_, 1);
lean_del_object(v___x_1936_);
v_log_1917_ = v_log_1929_;
v_action_1918_ = v___x_1939_;
v_wantsRebuild_1919_ = v_noBuild_1938_;
v_canceled_1920_ = v_canceled_1932_;
v_trace_1921_ = v_trace_1933_;
v_buildTime_1922_ = v_buildTime_1934_;
goto v___jp_1916_;
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2015_; uint8_t v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2021_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2013_, 1);
v___x_2015_ = lean_io_error_to_string(v_a_2014_);
v___x_2016_ = 3;
v___x_2017_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2017_, 0, v___x_2015_);
lean_ctor_set_uint8(v___x_2017_, sizeof(void*)*1, v___x_2016_);
v___x_2018_ = lean_array_get_size(v_log_1929_);
v___x_2019_ = lean_array_push(v_log_1929_, v___x_2017_);
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v___x_2019_);
v___x_2021_ = v___x_1936_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_trace_1933_);
lean_ctor_set(v_reuseFailAlloc_2023_, 2, v_buildTime_1934_);
lean_ctor_set_uint8(v_reuseFailAlloc_2023_, sizeof(void*)*3 + 2, v_canceled_1932_);
v___x_2021_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2022_; 
lean_ctor_set_uint8(v___x_2021_, sizeof(void*)*3, v___x_1939_);
lean_ctor_set_uint8(v___x_2021_, sizeof(void*)*3 + 1, v_noBuild_1938_);
v___x_2022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2018_);
lean_ctor_set(v___x_2022_, 1, v___x_2021_);
return v___x_2022_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___boxed(lean_object* v_url_2025_, lean_object* v_archiveFile_2026_, lean_object* v_headers_2027_, lean_object* v_depTrace_2028_, lean_object* v_traceFile_2029_, lean_object* v_action_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_){
_start:
{
uint8_t v_action_boxed_2034_; lean_object* v_res_2035_; 
v_action_boxed_2034_ = lean_unbox(v_action_2030_);
v_res_2035_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_2025_, v_archiveFile_2026_, v_headers_2027_, v_depTrace_2028_, v_traceFile_2029_, v_action_boxed_2034_, v_a_2031_, v_a_2032_);
lean_dec_ref(v_a_2031_);
lean_dec_ref(v_depTrace_2028_);
lean_dec_ref(v_headers_2027_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(lean_object* v_url_2036_, lean_object* v_archiveFile_2037_, lean_object* v_headers_2038_, lean_object* v_a_2039_, lean_object* v_depTrace_2040_, lean_object* v_traceFile_2041_, uint8_t v_action_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_2036_, v_archiveFile_2037_, v_headers_2038_, v_depTrace_2040_, v_traceFile_2041_, v_action_2042_, v_a_2046_, v_a_2047_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___boxed(lean_object* v_url_2050_, lean_object* v_archiveFile_2051_, lean_object* v_headers_2052_, lean_object* v_a_2053_, lean_object* v_depTrace_2054_, lean_object* v_traceFile_2055_, lean_object* v_action_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_){
_start:
{
uint8_t v_action_boxed_2063_; lean_object* v_res_2064_; 
v_action_boxed_2063_ = lean_unbox(v_action_2056_);
v_res_2064_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(v_url_2050_, v_archiveFile_2051_, v_headers_2052_, v_a_2053_, v_depTrace_2054_, v_traceFile_2055_, v_action_boxed_2063_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_);
lean_dec_ref(v_a_2060_);
lean_dec(v_a_2059_);
lean_dec(v_a_2058_);
lean_dec(v_a_2057_);
lean_dec_ref(v_depTrace_2054_);
lean_dec_ref(v_a_2053_);
lean_dec_ref(v_headers_2052_);
return v_res_2064_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(lean_object* v_info_2065_, lean_object* v_self_2066_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = lean_io_metadata(v_info_2065_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; lean_object* v_modified_2070_; uint8_t v___x_2071_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_a_2069_);
lean_dec_ref_known(v___x_2068_, 1);
v_modified_2070_ = lean_ctor_get(v_a_2069_, 1);
lean_inc_ref(v_modified_2070_);
lean_dec(v_a_2069_);
v___x_2071_ = l_IO_FS_instOrdSystemTime_ord(v_self_2066_, v_modified_2070_);
lean_dec_ref(v_modified_2070_);
if (v___x_2071_ == 0)
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
uint8_t v___x_2074_; 
lean_dec_ref_known(v___x_2068_, 1);
v___x_2074_ = 0;
return v___x_2074_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___boxed(lean_object* v_info_2075_, lean_object* v_self_2076_, lean_object* v_a_2077_){
_start:
{
uint8_t v_res_2078_; lean_object* v_r_2079_; 
v_res_2078_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_2075_, v_self_2076_);
lean_dec_ref(v_self_2076_);
lean_dec_ref(v_info_2075_);
v_r_2079_ = lean_box(v_res_2078_);
return v_r_2079_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(lean_object* v_x_2080_, lean_object* v_x_2081_){
_start:
{
if (lean_obj_tag(v_x_2080_) == 0)
{
if (lean_obj_tag(v_x_2081_) == 0)
{
uint8_t v___x_2082_; 
v___x_2082_ = 1;
return v___x_2082_;
}
else
{
uint8_t v___x_2083_; 
v___x_2083_ = 0;
return v___x_2083_;
}
}
else
{
if (lean_obj_tag(v_x_2081_) == 0)
{
uint8_t v___x_2084_; 
v___x_2084_ = 0;
return v___x_2084_;
}
else
{
lean_object* v_val_2085_; lean_object* v_val_2086_; uint64_t v___x_2087_; uint64_t v___x_2088_; uint8_t v___x_2089_; 
v_val_2085_ = lean_ctor_get(v_x_2080_, 0);
v_val_2086_ = lean_ctor_get(v_x_2081_, 0);
v___x_2087_ = lean_unbox_uint64(v_val_2085_);
v___x_2088_ = lean_unbox_uint64(v_val_2086_);
v___x_2089_ = lean_uint64_dec_eq(v___x_2087_, v___x_2088_);
return v___x_2089_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2090_, lean_object* v_x_2091_){
_start:
{
uint8_t v_res_2092_; lean_object* v_r_2093_; 
v_res_2092_ = l_instBEqOption_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v_x_2090_, v_x_2091_);
lean_dec(v_x_2091_);
lean_dec(v_x_2090_);
v_r_2093_ = lean_box(v_res_2092_);
return v_r_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(lean_object* v_info_2094_, lean_object* v_depTrace_2095_, lean_object* v_depHash_2096_, lean_object* v_oldTrace_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_){
_start:
{
uint64_t v_hash_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; uint8_t v___x_2104_; 
v_hash_2101_ = lean_ctor_get_uint64(v_depTrace_2095_, sizeof(void*)*3);
v___x_2102_ = lean_box_uint64(v_hash_2101_);
v___x_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
v___x_2104_ = l_instBEqOption_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v___x_2103_, v_depHash_2096_);
lean_dec_ref_known(v___x_2103_, 1);
if (v___x_2104_ == 0)
{
lean_object* v_toBuildConfig_2105_; uint8_t v_oldMode_2106_; 
v_toBuildConfig_2105_ = lean_ctor_get(v_a_2098_, 0);
v_oldMode_2106_ = lean_ctor_get_uint8(v_toBuildConfig_2105_, sizeof(void*)*5);
if (v_oldMode_2106_ == 0)
{
uint8_t v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2107_ = 0;
v___x_2108_ = lean_box(v___x_2107_);
v___x_2109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
lean_ctor_set(v___x_2109_, 1, v_a_2099_);
return v___x_2109_;
}
else
{
uint8_t v___x_2110_; 
v___x_2110_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_2094_, v_oldTrace_2097_);
if (v___x_2110_ == 0)
{
uint8_t v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2111_ = 0;
v___x_2112_ = lean_box(v___x_2111_);
v___x_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
lean_ctor_set(v___x_2113_, 1, v_a_2099_);
return v___x_2113_;
}
else
{
uint8_t v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2114_ = 1;
v___x_2115_ = lean_box(v___x_2114_);
v___x_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
lean_ctor_set(v___x_2116_, 1, v_a_2099_);
return v___x_2116_;
}
}
}
else
{
uint8_t v___x_2117_; 
v___x_2117_ = l_System_FilePath_pathExists(v_info_2094_);
if (v___x_2117_ == 0)
{
uint8_t v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2118_ = 0;
v___x_2119_ = lean_box(v___x_2118_);
v___x_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
lean_ctor_set(v___x_2120_, 1, v_a_2099_);
return v___x_2120_;
}
else
{
uint8_t v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2121_ = 2;
v___x_2122_ = lean_box(v___x_2121_);
v___x_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
lean_ctor_set(v___x_2123_, 1, v_a_2099_);
return v___x_2123_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg___boxed(lean_object* v_info_2124_, lean_object* v_depTrace_2125_, lean_object* v_depHash_2126_, lean_object* v_oldTrace_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_2124_, v_depTrace_2125_, v_depHash_2126_, v_oldTrace_2127_, v_a_2128_, v_a_2129_);
lean_dec_ref(v_a_2128_);
lean_dec_ref(v_oldTrace_2127_);
lean_dec(v_depHash_2126_);
lean_dec_ref(v_depTrace_2125_);
lean_dec_ref(v_info_2124_);
return v_res_2131_;
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
lean_object* v___y_2159_; lean_object* v___x_2163_; lean_object* v___x_2164_; uint8_t v___x_2165_; 
v___x_2163_ = lean_obj_tag_nat(v_a_2153_);
v___x_2164_ = lean_unsigned_to_nat(0u);
v___x_2165_ = lean_nat_dec_eq(v___x_2163_, v___x_2164_);
if (v___x_2165_ == 0)
{
lean_object* v_log_2166_; uint8_t v_action_2167_; uint8_t v_wantsRebuild_2168_; uint8_t v_canceled_2169_; lean_object* v_trace_2170_; lean_object* v_buildTime_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2191_; 
v_log_2166_ = lean_ctor_get(v_a_2154_, 0);
v_action_2167_ = lean_ctor_get_uint8(v_a_2154_, sizeof(void*)*3);
v_wantsRebuild_2168_ = lean_ctor_get_uint8(v_a_2154_, sizeof(void*)*3 + 1);
v_canceled_2169_ = lean_ctor_get_uint8(v_a_2154_, sizeof(void*)*3 + 2);
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
lean_inc(v_log_2166_);
lean_dec(v_a_2154_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2191_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
uint8_t v___x_2175_; uint8_t v___x_2176_; lean_object* v___x_2178_; 
v___x_2175_ = 2;
v___x_2176_ = l_Lake_JobAction_merge(v_action_2167_, v___x_2175_);
if (v_isShared_2174_ == 0)
{
v___x_2178_ = v___x_2173_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_log_2166_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v_trace_2170_);
lean_ctor_set(v_reuseFailAlloc_2190_, 2, v_buildTime_2171_);
lean_ctor_set_uint8(v_reuseFailAlloc_2190_, sizeof(void*)*3 + 1, v_wantsRebuild_2168_);
lean_ctor_set_uint8(v_reuseFailAlloc_2190_, sizeof(void*)*3 + 2, v_canceled_2169_);
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
v_oldMode_2196_ = lean_ctor_get_uint8(v_toBuildConfig_2195_, sizeof(void*)*5);
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
uint8_t v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; uint8_t v___y_2244_; uint8_t v___y_2245_; lean_object* v___y_2246_; uint8_t v_a_2272_; lean_object* v_a_2273_; lean_object* v_a_2289_; lean_object* v_a_2290_; lean_object* v_log_2292_; uint8_t v_action_2293_; uint8_t v_wantsRebuild_2294_; uint8_t v_canceled_2295_; lean_object* v_trace_2296_; lean_object* v_buildTime_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2336_; 
v_log_2292_ = lean_ctor_get(v_a_2237_, 0);
v_action_2293_ = lean_ctor_get_uint8(v_a_2237_, sizeof(void*)*3);
v_wantsRebuild_2294_ = lean_ctor_get_uint8(v_a_2237_, sizeof(void*)*3 + 1);
v_canceled_2295_ = lean_ctor_get_uint8(v_a_2237_, sizeof(void*)*3 + 2);
v_trace_2296_ = lean_ctor_get(v_a_2237_, 1);
v_buildTime_2297_ = lean_ctor_get(v_a_2237_, 2);
v_isSharedCheck_2336_ = !lean_is_exclusive(v_a_2237_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2299_ = v_a_2237_;
v_isShared_2300_ = v_isSharedCheck_2336_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_buildTime_2297_);
lean_inc(v_trace_2296_);
lean_inc(v_log_2292_);
lean_dec(v_a_2237_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2336_;
goto v_resetjp_2298_;
}
v___jp_2239_:
{
uint8_t v___x_2247_; uint8_t v___x_2248_; uint8_t v___x_2249_; lean_object* v___x_2250_; 
v___x_2247_ = 1;
v___x_2248_ = 3;
v___x_2249_ = l_Lake_JobAction_merge(v___y_2240_, v___x_2248_);
v___x_2250_ = l_Lake_untar(v_archiveFile_2230_, v___y_2241_, v___x_2247_, v___y_2243_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v_a_2251_; lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2260_; 
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
v_a_2252_ = lean_ctor_get(v___x_2250_, 1);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2254_ = v___x_2250_;
v_isShared_2255_ = v_isSharedCheck_2260_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_inc(v_a_2251_);
lean_dec(v___x_2250_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2260_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2256_; lean_object* v___x_2258_; 
v___x_2256_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2256_, 0, v_a_2252_);
lean_ctor_set(v___x_2256_, 1, v___y_2246_);
lean_ctor_set(v___x_2256_, 2, v___y_2242_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*3, v___x_2249_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*3 + 1, v___y_2245_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*3 + 2, v___y_2244_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 1, v___x_2256_);
v___x_2258_ = v___x_2254_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 2, 0);
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
else
{
lean_object* v_a_2261_; lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2270_; 
v_a_2261_ = lean_ctor_get(v___x_2250_, 0);
v_a_2262_ = lean_ctor_get(v___x_2250_, 1);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2264_ = v___x_2250_;
v_isShared_2265_ = v_isSharedCheck_2270_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_inc(v_a_2261_);
lean_dec(v___x_2250_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2270_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v___x_2268_; 
v___x_2266_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2266_, 0, v_a_2262_);
lean_ctor_set(v___x_2266_, 1, v___y_2246_);
lean_ctor_set(v___x_2266_, 2, v___y_2242_);
lean_ctor_set_uint8(v___x_2266_, sizeof(void*)*3, v___x_2249_);
lean_ctor_set_uint8(v___x_2266_, sizeof(void*)*3 + 1, v___y_2245_);
lean_ctor_set_uint8(v___x_2266_, sizeof(void*)*3 + 2, v___y_2244_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 1, v___x_2266_);
v___x_2268_ = v___x_2264_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2261_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v___x_2266_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
v___jp_2271_:
{
lean_object* v_config_2274_; lean_object* v_dir_2275_; lean_object* v_buildDir_2276_; lean_object* v_log_2277_; uint8_t v_action_2278_; uint8_t v_wantsRebuild_2279_; uint8_t v_canceled_2280_; lean_object* v_trace_2281_; lean_object* v_buildTime_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; uint8_t v___x_2285_; 
v_config_2274_ = lean_ctor_get(v_self_2228_, 6);
lean_inc_ref(v_config_2274_);
v_dir_2275_ = lean_ctor_get(v_self_2228_, 4);
lean_inc_ref(v_dir_2275_);
lean_dec_ref(v_self_2228_);
v_buildDir_2276_ = lean_ctor_get(v_config_2274_, 5);
lean_inc_ref(v_buildDir_2276_);
lean_dec_ref(v_config_2274_);
v_log_2277_ = lean_ctor_get(v_a_2273_, 0);
v_action_2278_ = lean_ctor_get_uint8(v_a_2273_, sizeof(void*)*3);
v_wantsRebuild_2279_ = lean_ctor_get_uint8(v_a_2273_, sizeof(void*)*3 + 1);
v_canceled_2280_ = lean_ctor_get_uint8(v_a_2273_, sizeof(void*)*3 + 2);
v_trace_2281_ = lean_ctor_get(v_a_2273_, 1);
v_buildTime_2282_ = lean_ctor_get(v_a_2273_, 2);
v___x_2283_ = l_System_FilePath_normalize(v_buildDir_2276_);
v___x_2284_ = l_Lake_joinRelative(v_dir_2275_, v___x_2283_);
v___x_2285_ = l_System_FilePath_pathExists(v___x_2284_);
if (v_a_2272_ == 0)
{
lean_inc(v_buildTime_2282_);
lean_inc_ref(v_trace_2281_);
lean_inc_ref(v_log_2277_);
lean_dec_ref(v_a_2273_);
v___y_2240_ = v_action_2278_;
v___y_2241_ = v___x_2284_;
v___y_2242_ = v_buildTime_2282_;
v___y_2243_ = v_log_2277_;
v___y_2244_ = v_canceled_2280_;
v___y_2245_ = v_wantsRebuild_2279_;
v___y_2246_ = v_trace_2281_;
goto v___jp_2239_;
}
else
{
if (v___x_2285_ == 0)
{
lean_inc(v_buildTime_2282_);
lean_inc_ref(v_trace_2281_);
lean_inc_ref(v_log_2277_);
lean_dec_ref(v_a_2273_);
v___y_2240_ = v_action_2278_;
v___y_2241_ = v___x_2284_;
v___y_2242_ = v_buildTime_2282_;
v___y_2243_ = v_log_2277_;
v___y_2244_ = v_canceled_2280_;
v___y_2245_ = v_wantsRebuild_2279_;
v___y_2246_ = v_trace_2281_;
goto v___jp_2239_;
}
else
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
lean_dec_ref(v___x_2284_);
lean_dec_ref(v_archiveFile_2230_);
v___x_2286_ = lean_box(0);
v___x_2287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
lean_ctor_set(v___x_2287_, 1, v_a_2273_);
return v___x_2287_;
}
}
}
v___jp_2288_:
{
lean_object* v___x_2291_; 
v___x_2291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2291_, 0, v_a_2289_);
lean_ctor_set(v___x_2291_, 1, v_a_2290_);
return v___x_2291_;
}
v_resetjp_2298_:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; uint64_t v___x_2303_; uint64_t v___x_2304_; uint64_t v_depTrace_2305_; lean_object* v___x_2306_; lean_object* v_traceFile_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; lean_object* v___x_2312_; 
v___x_2301_ = lean_unsigned_to_nat(0u);
v___x_2302_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0));
v___x_2303_ = l_Lake_Hash_nil;
v___x_2304_ = lean_string_hash(v_url_2229_);
v_depTrace_2305_ = lean_uint64_mix_hash(v___x_2303_, v___x_2304_);
v___x_2306_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1));
lean_inc_ref(v_archiveFile_2230_);
v_traceFile_2307_ = l_System_FilePath_addExtension(v_archiveFile_2230_, v___x_2306_);
v___x_2308_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2));
v___x_2309_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4, &l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4_once, _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4);
v___x_2310_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_2310_, 0, v___x_2308_);
lean_ctor_set(v___x_2310_, 1, v___x_2302_);
lean_ctor_set(v___x_2310_, 2, v___x_2309_);
lean_ctor_set_uint64(v___x_2310_, sizeof(void*)*3, v_depTrace_2305_);
v___x_2311_ = 4;
lean_inc_ref(v_traceFile_2307_);
v___x_2312_ = l_Lake_readTraceFile(v_traceFile_2307_, v_log_2292_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v_a_2314_; lean_object* v___x_2316_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2313_);
v_a_2314_ = lean_ctor_get(v___x_2312_, 1);
lean_inc(v_a_2314_);
lean_dec_ref_known(v___x_2312_, 2);
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 0, v_a_2314_);
v___x_2316_ = v___x_2299_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2314_);
lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_trace_2296_);
lean_ctor_set(v_reuseFailAlloc_2330_, 2, v_buildTime_2297_);
lean_ctor_set_uint8(v_reuseFailAlloc_2330_, sizeof(void*)*3, v_action_2293_);
lean_ctor_set_uint8(v_reuseFailAlloc_2330_, sizeof(void*)*3 + 1, v_wantsRebuild_2294_);
lean_ctor_set_uint8(v_reuseFailAlloc_2330_, sizeof(void*)*3 + 2, v_canceled_2295_);
v___x_2316_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
lean_object* v___x_2317_; 
v___x_2317_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_2232_, v_archiveFile_2230_, v___x_2310_, v_a_2313_, v___x_2309_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v___x_2316_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v_a_2319_; lean_object* v___x_2320_; uint8_t v___x_2321_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2318_);
v_a_2319_ = lean_ctor_get(v___x_2317_, 1);
lean_inc(v_a_2319_);
lean_dec_ref_known(v___x_2317_, 2);
v___x_2320_ = lean_obj_tag_nat(v_a_2318_);
lean_dec(v_a_2318_);
v___x_2321_ = lean_nat_dec_eq(v___x_2320_, v___x_2301_);
if (v___x_2321_ == 0)
{
uint8_t v___x_2322_; 
lean_dec_ref_known(v___x_2310_, 3);
lean_dec_ref(v_traceFile_2307_);
lean_dec_ref(v_url_2229_);
v___x_2322_ = 1;
v_a_2272_ = v___x_2322_;
v_a_2273_ = v_a_2319_;
goto v___jp_2271_;
}
else
{
uint8_t v___x_2323_; lean_object* v___x_2324_; 
v___x_2323_ = 0;
lean_inc_ref(v_archiveFile_2230_);
v___x_2324_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_2229_, v_archiveFile_2230_, v_headers_2231_, v___x_2310_, v_traceFile_2307_, v___x_2311_, v_a_2236_, v_a_2319_);
lean_dec_ref_known(v___x_2310_, 3);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 1);
lean_inc(v_a_2325_);
lean_dec_ref_known(v___x_2324_, 2);
v_a_2272_ = v___x_2323_;
v_a_2273_ = v_a_2325_;
goto v___jp_2271_;
}
else
{
lean_object* v_a_2326_; lean_object* v_a_2327_; 
lean_dec_ref(v_archiveFile_2230_);
lean_dec_ref(v_self_2228_);
v_a_2326_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2326_);
v_a_2327_ = lean_ctor_get(v___x_2324_, 1);
lean_inc(v_a_2327_);
lean_dec_ref_known(v___x_2324_, 2);
v_a_2289_ = v_a_2326_;
v_a_2290_ = v_a_2327_;
goto v___jp_2288_;
}
}
}
else
{
lean_object* v_a_2328_; lean_object* v_a_2329_; 
lean_dec_ref_known(v___x_2310_, 3);
lean_dec_ref(v_traceFile_2307_);
lean_dec_ref(v_archiveFile_2230_);
lean_dec_ref(v_url_2229_);
lean_dec_ref(v_self_2228_);
v_a_2328_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2328_);
v_a_2329_ = lean_ctor_get(v___x_2317_, 1);
lean_inc(v_a_2329_);
lean_dec_ref_known(v___x_2317_, 2);
v_a_2289_ = v_a_2328_;
v_a_2290_ = v_a_2329_;
goto v___jp_2288_;
}
}
}
else
{
lean_object* v_a_2331_; lean_object* v_a_2332_; lean_object* v___x_2334_; 
lean_dec_ref_known(v___x_2310_, 3);
lean_dec_ref(v_traceFile_2307_);
lean_dec_ref(v_archiveFile_2230_);
lean_dec_ref(v_url_2229_);
lean_dec_ref(v_self_2228_);
v_a_2331_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2331_);
v_a_2332_ = lean_ctor_get(v___x_2312_, 1);
lean_inc(v_a_2332_);
lean_dec_ref_known(v___x_2312_, 2);
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 0, v_a_2332_);
v___x_2334_ = v___x_2299_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_a_2332_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_trace_2296_);
lean_ctor_set(v_reuseFailAlloc_2335_, 2, v_buildTime_2297_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, sizeof(void*)*3, v_action_2293_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, sizeof(void*)*3 + 1, v_wantsRebuild_2294_);
lean_ctor_set_uint8(v_reuseFailAlloc_2335_, sizeof(void*)*3 + 2, v_canceled_2295_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
v_a_2289_ = v_a_2331_;
v_a_2290_ = v___x_2334_;
goto v___jp_2288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___boxed(lean_object* v_self_2337_, lean_object* v_url_2338_, lean_object* v_archiveFile_2339_, lean_object* v_headers_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_self_2337_, v_url_2338_, v_archiveFile_2339_, v_headers_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_);
lean_dec_ref(v_a_2345_);
lean_dec(v_a_2344_);
lean_dec(v_a_2343_);
lean_dec(v_a_2342_);
lean_dec_ref(v_a_2341_);
lean_dec_ref(v_headers_2340_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(lean_object* v_a_2349_, lean_object* v_info_2350_, lean_object* v_depTrace_2351_, lean_object* v_depHash_2352_, lean_object* v_oldTrace_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_2350_, v_depTrace_2351_, v_depHash_2352_, v_oldTrace_2353_, v_a_2357_, v_a_2358_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___boxed(lean_object* v_a_2361_, lean_object* v_info_2362_, lean_object* v_depTrace_2363_, lean_object* v_depHash_2364_, lean_object* v_oldTrace_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(v_a_2361_, v_info_2362_, v_depTrace_2363_, v_depHash_2364_, v_oldTrace_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec_ref(v_a_2369_);
lean_dec(v_a_2368_);
lean_dec(v_a_2367_);
lean_dec(v_a_2366_);
lean_dec_ref(v_oldTrace_2365_);
lean_dec(v_depHash_2364_);
lean_dec_ref(v_depTrace_2363_);
lean_dec_ref(v_info_2362_);
lean_dec_ref(v_a_2361_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(lean_object* v_getUrl_2373_, lean_object* v_pkg_2374_, lean_object* v_archiveFile_2375_, lean_object* v_headers_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
uint8_t v_r_2385_; lean_object* v___y_2386_; lean_object* v_a_2390_; lean_object* v___x_2407_; 
lean_inc_ref(v___y_2381_);
lean_inc(v___y_2380_);
lean_inc(v___y_2379_);
lean_inc(v___y_2378_);
lean_inc_ref(v___y_2377_);
lean_inc_ref(v_pkg_2374_);
v___x_2407_ = lean_apply_8(v_getUrl_2373_, v_pkg_2374_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, lean_box(0));
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v_a_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
v_a_2409_ = lean_ctor_get(v___x_2407_, 1);
lean_inc(v_a_2409_);
lean_dec_ref_known(v___x_2407_, 2);
lean_inc_ref(v_pkg_2374_);
v___x_2410_ = lean_apply_1(v_archiveFile_2375_, v_pkg_2374_);
v___x_2411_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_2374_, v_a_2408_, v___x_2410_, v_headers_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v_a_2409_);
lean_dec_ref(v___y_2377_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; uint8_t v___x_2413_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 1);
lean_inc(v_a_2412_);
lean_dec_ref_known(v___x_2411_, 2);
v___x_2413_ = 1;
v_r_2385_ = v___x_2413_;
v___y_2386_ = v_a_2412_;
goto v___jp_2384_;
}
else
{
lean_object* v_a_2414_; 
v_a_2414_ = lean_ctor_get(v___x_2411_, 1);
lean_inc(v_a_2414_);
lean_dec_ref_known(v___x_2411_, 2);
v_a_2390_ = v_a_2414_;
goto v___jp_2389_;
}
}
else
{
lean_object* v_a_2415_; 
lean_dec_ref(v___y_2377_);
lean_dec_ref(v_archiveFile_2375_);
lean_dec_ref(v_pkg_2374_);
v_a_2415_ = lean_ctor_get(v___x_2407_, 1);
lean_inc(v_a_2415_);
lean_dec_ref_known(v___x_2407_, 2);
v_a_2390_ = v_a_2415_;
goto v___jp_2389_;
}
v___jp_2384_:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = lean_box(v_r_2385_);
v___x_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
lean_ctor_set(v___x_2388_, 1, v___y_2386_);
return v___x_2388_;
}
v___jp_2389_:
{
lean_object* v_log_2391_; uint8_t v_action_2392_; uint8_t v_wantsRebuild_2393_; uint8_t v_canceled_2394_; lean_object* v_trace_2395_; lean_object* v_buildTime_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2406_; 
v_log_2391_ = lean_ctor_get(v_a_2390_, 0);
v_action_2392_ = lean_ctor_get_uint8(v_a_2390_, sizeof(void*)*3);
v_wantsRebuild_2393_ = lean_ctor_get_uint8(v_a_2390_, sizeof(void*)*3 + 1);
v_canceled_2394_ = lean_ctor_get_uint8(v_a_2390_, sizeof(void*)*3 + 2);
v_trace_2395_ = lean_ctor_get(v_a_2390_, 1);
v_buildTime_2396_ = lean_ctor_get(v_a_2390_, 2);
v_isSharedCheck_2406_ = !lean_is_exclusive(v_a_2390_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2398_ = v_a_2390_;
v_isShared_2399_ = v_isSharedCheck_2406_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_buildTime_2396_);
lean_inc(v_trace_2395_);
lean_inc(v_log_2391_);
lean_dec(v_a_2390_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2406_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
uint8_t v___x_2400_; uint8_t v___x_2401_; lean_object* v___x_2403_; 
v___x_2400_ = 4;
v___x_2401_ = l_Lake_JobAction_merge(v_action_2392_, v___x_2400_);
if (v_isShared_2399_ == 0)
{
v___x_2403_ = v___x_2398_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_log_2391_);
lean_ctor_set(v_reuseFailAlloc_2405_, 1, v_trace_2395_);
lean_ctor_set(v_reuseFailAlloc_2405_, 2, v_buildTime_2396_);
lean_ctor_set_uint8(v_reuseFailAlloc_2405_, sizeof(void*)*3 + 1, v_wantsRebuild_2393_);
lean_ctor_set_uint8(v_reuseFailAlloc_2405_, sizeof(void*)*3 + 2, v_canceled_2394_);
v___x_2403_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
uint8_t v___x_2404_; 
lean_ctor_set_uint8(v___x_2403_, sizeof(void*)*3, v___x_2401_);
v___x_2404_ = 0;
v_r_2385_ = v___x_2404_;
v___y_2386_ = v___x_2403_;
goto v___jp_2384_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* v_getUrl_2416_, lean_object* v_pkg_2417_, lean_object* v_archiveFile_2418_, lean_object* v_headers_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(v_getUrl_2416_, v_pkg_2417_, v_archiveFile_2418_, v_headers_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v_headers_2419_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(lean_object* v_getUrl_2428_, lean_object* v_archiveFile_2429_, lean_object* v_headers_2430_, lean_object* v_facet_2431_, lean_object* v___x_2432_, lean_object* v_pkg_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v_baseName_2441_; lean_object* v___f_2442_; uint8_t v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v_baseName_2441_ = lean_ctor_get(v_pkg_2433_, 1);
lean_inc(v_baseName_2441_);
v___f_2442_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2442_, 0, v_getUrl_2428_);
lean_closure_set(v___f_2442_, 1, v_pkg_2433_);
lean_closure_set(v___f_2442_, 2, v_archiveFile_2429_);
lean_closure_set(v___f_2442_, 3, v_headers_2430_);
v___x_2443_ = 1;
v___x_2444_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2441_, v___x_2443_);
v___x_2445_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2446_ = lean_string_append(v___x_2444_, v___x_2445_);
v___x_2447_ = l_Lake_Name_eraseHead(v_facet_2431_);
v___x_2448_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2447_, v___x_2443_);
v___x_2449_ = lean_string_append(v___x_2446_, v___x_2448_);
lean_dec_ref(v___x_2448_);
v___x_2450_ = lean_unsigned_to_nat(0u);
v___x_2451_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_2432_);
v___x_2452_ = lean_alloc_closure((void*)(l_Lake_Job_async___boxed), 12, 5);
lean_closure_set(v___x_2452_, 0, lean_box(0));
lean_closure_set(v___x_2452_, 1, v___x_2432_);
lean_closure_set(v___x_2452_, 2, v___f_2442_);
lean_closure_set(v___x_2452_, 3, v___x_2450_);
lean_closure_set(v___x_2452_, 4, v___x_2451_);
v___x_2453_ = lean_alloc_closure((void*)(l_Lake_JobM_runSpawnM___boxed), 9, 2);
lean_closure_set(v___x_2453_, 0, lean_box(0));
lean_closure_set(v___x_2453_, 1, v___x_2452_);
v___x_2454_ = lean_alloc_closure((void*)(l_Lake_FetchM_runJobM___boxed), 9, 2);
lean_closure_set(v___x_2454_, 0, lean_box(0));
lean_closure_set(v___x_2454_, 1, v___x_2453_);
v___x_2455_ = l_Lake_ensureJob___redArg(v___x_2432_, v___x_2454_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2480_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
v_a_2457_ = lean_ctor_get(v___x_2455_, 1);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2459_ = v___x_2455_;
v_isShared_2460_ = v_isSharedCheck_2480_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_inc(v_a_2456_);
lean_dec(v___x_2455_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2480_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v_task_2461_; lean_object* v_kind_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2478_; 
v_task_2461_ = lean_ctor_get(v_a_2456_, 0);
v_kind_2462_ = lean_ctor_get(v_a_2456_, 1);
v_isSharedCheck_2478_ = !lean_is_exclusive(v_a_2456_);
if (v_isSharedCheck_2478_ == 0)
{
lean_object* v_unused_2479_; 
v_unused_2479_ = lean_ctor_get(v_a_2456_, 2);
lean_dec(v_unused_2479_);
v___x_2464_ = v_a_2456_;
v_isShared_2465_ = v_isSharedCheck_2478_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_kind_2462_);
lean_inc(v_task_2461_);
lean_dec(v_a_2456_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2478_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v_registeredJobs_2466_; lean_object* v_job_2468_; 
v_registeredJobs_2466_ = lean_ctor_get(v___y_2438_, 4);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 2, v___x_2449_);
v_job_2468_ = v___x_2464_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_task_2461_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v_kind_2462_);
lean_ctor_set(v_reuseFailAlloc_2477_, 2, v___x_2449_);
v_job_2468_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2475_; 
lean_ctor_set_uint8(v_job_2468_, sizeof(void*)*3, v___x_2443_);
v___x_2469_ = lean_st_ref_take(v_registeredJobs_2466_);
lean_inc_ref(v_job_2468_);
v___x_2470_ = l_Lake_Job_toOpaque___redArg(v_job_2468_);
v___x_2471_ = lean_array_push(v___x_2469_, v___x_2470_);
v___x_2472_ = lean_st_ref_put(v_registeredJobs_2466_, v___x_2471_);
v___x_2473_ = l_Lake_Job_renew___redArg(v_job_2468_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v___x_2473_);
v___x_2475_ = v___x_2459_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v_a_2457_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2449_);
return v___x_2455_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* v_getUrl_2481_, lean_object* v_archiveFile_2482_, lean_object* v_headers_2483_, lean_object* v_facet_2484_, lean_object* v___x_2485_, lean_object* v_pkg_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(v_getUrl_2481_, v_archiveFile_2482_, v_headers_2483_, v_facet_2484_, v___x_2485_, v_pkg_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec(v___y_2488_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg(lean_object* v_facet_2502_, lean_object* v_archiveFile_2503_, lean_object* v_getUrl_2504_, lean_object* v_headers_2505_){
_start:
{
lean_object* v___x_2506_; lean_object* v___f_2507_; lean_object* v___x_2508_; uint8_t v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2506_ = l_Lake_instDataKindBool;
v___f_2507_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2507_, 0, v_getUrl_2504_);
lean_closure_set(v___f_2507_, 1, v_archiveFile_2503_);
lean_closure_set(v___f_2507_, 2, v_headers_2505_);
lean_closure_set(v___f_2507_, 3, v_facet_2502_);
lean_closure_set(v___f_2507_, 4, v___x_2506_);
v___x_2508_ = l_Lake_Package_keyword;
v___x_2509_ = 1;
v___x_2510_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3));
v___x_2511_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2511_, 0, v___x_2508_);
lean_ctor_set(v___x_2511_, 1, v___f_2507_);
lean_ctor_set(v___x_2511_, 2, v___x_2506_);
lean_ctor_set(v___x_2511_, 3, v___x_2510_);
lean_ctor_set_uint8(v___x_2511_, sizeof(void*)*4, v___x_2509_);
lean_ctor_set_uint8(v___x_2511_, sizeof(void*)*4 + 1, v___x_2509_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig(lean_object* v_facet_2512_, lean_object* v_archiveFile_2513_, lean_object* v_getUrl_2514_, lean_object* v_headers_2515_, lean_object* v_inst_2516_){
_start:
{
lean_object* v___x_2517_; lean_object* v___f_2518_; lean_object* v___x_2519_; uint8_t v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2517_ = l_Lake_instDataKindBool;
v___f_2518_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2518_, 0, v_getUrl_2514_);
lean_closure_set(v___f_2518_, 1, v_archiveFile_2513_);
lean_closure_set(v___f_2518_, 2, v_headers_2515_);
lean_closure_set(v___f_2518_, 3, v_facet_2512_);
lean_closure_set(v___f_2518_, 4, v___x_2517_);
v___x_2519_ = l_Lake_Package_keyword;
v___x_2520_ = 1;
v___x_2521_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3));
v___x_2522_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2522_, 0, v___x_2519_);
lean_ctor_set(v___x_2522_, 1, v___f_2518_);
lean_ctor_set(v___x_2522_, 2, v___x_2517_);
lean_ctor_set(v___x_2522_, 3, v___x_2521_);
lean_ctor_set_uint8(v___x_2522_, sizeof(void*)*4, v___x_2520_);
lean_ctor_set_uint8(v___x_2522_, sizeof(void*)*4 + 1, v___x_2520_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(lean_object* v_what_2524_, lean_object* v_baseName_2525_, lean_object* v_optFacet_2526_, uint8_t v_success_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v_a_2536_; lean_object* v_a_2537_; 
if (v_success_2527_ == 0)
{
lean_object* v_toBuildConfig_2559_; uint8_t v_verbosity_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; uint8_t v___x_2564_; 
v_toBuildConfig_2559_ = lean_ctor_get(v___y_2532_, 0);
v_verbosity_2560_ = lean_ctor_get_uint8(v_toBuildConfig_2559_, sizeof(void*)*5 + 4);
v___x_2561_ = lean_box(v_verbosity_2560_);
v___x_2562_ = lean_obj_tag_nat(v___x_2561_);
lean_dec(v___x_2561_);
v___x_2563_ = lean_unsigned_to_nat(2u);
v___x_2564_ = lean_nat_dec_eq(v___x_2562_, v___x_2563_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2565_; 
lean_dec(v_optFacet_2526_);
lean_dec(v_baseName_2525_);
v___x_2565_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_2536_ = v___x_2565_;
v_a_2537_ = v___y_2533_;
goto v___jp_2535_;
}
else
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2566_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_2567_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2525_, v___x_2564_);
v___x_2568_ = lean_string_append(v___x_2566_, v___x_2567_);
lean_dec_ref(v___x_2567_);
v___x_2569_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2570_ = lean_string_append(v___x_2568_, v___x_2569_);
v___x_2571_ = l_Lake_Name_eraseHead(v_optFacet_2526_);
v___x_2572_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2571_, v___x_2564_);
v___x_2573_ = lean_string_append(v___x_2570_, v___x_2572_);
lean_dec_ref(v___x_2572_);
v___x_2574_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2575_ = lean_string_append(v___x_2573_, v___x_2574_);
v_a_2536_ = v___x_2575_;
v_a_2537_ = v___y_2533_;
goto v___jp_2535_;
}
}
else
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
lean_dec(v_optFacet_2526_);
lean_dec(v_baseName_2525_);
v___x_2576_ = lean_box(0);
v___x_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
lean_ctor_set(v___x_2577_, 1, v___y_2533_);
return v___x_2577_;
}
v___jp_2535_:
{
lean_object* v_log_2538_; uint8_t v_action_2539_; uint8_t v_wantsRebuild_2540_; uint8_t v_canceled_2541_; lean_object* v_trace_2542_; lean_object* v_buildTime_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2558_; 
v_log_2538_ = lean_ctor_get(v_a_2537_, 0);
v_action_2539_ = lean_ctor_get_uint8(v_a_2537_, sizeof(void*)*3);
v_wantsRebuild_2540_ = lean_ctor_get_uint8(v_a_2537_, sizeof(void*)*3 + 1);
v_canceled_2541_ = lean_ctor_get_uint8(v_a_2537_, sizeof(void*)*3 + 2);
v_trace_2542_ = lean_ctor_get(v_a_2537_, 1);
v_buildTime_2543_ = lean_ctor_get(v_a_2537_, 2);
v_isSharedCheck_2558_ = !lean_is_exclusive(v_a_2537_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2545_ = v_a_2537_;
v_isShared_2546_ = v_isSharedCheck_2558_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_buildTime_2543_);
lean_inc(v_trace_2542_);
lean_inc(v_log_2538_);
lean_dec(v_a_2537_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2558_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; uint8_t v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2555_; 
v___x_2547_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0));
v___x_2548_ = lean_string_append(v___x_2547_, v_what_2524_);
v___x_2549_ = lean_string_append(v___x_2548_, v_a_2536_);
lean_dec_ref(v_a_2536_);
v___x_2550_ = 3;
v___x_2551_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2551_, 0, v___x_2549_);
lean_ctor_set_uint8(v___x_2551_, sizeof(void*)*1, v___x_2550_);
v___x_2552_ = lean_array_get_size(v_log_2538_);
v___x_2553_ = lean_array_push(v_log_2538_, v___x_2551_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v___x_2553_);
v___x_2555_ = v___x_2545_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2553_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v_trace_2542_);
lean_ctor_set(v_reuseFailAlloc_2557_, 2, v_buildTime_2543_);
lean_ctor_set_uint8(v_reuseFailAlloc_2557_, sizeof(void*)*3, v_action_2539_);
lean_ctor_set_uint8(v_reuseFailAlloc_2557_, sizeof(void*)*3 + 1, v_wantsRebuild_2540_);
lean_ctor_set_uint8(v_reuseFailAlloc_2557_, sizeof(void*)*3 + 2, v_canceled_2541_);
v___x_2555_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
lean_object* v___x_2556_; 
v___x_2556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2552_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
return v___x_2556_;
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(lean_object* v_what_2635_, lean_object* v_optFacet_2636_, lean_object* v_facet_2637_, lean_object* v___x_2638_, lean_object* v_pkg_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v_baseName_2647_; lean_object* v_keyName_2648_; lean_object* v___f_2649_; uint8_t v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___f_2660_; uint8_t v___x_2661_; lean_object* v___x_2662_; 
v_baseName_2647_ = lean_ctor_get(v_pkg_2639_, 1);
v_keyName_2648_ = lean_ctor_get(v_pkg_2639_, 2);
lean_inc(v_optFacet_2636_);
lean_inc_n(v_baseName_2647_, 2);
v___f_2649_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 3);
lean_closure_set(v___f_2649_, 0, v_what_2635_);
lean_closure_set(v___f_2649_, 1, v_baseName_2647_);
lean_closure_set(v___f_2649_, 2, v_optFacet_2636_);
v___x_2650_ = 1;
v___x_2651_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2647_, v___x_2650_);
v___x_2652_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2653_ = lean_string_append(v___x_2651_, v___x_2652_);
v___x_2654_ = l_Lake_Name_eraseHead(v_facet_2637_);
v___x_2655_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2654_, v___x_2650_);
v___x_2656_ = lean_string_append(v___x_2653_, v___x_2655_);
lean_dec_ref(v___x_2655_);
lean_inc(v_keyName_2648_);
v___x_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2657_, 0, v_keyName_2648_);
v___x_2658_ = l_Lake_Package_keyword;
v___x_2659_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2657_);
lean_ctor_set(v___x_2659_, 1, v___x_2658_);
lean_ctor_set(v___x_2659_, 2, v_pkg_2639_);
lean_ctor_set(v___x_2659_, 3, v_optFacet_2636_);
lean_inc(v___x_2638_);
v___f_2660_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2660_, 0, v___x_2659_);
lean_closure_set(v___f_2660_, 1, v___x_2638_);
lean_closure_set(v___f_2660_, 2, v___f_2649_);
v___x_2661_ = 0;
v___x_2662_ = l_Lake_ensureJob___redArg(v___x_2638_, v___f_2660_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2687_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
v_a_2664_ = lean_ctor_get(v___x_2662_, 1);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2666_ = v___x_2662_;
v_isShared_2667_ = v_isSharedCheck_2687_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_inc(v_a_2663_);
lean_dec(v___x_2662_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2687_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v_task_2668_; lean_object* v_kind_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2685_; 
v_task_2668_ = lean_ctor_get(v_a_2663_, 0);
v_kind_2669_ = lean_ctor_get(v_a_2663_, 1);
v_isSharedCheck_2685_ = !lean_is_exclusive(v_a_2663_);
if (v_isSharedCheck_2685_ == 0)
{
lean_object* v_unused_2686_; 
v_unused_2686_ = lean_ctor_get(v_a_2663_, 2);
lean_dec(v_unused_2686_);
v___x_2671_ = v_a_2663_;
v_isShared_2672_ = v_isSharedCheck_2685_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_kind_2669_);
lean_inc(v_task_2668_);
lean_dec(v_a_2663_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2685_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v_registeredJobs_2673_; lean_object* v_job_2675_; 
v_registeredJobs_2673_ = lean_ctor_get(v___y_2644_, 4);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 2, v___x_2656_);
v_job_2675_ = v___x_2671_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_task_2668_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_kind_2669_);
lean_ctor_set(v_reuseFailAlloc_2684_, 2, v___x_2656_);
v_job_2675_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2682_; 
lean_ctor_set_uint8(v_job_2675_, sizeof(void*)*3, v___x_2661_);
v___x_2676_ = lean_st_ref_take(v_registeredJobs_2673_);
lean_inc_ref(v_job_2675_);
v___x_2677_ = l_Lake_Job_toOpaque___redArg(v_job_2675_);
v___x_2678_ = lean_array_push(v___x_2676_, v___x_2677_);
v___x_2679_ = lean_st_ref_put(v_registeredJobs_2673_, v___x_2678_);
v___x_2680_ = l_Lake_Job_renew___redArg(v_job_2675_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 0, v___x_2680_);
v___x_2682_ = v___x_2666_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2680_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v_a_2664_);
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
lean_dec_ref(v___x_2656_);
return v___x_2662_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed(lean_object* v_what_2688_, lean_object* v_optFacet_2689_, lean_object* v_facet_2690_, lean_object* v___x_2691_, lean_object* v_pkg_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(v_what_2688_, v_optFacet_2689_, v_facet_2690_, v___x_2691_, v_pkg_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
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
lean_closure_set(v___f_2712_, 2, v_facet_2708_);
lean_closure_set(v___f_2712_, 3, v___x_2711_);
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
lean_closure_set(v___f_2723_, 2, v_facet_2717_);
lean_closure_set(v___f_2723_, 3, v___x_2722_);
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
lean_object* v_toBuildConfig_2762_; uint8_t v_verbosity_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; uint8_t v___x_2767_; 
v_toBuildConfig_2762_ = lean_ctor_get(v___y_2736_, 0);
v_verbosity_2763_ = lean_ctor_get_uint8(v_toBuildConfig_2762_, sizeof(void*)*5 + 4);
v___x_2764_ = lean_box(v_verbosity_2763_);
v___x_2765_ = lean_obj_tag_nat(v___x_2764_);
lean_dec(v___x_2764_);
v___x_2766_ = lean_unsigned_to_nat(2u);
v___x_2767_ = lean_nat_dec_eq(v___x_2765_, v___x_2766_);
if (v___x_2767_ == 0)
{
lean_object* v___x_2768_; 
lean_dec(v___x_2730_);
lean_dec(v_baseName_2729_);
v___x_2768_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_2740_ = v___x_2768_;
v_a_2741_ = v___y_2737_;
goto v___jp_2739_;
}
else
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2769_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_2770_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2729_, v___x_2767_);
v___x_2771_ = lean_string_append(v___x_2769_, v___x_2770_);
lean_dec_ref(v___x_2770_);
v___x_2772_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2773_ = lean_string_append(v___x_2771_, v___x_2772_);
v___x_2774_ = l_Lake_Name_eraseHead(v___x_2730_);
v___x_2775_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2774_, v___x_2767_);
v___x_2776_ = lean_string_append(v___x_2773_, v___x_2775_);
lean_dec_ref(v___x_2775_);
v___x_2777_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2778_ = lean_string_append(v___x_2776_, v___x_2777_);
v_a_2740_ = v___x_2778_;
v_a_2741_ = v___y_2737_;
goto v___jp_2739_;
}
}
else
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
lean_dec(v___x_2730_);
lean_dec(v_baseName_2729_);
v___x_2779_ = lean_box(0);
v___x_2780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2779_);
lean_ctor_set(v___x_2780_, 1, v___y_2737_);
return v___x_2780_;
}
v___jp_2739_:
{
lean_object* v_log_2742_; uint8_t v_action_2743_; uint8_t v_wantsRebuild_2744_; uint8_t v_canceled_2745_; lean_object* v_trace_2746_; lean_object* v_buildTime_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2761_; 
v_log_2742_ = lean_ctor_get(v_a_2741_, 0);
v_action_2743_ = lean_ctor_get_uint8(v_a_2741_, sizeof(void*)*3);
v_wantsRebuild_2744_ = lean_ctor_get_uint8(v_a_2741_, sizeof(void*)*3 + 1);
v_canceled_2745_ = lean_ctor_get_uint8(v_a_2741_, sizeof(void*)*3 + 2);
v_trace_2746_ = lean_ctor_get(v_a_2741_, 1);
v_buildTime_2747_ = lean_ctor_get(v_a_2741_, 2);
v_isSharedCheck_2761_ = !lean_is_exclusive(v_a_2741_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2749_ = v_a_2741_;
v_isShared_2750_ = v_isSharedCheck_2761_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_buildTime_2747_);
lean_inc(v_trace_2746_);
lean_inc(v_log_2742_);
lean_dec(v_a_2741_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2761_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; uint8_t v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2758_; 
v___x_2751_ = ((lean_object*)(l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0));
v___x_2752_ = lean_string_append(v___x_2751_, v_a_2740_);
lean_dec_ref(v_a_2740_);
v___x_2753_ = 3;
v___x_2754_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2754_, 0, v___x_2752_);
lean_ctor_set_uint8(v___x_2754_, sizeof(void*)*1, v___x_2753_);
v___x_2755_ = lean_array_get_size(v_log_2742_);
v___x_2756_ = lean_array_push(v_log_2742_, v___x_2754_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v___x_2756_);
v___x_2758_ = v___x_2749_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2756_);
lean_ctor_set(v_reuseFailAlloc_2760_, 1, v_trace_2746_);
lean_ctor_set(v_reuseFailAlloc_2760_, 2, v_buildTime_2747_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, sizeof(void*)*3, v_action_2743_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, sizeof(void*)*3 + 1, v_wantsRebuild_2744_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, sizeof(void*)*3 + 2, v_canceled_2745_);
v___x_2758_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
lean_object* v___x_2759_; 
v___x_2759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2755_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
return v___x_2759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1___boxed(lean_object* v_baseName_2781_, lean_object* v___x_2782_, lean_object* v_success_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
uint8_t v_success_boxed_2791_; lean_object* v_res_2792_; 
v_success_boxed_2791_ = lean_unbox(v_success_2783_);
v_res_2792_ = l_Lake_Package_buildCacheFacetConfig___lam__1(v_baseName_2781_, v___x_2782_, v_success_boxed_2791_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2(lean_object* v___x_2793_, lean_object* v___x_2794_, lean_object* v___x_2795_, lean_object* v_pkg_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v_baseName_2804_; lean_object* v_keyName_2805_; lean_object* v___f_2806_; uint8_t v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___f_2817_; uint8_t v___x_2818_; lean_object* v___x_2819_; 
v_baseName_2804_ = lean_ctor_get(v_pkg_2796_, 1);
v_keyName_2805_ = lean_ctor_get(v_pkg_2796_, 2);
lean_inc(v___x_2793_);
lean_inc_n(v_baseName_2804_, 2);
v___f_2806_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2806_, 0, v_baseName_2804_);
lean_closure_set(v___f_2806_, 1, v___x_2793_);
v___x_2807_ = 1;
v___x_2808_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2804_, v___x_2807_);
v___x_2809_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2810_ = lean_string_append(v___x_2808_, v___x_2809_);
v___x_2811_ = l_Lake_Name_eraseHead(v___x_2794_);
v___x_2812_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2811_, v___x_2807_);
v___x_2813_ = lean_string_append(v___x_2810_, v___x_2812_);
lean_dec_ref(v___x_2812_);
lean_inc(v_keyName_2805_);
v___x_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2814_, 0, v_keyName_2805_);
v___x_2815_ = l_Lake_Package_keyword;
v___x_2816_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2814_);
lean_ctor_set(v___x_2816_, 1, v___x_2815_);
lean_ctor_set(v___x_2816_, 2, v_pkg_2796_);
lean_ctor_set(v___x_2816_, 3, v___x_2793_);
lean_inc(v___x_2795_);
v___f_2817_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2817_, 0, v___x_2816_);
lean_closure_set(v___f_2817_, 1, v___x_2795_);
lean_closure_set(v___f_2817_, 2, v___f_2806_);
v___x_2818_ = 0;
v___x_2819_ = l_Lake_ensureJob___redArg(v___x_2795_, v___f_2817_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2844_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
v_a_2821_ = lean_ctor_get(v___x_2819_, 1);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2823_ = v___x_2819_;
v_isShared_2824_ = v_isSharedCheck_2844_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_inc(v_a_2820_);
lean_dec(v___x_2819_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2844_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v_task_2825_; lean_object* v_kind_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2842_; 
v_task_2825_ = lean_ctor_get(v_a_2820_, 0);
v_kind_2826_ = lean_ctor_get(v_a_2820_, 1);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_a_2820_);
if (v_isSharedCheck_2842_ == 0)
{
lean_object* v_unused_2843_; 
v_unused_2843_ = lean_ctor_get(v_a_2820_, 2);
lean_dec(v_unused_2843_);
v___x_2828_ = v_a_2820_;
v_isShared_2829_ = v_isSharedCheck_2842_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_kind_2826_);
lean_inc(v_task_2825_);
lean_dec(v_a_2820_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2842_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v_registeredJobs_2830_; lean_object* v_job_2832_; 
v_registeredJobs_2830_ = lean_ctor_get(v___y_2801_, 4);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 2, v___x_2813_);
v_job_2832_ = v___x_2828_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_task_2825_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v_kind_2826_);
lean_ctor_set(v_reuseFailAlloc_2841_, 2, v___x_2813_);
v_job_2832_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2839_; 
lean_ctor_set_uint8(v_job_2832_, sizeof(void*)*3, v___x_2818_);
v___x_2833_ = lean_st_ref_take(v_registeredJobs_2830_);
lean_inc_ref(v_job_2832_);
v___x_2834_ = l_Lake_Job_toOpaque___redArg(v_job_2832_);
v___x_2835_ = lean_array_push(v___x_2833_, v___x_2834_);
v___x_2836_ = lean_st_ref_put(v_registeredJobs_2830_, v___x_2835_);
v___x_2837_ = l_Lake_Job_renew___redArg(v_job_2832_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 0, v___x_2837_);
v___x_2839_ = v___x_2823_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2837_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_a_2821_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2813_);
return v___x_2819_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2___boxed(lean_object* v___x_2845_, lean_object* v___x_2846_, lean_object* v___x_2847_, lean_object* v_pkg_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_Lake_Package_buildCacheFacetConfig___lam__2(v___x_2845_, v___x_2846_, v___x_2847_, v_pkg_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec(v___y_2850_);
return v_res_2856_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___f_2860_; 
v___x_2857_ = l_Lake_instDataKindUnit;
v___x_2858_ = l_Lake_Package_buildCacheFacet;
v___x_2859_ = l_Lake_Package_optBuildCacheFacet;
v___f_2860_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2860_, 0, v___x_2859_);
lean_closure_set(v___f_2860_, 1, v___x_2858_);
lean_closure_set(v___f_2860_, 2, v___x_2857_);
return v___f_2860_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2861_; uint8_t v___x_2862_; lean_object* v___x_2863_; lean_object* v___f_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___f_2861_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_2862_ = 1;
v___x_2863_ = l_Lake_instDataKindUnit;
v___f_2864_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__0, &l_Lake_Package_buildCacheFacetConfig___closed__0_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__0);
v___x_2865_ = l_Lake_Package_keyword;
v___x_2866_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
lean_ctor_set(v___x_2866_, 1, v___f_2864_);
lean_ctor_set(v___x_2866_, 2, v___x_2863_);
lean_ctor_set(v___x_2866_, 3, v___f_2861_);
lean_ctor_set_uint8(v___x_2866_, sizeof(void*)*4, v___x_2862_);
lean_ctor_set_uint8(v___x_2866_, sizeof(void*)*4 + 1, v___x_2862_);
return v___x_2866_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig(void){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__1, &l_Lake_Package_buildCacheFacetConfig___closed__1_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__1);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0(lean_object* v_pkg_2869_, lean_object* v_dir_2870_, lean_object* v___x_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
uint8_t v_r_2880_; lean_object* v___y_2881_; lean_object* v_a_2885_; lean_object* v___x_2902_; 
lean_inc_ref(v_pkg_2869_);
v___x_2902_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_pkg_2869_, v___y_2876_, v___y_2877_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v_a_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_a_2903_);
v_a_2904_ = lean_ctor_get(v___x_2902_, 1);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2902_, 2);
v___x_2905_ = l_Lake_defaultLakeDir;
v___x_2906_ = l_Lake_joinRelative(v_dir_2870_, v___x_2905_);
v___x_2907_ = ((lean_object*)(l_Lake_Package_optBarrelFacetConfig___lam__0___closed__0));
v___x_2908_ = l_Lake_joinRelative(v___x_2906_, v___x_2907_);
v___x_2909_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_2869_, v_a_2903_, v___x_2908_, v___x_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v_a_2904_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; uint8_t v___x_2911_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 1);
lean_inc(v_a_2910_);
lean_dec_ref_known(v___x_2909_, 2);
v___x_2911_ = 1;
v_r_2880_ = v___x_2911_;
v___y_2881_ = v_a_2910_;
goto v___jp_2879_;
}
else
{
lean_object* v_a_2912_; 
v_a_2912_ = lean_ctor_get(v___x_2909_, 1);
lean_inc(v_a_2912_);
lean_dec_ref_known(v___x_2909_, 2);
v_a_2885_ = v_a_2912_;
goto v___jp_2884_;
}
}
else
{
lean_object* v_a_2913_; 
lean_dec_ref(v_dir_2870_);
lean_dec_ref(v_pkg_2869_);
v_a_2913_ = lean_ctor_get(v___x_2902_, 1);
lean_inc(v_a_2913_);
lean_dec_ref_known(v___x_2902_, 2);
v_a_2885_ = v_a_2913_;
goto v___jp_2884_;
}
v___jp_2879_:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2882_ = lean_box(v_r_2880_);
v___x_2883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2882_);
lean_ctor_set(v___x_2883_, 1, v___y_2881_);
return v___x_2883_;
}
v___jp_2884_:
{
lean_object* v_log_2886_; uint8_t v_action_2887_; uint8_t v_wantsRebuild_2888_; uint8_t v_canceled_2889_; lean_object* v_trace_2890_; lean_object* v_buildTime_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2901_; 
v_log_2886_ = lean_ctor_get(v_a_2885_, 0);
v_action_2887_ = lean_ctor_get_uint8(v_a_2885_, sizeof(void*)*3);
v_wantsRebuild_2888_ = lean_ctor_get_uint8(v_a_2885_, sizeof(void*)*3 + 1);
v_canceled_2889_ = lean_ctor_get_uint8(v_a_2885_, sizeof(void*)*3 + 2);
v_trace_2890_ = lean_ctor_get(v_a_2885_, 1);
v_buildTime_2891_ = lean_ctor_get(v_a_2885_, 2);
v_isSharedCheck_2901_ = !lean_is_exclusive(v_a_2885_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2893_ = v_a_2885_;
v_isShared_2894_ = v_isSharedCheck_2901_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_buildTime_2891_);
lean_inc(v_trace_2890_);
lean_inc(v_log_2886_);
lean_dec(v_a_2885_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2901_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
uint8_t v___x_2895_; uint8_t v___x_2896_; lean_object* v___x_2898_; 
v___x_2895_ = 4;
v___x_2896_ = l_Lake_JobAction_merge(v_action_2887_, v___x_2895_);
if (v_isShared_2894_ == 0)
{
v___x_2898_ = v___x_2893_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_log_2886_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v_trace_2890_);
lean_ctor_set(v_reuseFailAlloc_2900_, 2, v_buildTime_2891_);
lean_ctor_set_uint8(v_reuseFailAlloc_2900_, sizeof(void*)*3 + 1, v_wantsRebuild_2888_);
lean_ctor_set_uint8(v_reuseFailAlloc_2900_, sizeof(void*)*3 + 2, v_canceled_2889_);
v___x_2898_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
uint8_t v___x_2899_; 
lean_ctor_set_uint8(v___x_2898_, sizeof(void*)*3, v___x_2896_);
v___x_2899_ = 0;
v_r_2880_ = v___x_2899_;
v___y_2881_ = v___x_2898_;
goto v___jp_2879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0___boxed(lean_object* v_pkg_2914_, lean_object* v_dir_2915_, lean_object* v___x_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_Lake_Package_optBarrelFacetConfig___lam__0(v_pkg_2914_, v_dir_2915_, v___x_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec_ref(v___x_2916_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1(lean_object* v___x_2925_, lean_object* v___f_2926_, lean_object* v___x_2927_, lean_object* v___x_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2936_ = l_Lake_Job_async___redArg(v___x_2925_, v___f_2926_, v___x_2927_, v___x_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
v___x_2937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
lean_ctor_set(v___x_2937_, 1, v___y_2934_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1___boxed(lean_object* v___x_2938_, lean_object* v___f_2939_, lean_object* v___x_2940_, lean_object* v___x_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_Lake_Package_optBarrelFacetConfig___lam__1(v___x_2938_, v___f_2939_, v___x_2940_, v___x_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec(v___y_2944_);
lean_dec(v___y_2943_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2(lean_object* v___x_2950_, lean_object* v___x_2951_, lean_object* v___x_2952_, lean_object* v_pkg_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_){
_start:
{
lean_object* v_baseName_2961_; lean_object* v_dir_2962_; lean_object* v___f_2963_; uint8_t v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___f_2973_; lean_object* v___x_2974_; 
v_baseName_2961_ = lean_ctor_get(v_pkg_2953_, 1);
lean_inc(v_baseName_2961_);
v_dir_2962_ = lean_ctor_get(v_pkg_2953_, 4);
lean_inc_ref(v_dir_2962_);
v___f_2963_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2963_, 0, v_pkg_2953_);
lean_closure_set(v___f_2963_, 1, v_dir_2962_);
lean_closure_set(v___f_2963_, 2, v___x_2950_);
v___x_2964_ = 1;
v___x_2965_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2961_, v___x_2964_);
v___x_2966_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2967_ = lean_string_append(v___x_2965_, v___x_2966_);
v___x_2968_ = l_Lake_Name_eraseHead(v___x_2951_);
v___x_2969_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2968_, v___x_2964_);
v___x_2970_ = lean_string_append(v___x_2967_, v___x_2969_);
lean_dec_ref(v___x_2969_);
v___x_2971_ = lean_unsigned_to_nat(0u);
v___x_2972_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_2952_);
v___f_2973_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2973_, 0, v___x_2952_);
lean_closure_set(v___f_2973_, 1, v___f_2963_);
lean_closure_set(v___f_2973_, 2, v___x_2971_);
lean_closure_set(v___f_2973_, 3, v___x_2972_);
v___x_2974_ = l_Lake_ensureJob___redArg(v___x_2952_, v___f_2973_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2999_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
v_a_2976_ = lean_ctor_get(v___x_2974_, 1);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2978_ = v___x_2974_;
v_isShared_2979_ = v_isSharedCheck_2999_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_inc(v_a_2975_);
lean_dec(v___x_2974_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2999_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v_task_2980_; lean_object* v_kind_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2997_; 
v_task_2980_ = lean_ctor_get(v_a_2975_, 0);
v_kind_2981_ = lean_ctor_get(v_a_2975_, 1);
v_isSharedCheck_2997_ = !lean_is_exclusive(v_a_2975_);
if (v_isSharedCheck_2997_ == 0)
{
lean_object* v_unused_2998_; 
v_unused_2998_ = lean_ctor_get(v_a_2975_, 2);
lean_dec(v_unused_2998_);
v___x_2983_ = v_a_2975_;
v_isShared_2984_ = v_isSharedCheck_2997_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_kind_2981_);
lean_inc(v_task_2980_);
lean_dec(v_a_2975_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2997_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v_registeredJobs_2985_; lean_object* v_job_2987_; 
v_registeredJobs_2985_ = lean_ctor_get(v___y_2958_, 4);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 2, v___x_2970_);
v_job_2987_ = v___x_2983_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_task_2980_);
lean_ctor_set(v_reuseFailAlloc_2996_, 1, v_kind_2981_);
lean_ctor_set(v_reuseFailAlloc_2996_, 2, v___x_2970_);
v_job_2987_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2994_; 
lean_ctor_set_uint8(v_job_2987_, sizeof(void*)*3, v___x_2964_);
v___x_2988_ = lean_st_ref_take(v_registeredJobs_2985_);
lean_inc_ref(v_job_2987_);
v___x_2989_ = l_Lake_Job_toOpaque___redArg(v_job_2987_);
v___x_2990_ = lean_array_push(v___x_2988_, v___x_2989_);
v___x_2991_ = lean_st_ref_put(v_registeredJobs_2985_, v___x_2990_);
v___x_2992_ = l_Lake_Job_renew___redArg(v_job_2987_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 0, v___x_2992_);
v___x_2994_ = v___x_2978_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2992_);
lean_ctor_set(v_reuseFailAlloc_2995_, 1, v_a_2976_);
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
else
{
lean_dec_ref(v___x_2970_);
return v___x_2974_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2___boxed(lean_object* v___x_3000_, lean_object* v___x_3001_, lean_object* v___x_3002_, lean_object* v_pkg_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_Lake_Package_optBarrelFacetConfig___lam__2(v___x_3000_, v___x_3001_, v___x_3002_, v_pkg_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec(v___y_3005_);
return v_res_3011_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___f_3015_; 
v___x_3012_ = l_Lake_instDataKindBool;
v___x_3013_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_3014_ = l_Lake_Reservoir_lakeHeaders;
v___f_3015_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_3015_, 0, v___x_3014_);
lean_closure_set(v___f_3015_, 1, v___x_3013_);
lean_closure_set(v___f_3015_, 2, v___x_3012_);
return v___f_3015_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3016_; uint8_t v___x_3017_; lean_object* v___x_3018_; lean_object* v___f_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___f_3016_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_3017_ = 1;
v___x_3018_ = l_Lake_instDataKindBool;
v___f_3019_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__0, &l_Lake_Package_optBarrelFacetConfig___closed__0_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__0);
v___x_3020_ = l_Lake_Package_keyword;
v___x_3021_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3021_, 0, v___x_3020_);
lean_ctor_set(v___x_3021_, 1, v___f_3019_);
lean_ctor_set(v___x_3021_, 2, v___x_3018_);
lean_ctor_set(v___x_3021_, 3, v___f_3016_);
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*4, v___x_3017_);
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*4 + 1, v___x_3017_);
return v___x_3021_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig(void){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__1, &l_Lake_Package_optBarrelFacetConfig___closed__1_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__1);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1(lean_object* v_baseName_3024_, lean_object* v___x_3025_, uint8_t v_success_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
lean_object* v_a_3035_; lean_object* v_a_3036_; 
if (v_success_3026_ == 0)
{
lean_object* v_toBuildConfig_3057_; uint8_t v_verbosity_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; 
v_toBuildConfig_3057_ = lean_ctor_get(v___y_3031_, 0);
v_verbosity_3058_ = lean_ctor_get_uint8(v_toBuildConfig_3057_, sizeof(void*)*5 + 4);
v___x_3059_ = lean_box(v_verbosity_3058_);
v___x_3060_ = lean_obj_tag_nat(v___x_3059_);
lean_dec(v___x_3059_);
v___x_3061_ = lean_unsigned_to_nat(2u);
v___x_3062_ = lean_nat_dec_eq(v___x_3060_, v___x_3061_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3063_; 
lean_dec(v___x_3025_);
lean_dec(v_baseName_3024_);
v___x_3063_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_3035_ = v___x_3063_;
v_a_3036_ = v___y_3032_;
goto v___jp_3034_;
}
else
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3064_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_3065_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3024_, v___x_3062_);
v___x_3066_ = lean_string_append(v___x_3064_, v___x_3065_);
lean_dec_ref(v___x_3065_);
v___x_3067_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3068_ = lean_string_append(v___x_3066_, v___x_3067_);
v___x_3069_ = l_Lake_Name_eraseHead(v___x_3025_);
v___x_3070_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3069_, v___x_3062_);
v___x_3071_ = lean_string_append(v___x_3068_, v___x_3070_);
lean_dec_ref(v___x_3070_);
v___x_3072_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_3073_ = lean_string_append(v___x_3071_, v___x_3072_);
v_a_3035_ = v___x_3073_;
v_a_3036_ = v___y_3032_;
goto v___jp_3034_;
}
}
else
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
lean_dec(v___x_3025_);
lean_dec(v_baseName_3024_);
v___x_3074_ = lean_box(0);
v___x_3075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
lean_ctor_set(v___x_3075_, 1, v___y_3032_);
return v___x_3075_;
}
v___jp_3034_:
{
lean_object* v_log_3037_; uint8_t v_action_3038_; uint8_t v_wantsRebuild_3039_; uint8_t v_canceled_3040_; lean_object* v_trace_3041_; lean_object* v_buildTime_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3056_; 
v_log_3037_ = lean_ctor_get(v_a_3036_, 0);
v_action_3038_ = lean_ctor_get_uint8(v_a_3036_, sizeof(void*)*3);
v_wantsRebuild_3039_ = lean_ctor_get_uint8(v_a_3036_, sizeof(void*)*3 + 1);
v_canceled_3040_ = lean_ctor_get_uint8(v_a_3036_, sizeof(void*)*3 + 2);
v_trace_3041_ = lean_ctor_get(v_a_3036_, 1);
v_buildTime_3042_ = lean_ctor_get(v_a_3036_, 2);
v_isSharedCheck_3056_ = !lean_is_exclusive(v_a_3036_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3044_ = v_a_3036_;
v_isShared_3045_ = v_isSharedCheck_3056_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_buildTime_3042_);
lean_inc(v_trace_3041_);
lean_inc(v_log_3037_);
lean_dec(v_a_3036_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3056_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; uint8_t v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3053_; 
v___x_3046_ = ((lean_object*)(l_Lake_Package_barrelFacetConfig___lam__1___closed__0));
v___x_3047_ = lean_string_append(v___x_3046_, v_a_3035_);
lean_dec_ref(v_a_3035_);
v___x_3048_ = 3;
v___x_3049_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3049_, 0, v___x_3047_);
lean_ctor_set_uint8(v___x_3049_, sizeof(void*)*1, v___x_3048_);
v___x_3050_ = lean_array_get_size(v_log_3037_);
v___x_3051_ = lean_array_push(v_log_3037_, v___x_3049_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 0, v___x_3051_);
v___x_3053_ = v___x_3044_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3051_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v_trace_3041_);
lean_ctor_set(v_reuseFailAlloc_3055_, 2, v_buildTime_3042_);
lean_ctor_set_uint8(v_reuseFailAlloc_3055_, sizeof(void*)*3, v_action_3038_);
lean_ctor_set_uint8(v_reuseFailAlloc_3055_, sizeof(void*)*3 + 1, v_wantsRebuild_3039_);
lean_ctor_set_uint8(v_reuseFailAlloc_3055_, sizeof(void*)*3 + 2, v_canceled_3040_);
v___x_3053_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
lean_object* v___x_3054_; 
v___x_3054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3050_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
return v___x_3054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1___boxed(lean_object* v_baseName_3076_, lean_object* v___x_3077_, lean_object* v_success_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
uint8_t v_success_boxed_3086_; lean_object* v_res_3087_; 
v_success_boxed_3086_ = lean_unbox(v_success_3078_);
v_res_3087_ = l_Lake_Package_barrelFacetConfig___lam__1(v_baseName_3076_, v___x_3077_, v_success_boxed_3086_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2(lean_object* v___x_3088_, lean_object* v___x_3089_, lean_object* v___x_3090_, lean_object* v_pkg_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v_baseName_3099_; lean_object* v_keyName_3100_; lean_object* v___f_3101_; uint8_t v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___f_3112_; uint8_t v___x_3113_; lean_object* v___x_3114_; 
v_baseName_3099_ = lean_ctor_get(v_pkg_3091_, 1);
v_keyName_3100_ = lean_ctor_get(v_pkg_3091_, 2);
lean_inc(v___x_3088_);
lean_inc_n(v_baseName_3099_, 2);
v___f_3101_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_3101_, 0, v_baseName_3099_);
lean_closure_set(v___f_3101_, 1, v___x_3088_);
v___x_3102_ = 1;
v___x_3103_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3099_, v___x_3102_);
v___x_3104_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3105_ = lean_string_append(v___x_3103_, v___x_3104_);
v___x_3106_ = l_Lake_Name_eraseHead(v___x_3089_);
v___x_3107_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3106_, v___x_3102_);
v___x_3108_ = lean_string_append(v___x_3105_, v___x_3107_);
lean_dec_ref(v___x_3107_);
lean_inc(v_keyName_3100_);
v___x_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3109_, 0, v_keyName_3100_);
v___x_3110_ = l_Lake_Package_keyword;
v___x_3111_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3109_);
lean_ctor_set(v___x_3111_, 1, v___x_3110_);
lean_ctor_set(v___x_3111_, 2, v_pkg_3091_);
lean_ctor_set(v___x_3111_, 3, v___x_3088_);
lean_inc(v___x_3090_);
v___f_3112_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3112_, 0, v___x_3111_);
lean_closure_set(v___f_3112_, 1, v___x_3090_);
lean_closure_set(v___f_3112_, 2, v___f_3101_);
v___x_3113_ = 0;
v___x_3114_ = l_Lake_ensureJob___redArg(v___x_3090_, v___f_3112_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3139_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
v_a_3116_ = lean_ctor_get(v___x_3114_, 1);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3118_ = v___x_3114_;
v_isShared_3119_ = v_isSharedCheck_3139_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_inc(v_a_3115_);
lean_dec(v___x_3114_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3139_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v_task_3120_; lean_object* v_kind_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3137_; 
v_task_3120_ = lean_ctor_get(v_a_3115_, 0);
v_kind_3121_ = lean_ctor_get(v_a_3115_, 1);
v_isSharedCheck_3137_ = !lean_is_exclusive(v_a_3115_);
if (v_isSharedCheck_3137_ == 0)
{
lean_object* v_unused_3138_; 
v_unused_3138_ = lean_ctor_get(v_a_3115_, 2);
lean_dec(v_unused_3138_);
v___x_3123_ = v_a_3115_;
v_isShared_3124_ = v_isSharedCheck_3137_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_kind_3121_);
lean_inc(v_task_3120_);
lean_dec(v_a_3115_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3137_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v_registeredJobs_3125_; lean_object* v_job_3127_; 
v_registeredJobs_3125_ = lean_ctor_get(v___y_3096_, 4);
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 2, v___x_3108_);
v_job_3127_ = v___x_3123_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_task_3120_);
lean_ctor_set(v_reuseFailAlloc_3136_, 1, v_kind_3121_);
lean_ctor_set(v_reuseFailAlloc_3136_, 2, v___x_3108_);
v_job_3127_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3134_; 
lean_ctor_set_uint8(v_job_3127_, sizeof(void*)*3, v___x_3113_);
v___x_3128_ = lean_st_ref_take(v_registeredJobs_3125_);
lean_inc_ref(v_job_3127_);
v___x_3129_ = l_Lake_Job_toOpaque___redArg(v_job_3127_);
v___x_3130_ = lean_array_push(v___x_3128_, v___x_3129_);
v___x_3131_ = lean_st_ref_put(v_registeredJobs_3125_, v___x_3130_);
v___x_3132_ = l_Lake_Job_renew___redArg(v_job_3127_);
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 0, v___x_3132_);
v___x_3134_ = v___x_3118_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3132_);
lean_ctor_set(v_reuseFailAlloc_3135_, 1, v_a_3116_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3108_);
return v___x_3114_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2___boxed(lean_object* v___x_3140_, lean_object* v___x_3141_, lean_object* v___x_3142_, lean_object* v_pkg_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l_Lake_Package_barrelFacetConfig___lam__2(v___x_3140_, v___x_3141_, v___x_3142_, v_pkg_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec(v___y_3146_);
lean_dec(v___y_3145_);
return v_res_3151_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___f_3155_; 
v___x_3152_ = l_Lake_instDataKindUnit;
v___x_3153_ = l_Lake_Package_reservoirBarrelFacet;
v___x_3154_ = l_Lake_Package_optReservoirBarrelFacet;
v___f_3155_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_3155_, 0, v___x_3154_);
lean_closure_set(v___f_3155_, 1, v___x_3153_);
lean_closure_set(v___f_3155_, 2, v___x_3152_);
return v___f_3155_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3156_; uint8_t v___x_3157_; lean_object* v___x_3158_; lean_object* v___f_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___f_3156_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_3157_ = 1;
v___x_3158_ = l_Lake_instDataKindUnit;
v___f_3159_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__0, &l_Lake_Package_barrelFacetConfig___closed__0_once, _init_l_Lake_Package_barrelFacetConfig___closed__0);
v___x_3160_ = l_Lake_Package_keyword;
v___x_3161_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
lean_ctor_set(v___x_3161_, 1, v___f_3159_);
lean_ctor_set(v___x_3161_, 2, v___x_3158_);
lean_ctor_set(v___x_3161_, 3, v___f_3156_);
lean_ctor_set_uint8(v___x_3161_, sizeof(void*)*4, v___x_3157_);
lean_ctor_set_uint8(v___x_3161_, sizeof(void*)*4 + 1, v___x_3157_);
return v___x_3161_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig(void){
_start:
{
lean_object* v___x_3162_; 
v___x_3162_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__1, &l_Lake_Package_barrelFacetConfig___closed__1_once, _init_l_Lake_Package_barrelFacetConfig___closed__1);
return v___x_3162_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(lean_object* v_pkg_3163_, lean_object* v_dir_3164_, lean_object* v_buildArchive_3165_, lean_object* v___x_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
uint8_t v_r_3175_; lean_object* v___y_3176_; lean_object* v_a_3180_; lean_object* v___x_3197_; 
lean_inc_ref(v_pkg_3163_);
v___x_3197_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_pkg_3163_, v___y_3172_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v_a_3198_; lean_object* v_a_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
lean_inc(v_a_3198_);
v_a_3199_ = lean_ctor_get(v___x_3197_, 1);
lean_inc(v_a_3199_);
lean_dec_ref_known(v___x_3197_, 2);
v___x_3200_ = l_Lake_defaultLakeDir;
v___x_3201_ = l_Lake_joinRelative(v_dir_3164_, v___x_3200_);
v___x_3202_ = l_Lake_joinRelative(v___x_3201_, v_buildArchive_3165_);
v___x_3203_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_3163_, v_a_3198_, v___x_3202_, v___x_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v_a_3199_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; uint8_t v___x_3205_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 1);
lean_inc(v_a_3204_);
lean_dec_ref_known(v___x_3203_, 2);
v___x_3205_ = 1;
v_r_3175_ = v___x_3205_;
v___y_3176_ = v_a_3204_;
goto v___jp_3174_;
}
else
{
lean_object* v_a_3206_; 
v_a_3206_ = lean_ctor_get(v___x_3203_, 1);
lean_inc(v_a_3206_);
lean_dec_ref_known(v___x_3203_, 2);
v_a_3180_ = v_a_3206_;
goto v___jp_3179_;
}
}
else
{
lean_object* v_a_3207_; 
lean_dec_ref(v_buildArchive_3165_);
lean_dec_ref(v_dir_3164_);
lean_dec_ref(v_pkg_3163_);
v_a_3207_ = lean_ctor_get(v___x_3197_, 1);
lean_inc(v_a_3207_);
lean_dec_ref_known(v___x_3197_, 2);
v_a_3180_ = v_a_3207_;
goto v___jp_3179_;
}
v___jp_3174_:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3177_ = lean_box(v_r_3175_);
v___x_3178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
lean_ctor_set(v___x_3178_, 1, v___y_3176_);
return v___x_3178_;
}
v___jp_3179_:
{
lean_object* v_log_3181_; uint8_t v_action_3182_; uint8_t v_wantsRebuild_3183_; uint8_t v_canceled_3184_; lean_object* v_trace_3185_; lean_object* v_buildTime_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3196_; 
v_log_3181_ = lean_ctor_get(v_a_3180_, 0);
v_action_3182_ = lean_ctor_get_uint8(v_a_3180_, sizeof(void*)*3);
v_wantsRebuild_3183_ = lean_ctor_get_uint8(v_a_3180_, sizeof(void*)*3 + 1);
v_canceled_3184_ = lean_ctor_get_uint8(v_a_3180_, sizeof(void*)*3 + 2);
v_trace_3185_ = lean_ctor_get(v_a_3180_, 1);
v_buildTime_3186_ = lean_ctor_get(v_a_3180_, 2);
v_isSharedCheck_3196_ = !lean_is_exclusive(v_a_3180_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3188_ = v_a_3180_;
v_isShared_3189_ = v_isSharedCheck_3196_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_buildTime_3186_);
lean_inc(v_trace_3185_);
lean_inc(v_log_3181_);
lean_dec(v_a_3180_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3196_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
uint8_t v___x_3190_; uint8_t v___x_3191_; lean_object* v___x_3193_; 
v___x_3190_ = 4;
v___x_3191_ = l_Lake_JobAction_merge(v_action_3182_, v___x_3190_);
if (v_isShared_3189_ == 0)
{
v___x_3193_ = v___x_3188_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_log_3181_);
lean_ctor_set(v_reuseFailAlloc_3195_, 1, v_trace_3185_);
lean_ctor_set(v_reuseFailAlloc_3195_, 2, v_buildTime_3186_);
lean_ctor_set_uint8(v_reuseFailAlloc_3195_, sizeof(void*)*3 + 1, v_wantsRebuild_3183_);
lean_ctor_set_uint8(v_reuseFailAlloc_3195_, sizeof(void*)*3 + 2, v_canceled_3184_);
v___x_3193_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
uint8_t v___x_3194_; 
lean_ctor_set_uint8(v___x_3193_, sizeof(void*)*3, v___x_3191_);
v___x_3194_ = 0;
v_r_3175_ = v___x_3194_;
v___y_3176_ = v___x_3193_;
goto v___jp_3174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed(lean_object* v_pkg_3208_, lean_object* v_dir_3209_, lean_object* v_buildArchive_3210_, lean_object* v___x_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v_res_3219_; 
v_res_3219_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(v_pkg_3208_, v_dir_3209_, v_buildArchive_3210_, v___x_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
lean_dec_ref(v___y_3216_);
lean_dec(v___y_3215_);
lean_dec(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec_ref(v___x_3211_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(lean_object* v___x_3220_, lean_object* v___x_3221_, lean_object* v___x_3222_, lean_object* v___x_3223_, lean_object* v_pkg_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
lean_object* v_baseName_3232_; lean_object* v_dir_3233_; lean_object* v_buildArchive_3234_; lean_object* v___f_3235_; uint8_t v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___f_3244_; lean_object* v___x_3245_; 
v_baseName_3232_ = lean_ctor_get(v_pkg_3224_, 1);
lean_inc(v_baseName_3232_);
v_dir_3233_ = lean_ctor_get(v_pkg_3224_, 4);
lean_inc_ref(v_dir_3233_);
v_buildArchive_3234_ = lean_ctor_get(v_pkg_3224_, 21);
lean_inc_ref(v_buildArchive_3234_);
v___f_3235_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed), 11, 4);
lean_closure_set(v___f_3235_, 0, v_pkg_3224_);
lean_closure_set(v___f_3235_, 1, v_dir_3233_);
lean_closure_set(v___f_3235_, 2, v_buildArchive_3234_);
lean_closure_set(v___f_3235_, 3, v___x_3220_);
v___x_3236_ = 1;
v___x_3237_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3232_, v___x_3236_);
v___x_3238_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3239_ = lean_string_append(v___x_3237_, v___x_3238_);
v___x_3240_ = l_Lake_Name_eraseHead(v___x_3221_);
v___x_3241_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3240_, v___x_3236_);
v___x_3242_ = lean_string_append(v___x_3239_, v___x_3241_);
lean_dec_ref(v___x_3241_);
v___x_3243_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_3222_);
v___f_3244_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_3244_, 0, v___x_3222_);
lean_closure_set(v___f_3244_, 1, v___f_3235_);
lean_closure_set(v___f_3244_, 2, v___x_3223_);
lean_closure_set(v___f_3244_, 3, v___x_3243_);
v___x_3245_ = l_Lake_ensureJob___redArg(v___x_3222_, v___f_3244_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_object* v_a_3246_; lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3270_; 
v_a_3246_ = lean_ctor_get(v___x_3245_, 0);
v_a_3247_ = lean_ctor_get(v___x_3245_, 1);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3249_ = v___x_3245_;
v_isShared_3250_ = v_isSharedCheck_3270_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_inc(v_a_3246_);
lean_dec(v___x_3245_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3270_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v_task_3251_; lean_object* v_kind_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3268_; 
v_task_3251_ = lean_ctor_get(v_a_3246_, 0);
v_kind_3252_ = lean_ctor_get(v_a_3246_, 1);
v_isSharedCheck_3268_ = !lean_is_exclusive(v_a_3246_);
if (v_isSharedCheck_3268_ == 0)
{
lean_object* v_unused_3269_; 
v_unused_3269_ = lean_ctor_get(v_a_3246_, 2);
lean_dec(v_unused_3269_);
v___x_3254_ = v_a_3246_;
v_isShared_3255_ = v_isSharedCheck_3268_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_kind_3252_);
lean_inc(v_task_3251_);
lean_dec(v_a_3246_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3268_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v_registeredJobs_3256_; lean_object* v_job_3258_; 
v_registeredJobs_3256_ = lean_ctor_get(v___y_3229_, 4);
if (v_isShared_3255_ == 0)
{
lean_ctor_set(v___x_3254_, 2, v___x_3242_);
v_job_3258_ = v___x_3254_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_task_3251_);
lean_ctor_set(v_reuseFailAlloc_3267_, 1, v_kind_3252_);
lean_ctor_set(v_reuseFailAlloc_3267_, 2, v___x_3242_);
v_job_3258_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3265_; 
lean_ctor_set_uint8(v_job_3258_, sizeof(void*)*3, v___x_3236_);
v___x_3259_ = lean_st_ref_take(v_registeredJobs_3256_);
lean_inc_ref(v_job_3258_);
v___x_3260_ = l_Lake_Job_toOpaque___redArg(v_job_3258_);
v___x_3261_ = lean_array_push(v___x_3259_, v___x_3260_);
v___x_3262_ = lean_st_ref_put(v_registeredJobs_3256_, v___x_3261_);
v___x_3263_ = l_Lake_Job_renew___redArg(v_job_3258_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 0, v___x_3263_);
v___x_3265_ = v___x_3249_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v___x_3263_);
lean_ctor_set(v_reuseFailAlloc_3266_, 1, v_a_3247_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3242_);
return v___x_3245_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_3271_, lean_object* v___x_3272_, lean_object* v___x_3273_, lean_object* v___x_3274_, lean_object* v_pkg_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(v___x_3271_, v___x_3272_, v___x_3273_, v___x_3274_, v_pkg_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec(v___y_3277_);
return v_res_3283_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___f_3290_; 
v___x_3286_ = lean_unsigned_to_nat(0u);
v___x_3287_ = l_Lake_instDataKindBool;
v___x_3288_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_3289_ = ((lean_object*)(l_Lake_Package_optGitHubReleaseFacetConfig___closed__0));
v___f_3290_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed), 12, 4);
lean_closure_set(v___f_3290_, 0, v___x_3289_);
lean_closure_set(v___f_3290_, 1, v___x_3288_);
lean_closure_set(v___f_3290_, 2, v___x_3287_);
lean_closure_set(v___f_3290_, 3, v___x_3286_);
return v___f_3290_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_3291_; uint8_t v___x_3292_; lean_object* v___x_3293_; lean_object* v___f_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___f_3291_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_3292_ = 1;
v___x_3293_ = l_Lake_instDataKindBool;
v___f_3294_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__1, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1);
v___x_3295_ = l_Lake_Package_keyword;
v___x_3296_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3296_, 0, v___x_3295_);
lean_ctor_set(v___x_3296_, 1, v___f_3294_);
lean_ctor_set(v___x_3296_, 2, v___x_3293_);
lean_ctor_set(v___x_3296_, 3, v___f_3291_);
lean_ctor_set_uint8(v___x_3296_, sizeof(void*)*4, v___x_3292_);
lean_ctor_set_uint8(v___x_3296_, sizeof(void*)*4 + 1, v___x_3292_);
return v___x_3296_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_3297_; 
v___x_3297_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__2, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__2_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1(lean_object* v_baseName_3299_, lean_object* v___x_3300_, uint8_t v_success_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_){
_start:
{
lean_object* v_a_3310_; lean_object* v_a_3311_; 
if (v_success_3301_ == 0)
{
lean_object* v_toBuildConfig_3332_; uint8_t v_verbosity_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; uint8_t v___x_3337_; 
v_toBuildConfig_3332_ = lean_ctor_get(v___y_3306_, 0);
v_verbosity_3333_ = lean_ctor_get_uint8(v_toBuildConfig_3332_, sizeof(void*)*5 + 4);
v___x_3334_ = lean_box(v_verbosity_3333_);
v___x_3335_ = lean_obj_tag_nat(v___x_3334_);
lean_dec(v___x_3334_);
v___x_3336_ = lean_unsigned_to_nat(2u);
v___x_3337_ = lean_nat_dec_eq(v___x_3335_, v___x_3336_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3338_; 
lean_dec(v___x_3300_);
lean_dec(v_baseName_3299_);
v___x_3338_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_3310_ = v___x_3338_;
v_a_3311_ = v___y_3307_;
goto v___jp_3309_;
}
else
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3339_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_3340_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3299_, v___x_3337_);
v___x_3341_ = lean_string_append(v___x_3339_, v___x_3340_);
lean_dec_ref(v___x_3340_);
v___x_3342_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3343_ = lean_string_append(v___x_3341_, v___x_3342_);
v___x_3344_ = l_Lake_Name_eraseHead(v___x_3300_);
v___x_3345_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3344_, v___x_3337_);
v___x_3346_ = lean_string_append(v___x_3343_, v___x_3345_);
lean_dec_ref(v___x_3345_);
v___x_3347_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_3348_ = lean_string_append(v___x_3346_, v___x_3347_);
v_a_3310_ = v___x_3348_;
v_a_3311_ = v___y_3307_;
goto v___jp_3309_;
}
}
else
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
lean_dec(v___x_3300_);
lean_dec(v_baseName_3299_);
v___x_3349_ = lean_box(0);
v___x_3350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3349_);
lean_ctor_set(v___x_3350_, 1, v___y_3307_);
return v___x_3350_;
}
v___jp_3309_:
{
lean_object* v_log_3312_; uint8_t v_action_3313_; uint8_t v_wantsRebuild_3314_; uint8_t v_canceled_3315_; lean_object* v_trace_3316_; lean_object* v_buildTime_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3331_; 
v_log_3312_ = lean_ctor_get(v_a_3311_, 0);
v_action_3313_ = lean_ctor_get_uint8(v_a_3311_, sizeof(void*)*3);
v_wantsRebuild_3314_ = lean_ctor_get_uint8(v_a_3311_, sizeof(void*)*3 + 1);
v_canceled_3315_ = lean_ctor_get_uint8(v_a_3311_, sizeof(void*)*3 + 2);
v_trace_3316_ = lean_ctor_get(v_a_3311_, 1);
v_buildTime_3317_ = lean_ctor_get(v_a_3311_, 2);
v_isSharedCheck_3331_ = !lean_is_exclusive(v_a_3311_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3319_ = v_a_3311_;
v_isShared_3320_ = v_isSharedCheck_3331_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_buildTime_3317_);
lean_inc(v_trace_3316_);
lean_inc(v_log_3312_);
lean_dec(v_a_3311_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3331_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; uint8_t v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3328_; 
v___x_3321_ = ((lean_object*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0));
v___x_3322_ = lean_string_append(v___x_3321_, v_a_3310_);
lean_dec_ref(v_a_3310_);
v___x_3323_ = 3;
v___x_3324_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3324_, 0, v___x_3322_);
lean_ctor_set_uint8(v___x_3324_, sizeof(void*)*1, v___x_3323_);
v___x_3325_ = lean_array_get_size(v_log_3312_);
v___x_3326_ = lean_array_push(v_log_3312_, v___x_3324_);
if (v_isShared_3320_ == 0)
{
lean_ctor_set(v___x_3319_, 0, v___x_3326_);
v___x_3328_ = v___x_3319_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v___x_3326_);
lean_ctor_set(v_reuseFailAlloc_3330_, 1, v_trace_3316_);
lean_ctor_set(v_reuseFailAlloc_3330_, 2, v_buildTime_3317_);
lean_ctor_set_uint8(v_reuseFailAlloc_3330_, sizeof(void*)*3, v_action_3313_);
lean_ctor_set_uint8(v_reuseFailAlloc_3330_, sizeof(void*)*3 + 1, v_wantsRebuild_3314_);
lean_ctor_set_uint8(v_reuseFailAlloc_3330_, sizeof(void*)*3 + 2, v_canceled_3315_);
v___x_3328_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
lean_object* v___x_3329_; 
v___x_3329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3325_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
return v___x_3329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed(lean_object* v_baseName_3351_, lean_object* v___x_3352_, lean_object* v_success_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_){
_start:
{
uint8_t v_success_boxed_3361_; lean_object* v_res_3362_; 
v_success_boxed_3361_ = lean_unbox(v_success_3353_);
v_res_3362_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__1(v_baseName_3351_, v___x_3352_, v_success_boxed_3361_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
lean_dec_ref(v___y_3358_);
lean_dec(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2(lean_object* v___x_3363_, lean_object* v___x_3364_, lean_object* v___x_3365_, lean_object* v_pkg_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
lean_object* v_baseName_3374_; lean_object* v_keyName_3375_; lean_object* v___f_3376_; uint8_t v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___f_3387_; uint8_t v___x_3388_; lean_object* v___x_3389_; 
v_baseName_3374_ = lean_ctor_get(v_pkg_3366_, 1);
v_keyName_3375_ = lean_ctor_get(v_pkg_3366_, 2);
lean_inc(v___x_3363_);
lean_inc_n(v_baseName_3374_, 2);
v___f_3376_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_3376_, 0, v_baseName_3374_);
lean_closure_set(v___f_3376_, 1, v___x_3363_);
v___x_3377_ = 1;
v___x_3378_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3374_, v___x_3377_);
v___x_3379_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3380_ = lean_string_append(v___x_3378_, v___x_3379_);
v___x_3381_ = l_Lake_Name_eraseHead(v___x_3364_);
v___x_3382_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3381_, v___x_3377_);
v___x_3383_ = lean_string_append(v___x_3380_, v___x_3382_);
lean_dec_ref(v___x_3382_);
lean_inc(v_keyName_3375_);
v___x_3384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3384_, 0, v_keyName_3375_);
v___x_3385_ = l_Lake_Package_keyword;
v___x_3386_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3384_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
lean_ctor_set(v___x_3386_, 2, v_pkg_3366_);
lean_ctor_set(v___x_3386_, 3, v___x_3363_);
lean_inc(v___x_3365_);
v___f_3387_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3387_, 0, v___x_3386_);
lean_closure_set(v___f_3387_, 1, v___x_3365_);
lean_closure_set(v___f_3387_, 2, v___f_3376_);
v___x_3388_ = 0;
v___x_3389_ = l_Lake_ensureJob___redArg(v___x_3365_, v___f_3387_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v_a_3390_; lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3414_; 
v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
v_a_3391_ = lean_ctor_get(v___x_3389_, 1);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3393_ = v___x_3389_;
v_isShared_3394_ = v_isSharedCheck_3414_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_inc(v_a_3390_);
lean_dec(v___x_3389_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3414_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v_task_3395_; lean_object* v_kind_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3412_; 
v_task_3395_ = lean_ctor_get(v_a_3390_, 0);
v_kind_3396_ = lean_ctor_get(v_a_3390_, 1);
v_isSharedCheck_3412_ = !lean_is_exclusive(v_a_3390_);
if (v_isSharedCheck_3412_ == 0)
{
lean_object* v_unused_3413_; 
v_unused_3413_ = lean_ctor_get(v_a_3390_, 2);
lean_dec(v_unused_3413_);
v___x_3398_ = v_a_3390_;
v_isShared_3399_ = v_isSharedCheck_3412_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_kind_3396_);
lean_inc(v_task_3395_);
lean_dec(v_a_3390_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3412_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v_registeredJobs_3400_; lean_object* v_job_3402_; 
v_registeredJobs_3400_ = lean_ctor_get(v___y_3371_, 4);
if (v_isShared_3399_ == 0)
{
lean_ctor_set(v___x_3398_, 2, v___x_3383_);
v_job_3402_ = v___x_3398_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_task_3395_);
lean_ctor_set(v_reuseFailAlloc_3411_, 1, v_kind_3396_);
lean_ctor_set(v_reuseFailAlloc_3411_, 2, v___x_3383_);
v_job_3402_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3409_; 
lean_ctor_set_uint8(v_job_3402_, sizeof(void*)*3, v___x_3388_);
v___x_3403_ = lean_st_ref_take(v_registeredJobs_3400_);
lean_inc_ref(v_job_3402_);
v___x_3404_ = l_Lake_Job_toOpaque___redArg(v_job_3402_);
v___x_3405_ = lean_array_push(v___x_3403_, v___x_3404_);
v___x_3406_ = lean_st_ref_put(v_registeredJobs_3400_, v___x_3405_);
v___x_3407_ = l_Lake_Job_renew___redArg(v_job_3402_);
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 0, v___x_3407_);
v___x_3409_ = v___x_3393_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3407_);
lean_ctor_set(v_reuseFailAlloc_3410_, 1, v_a_3391_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3383_);
return v___x_3389_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_3415_, lean_object* v___x_3416_, lean_object* v___x_3417_, lean_object* v_pkg_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
lean_object* v_res_3426_; 
v_res_3426_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__2(v___x_3415_, v___x_3416_, v___x_3417_, v_pkg_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
lean_dec_ref(v___y_3423_);
lean_dec(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec(v___y_3420_);
return v_res_3426_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___f_3430_; 
v___x_3427_ = l_Lake_instDataKindUnit;
v___x_3428_ = l_Lake_Package_gitHubReleaseFacet;
v___x_3429_ = l_Lake_Package_optGitHubReleaseFacet;
v___f_3430_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_3430_, 0, v___x_3429_);
lean_closure_set(v___f_3430_, 1, v___x_3428_);
lean_closure_set(v___f_3430_, 2, v___x_3427_);
return v___f_3430_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3431_; uint8_t v___x_3432_; lean_object* v___x_3433_; lean_object* v___f_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___f_3431_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_3432_ = 1;
v___x_3433_ = l_Lake_instDataKindUnit;
v___f_3434_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__0, &l_Lake_Package_gitHubReleaseFacetConfig___closed__0_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0);
v___x_3435_ = l_Lake_Package_keyword;
v___x_3436_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
lean_ctor_set(v___x_3436_, 1, v___f_3434_);
lean_ctor_set(v___x_3436_, 2, v___x_3433_);
lean_ctor_set(v___x_3436_, 3, v___f_3431_);
lean_ctor_set_uint8(v___x_3436_, sizeof(void*)*4, v___x_3432_);
lean_ctor_set_uint8(v___x_3436_, sizeof(void*)*4 + 1, v___x_3432_);
return v___x_3436_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_3437_; 
v___x_3437_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__1, &l_Lake_Package_gitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(lean_object* v_build_3438_, uint8_t v_x_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_){
_start:
{
lean_object* v_log_3447_; uint8_t v_action_3448_; uint8_t v_wantsRebuild_3449_; uint8_t v_canceled_3450_; lean_object* v_buildTime_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3460_; 
v_log_3447_ = lean_ctor_get(v___y_3445_, 0);
v_action_3448_ = lean_ctor_get_uint8(v___y_3445_, sizeof(void*)*3);
v_wantsRebuild_3449_ = lean_ctor_get_uint8(v___y_3445_, sizeof(void*)*3 + 1);
v_canceled_3450_ = lean_ctor_get_uint8(v___y_3445_, sizeof(void*)*3 + 2);
v_buildTime_3451_ = lean_ctor_get(v___y_3445_, 2);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___y_3445_);
if (v_isSharedCheck_3460_ == 0)
{
lean_object* v_unused_3461_; 
v_unused_3461_ = lean_ctor_get(v___y_3445_, 1);
lean_dec(v_unused_3461_);
v___x_3453_ = v___y_3445_;
v_isShared_3454_ = v_isSharedCheck_3460_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_buildTime_3451_);
lean_inc(v_log_3447_);
lean_dec(v___y_3445_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3460_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3455_; lean_object* v___x_3457_; 
v___x_3455_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 1, v___x_3455_);
v___x_3457_ = v___x_3453_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_log_3447_);
lean_ctor_set(v_reuseFailAlloc_3459_, 1, v___x_3455_);
lean_ctor_set(v_reuseFailAlloc_3459_, 2, v_buildTime_3451_);
lean_ctor_set_uint8(v_reuseFailAlloc_3459_, sizeof(void*)*3, v_action_3448_);
lean_ctor_set_uint8(v_reuseFailAlloc_3459_, sizeof(void*)*3 + 1, v_wantsRebuild_3449_);
lean_ctor_set_uint8(v_reuseFailAlloc_3459_, sizeof(void*)*3 + 2, v_canceled_3450_);
v___x_3457_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
lean_object* v___x_3458_; 
lean_inc_ref(v___y_3444_);
lean_inc(v___y_3443_);
lean_inc(v___y_3442_);
lean_inc(v___y_3441_);
v___x_3458_ = lean_apply_7(v_build_3438_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___x_3457_, lean_box(0));
return v___x_3458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed(lean_object* v_build_3462_, lean_object* v_x_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
uint8_t v_x_1627__boxed_3471_; lean_object* v_res_3472_; 
v_x_1627__boxed_3471_ = lean_unbox(v_x_3463_);
v_res_3472_ = l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(v_build_3462_, v_x_1627__boxed_3471_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec(v___y_3466_);
lean_dec(v___y_3465_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg(lean_object* v_self_3473_, lean_object* v_build_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_){
_start:
{
lean_object* v_wsIdx_3482_; lean_object* v___x_3483_; uint8_t v___x_3484_; 
v_wsIdx_3482_ = lean_ctor_get(v_self_3473_, 0);
v___x_3483_ = lean_unsigned_to_nat(0u);
v___x_3484_ = lean_nat_dec_eq(v_wsIdx_3482_, v___x_3483_);
if (v___x_3484_ == 0)
{
lean_object* v___f_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___f_3485_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3485_, 0, v_build_3474_);
v___x_3486_ = lean_box(0);
lean_inc_ref(v_a_3475_);
v___x_3487_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_3473_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3498_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
v_a_3489_ = lean_ctor_get(v___x_3487_, 1);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3491_ = v___x_3487_;
v_isShared_3492_ = v_isSharedCheck_3498_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_inc(v_a_3488_);
lean_dec(v___x_3487_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3498_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3496_; 
v___x_3493_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3494_ = l_Lake_Job_bindM___redArg(v___x_3486_, v_a_3488_, v___f_3485_, v___x_3483_, v___x_3484_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v___x_3493_);
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 0, v___x_3494_);
v___x_3496_ = v___x_3491_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v___x_3494_);
lean_ctor_set(v_reuseFailAlloc_3497_, 1, v_a_3489_);
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
lean_object* v_a_3499_; lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3507_; 
lean_dec_ref(v___f_3485_);
lean_dec_ref(v_a_3475_);
v_a_3499_ = lean_ctor_get(v___x_3487_, 0);
v_a_3500_ = lean_ctor_get(v___x_3487_, 1);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3502_ = v___x_3487_;
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_inc(v_a_3499_);
lean_dec(v___x_3487_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3505_; 
if (v_isShared_3503_ == 0)
{
v___x_3505_ = v___x_3502_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3499_);
lean_ctor_set(v_reuseFailAlloc_3506_, 1, v_a_3500_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
}
else
{
uint8_t v___x_3508_; uint8_t v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
lean_dec_ref(v_self_3473_);
v___x_3508_ = 0;
v___x_3509_ = 0;
v___x_3510_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3511_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3511_, 0, v_a_3480_);
lean_ctor_set(v___x_3511_, 1, v___x_3510_);
lean_ctor_set(v___x_3511_, 2, v___x_3483_);
lean_ctor_set_uint8(v___x_3511_, sizeof(void*)*3, v___x_3508_);
lean_ctor_set_uint8(v___x_3511_, sizeof(void*)*3 + 1, v___x_3509_);
lean_ctor_set_uint8(v___x_3511_, sizeof(void*)*3 + 2, v___x_3509_);
lean_inc_ref(v_a_3479_);
lean_inc(v_a_3478_);
lean_inc(v_a_3477_);
lean_inc(v_a_3476_);
v___x_3512_ = lean_apply_7(v_build_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v___x_3511_, lean_box(0));
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3522_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 1);
v_a_3514_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3516_ = v___x_3512_;
v_isShared_3517_ = v_isSharedCheck_3522_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3513_);
lean_inc(v_a_3514_);
lean_dec(v___x_3512_);
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
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 2, 0);
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
else
{
lean_object* v_a_3523_; lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3532_; 
v_a_3523_ = lean_ctor_get(v___x_3512_, 1);
v_a_3524_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3526_ = v___x_3512_;
v_isShared_3527_ = v_isSharedCheck_3532_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3523_);
lean_inc(v_a_3524_);
lean_dec(v___x_3512_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3532_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v_log_3528_; lean_object* v___x_3530_; 
v_log_3528_ = lean_ctor_get(v_a_3523_, 0);
lean_inc_ref(v_log_3528_);
lean_dec(v_a_3523_);
if (v_isShared_3527_ == 0)
{
lean_ctor_set(v___x_3526_, 1, v_log_3528_);
v___x_3530_ = v___x_3526_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3524_);
lean_ctor_set(v_reuseFailAlloc_3531_, 1, v_log_3528_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___boxed(lean_object* v_self_3533_, lean_object* v_build_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_3533_, v_build_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_);
lean_dec_ref(v_a_3539_);
lean_dec(v_a_3538_);
lean_dec(v_a_3537_);
lean_dec(v_a_3536_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync(lean_object* v_00_u03b1_3543_, lean_object* v_self_3544_, lean_object* v_build_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_){
_start:
{
lean_object* v___x_3553_; 
v___x_3553_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_3544_, v_build_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_);
return v___x_3553_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___boxed(lean_object* v_00_u03b1_3554_, lean_object* v_self_3555_, lean_object* v_build_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_){
_start:
{
lean_object* v_res_3564_; 
v_res_3564_ = l_Lake_Package_afterBuildCacheAsync(v_00_u03b1_3554_, v_self_3555_, v_build_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_);
lean_dec_ref(v_a_3561_);
lean_dec(v_a_3560_);
lean_dec(v_a_3559_);
lean_dec(v_a_3558_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0(lean_object* v_build_3565_, uint8_t v_x_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_){
_start:
{
lean_object* v_log_3574_; uint8_t v_action_3575_; uint8_t v_wantsRebuild_3576_; uint8_t v_canceled_3577_; lean_object* v_buildTime_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3587_; 
v_log_3574_ = lean_ctor_get(v___y_3572_, 0);
v_action_3575_ = lean_ctor_get_uint8(v___y_3572_, sizeof(void*)*3);
v_wantsRebuild_3576_ = lean_ctor_get_uint8(v___y_3572_, sizeof(void*)*3 + 1);
v_canceled_3577_ = lean_ctor_get_uint8(v___y_3572_, sizeof(void*)*3 + 2);
v_buildTime_3578_ = lean_ctor_get(v___y_3572_, 2);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___y_3572_);
if (v_isSharedCheck_3587_ == 0)
{
lean_object* v_unused_3588_; 
v_unused_3588_ = lean_ctor_get(v___y_3572_, 1);
lean_dec(v_unused_3588_);
v___x_3580_ = v___y_3572_;
v_isShared_3581_ = v_isSharedCheck_3587_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_buildTime_3578_);
lean_inc(v_log_3574_);
lean_dec(v___y_3572_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3587_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3582_; lean_object* v___x_3584_; 
v___x_3582_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
if (v_isShared_3581_ == 0)
{
lean_ctor_set(v___x_3580_, 1, v___x_3582_);
v___x_3584_ = v___x_3580_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_log_3574_);
lean_ctor_set(v_reuseFailAlloc_3586_, 1, v___x_3582_);
lean_ctor_set(v_reuseFailAlloc_3586_, 2, v_buildTime_3578_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, sizeof(void*)*3, v_action_3575_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, sizeof(void*)*3 + 1, v_wantsRebuild_3576_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, sizeof(void*)*3 + 2, v_canceled_3577_);
v___x_3584_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
lean_object* v___x_3585_; 
lean_inc_ref(v___y_3571_);
lean_inc(v___y_3570_);
lean_inc(v___y_3569_);
lean_inc(v___y_3568_);
v___x_3585_ = lean_apply_7(v_build_3565_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___x_3584_, lean_box(0));
return v___x_3585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed(lean_object* v_build_3589_, lean_object* v_x_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_){
_start:
{
uint8_t v_x_1657__boxed_3598_; lean_object* v_res_3599_; 
v_x_1657__boxed_3598_ = lean_unbox(v_x_3590_);
v_res_3599_ = l_Lake_Package_afterBuildCacheSync___redArg___lam__0(v_build_3589_, v_x_1657__boxed_3598_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec(v___y_3592_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg(lean_object* v_self_3600_, lean_object* v_build_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_){
_start:
{
lean_object* v_wsIdx_3609_; lean_object* v___x_3610_; uint8_t v___x_3611_; lean_object* v___x_3612_; 
v_wsIdx_3609_ = lean_ctor_get(v_self_3600_, 0);
v___x_3610_ = lean_unsigned_to_nat(0u);
v___x_3611_ = lean_nat_dec_eq(v_wsIdx_3609_, v___x_3610_);
v___x_3612_ = lean_box(0);
if (v___x_3611_ == 0)
{
lean_object* v___f_3613_; lean_object* v___x_3614_; 
v___f_3613_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3613_, 0, v_build_3601_);
lean_inc_ref(v_a_3602_);
v___x_3614_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_3600_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_object* v_a_3615_; lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3625_; 
v_a_3615_ = lean_ctor_get(v___x_3614_, 0);
v_a_3616_ = lean_ctor_get(v___x_3614_, 1);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3618_ = v___x_3614_;
v_isShared_3619_ = v_isSharedCheck_3625_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_inc(v_a_3615_);
lean_dec(v___x_3614_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3625_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3623_; 
v___x_3620_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3621_ = l_Lake_Job_mapM___redArg(v___x_3612_, v_a_3615_, v___f_3613_, v___x_3610_, v___x_3611_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v___x_3620_);
if (v_isShared_3619_ == 0)
{
lean_ctor_set(v___x_3618_, 0, v___x_3621_);
v___x_3623_ = v___x_3618_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v___x_3621_);
lean_ctor_set(v_reuseFailAlloc_3624_, 1, v_a_3616_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
else
{
lean_object* v_a_3626_; lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
lean_dec_ref(v___f_3613_);
lean_dec_ref(v_a_3602_);
v_a_3626_ = lean_ctor_get(v___x_3614_, 0);
v_a_3627_ = lean_ctor_get(v___x_3614_, 1);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3614_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_inc(v_a_3626_);
lean_dec(v___x_3614_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3626_);
lean_ctor_set(v_reuseFailAlloc_3633_, 1, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
}
else
{
lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
lean_dec_ref(v_self_3600_);
v___x_3635_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_3636_ = l_Lake_Job_async___redArg(v___x_3612_, v_build_3601_, v___x_3610_, v___x_3635_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_);
v___x_3637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3637_, 0, v___x_3636_);
lean_ctor_set(v___x_3637_, 1, v_a_3607_);
return v___x_3637_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___boxed(lean_object* v_self_3638_, lean_object* v_build_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_){
_start:
{
lean_object* v_res_3647_; 
v_res_3647_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3638_, v_build_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_);
lean_dec_ref(v_a_3644_);
lean_dec(v_a_3643_);
lean_dec(v_a_3642_);
lean_dec(v_a_3641_);
return v_res_3647_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync(lean_object* v_00_u03b1_3648_, lean_object* v_self_3649_, lean_object* v_build_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_){
_start:
{
lean_object* v___x_3658_; 
v___x_3658_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3649_, v_build_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_);
return v___x_3658_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___boxed(lean_object* v_00_u03b1_3659_, lean_object* v_self_3660_, lean_object* v_build_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = l_Lake_Package_afterBuildCacheSync(v_00_u03b1_3659_, v_self_3660_, v_build_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
lean_dec_ref(v_a_3666_);
lean_dec(v_a_3665_);
lean_dec(v_a_3664_);
lean_dec(v_a_3663_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(lean_object* v_k_3670_, lean_object* v_v_3671_, lean_object* v_t_3672_){
_start:
{
if (lean_obj_tag(v_t_3672_) == 0)
{
lean_object* v_size_3673_; lean_object* v_k_3674_; lean_object* v_v_3675_; lean_object* v_l_3676_; lean_object* v_r_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3957_; 
v_size_3673_ = lean_ctor_get(v_t_3672_, 0);
v_k_3674_ = lean_ctor_get(v_t_3672_, 1);
v_v_3675_ = lean_ctor_get(v_t_3672_, 2);
v_l_3676_ = lean_ctor_get(v_t_3672_, 3);
v_r_3677_ = lean_ctor_get(v_t_3672_, 4);
v_isSharedCheck_3957_ = !lean_is_exclusive(v_t_3672_);
if (v_isSharedCheck_3957_ == 0)
{
v___x_3679_ = v_t_3672_;
v_isShared_3680_ = v_isSharedCheck_3957_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_r_3677_);
lean_inc(v_l_3676_);
lean_inc(v_v_3675_);
lean_inc(v_k_3674_);
lean_inc(v_size_3673_);
lean_dec(v_t_3672_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3957_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
uint8_t v___x_3681_; 
v___x_3681_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3670_, v_k_3674_);
switch(v___x_3681_)
{
case 0:
{
lean_object* v_impl_3682_; lean_object* v___x_3683_; 
lean_dec(v_size_3673_);
v_impl_3682_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3670_, v_v_3671_, v_l_3676_);
v___x_3683_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3677_) == 0)
{
lean_object* v_size_3684_; lean_object* v_size_3685_; lean_object* v_k_3686_; lean_object* v_v_3687_; lean_object* v_l_3688_; lean_object* v_r_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; uint8_t v___x_3692_; 
v_size_3684_ = lean_ctor_get(v_r_3677_, 0);
v_size_3685_ = lean_ctor_get(v_impl_3682_, 0);
v_k_3686_ = lean_ctor_get(v_impl_3682_, 1);
v_v_3687_ = lean_ctor_get(v_impl_3682_, 2);
v_l_3688_ = lean_ctor_get(v_impl_3682_, 3);
v_r_3689_ = lean_ctor_get(v_impl_3682_, 4);
lean_inc(v_r_3689_);
v___x_3690_ = lean_unsigned_to_nat(3u);
v___x_3691_ = lean_nat_mul(v___x_3690_, v_size_3684_);
v___x_3692_ = lean_nat_dec_lt(v___x_3691_, v_size_3685_);
lean_dec(v___x_3691_);
if (v___x_3692_ == 0)
{
lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3696_; 
lean_dec(v_r_3689_);
v___x_3693_ = lean_nat_add(v___x_3683_, v_size_3685_);
v___x_3694_ = lean_nat_add(v___x_3693_, v_size_3684_);
lean_dec(v___x_3693_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 3, v_impl_3682_);
lean_ctor_set(v___x_3679_, 0, v___x_3694_);
v___x_3696_ = v___x_3679_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3694_);
lean_ctor_set(v_reuseFailAlloc_3697_, 1, v_k_3674_);
lean_ctor_set(v_reuseFailAlloc_3697_, 2, v_v_3675_);
lean_ctor_set(v_reuseFailAlloc_3697_, 3, v_impl_3682_);
lean_ctor_set(v_reuseFailAlloc_3697_, 4, v_r_3677_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
else
{
lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3763_; 
lean_inc(v_l_3688_);
lean_inc(v_v_3687_);
lean_inc(v_k_3686_);
lean_inc(v_size_3685_);
v_isSharedCheck_3763_ = !lean_is_exclusive(v_impl_3682_);
if (v_isSharedCheck_3763_ == 0)
{
lean_object* v_unused_3764_; lean_object* v_unused_3765_; lean_object* v_unused_3766_; lean_object* v_unused_3767_; lean_object* v_unused_3768_; 
v_unused_3764_ = lean_ctor_get(v_impl_3682_, 4);
lean_dec(v_unused_3764_);
v_unused_3765_ = lean_ctor_get(v_impl_3682_, 3);
lean_dec(v_unused_3765_);
v_unused_3766_ = lean_ctor_get(v_impl_3682_, 2);
lean_dec(v_unused_3766_);
v_unused_3767_ = lean_ctor_get(v_impl_3682_, 1);
lean_dec(v_unused_3767_);
v_unused_3768_ = lean_ctor_get(v_impl_3682_, 0);
lean_dec(v_unused_3768_);
v___x_3699_ = v_impl_3682_;
v_isShared_3700_ = v_isSharedCheck_3763_;
goto v_resetjp_3698_;
}
else
{
lean_dec(v_impl_3682_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3763_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v_size_3701_; lean_object* v_size_3702_; lean_object* v_k_3703_; lean_object* v_v_3704_; lean_object* v_l_3705_; lean_object* v_r_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; uint8_t v___x_3709_; 
v_size_3701_ = lean_ctor_get(v_l_3688_, 0);
v_size_3702_ = lean_ctor_get(v_r_3689_, 0);
v_k_3703_ = lean_ctor_get(v_r_3689_, 1);
v_v_3704_ = lean_ctor_get(v_r_3689_, 2);
v_l_3705_ = lean_ctor_get(v_r_3689_, 3);
v_r_3706_ = lean_ctor_get(v_r_3689_, 4);
v___x_3707_ = lean_unsigned_to_nat(2u);
v___x_3708_ = lean_nat_mul(v___x_3707_, v_size_3701_);
v___x_3709_ = lean_nat_dec_lt(v_size_3702_, v___x_3708_);
lean_dec(v___x_3708_);
if (v___x_3709_ == 0)
{
lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3738_; 
lean_inc(v_r_3706_);
lean_inc(v_l_3705_);
lean_inc(v_v_3704_);
lean_inc(v_k_3703_);
v_isSharedCheck_3738_ = !lean_is_exclusive(v_r_3689_);
if (v_isSharedCheck_3738_ == 0)
{
lean_object* v_unused_3739_; lean_object* v_unused_3740_; lean_object* v_unused_3741_; lean_object* v_unused_3742_; lean_object* v_unused_3743_; 
v_unused_3739_ = lean_ctor_get(v_r_3689_, 4);
lean_dec(v_unused_3739_);
v_unused_3740_ = lean_ctor_get(v_r_3689_, 3);
lean_dec(v_unused_3740_);
v_unused_3741_ = lean_ctor_get(v_r_3689_, 2);
lean_dec(v_unused_3741_);
v_unused_3742_ = lean_ctor_get(v_r_3689_, 1);
lean_dec(v_unused_3742_);
v_unused_3743_ = lean_ctor_get(v_r_3689_, 0);
lean_dec(v_unused_3743_);
v___x_3711_ = v_r_3689_;
v_isShared_3712_ = v_isSharedCheck_3738_;
goto v_resetjp_3710_;
}
else
{
lean_dec(v_r_3689_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3738_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___x_3726_; lean_object* v___y_3728_; 
v___x_3713_ = lean_nat_add(v___x_3683_, v_size_3685_);
lean_dec(v_size_3685_);
v___x_3714_ = lean_nat_add(v___x_3713_, v_size_3684_);
lean_dec(v___x_3713_);
v___x_3726_ = lean_nat_add(v___x_3683_, v_size_3701_);
if (lean_obj_tag(v_l_3705_) == 0)
{
lean_object* v_size_3736_; 
v_size_3736_ = lean_ctor_get(v_l_3705_, 0);
lean_inc(v_size_3736_);
v___y_3728_ = v_size_3736_;
goto v___jp_3727_;
}
else
{
lean_object* v___x_3737_; 
v___x_3737_ = lean_unsigned_to_nat(0u);
v___y_3728_ = v___x_3737_;
goto v___jp_3727_;
}
v___jp_3715_:
{
lean_object* v___x_3719_; lean_object* v___x_3721_; 
v___x_3719_ = lean_nat_add(v___y_3717_, v___y_3718_);
lean_dec(v___y_3718_);
lean_dec(v___y_3717_);
if (v_isShared_3712_ == 0)
{
lean_ctor_set(v___x_3711_, 4, v_r_3677_);
lean_ctor_set(v___x_3711_, 3, v_r_3706_);
lean_ctor_set(v___x_3711_, 2, v_v_3675_);
lean_ctor_set(v___x_3711_, 1, v_k_3674_);
lean_ctor_set(v___x_3711_, 0, v___x_3719_);
v___x_3721_ = v___x_3711_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3719_);
lean_ctor_set(v_reuseFailAlloc_3725_, 1, v_k_3674_);
lean_ctor_set(v_reuseFailAlloc_3725_, 2, v_v_3675_);
lean_ctor_set(v_reuseFailAlloc_3725_, 3, v_r_3706_);
lean_ctor_set(v_reuseFailAlloc_3725_, 4, v_r_3677_);
v___x_3721_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
lean_object* v___x_3723_; 
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 4, v___x_3721_);
lean_ctor_set(v___x_3699_, 3, v___y_3716_);
lean_ctor_set(v___x_3699_, 2, v_v_3704_);
lean_ctor_set(v___x_3699_, 1, v_k_3703_);
lean_ctor_set(v___x_3699_, 0, v___x_3714_);
v___x_3723_ = v___x_3699_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___x_3714_);
lean_ctor_set(v_reuseFailAlloc_3724_, 1, v_k_3703_);
lean_ctor_set(v_reuseFailAlloc_3724_, 2, v_v_3704_);
lean_ctor_set(v_reuseFailAlloc_3724_, 3, v___y_3716_);
lean_ctor_set(v_reuseFailAlloc_3724_, 4, v___x_3721_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
}
v___jp_3727_:
{
lean_object* v___x_3729_; lean_object* v___x_3731_; 
v___x_3729_ = lean_nat_add(v___x_3726_, v___y_3728_);
lean_dec(v___y_3728_);
lean_dec(v___x_3726_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 4, v_l_3705_);
lean_ctor_set(v___x_3679_, 3, v_l_3688_);
lean_ctor_set(v___x_3679_, 2, v_v_3687_);
lean_ctor_set(v___x_3679_, 1, v_k_3686_);
lean_ctor_set(v___x_3679_, 0, v___x_3729_);
v___x_3731_ = v___x_3679_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3729_);
lean_ctor_set(v_reuseFailAlloc_3735_, 1, v_k_3686_);
lean_ctor_set(v_reuseFailAlloc_3735_, 2, v_v_3687_);
lean_ctor_set(v_reuseFailAlloc_3735_, 3, v_l_3688_);
lean_ctor_set(v_reuseFailAlloc_3735_, 4, v_l_3705_);
v___x_3731_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
lean_object* v___x_3732_; 
v___x_3732_ = lean_nat_add(v___x_3683_, v_size_3684_);
if (lean_obj_tag(v_r_3706_) == 0)
{
lean_object* v_size_3733_; 
v_size_3733_ = lean_ctor_get(v_r_3706_, 0);
lean_inc(v_size_3733_);
v___y_3716_ = v___x_3731_;
v___y_3717_ = v___x_3732_;
v___y_3718_ = v_size_3733_;
goto v___jp_3715_;
}
else
{
lean_object* v___x_3734_; 
v___x_3734_ = lean_unsigned_to_nat(0u);
v___y_3716_ = v___x_3731_;
v___y_3717_ = v___x_3732_;
v___y_3718_ = v___x_3734_;
goto v___jp_3715_;
}
}
}
}
}
else
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3749_; 
lean_del_object(v___x_3679_);
v___x_3744_ = lean_nat_add(v___x_3683_, v_size_3685_);
lean_dec(v_size_3685_);
v___x_3745_ = lean_nat_add(v___x_3744_, v_size_3684_);
lean_dec(v___x_3744_);
v___x_3746_ = lean_nat_add(v___x_3683_, v_size_3684_);
v___x_3747_ = lean_nat_add(v___x_3746_, v_size_3702_);
lean_dec(v___x_3746_);
lean_inc_ref(v_r_3677_);
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 4, v_r_3677_);
lean_ctor_set(v___x_3699_, 3, v_r_3689_);
lean_ctor_set(v___x_3699_, 2, v_v_3675_);
lean_ctor_set(v___x_3699_, 1, v_k_3674_);
lean_ctor_set(v___x_3699_, 0, v___x_3747_);
v___x_3749_ = v___x_3699_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v___x_3747_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v_k_3674_);
lean_ctor_set(v_reuseFailAlloc_3762_, 2, v_v_3675_);
lean_ctor_set(v_reuseFailAlloc_3762_, 3, v_r_3689_);
lean_ctor_set(v_reuseFailAlloc_3762_, 4, v_r_3677_);
v___x_3749_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
v_isSharedCheck_3756_ = !lean_is_exclusive(v_r_3677_);
if (v_isSharedCheck_3756_ == 0)
{
lean_object* v_unused_3757_; lean_object* v_unused_3758_; lean_object* v_unused_3759_; lean_object* v_unused_3760_; lean_object* v_unused_3761_; 
v_unused_3757_ = lean_ctor_get(v_r_3677_, 4);
lean_dec(v_unused_3757_);
v_unused_3758_ = lean_ctor_get(v_r_3677_, 3);
lean_dec(v_unused_3758_);
v_unused_3759_ = lean_ctor_get(v_r_3677_, 2);
lean_dec(v_unused_3759_);
v_unused_3760_ = lean_ctor_get(v_r_3677_, 1);
lean_dec(v_unused_3760_);
v_unused_3761_ = lean_ctor_get(v_r_3677_, 0);
lean_dec(v_unused_3761_);
v___x_3751_ = v_r_3677_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_dec(v_r_3677_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
lean_ctor_set(v___x_3751_, 4, v___x_3749_);
lean_ctor_set(v___x_3751_, 3, v_l_3688_);
lean_ctor_set(v___x_3751_, 2, v_v_3687_);
lean_ctor_set(v___x_3751_, 1, v_k_3686_);
lean_ctor_set(v___x_3751_, 0, v___x_3745_);
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v___x_3745_);
lean_ctor_set(v_reuseFailAlloc_3755_, 1, v_k_3686_);
lean_ctor_set(v_reuseFailAlloc_3755_, 2, v_v_3687_);
lean_ctor_set(v_reuseFailAlloc_3755_, 3, v_l_3688_);
lean_ctor_set(v_reuseFailAlloc_3755_, 4, v___x_3749_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3769_; 
v_l_3769_ = lean_ctor_get(v_impl_3682_, 3);
if (lean_obj_tag(v_l_3769_) == 0)
{
lean_object* v_r_3770_; lean_object* v_k_3771_; lean_object* v_v_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3783_; 
lean_inc_ref(v_l_3769_);
v_r_3770_ = lean_ctor_get(v_impl_3682_, 4);
v_k_3771_ = lean_ctor_get(v_impl_3682_, 1);
v_v_3772_ = lean_ctor_get(v_impl_3682_, 2);
v_isSharedCheck_3783_ = !lean_is_exclusive(v_impl_3682_);
if (v_isSharedCheck_3783_ == 0)
{
lean_object* v_unused_3784_; lean_object* v_unused_3785_; 
v_unused_3784_ = lean_ctor_get(v_impl_3682_, 3);
lean_dec(v_unused_3784_);
v_unused_3785_ = lean_ctor_get(v_impl_3682_, 0);
lean_dec(v_unused_3785_);
v___x_3774_ = v_impl_3682_;
v_isShared_3775_ = v_isSharedCheck_3783_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_r_3770_);
lean_inc(v_v_3772_);
lean_inc(v_k_3771_);
lean_dec(v_impl_3682_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3783_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3776_; lean_object* v___x_3778_; 
v___x_3776_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3770_);
if (v_isShared_3775_ == 0)
{
lean_ctor_set(v___x_3774_, 3, v_r_3770_);
lean_ctor_set(v___x_3774_, 2, v_v_3675_);
lean_ctor_set(v___x_3774_, 1, v_k_3674_);
lean_ctor_set(v___x_3774_, 0, v___x_3683_);
v___x_3778_ = v___x_3774_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3683_);
lean_ctor_set(v_reuseFailAlloc_3782_, 1, v_k_3674_);
lean_ctor_set(v_reuseFailAlloc_3782_, 2, v_v_3675_);
lean_ctor_set(v_reuseFailAlloc_3782_, 3, v_r_3770_);
lean_ctor_set(v_reuseFailAlloc_3782_, 4, v_r_3770_);
v___x_3778_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
lean_object* v___x_3780_; 
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 4, v___x_3778_);
lean_ctor_set(v___x_3679_, 3, v_l_3769_);
lean_ctor_set(v___x_3679_, 2, v_v_3772_);
lean_ctor_set(v___x_3679_, 1, v_k_3771_);
lean_ctor_set(v___x_3679_, 0, v___x_3776_);
v___x_3780_ = v___x_3679_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3776_);
lean_ctor_set(v_reuseFailAlloc_3781_, 1, v_k_3771_);
lean_ctor_set(v_reuseFailAlloc_3781_, 2, v_v_3772_);
lean_ctor_set(v_reuseFailAlloc_3781_, 3, v_l_3769_);
lean_ctor_set(v_reuseFailAlloc_3781_, 4, v___x_3778_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
else
{
lean_object* v_r_3786_; 
v_r_3786_ = lean_ctor_get(v_impl_3682_, 4);
lean_inc(v_r_3786_);
if (lean_obj_tag(v_r_3786_) == 0)
{
lean_object* v_k_3787_; lean_object* v_v_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3811_; 
lean_inc(v_l_3769_);
v_k_3787_ = lean_ctor_get(v_impl_3682_, 1);
v_v_3788_ = lean_ctor_get(v_impl_3682_, 2);
v_isSharedCheck_3811_ = !lean_is_exclusive(v_impl_3682_);
if (v_isSharedCheck_3811_ == 0)
{
lean_object* v_unused_3812_; lean_object* v_unused_3813_; lean_object* v_unused_3814_; 
v_unused_3812_ = lean_ctor_get(v_impl_3682_, 4);
lean_dec(v_unused_3812_);
v_unused_3813_ = lean_ctor_get(v_impl_3682_, 3);
lean_dec(v_unused_3813_);
v_unused_3814_ = lean_ctor_get(v_impl_3682_, 0);
lean_dec(v_unused_3814_);
v___x_3790_ = v_impl_3682_;
v_isShared_3791_ = v_isSharedCheck_3811_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_v_3788_);
lean_inc(v_k_3787_);
lean_dec(v_impl_3682_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3811_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v_k_3792_; lean_object* v_v_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3807_; 
v_k_3792_ = lean_ctor_get(v_r_3786_, 1);
v_v_3793_ = lean_ctor_get(v_r_3786_, 2);
v_isSharedCheck_3807_ = !lean_is_exclusive(v_r_3786_);
if (v_isSharedCheck_3807_ == 0)
{
lean_object* v_unused_3808_; lean_object* v_unused_3809_; lean_object* v_unused_3810_; 
v_unused_3808_ = lean_ctor_get(v_r_3786_, 4);
lean_dec(v_unused_3808_);
v_unused_3809_ = lean_ctor_get(v_r_3786_, 3);
lean_dec(v_unused_3809_);
v_unused_3810_ = lean_ctor_get(v_r_3786_, 0);
lean_dec(v_unused_3810_);
v___x_3795_ = v_r_3786_;
v_isShared_3796_ = v_isSharedCheck_3807_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_v_3793_);
lean_inc(v_k_3792_);
lean_dec(v_r_3786_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3807_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3797_; lean_object* v___x_3799_; 
v___x_3797_ = lean_unsigned_to_nat(3u);
if (v_isShared_3796_ == 0)
{
lean_ctor_set(v___x_3795_, 4, v_l_3769_);
lean_ctor_set(v___x_3795_, 3, v_l_3769_);
lean_ctor_set(v___x_3795_, 2, v_v_3788_);
lean_ctor_set(v___x_3795_, 1, v_k_3787_);
lean_ctor_set(v___x_3795_, 0, v___x_3683_);
v___x_3799_ = v___x_3795_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3683_);
lean_ctor_set(v_reuseFailAlloc_3806_, 1, v_k_3787_);
lean_ctor_set(v_reuseFailAlloc_3806_, 2, v_v_3788_);
lean_ctor_set(v_reuseFailAlloc_3806_, 3, v_l_3769_);
lean_ctor_set(v_reuseFailAlloc_3806_, 4, v_l_3769_);
v___x_3799_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
lean_object* v___x_3801_; 
if (v_isShared_3791_ == 0)
{
lean_ctor_set(v___x_3790_, 4, v_l_3769_);
lean_ctor_set(v___x_3790_, 2, v_v_3675_);
lean_ctor_set(v___x_3790_, 1, v_k_3674_);
lean_ctor_set(v___x_3790_, 0, v___x_3683_);
v___x_3801_ = v___x_3790_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v___x_3683_);
lean_ctor_set(v_reuseFailAlloc_3805_, 1, v_k_3674_);
lean_ctor_set(v_reuseFailAlloc_3805_, 2, v_v_3675_);
lean_ctor_set(v_reuseFailAlloc_3805_, 3, v_l_3769_);
lean_ctor_set(v_reuseFailAlloc_3805_, 4, v_l_3769_);
v___x_3801_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
lean_object* v___x_3803_; 
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 4, v___x_3801_);
lean_ctor_set(v___x_3679_, 3, v___x_3799_);
lean_ctor_set(v___x_3679_, 2, v_v_3793_);
lean_ctor_set(v___x_3679_, 1, v_k_3792_);
lean_ctor_set(v___x_3679_, 0, v___x_3797_);
v___x_3803_ = v___x_3679_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v___x_3797_);
lean_ctor_set(v_reuseFailAlloc_3804_, 1, v_k_3792_);
lean_ctor_set(v_reuseFailAlloc_3804_, 2, v_v_3793_);
lean_ctor_set(v_reuseFailAlloc_3804_, 3, v___x_3799_);
lean_ctor_set(v_reuseFailAlloc_3804_, 4, v___x_3801_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
}
}
}
else
{
lean_object* v___x_3815_; lean_object* v___x_3817_; 
v___x_3815_ = lean_unsigned_to_nat(2u);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 4, v_r_3786_);
lean_ctor_set(v___x_3679_, 3, v_impl_3682_);
lean_ctor_set(v___x_3679_, 0, v___x_3815_);
v___x_3817_ = v___x_3679_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3815_);
lean_ctor_set(v_reuseFailAlloc_3818_, 1, v_k_3674_);
lean_ctor_set(v_reuseFailAlloc_3818_, 2, v_v_3675_);
lean_ctor_set(v_reuseFailAlloc_3818_, 3, v_impl_3682_);
lean_ctor_set(v_reuseFailAlloc_3818_, 4, v_r_3786_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3820_; 
lean_dec(v_v_3675_);
lean_dec(v_k_3674_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 2, v_v_3671_);
lean_ctor_set(v___x_3679_, 1, v_k_3670_);
v___x_3820_ = v___x_3679_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_size_3673_);
lean_ctor_set(v_reuseFailAlloc_3821_, 1, v_k_3670_);
lean_ctor_set(v_reuseFailAlloc_3821_, 2, v_v_3671_);
lean_ctor_set(v_reuseFailAlloc_3821_, 3, v_l_3676_);
lean_ctor_set(v_reuseFailAlloc_3821_, 4, v_r_3677_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
default: 
{
lean_object* v_impl_3822_; lean_object* v___x_3823_; 
lean_dec(v_size_3673_);
v_impl_3822_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3670_, v_v_3671_, v_r_3677_);
v___x_3823_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3676_) == 0)
{
lean_object* v_size_3824_; lean_object* v_size_3825_; lean_object* v_k_3826_; lean_object* v_v_3827_; lean_object* v_l_3828_; lean_object* v_r_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; uint8_t v___x_3832_; 
v_size_3824_ = lean_ctor_get(v_l_3676_, 0);
v_size_3825_ = lean_ctor_get(v_impl_3822_, 0);
v_k_3826_ = lean_ctor_get(v_impl_3822_, 1);
v_v_3827_ = lean_ctor_get(v_impl_3822_, 2);
v_l_3828_ = lean_ctor_get(v_impl_3822_, 3);
lean_inc(v_l_3828_);
v_r_3829_ = lean_ctor_get(v_impl_3822_, 4);
v___x_3830_ = lean_unsigned_to_nat(3u);
v___x_3831_ = lean_nat_mul(v___x_3830_, v_size_3824_);
v___x_3832_ = lean_nat_dec_lt(v___x_3831_, v_size_3825_);
lean_dec(v___x_3831_);
if (v___x_3832_ == 0)
{
lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3836_; 
lean_dec(v_l_3828_);
v___x_3833_ = lean_nat_add(v___x_3823_, v_size_3824_);
v___x_3834_ = lean_nat_add(v___x_3833_, v_size_3825_);
lean_dec(v___x_3833_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 4, v_impl_3822_);
lean_ctor_set(v___x_3679_, 0, v___x_3834_);
v___x_3836_ = v___x_3679_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v___x_3834_);
lean_ctor_set(v_reuseFailAlloc_3837_, 1, v_k_3674_);
lean_ctor_set(v_reuseFailAlloc_3837_, 2, v_v_3675_);
lean_ctor_set(v_reuseFailAlloc_3837_, 3, v_l_3676_);
lean_ctor_set(v_reuseFailAlloc_3837_, 4, v_impl_3822_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
else
{
lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3901_; 
lean_inc(v_r_3829_);
lean_inc(v_v_3827_);
lean_inc(v_k_3826_);
lean_inc(v_size_3825_);
v_isSharedCheck_3901_ = !lean_is_exclusive(v_impl_3822_);
if (v_isSharedCheck_3901_ == 0)
{
lean_object* v_unused_3902_; lean_object* v_unused_3903_; lean_object* v_unused_3904_; lean_object* v_unused_3905_; lean_object* v_unused_3906_; 
v_unused_3902_ = lean_ctor_get(v_impl_3822_, 4);
lean_dec(v_unused_3902_);
v_unused_3903_ = lean_ctor_get(v_impl_3822_, 3);
lean_dec(v_unused_3903_);
v_unused_3904_ = lean_ctor_get(v_impl_3822_, 2);
lean_dec(v_unused_3904_);
v_unused_3905_ = lean_ctor_get(v_impl_3822_, 1);
lean_dec(v_unused_3905_);
v_unused_3906_ = lean_ctor_get(v_impl_3822_, 0);
lean_dec(v_unused_3906_);
v___x_3839_ = v_impl_3822_;
v_isShared_3840_ = v_isSharedCheck_3901_;
goto v_resetjp_3838_;
}
else
{
lean_dec(v_impl_3822_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3901_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v_size_3841_; lean_object* v_k_3842_; lean_object* v_v_3843_; lean_object* v_l_3844_; lean_object* v_r_3845_; lean_object* v_size_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; uint8_t v___x_3849_; 
v_size_3841_ = lean_ctor_get(v_l_3828_, 0);
v_k_3842_ = lean_ctor_get(v_l_3828_, 1);
v_v_3843_ = lean_ctor_get(v_l_3828_, 2);
v_l_3844_ = lean_ctor_get(v_l_3828_, 3);
v_r_3845_ = lean_ctor_get(v_l_3828_, 4);
v_size_3846_ = lean_ctor_get(v_r_3829_, 0);
v___x_3847_ = lean_unsigned_to_nat(2u);
v___x_3848_ = lean_nat_mul(v___x_3847_, v_size_3846_);
v___x_3849_ = lean_nat_dec_lt(v_size_3841_, v___x_3848_);
lean_dec(v___x_3848_);
if (v___x_3849_ == 0)
{
lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3877_; 
lean_inc(v_r_3845_);
lean_inc(v_l_3844_);
lean_inc(v_v_3843_);
lean_inc(v_k_3842_);
v_isSharedCheck_3877_ = !lean_is_exclusive(v_l_3828_);
if (v_isSharedCheck_3877_ == 0)
{
lean_object* v_unused_3878_; lean_object* v_unused_3879_; lean_object* v_unused_3880_; lean_object* v_unused_3881_; lean_object* v_unused_3882_; 
v_unused_3878_ = lean_ctor_get(v_l_3828_, 4);
lean_dec(v_unused_3878_);
v_unused_3879_ = lean_ctor_get(v_l_3828_, 3);
lean_dec(v_unused_3879_);
v_unused_3880_ = lean_ctor_get(v_l_3828_, 2);
lean_dec(v_unused_3880_);
v_unused_3881_ = lean_ctor_get(v_l_3828_, 1);
lean_dec(v_unused_3881_);
v_unused_3882_ = lean_ctor_get(v_l_3828_, 0);
lean_dec(v_unused_3882_);
v___x_3851_ = v_l_3828_;
v_isShared_3852_ = v_isSharedCheck_3877_;
goto v_resetjp_3850_;
}
else
{
lean_dec(v_l_3828_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3877_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3867_; 
v___x_3853_ = lean_nat_add(v___x_3823_, v_size_3824_);
v___x_3854_ = lean_nat_add(v___x_3853_, v_size_3825_);
lean_dec(v_size_3825_);
if (lean_obj_tag(v_l_3844_) == 0)
{
lean_object* v_size_3875_; 
v_size_3875_ = lean_ctor_get(v_l_3844_, 0);
lean_inc(v_size_3875_);
v___y_3867_ = v_size_3875_;
goto v___jp_3866_;
}
else
{
lean_object* v___x_3876_; 
v___x_3876_ = lean_unsigned_to_nat(0u);
v___y_3867_ = v___x_3876_;
goto v___jp_3866_;
}
v___jp_3855_:
{
lean_object* v___x_3859_; lean_object* v___x_3861_; 
v___x_3859_ = lean_nat_add(v___y_3857_, v___y_3858_);
lean_dec(v___y_3858_);
lean_dec(v___y_3857_);
if (v_isShared_3852_ == 0)
{
lean_ctor_set(v___x_3851_, 4, v_r_3829_);
lean_ctor_set(v___x_3851_, 3, v_r_3845_);
lean_ctor_set(v___x_3851_, 2, v_v_3827_);
lean_ctor_set(v___x_3851_, 1, v_k_3826_);
lean_ctor_set(v___x_3851_, 0, v___x_3859_);
v___x_3861_ = v___x_3851_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3859_);
lean_ctor_set(v_reuseFailAlloc_3865_, 1, v_k_3826_);
lean_ctor_set(v_reuseFailAlloc_3865_, 2, v_v_3827_);
lean_ctor_set(v_reuseFailAlloc_3865_, 3, v_r_3845_);
lean_ctor_set(v_reuseFailAlloc_3865_, 4, v_r_3829_);
v___x_3861_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
lean_object* v___x_3863_; 
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 4, v___x_3861_);
lean_ctor_set(v___x_3839_, 3, v___y_3856_);
lean_ctor_set(v___x_3839_, 2, v_v_3843_);
lean_ctor_set(v___x_3839_, 1, v_k_3842_);
lean_ctor_set(v___x_3839_, 0, v___x_3854_);
v___x_3863_ = v___x_3839_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3854_);
lean_ctor_set(v_reuseFailAlloc_3864_, 1, v_k_3842_);
lean_ctor_set(v_reuseFailAlloc_3864_, 2, v_v_3843_);
lean_ctor_set(v_reuseFailAlloc_3864_, 3, v___y_3856_);
lean_ctor_set(v_reuseFailAlloc_3864_, 4, v___x_3861_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
v___jp_3866_:
{
lean_object* v___x_3868_; lean_object* v___x_3870_; 
v___x_3868_ = lean_nat_add(v___x_3853_, v___y_3867_);
lean_dec(v___y_3867_);
lean_dec(v___x_3853_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 4, v_l_3844_);
lean_ctor_set(v___x_3679_, 0, v___x_3868_);
v___x_3870_ = v___x_3679_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v___x_3868_);
lean_ctor_set(v_reuseFailAlloc_3874_, 1, v_k_3674_);
lean_ctor_set(v_reuseFailAlloc_3874_, 2, v_v_3675_);
lean_ctor_set(v_reuseFailAlloc_3874_, 3, v_l_3676_);
lean_ctor_set(v_reuseFailAlloc_3874_, 4, v_l_3844_);
v___x_3870_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
lean_object* v___x_3871_; 
v___x_3871_ = lean_nat_add(v___x_3823_, v_size_3846_);
if (lean_obj_tag(v_r_3845_) == 0)
{
lean_object* v_size_3872_; 
v_size_3872_ = lean_ctor_get(v_r_3845_, 0);
lean_inc(v_size_3872_);
v___y_3856_ = v___x_3870_;
v___y_3857_ = v___x_3871_;
v___y_3858_ = v_size_3872_;
goto v___jp_3855_;
}
else
{
lean_object* v___x_3873_; 
v___x_3873_ = lean_unsigned_to_nat(0u);
v___y_3856_ = v___x_3870_;
v___y_3857_ = v___x_3871_;
v___y_3858_ = v___x_3873_;
goto v___jp_3855_;
}
}
}
}
}
else
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3887_; 
lean_del_object(v___x_3679_);
v___x_3883_ = lean_nat_add(v___x_3823_, v_size_3824_);
v___x_3884_ = lean_nat_add(v___x_3883_, v_size_3825_);
lean_dec(v_size_3825_);
v___x_3885_ = lean_nat_add(v___x_3883_, v_size_3841_);
lean_dec(v___x_3883_);
lean_inc_ref(v_l_3676_);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 4, v_l_3828_);
lean_ctor_set(v___x_3839_, 3, v_l_3676_);
lean_ctor_set(v___x_3839_, 2, v_v_3675_);
lean_ctor_set(v___x_3839_, 1, v_k_3674_);
lean_ctor_set(v___x_3839_, 0, v___x_3885_);
v___x_3887_ = v___x_3839_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v___x_3885_);
lean_ctor_set(v_reuseFailAlloc_3900_, 1, v_k_3674_);
lean_ctor_set(v_reuseFailAlloc_3900_, 2, v_v_3675_);
lean_ctor_set(v_reuseFailAlloc_3900_, 3, v_l_3676_);
lean_ctor_set(v_reuseFailAlloc_3900_, 4, v_l_3828_);
v___x_3887_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3894_; 
v_isSharedCheck_3894_ = !lean_is_exclusive(v_l_3676_);
if (v_isSharedCheck_3894_ == 0)
{
lean_object* v_unused_3895_; lean_object* v_unused_3896_; lean_object* v_unused_3897_; lean_object* v_unused_3898_; lean_object* v_unused_3899_; 
v_unused_3895_ = lean_ctor_get(v_l_3676_, 4);
lean_dec(v_unused_3895_);
v_unused_3896_ = lean_ctor_get(v_l_3676_, 3);
lean_dec(v_unused_3896_);
v_unused_3897_ = lean_ctor_get(v_l_3676_, 2);
lean_dec(v_unused_3897_);
v_unused_3898_ = lean_ctor_get(v_l_3676_, 1);
lean_dec(v_unused_3898_);
v_unused_3899_ = lean_ctor_get(v_l_3676_, 0);
lean_dec(v_unused_3899_);
v___x_3889_ = v_l_3676_;
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
else
{
lean_dec(v_l_3676_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3892_; 
if (v_isShared_3890_ == 0)
{
lean_ctor_set(v___x_3889_, 4, v_r_3829_);
lean_ctor_set(v___x_3889_, 3, v___x_3887_);
lean_ctor_set(v___x_3889_, 2, v_v_3827_);
lean_ctor_set(v___x_3889_, 1, v_k_3826_);
lean_ctor_set(v___x_3889_, 0, v___x_3884_);
v___x_3892_ = v___x_3889_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v___x_3884_);
lean_ctor_set(v_reuseFailAlloc_3893_, 1, v_k_3826_);
lean_ctor_set(v_reuseFailAlloc_3893_, 2, v_v_3827_);
lean_ctor_set(v_reuseFailAlloc_3893_, 3, v___x_3887_);
lean_ctor_set(v_reuseFailAlloc_3893_, 4, v_r_3829_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
return v___x_3892_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3907_; 
v_l_3907_ = lean_ctor_get(v_impl_3822_, 3);
lean_inc(v_l_3907_);
if (lean_obj_tag(v_l_3907_) == 0)
{
lean_object* v_r_3908_; lean_object* v_k_3909_; lean_object* v_v_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3933_; 
v_r_3908_ = lean_ctor_get(v_impl_3822_, 4);
v_k_3909_ = lean_ctor_get(v_impl_3822_, 1);
v_v_3910_ = lean_ctor_get(v_impl_3822_, 2);
v_isSharedCheck_3933_ = !lean_is_exclusive(v_impl_3822_);
if (v_isSharedCheck_3933_ == 0)
{
lean_object* v_unused_3934_; lean_object* v_unused_3935_; 
v_unused_3934_ = lean_ctor_get(v_impl_3822_, 3);
lean_dec(v_unused_3934_);
v_unused_3935_ = lean_ctor_get(v_impl_3822_, 0);
lean_dec(v_unused_3935_);
v___x_3912_ = v_impl_3822_;
v_isShared_3913_ = v_isSharedCheck_3933_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_r_3908_);
lean_inc(v_v_3910_);
lean_inc(v_k_3909_);
lean_dec(v_impl_3822_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3933_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v_k_3914_; lean_object* v_v_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3929_; 
v_k_3914_ = lean_ctor_get(v_l_3907_, 1);
v_v_3915_ = lean_ctor_get(v_l_3907_, 2);
v_isSharedCheck_3929_ = !lean_is_exclusive(v_l_3907_);
if (v_isSharedCheck_3929_ == 0)
{
lean_object* v_unused_3930_; lean_object* v_unused_3931_; lean_object* v_unused_3932_; 
v_unused_3930_ = lean_ctor_get(v_l_3907_, 4);
lean_dec(v_unused_3930_);
v_unused_3931_ = lean_ctor_get(v_l_3907_, 3);
lean_dec(v_unused_3931_);
v_unused_3932_ = lean_ctor_get(v_l_3907_, 0);
lean_dec(v_unused_3932_);
v___x_3917_ = v_l_3907_;
v_isShared_3918_ = v_isSharedCheck_3929_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_v_3915_);
lean_inc(v_k_3914_);
lean_dec(v_l_3907_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3929_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3919_; lean_object* v___x_3921_; 
v___x_3919_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3908_, 2);
if (v_isShared_3918_ == 0)
{
lean_ctor_set(v___x_3917_, 4, v_r_3908_);
lean_ctor_set(v___x_3917_, 3, v_r_3908_);
lean_ctor_set(v___x_3917_, 2, v_v_3675_);
lean_ctor_set(v___x_3917_, 1, v_k_3674_);
lean_ctor_set(v___x_3917_, 0, v___x_3823_);
v___x_3921_ = v___x_3917_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3823_);
lean_ctor_set(v_reuseFailAlloc_3928_, 1, v_k_3674_);
lean_ctor_set(v_reuseFailAlloc_3928_, 2, v_v_3675_);
lean_ctor_set(v_reuseFailAlloc_3928_, 3, v_r_3908_);
lean_ctor_set(v_reuseFailAlloc_3928_, 4, v_r_3908_);
v___x_3921_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
lean_object* v___x_3923_; 
lean_inc(v_r_3908_);
if (v_isShared_3913_ == 0)
{
lean_ctor_set(v___x_3912_, 3, v_r_3908_);
lean_ctor_set(v___x_3912_, 0, v___x_3823_);
v___x_3923_ = v___x_3912_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3823_);
lean_ctor_set(v_reuseFailAlloc_3927_, 1, v_k_3909_);
lean_ctor_set(v_reuseFailAlloc_3927_, 2, v_v_3910_);
lean_ctor_set(v_reuseFailAlloc_3927_, 3, v_r_3908_);
lean_ctor_set(v_reuseFailAlloc_3927_, 4, v_r_3908_);
v___x_3923_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
lean_object* v___x_3925_; 
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 4, v___x_3923_);
lean_ctor_set(v___x_3679_, 3, v___x_3921_);
lean_ctor_set(v___x_3679_, 2, v_v_3915_);
lean_ctor_set(v___x_3679_, 1, v_k_3914_);
lean_ctor_set(v___x_3679_, 0, v___x_3919_);
v___x_3925_ = v___x_3679_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3919_);
lean_ctor_set(v_reuseFailAlloc_3926_, 1, v_k_3914_);
lean_ctor_set(v_reuseFailAlloc_3926_, 2, v_v_3915_);
lean_ctor_set(v_reuseFailAlloc_3926_, 3, v___x_3921_);
lean_ctor_set(v_reuseFailAlloc_3926_, 4, v___x_3923_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
}
}
else
{
lean_object* v_r_3936_; 
v_r_3936_ = lean_ctor_get(v_impl_3822_, 4);
lean_inc(v_r_3936_);
if (lean_obj_tag(v_r_3936_) == 0)
{
lean_object* v_k_3937_; lean_object* v_v_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3949_; 
v_k_3937_ = lean_ctor_get(v_impl_3822_, 1);
v_v_3938_ = lean_ctor_get(v_impl_3822_, 2);
v_isSharedCheck_3949_ = !lean_is_exclusive(v_impl_3822_);
if (v_isSharedCheck_3949_ == 0)
{
lean_object* v_unused_3950_; lean_object* v_unused_3951_; lean_object* v_unused_3952_; 
v_unused_3950_ = lean_ctor_get(v_impl_3822_, 4);
lean_dec(v_unused_3950_);
v_unused_3951_ = lean_ctor_get(v_impl_3822_, 3);
lean_dec(v_unused_3951_);
v_unused_3952_ = lean_ctor_get(v_impl_3822_, 0);
lean_dec(v_unused_3952_);
v___x_3940_ = v_impl_3822_;
v_isShared_3941_ = v_isSharedCheck_3949_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_v_3938_);
lean_inc(v_k_3937_);
lean_dec(v_impl_3822_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3949_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3942_; lean_object* v___x_3944_; 
v___x_3942_ = lean_unsigned_to_nat(3u);
if (v_isShared_3941_ == 0)
{
lean_ctor_set(v___x_3940_, 4, v_l_3907_);
lean_ctor_set(v___x_3940_, 2, v_v_3675_);
lean_ctor_set(v___x_3940_, 1, v_k_3674_);
lean_ctor_set(v___x_3940_, 0, v___x_3823_);
v___x_3944_ = v___x_3940_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3823_);
lean_ctor_set(v_reuseFailAlloc_3948_, 1, v_k_3674_);
lean_ctor_set(v_reuseFailAlloc_3948_, 2, v_v_3675_);
lean_ctor_set(v_reuseFailAlloc_3948_, 3, v_l_3907_);
lean_ctor_set(v_reuseFailAlloc_3948_, 4, v_l_3907_);
v___x_3944_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
lean_object* v___x_3946_; 
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 4, v_r_3936_);
lean_ctor_set(v___x_3679_, 3, v___x_3944_);
lean_ctor_set(v___x_3679_, 2, v_v_3938_);
lean_ctor_set(v___x_3679_, 1, v_k_3937_);
lean_ctor_set(v___x_3679_, 0, v___x_3942_);
v___x_3946_ = v___x_3679_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3942_);
lean_ctor_set(v_reuseFailAlloc_3947_, 1, v_k_3937_);
lean_ctor_set(v_reuseFailAlloc_3947_, 2, v_v_3938_);
lean_ctor_set(v_reuseFailAlloc_3947_, 3, v___x_3944_);
lean_ctor_set(v_reuseFailAlloc_3947_, 4, v_r_3936_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
}
}
else
{
lean_object* v___x_3953_; lean_object* v___x_3955_; 
v___x_3953_ = lean_unsigned_to_nat(2u);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 4, v_impl_3822_);
lean_ctor_set(v___x_3679_, 3, v_r_3936_);
lean_ctor_set(v___x_3679_, 0, v___x_3953_);
v___x_3955_ = v___x_3679_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v___x_3953_);
lean_ctor_set(v_reuseFailAlloc_3956_, 1, v_k_3674_);
lean_ctor_set(v_reuseFailAlloc_3956_, 2, v_v_3675_);
lean_ctor_set(v_reuseFailAlloc_3956_, 3, v_r_3936_);
lean_ctor_set(v_reuseFailAlloc_3956_, 4, v_impl_3822_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
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
lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3958_ = lean_unsigned_to_nat(1u);
v___x_3959_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3958_);
lean_ctor_set(v___x_3959_, 1, v_k_3670_);
lean_ctor_set(v___x_3959_, 2, v_v_3671_);
lean_ctor_set(v___x_3959_, 3, v_t_3672_);
lean_ctor_set(v___x_3959_, 4, v_t_3672_);
return v___x_3959_;
}
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3960_ = lean_box(1);
v___x_3961_ = l_Lake_Package_depsFacetConfig;
v___x_3962_ = l_Lake_Package_depsFacet;
v___x_3963_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3962_, v___x_3961_, v___x_3960_);
return v___x_3963_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; 
v___x_3964_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__0, &l_Lake_Package_initFacetConfigs___closed__0_once, _init_l_Lake_Package_initFacetConfigs___closed__0);
v___x_3965_ = l_Lake_Package_transDepsFacetConfig;
v___x_3966_ = l_Lake_Package_transDepsFacet;
v___x_3967_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3966_, v___x_3965_, v___x_3964_);
return v___x_3967_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3968_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__1, &l_Lake_Package_initFacetConfigs___closed__1_once, _init_l_Lake_Package_initFacetConfigs___closed__1);
v___x_3969_ = l_Lake_Package_defaultModulesFacetConfig;
v___x_3970_ = l_Lake_Package_defaultModulesFacet;
v___x_3971_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3970_, v___x_3969_, v___x_3968_);
return v___x_3971_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3972_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__2, &l_Lake_Package_initFacetConfigs___closed__2_once, _init_l_Lake_Package_initFacetConfigs___closed__2);
v___x_3973_ = l_Lake_Package_extraDepFacetConfig;
v___x_3974_ = l_Lake_Package_extraDepFacet;
v___x_3975_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3974_, v___x_3973_, v___x_3972_);
return v___x_3975_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3976_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__3, &l_Lake_Package_initFacetConfigs___closed__3_once, _init_l_Lake_Package_initFacetConfigs___closed__3);
v___x_3977_ = l_Lake_Package_optBuildCacheFacetConfig;
v___x_3978_ = l_Lake_Package_optBuildCacheFacet;
v___x_3979_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3978_, v___x_3977_, v___x_3976_);
return v___x_3979_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3980_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__4, &l_Lake_Package_initFacetConfigs___closed__4_once, _init_l_Lake_Package_initFacetConfigs___closed__4);
v___x_3981_ = l_Lake_Package_buildCacheFacetConfig;
v___x_3982_ = l_Lake_Package_buildCacheFacet;
v___x_3983_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3982_, v___x_3981_, v___x_3980_);
return v___x_3983_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v___x_3984_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__5, &l_Lake_Package_initFacetConfigs___closed__5_once, _init_l_Lake_Package_initFacetConfigs___closed__5);
v___x_3985_ = l_Lake_Package_optBarrelFacetConfig;
v___x_3986_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_3987_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3986_, v___x_3985_, v___x_3984_);
return v___x_3987_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__7(void){
_start:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3988_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__6, &l_Lake_Package_initFacetConfigs___closed__6_once, _init_l_Lake_Package_initFacetConfigs___closed__6);
v___x_3989_ = l_Lake_Package_barrelFacetConfig;
v___x_3990_ = l_Lake_Package_reservoirBarrelFacet;
v___x_3991_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3990_, v___x_3989_, v___x_3988_);
return v___x_3991_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__8(void){
_start:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3992_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__7, &l_Lake_Package_initFacetConfigs___closed__7_once, _init_l_Lake_Package_initFacetConfigs___closed__7);
v___x_3993_ = l_Lake_Package_optGitHubReleaseFacetConfig;
v___x_3994_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_3995_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3994_, v___x_3993_, v___x_3992_);
return v___x_3995_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__9(void){
_start:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
v___x_3996_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__8, &l_Lake_Package_initFacetConfigs___closed__8_once, _init_l_Lake_Package_initFacetConfigs___closed__8);
v___x_3997_ = l_Lake_Package_gitHubReleaseFacetConfig;
v___x_3998_ = l_Lake_Package_gitHubReleaseFacet;
v___x_3999_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3998_, v___x_3997_, v___x_3996_);
return v___x_3999_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs(void){
_start:
{
lean_object* v___x_4000_; 
v___x_4000_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__9, &l_Lake_Package_initFacetConfigs___closed__9_once, _init_l_Lake_Package_initFacetConfigs___closed__9);
return v___x_4000_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0(lean_object* v_00_u03b2_4001_, lean_object* v_k_4002_, lean_object* v_v_4003_, lean_object* v_t_4004_, lean_object* v_hl_4005_){
_start:
{
lean_object* v___x_4006_; 
v___x_4006_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_4002_, v_v_4003_, v_t_4004_);
return v___x_4006_;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs(void){
_start:
{
lean_object* v___x_4007_; 
v___x_4007_ = l_Lake_Package_initFacetConfigs;
return v___x_4007_;
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
