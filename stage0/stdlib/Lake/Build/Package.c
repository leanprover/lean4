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
lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg(lean_object* v_self_13_, lean_object* v_a_14_){
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
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_13_ = stack[0].m_obj;
lean_object* v_a_14_ = stack[1].m_obj;
lean_object* v_res_25_;
v_res_25_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg(v_self_13_, v_a_14_);
stack->m_obj
 = v_res_25_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___boxed(lean_object* v_self_26_, lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg(v_self_26_, v_a_27_);
lean_dec_ref(v_self_26_);
return v_res_29_;
}
}
lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps(lean_object* v_self_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg(v_self_30_, v_a_36_);
return v___x_38_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_30_ = stack[0].m_obj;
lean_object* v_a_31_ = stack[1].m_obj;
lean_object* v_a_32_ = stack[2].m_obj;
lean_object* v_a_33_ = stack[3].m_obj;
lean_object* v_a_34_ = stack[4].m_obj;
lean_object* v_a_35_ = stack[5].m_obj;
lean_object* v_a_36_ = stack[6].m_obj;
lean_object* v_res_39_;
v_res_39_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps(v_self_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_);
stack->m_obj
 = v_res_39_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___boxed(lean_object* v_self_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps(v_self_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_);
lean_dec_ref(v_a_45_);
lean_dec(v_a_44_);
lean_dec(v_a_43_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
lean_dec_ref(v_self_40_);
return v_res_48_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__1(size_t v_sz_49_, size_t v_i_50_, lean_object* v_bs_51_){
_start:
{
uint8_t v___x_52_; 
v___x_52_ = lean_usize_dec_lt(v_i_50_, v_sz_49_);
if (v___x_52_ == 0)
{
return v_bs_51_;
}
else
{
lean_object* v_v_53_; lean_object* v_keyName_54_; lean_object* v___x_55_; lean_object* v_bs_x27_56_; lean_object* v___x_57_; lean_object* v___x_58_; size_t v___x_59_; size_t v___x_60_; lean_object* v___x_61_; 
v_v_53_ = lean_array_uget_borrowed(v_bs_51_, v_i_50_);
v_keyName_54_ = lean_ctor_get(v_v_53_, 2);
lean_inc(v_keyName_54_);
v___x_55_ = lean_unsigned_to_nat(0u);
v_bs_x27_56_ = lean_array_uset(v_bs_51_, v_i_50_, v___x_55_);
v___x_57_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_keyName_54_, v___x_52_);
v___x_58_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
v___x_59_ = ((size_t)1ULL);
v___x_60_ = lean_usize_add(v_i_50_, v___x_59_);
v___x_61_ = lean_array_uset(v_bs_x27_56_, v_i_50_, v___x_58_);
v_i_50_ = v___x_60_;
v_bs_51_ = v___x_61_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_49_ = stack[0].m_num;
size_t v_i_50_ = stack[1].m_num;
lean_object* v_bs_51_ = stack[2].m_obj;
lean_object* v_res_63_;
v_res_63_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__1(v_sz_49_, v_i_50_, v_bs_51_);
stack->m_obj
 = v_res_63_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__1___boxed(lean_object* v_sz_64_, lean_object* v_i_65_, lean_object* v_bs_66_){
_start:
{
size_t v_sz_boxed_67_; size_t v_i_boxed_68_; lean_object* v_res_69_; 
v_sz_boxed_67_ = lean_unbox_usize(v_sz_64_);
lean_dec(v_sz_64_);
v_i_boxed_68_ = lean_unbox_usize(v_i_65_);
lean_dec(v_i_65_);
v_res_69_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__1(v_sz_boxed_67_, v_i_boxed_68_, v_bs_66_);
return v_res_69_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0(lean_object* v_as_71_, size_t v_i_72_, size_t v_stop_73_, lean_object* v_b_74_){
_start:
{
uint8_t v___x_75_; 
v___x_75_ = lean_usize_dec_eq(v_i_72_, v_stop_73_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v_baseName_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; size_t v___x_82_; size_t v___x_83_; 
v___x_76_ = lean_array_uget_borrowed(v_as_71_, v_i_72_);
v_baseName_77_ = lean_ctor_get(v___x_76_, 1);
lean_inc(v_baseName_77_);
v___x_78_ = l_Lean_Name_toString(v_baseName_77_, v___x_75_);
v___x_79_ = lean_string_append(v_b_74_, v___x_78_);
lean_dec_ref(v___x_78_);
v___x_80_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0));
v___x_81_ = lean_string_append(v___x_79_, v___x_80_);
v___x_82_ = ((size_t)1ULL);
v___x_83_ = lean_usize_add(v_i_72_, v___x_82_);
v_i_72_ = v___x_83_;
v_b_74_ = v___x_81_;
goto _start;
}
else
{
return v_b_74_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_71_ = stack[0].m_obj;
size_t v_i_72_ = stack[1].m_num;
size_t v_stop_73_ = stack[2].m_num;
lean_object* v_b_74_ = stack[3].m_obj;
lean_object* v_res_85_;
v_res_85_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0(v_as_71_, v_i_72_, v_stop_73_, v_b_74_);
stack->m_obj
 = v_res_85_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0___boxed(lean_object* v_as_86_, lean_object* v_i_87_, lean_object* v_stop_88_, lean_object* v_b_89_){
_start:
{
size_t v_i_boxed_90_; size_t v_stop_boxed_91_; lean_object* v_res_92_; 
v_i_boxed_90_ = lean_unbox_usize(v_i_87_);
lean_dec(v_i_87_);
v_stop_boxed_91_ = lean_unbox_usize(v_stop_88_);
lean_dec(v_stop_88_);
v_res_92_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0(v_as_86_, v_i_boxed_90_, v_stop_boxed_91_, v_b_89_);
lean_dec_ref(v_as_86_);
return v_res_92_;
}
}
lean_object* l_Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0(uint8_t v_fmt_93_, lean_object* v_a_94_){
_start:
{
lean_object* v___y_96_; 
if (v_fmt_93_ == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_103_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = lean_array_get_size(v_a_94_);
v___x_106_ = lean_nat_dec_lt(v___x_104_, v___x_105_);
if (v___x_106_ == 0)
{
lean_dec_ref(v_a_94_);
v___y_96_ = v___x_103_;
goto v___jp_95_;
}
else
{
size_t v___x_107_; size_t v___x_108_; lean_object* v___x_109_; 
v___x_107_ = ((size_t)0ULL);
v___x_108_ = lean_usize_of_nat(v___x_105_);
v___x_109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0(v_a_94_, v___x_107_, v___x_108_, v___x_103_);
lean_dec_ref(v_a_94_);
v___y_96_ = v___x_109_;
goto v___jp_95_;
}
}
else
{
size_t v_sz_110_; size_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_sz_110_ = lean_array_size(v_a_94_);
v___x_111_ = ((size_t)0ULL);
v___x_112_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__1(v_sz_110_, v___x_111_, v_a_94_);
v___x_113_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
v___x_114_ = l_Lean_Json_compress(v___x_113_);
return v___x_114_;
}
v___jp_95_:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_97_ = lean_unsigned_to_nat(1u);
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_string_utf8_byte_size(v___y_96_);
lean_inc_ref(v___y_96_);
v___x_100_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_100_, 0, v___y_96_);
lean_ctor_set(v___x_100_, 1, v___x_98_);
lean_ctor_set(v___x_100_, 2, v___x_99_);
v___x_101_ = l_String_Slice_Pos_prevn(v___x_100_, v___x_99_, v___x_97_);
lean_dec_ref_known(v___x_100_, 3);
v___x_102_ = lean_string_utf8_extract_fast(v___y_96_, v___x_98_, v___x_101_);
lean_dec(v___x_101_);
lean_dec_ref(v___y_96_);
return v___x_102_;
}
}
}
LEAN_EXPORT void l_Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_fmt_93_ = stack[0].m_num;
lean_object* v_a_94_ = stack[1].m_obj;
lean_object* v_res_115_;
v_res_115_ = l_Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0(v_fmt_93_, v_a_94_);
stack->m_obj
 = v_res_115_;
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0___boxed(lean_object* v_fmt_116_, lean_object* v_a_117_){
_start:
{
uint8_t v_fmt_boxed_118_; lean_object* v_res_119_; 
v_fmt_boxed_118_ = lean_unbox(v_fmt_116_);
v_res_119_ = l_Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0(v_fmt_boxed_118_, v_a_117_);
return v_res_119_;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig___closed__2(void){
_start:
{
uint8_t v___x_122_; lean_object* v___f_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_122_ = 1;
v___f_123_ = ((lean_object*)(l_Lake_Package_depsFacetConfig___closed__0));
v___x_124_ = 0;
v___x_125_ = lean_box(0);
v___x_126_ = ((lean_object*)(l_Lake_Package_depsFacetConfig___closed__1));
v___x_127_ = l_Lake_Package_keyword;
v___x_128_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_126_);
lean_ctor_set(v___x_128_, 2, v___x_125_);
lean_ctor_set(v___x_128_, 3, v___f_123_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*4, v___x_124_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*4 + 1, v___x_122_);
return v___x_128_;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig(void){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_Lake_Package_depsFacetConfig___closed__2, &l_Lake_Package_depsFacetConfig___closed__2_once, _init_l_Lake_Package_depsFacetConfig___closed__2);
return v___x_129_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_130_ = lean_box(0);
v___x_131_ = lean_unsigned_to_nat(16u);
v___x_132_ = lean_mk_array(v___x_131_, v___x_130_);
return v___x_132_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0);
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v___x_133_);
return v___x_135_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_138_ = ((lean_object*)(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__2));
v___x_139_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1);
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v___x_138_);
return v___x_140_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2(void){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3);
return v___x_141_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(lean_object* v_a_142_, lean_object* v_x_143_){
_start:
{
if (lean_obj_tag(v_x_143_) == 0)
{
uint8_t v___x_144_; 
v___x_144_ = 0;
return v___x_144_;
}
else
{
lean_object* v_key_145_; lean_object* v_tail_146_; lean_object* v_wsIdx_147_; lean_object* v_wsIdx_148_; uint8_t v___x_149_; 
v_key_145_ = lean_ctor_get(v_x_143_, 0);
v_tail_146_ = lean_ctor_get(v_x_143_, 2);
v_wsIdx_147_ = lean_ctor_get(v_key_145_, 0);
v_wsIdx_148_ = lean_ctor_get(v_a_142_, 0);
v___x_149_ = lean_nat_dec_eq(v_wsIdx_147_, v_wsIdx_148_);
if (v___x_149_ == 0)
{
v_x_143_ = v_tail_146_;
goto _start;
}
else
{
return v___x_149_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_142_ = stack[0].m_obj;
lean_object* v_x_143_ = stack[1].m_obj;
uint8_t v_res_151_;
v_res_151_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_142_, v_x_143_);
stack->m_num = v_res_151_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_a_152_, lean_object* v_x_153_){
_start:
{
uint8_t v_res_154_; lean_object* v_r_155_; 
v_res_154_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_152_, v_x_153_);
lean_dec(v_x_153_);
lean_dec_ref(v_a_152_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(lean_object* v_m_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_buckets_158_; lean_object* v_keyName_159_; lean_object* v___x_160_; uint64_t v___y_162_; 
v_buckets_158_ = lean_ctor_get(v_m_156_, 1);
v_keyName_159_ = lean_ctor_get(v_a_157_, 2);
v___x_160_ = lean_array_get_size(v_buckets_158_);
if (lean_obj_tag(v_keyName_159_) == 0)
{
uint64_t v___x_176_; 
v___x_176_ = 1723ULL;
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
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_156_ = stack[0].m_obj;
lean_object* v_a_157_ = stack[1].m_obj;
uint8_t v_res_178_;
v_res_178_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_m_156_, v_a_157_);
stack->m_num = v_res_178_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___boxed(lean_object* v_m_179_, lean_object* v_a_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_m_179_, v_a_180_);
lean_dec_ref(v_a_180_);
lean_dec_ref(v_m_179_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8___redArg(lean_object* v_x_183_, lean_object* v_x_184_){
_start:
{
if (lean_obj_tag(v_x_184_) == 0)
{
return v_x_183_;
}
else
{
lean_object* v_key_185_; lean_object* v_value_186_; lean_object* v_tail_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_214_; 
v_key_185_ = lean_ctor_get(v_x_184_, 0);
v_value_186_ = lean_ctor_get(v_x_184_, 1);
v_tail_187_ = lean_ctor_get(v_x_184_, 2);
v_isSharedCheck_214_ = !lean_is_exclusive(v_x_184_);
if (v_isSharedCheck_214_ == 0)
{
v___x_189_ = v_x_184_;
v_isShared_190_ = v_isSharedCheck_214_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_tail_187_);
lean_inc(v_value_186_);
lean_inc(v_key_185_);
lean_dec(v_x_184_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_214_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v_keyName_191_; lean_object* v___x_192_; uint64_t v___y_194_; 
v_keyName_191_ = lean_ctor_get(v_key_185_, 2);
v___x_192_ = lean_array_get_size(v_x_183_);
if (lean_obj_tag(v_keyName_191_) == 0)
{
uint64_t v___x_212_; 
v___x_212_ = 1723ULL;
v___y_194_ = v___x_212_;
goto v___jp_193_;
}
else
{
uint64_t v_hash_213_; 
v_hash_213_ = lean_ctor_get_uint64(v_keyName_191_, sizeof(void*)*2);
v___y_194_ = v_hash_213_;
goto v___jp_193_;
}
v___jp_193_:
{
uint64_t v___x_195_; uint64_t v___x_196_; uint64_t v_fold_197_; uint64_t v___x_198_; uint64_t v___x_199_; uint64_t v___x_200_; size_t v___x_201_; size_t v___x_202_; size_t v___x_203_; size_t v___x_204_; size_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_208_; 
v___x_195_ = 32ULL;
v___x_196_ = lean_uint64_shift_right(v___y_194_, v___x_195_);
v_fold_197_ = lean_uint64_xor(v___y_194_, v___x_196_);
v___x_198_ = 16ULL;
v___x_199_ = lean_uint64_shift_right(v_fold_197_, v___x_198_);
v___x_200_ = lean_uint64_xor(v_fold_197_, v___x_199_);
v___x_201_ = lean_uint64_to_usize(v___x_200_);
v___x_202_ = lean_usize_of_nat(v___x_192_);
v___x_203_ = ((size_t)1ULL);
v___x_204_ = lean_usize_sub(v___x_202_, v___x_203_);
v___x_205_ = lean_usize_land(v___x_201_, v___x_204_);
v___x_206_ = lean_array_uget_borrowed(v_x_183_, v___x_205_);
lean_inc(v___x_206_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 2, v___x_206_);
v___x_208_ = v___x_189_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_key_185_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_value_186_);
lean_ctor_set(v_reuseFailAlloc_211_, 2, v___x_206_);
v___x_208_ = v_reuseFailAlloc_211_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_209_; 
v___x_209_ = lean_array_uset(v_x_183_, v___x_205_, v___x_208_);
v_x_183_ = v___x_209_;
v_x_184_ = v_tail_187_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_i_215_, lean_object* v_source_216_, lean_object* v_target_217_){
_start:
{
lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_218_ = lean_array_get_size(v_source_216_);
v___x_219_ = lean_nat_dec_lt(v_i_215_, v___x_218_);
if (v___x_219_ == 0)
{
lean_dec_ref(v_source_216_);
lean_dec(v_i_215_);
return v_target_217_;
}
else
{
lean_object* v_es_220_; lean_object* v___x_221_; lean_object* v_source_222_; lean_object* v_target_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v_es_220_ = lean_array_fget(v_source_216_, v_i_215_);
v___x_221_ = lean_box(0);
v_source_222_ = lean_array_fset(v_source_216_, v_i_215_, v___x_221_);
v_target_223_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8___redArg(v_target_217_, v_es_220_);
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = lean_nat_add(v_i_215_, v___x_224_);
lean_dec(v_i_215_);
v_i_215_ = v___x_225_;
v_source_216_ = v_source_222_;
v_target_217_ = v_target_223_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(lean_object* v_data_227_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v_nbuckets_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_228_ = lean_array_get_size(v_data_227_);
v___x_229_ = lean_unsigned_to_nat(2u);
v_nbuckets_230_ = lean_nat_mul(v___x_228_, v___x_229_);
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_box(0);
v___x_233_ = lean_mk_array(v_nbuckets_230_, v___x_232_);
v___x_234_ = lean_array_propagate_mark(v_data_227_, v___x_233_);
v___x_235_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7___redArg(v___x_231_, v_data_227_, v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(lean_object* v_m_236_, lean_object* v_a_237_, lean_object* v_b_238_){
_start:
{
lean_object* v_size_239_; lean_object* v_buckets_240_; lean_object* v_keyName_241_; lean_object* v___x_242_; uint64_t v___y_244_; 
v_size_239_ = lean_ctor_get(v_m_236_, 0);
v_buckets_240_ = lean_ctor_get(v_m_236_, 1);
v_keyName_241_ = lean_ctor_get(v_a_237_, 2);
v___x_242_ = lean_array_get_size(v_buckets_240_);
if (lean_obj_tag(v_keyName_241_) == 0)
{
uint64_t v___x_281_; 
v___x_281_ = 1723ULL;
v___y_244_ = v___x_281_;
goto v___jp_243_;
}
else
{
uint64_t v_hash_282_; 
v_hash_282_ = lean_ctor_get_uint64(v_keyName_241_, sizeof(void*)*2);
v___y_244_ = v_hash_282_;
goto v___jp_243_;
}
v___jp_243_:
{
uint64_t v___x_245_; uint64_t v___x_246_; uint64_t v_fold_247_; uint64_t v___x_248_; uint64_t v___x_249_; uint64_t v___x_250_; size_t v___x_251_; size_t v___x_252_; size_t v___x_253_; size_t v___x_254_; size_t v___x_255_; lean_object* v_bkt_256_; uint8_t v___x_257_; 
v___x_245_ = 32ULL;
v___x_246_ = lean_uint64_shift_right(v___y_244_, v___x_245_);
v_fold_247_ = lean_uint64_xor(v___y_244_, v___x_246_);
v___x_248_ = 16ULL;
v___x_249_ = lean_uint64_shift_right(v_fold_247_, v___x_248_);
v___x_250_ = lean_uint64_xor(v_fold_247_, v___x_249_);
v___x_251_ = lean_uint64_to_usize(v___x_250_);
v___x_252_ = lean_usize_of_nat(v___x_242_);
v___x_253_ = ((size_t)1ULL);
v___x_254_ = lean_usize_sub(v___x_252_, v___x_253_);
v___x_255_ = lean_usize_land(v___x_251_, v___x_254_);
v_bkt_256_ = lean_array_uget_borrowed(v_buckets_240_, v___x_255_);
v___x_257_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_237_, v_bkt_256_);
if (v___x_257_ == 0)
{
lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_278_; 
lean_inc_ref(v_buckets_240_);
lean_inc(v_size_239_);
v_isSharedCheck_278_ = !lean_is_exclusive(v_m_236_);
if (v_isSharedCheck_278_ == 0)
{
lean_object* v_unused_279_; lean_object* v_unused_280_; 
v_unused_279_ = lean_ctor_get(v_m_236_, 1);
lean_dec(v_unused_279_);
v_unused_280_ = lean_ctor_get(v_m_236_, 0);
lean_dec(v_unused_280_);
v___x_259_ = v_m_236_;
v_isShared_260_ = v_isSharedCheck_278_;
goto v_resetjp_258_;
}
else
{
lean_dec(v_m_236_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_278_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v_size_x27_262_; lean_object* v___x_263_; lean_object* v_buckets_x27_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_261_ = lean_unsigned_to_nat(1u);
v_size_x27_262_ = lean_nat_add(v_size_239_, v___x_261_);
lean_dec(v_size_239_);
lean_inc(v_bkt_256_);
v___x_263_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_263_, 0, v_a_237_);
lean_ctor_set(v___x_263_, 1, v_b_238_);
lean_ctor_set(v___x_263_, 2, v_bkt_256_);
v_buckets_x27_264_ = lean_array_uset(v_buckets_240_, v___x_255_, v___x_263_);
v___x_265_ = lean_unsigned_to_nat(4u);
v___x_266_ = lean_nat_mul(v_size_x27_262_, v___x_265_);
v___x_267_ = lean_unsigned_to_nat(3u);
v___x_268_ = lean_nat_div(v___x_266_, v___x_267_);
lean_dec(v___x_266_);
v___x_269_ = lean_array_get_size(v_buckets_x27_264_);
v___x_270_ = lean_nat_dec_le(v___x_268_, v___x_269_);
lean_dec(v___x_268_);
if (v___x_270_ == 0)
{
lean_object* v_val_271_; lean_object* v___x_273_; 
v_val_271_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(v_buckets_x27_264_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 1, v_val_271_);
lean_ctor_set(v___x_259_, 0, v_size_x27_262_);
v___x_273_ = v___x_259_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_size_x27_262_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_val_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
else
{
lean_object* v___x_276_; 
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 1, v_buckets_x27_264_);
lean_ctor_set(v___x_259_, 0, v_size_x27_262_);
v___x_276_ = v___x_259_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_size_x27_262_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_buckets_x27_264_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
else
{
lean_dec(v_b_238_);
lean_dec_ref(v_a_237_);
return v_m_236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(lean_object* v_self_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_toHashSet_285_; lean_object* v_toArray_286_; uint8_t v___x_287_; 
v_toHashSet_285_ = lean_ctor_get(v_self_283_, 0);
v_toArray_286_ = lean_ctor_get(v_self_283_, 1);
v___x_287_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_toHashSet_285_, v_a_284_);
if (v___x_287_ == 0)
{
lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_297_; 
lean_inc_ref(v_toArray_286_);
lean_inc_ref(v_toHashSet_285_);
v_isSharedCheck_297_ = !lean_is_exclusive(v_self_283_);
if (v_isSharedCheck_297_ == 0)
{
lean_object* v_unused_298_; lean_object* v_unused_299_; 
v_unused_298_ = lean_ctor_get(v_self_283_, 1);
lean_dec(v_unused_298_);
v_unused_299_ = lean_ctor_get(v_self_283_, 0);
lean_dec(v_unused_299_);
v___x_289_ = v_self_283_;
v_isShared_290_ = v_isSharedCheck_297_;
goto v_resetjp_288_;
}
else
{
lean_dec(v_self_283_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_297_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_291_ = lean_box(0);
lean_inc_ref(v_a_284_);
v___x_292_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(v_toHashSet_285_, v_a_284_, v___x_291_);
v___x_293_ = lean_array_push(v_toArray_286_, v_a_284_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 1, v___x_293_);
lean_ctor_set(v___x_289_, 0, v___x_292_);
v___x_295_ = v___x_289_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
else
{
lean_dec_ref(v_a_284_);
return v_self_283_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(lean_object* v_as_300_, size_t v_i_301_, size_t v_stop_302_, lean_object* v_b_303_){
_start:
{
uint8_t v___x_304_; 
v___x_304_ = lean_usize_dec_eq(v_i_301_, v_stop_302_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; lean_object* v___x_306_; size_t v___x_307_; size_t v___x_308_; 
v___x_305_ = lean_array_uget_borrowed(v_as_300_, v_i_301_);
lean_inc(v___x_305_);
v___x_306_ = l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(v_b_303_, v___x_305_);
v___x_307_ = ((size_t)1ULL);
v___x_308_ = lean_usize_add(v_i_301_, v___x_307_);
v_i_301_ = v___x_308_;
v_b_303_ = v___x_306_;
goto _start;
}
else
{
return v_b_303_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_300_ = stack[0].m_obj;
size_t v_i_301_ = stack[1].m_num;
size_t v_stop_302_ = stack[2].m_num;
lean_object* v_b_303_ = stack[3].m_obj;
lean_object* v_res_310_;
v_res_310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_as_300_, v_i_301_, v_stop_302_, v_b_303_);
stack->m_obj
 = v_res_310_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1___boxed(lean_object* v_as_311_, lean_object* v_i_312_, lean_object* v_stop_313_, lean_object* v_b_314_){
_start:
{
size_t v_i_boxed_315_; size_t v_stop_boxed_316_; lean_object* v_res_317_; 
v_i_boxed_315_ = lean_unbox_usize(v_i_312_);
lean_dec(v_i_312_);
v_stop_boxed_316_ = lean_unbox_usize(v_stop_313_);
lean_dec(v_stop_313_);
v_res_317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_as_311_, v_i_boxed_315_, v_stop_boxed_316_, v_b_314_);
lean_dec_ref(v_as_311_);
return v_res_317_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(lean_object* v_as_318_, size_t v_i_319_, size_t v_stop_320_, lean_object* v_b_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = lean_usize_dec_eq(v_i_319_, v_stop_320_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v_keyName_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_330_ = lean_array_uget_borrowed(v_as_318_, v_i_319_);
v_keyName_331_ = lean_ctor_get(v___x_330_, 2);
v___x_332_ = l_Lake_Package_transDepsFacet;
lean_inc(v_keyName_331_);
v___x_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_333_, 0, v_keyName_331_);
v___x_334_ = l_Lake_Package_keyword;
lean_inc(v___x_330_);
v___x_335_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_335_, 0, v___x_333_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
lean_ctor_set(v___x_335_, 2, v___x_330_);
lean_ctor_set(v___x_335_, 3, v___x_332_);
lean_inc_ref(v___y_322_);
lean_inc_ref(v___y_326_);
lean_inc(v___y_325_);
lean_inc(v___y_324_);
lean_inc(v___y_323_);
v___x_336_ = lean_apply_7(v___y_322_, v___x_335_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, lean_box(0));
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v_a_338_; lean_object* v___x_339_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_337_);
v_a_338_ = lean_ctor_get(v___x_336_, 1);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_336_, 2);
v___x_339_ = l_Lake_Job_await___redArg(v_a_337_, v_a_338_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v_a_341_; lean_object* v___y_343_; lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
v_a_341_ = lean_ctor_get(v___x_339_, 1);
lean_inc(v_a_341_);
lean_dec_ref_known(v___x_339_, 2);
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_array_get_size(v_a_340_);
v___x_350_ = lean_nat_dec_lt(v___x_348_, v___x_349_);
if (v___x_350_ == 0)
{
lean_dec(v_a_340_);
v___y_343_ = v_b_321_;
goto v___jp_342_;
}
else
{
uint8_t v___x_351_; 
v___x_351_ = lean_nat_dec_le(v___x_349_, v___x_349_);
if (v___x_351_ == 0)
{
if (v___x_350_ == 0)
{
lean_dec(v_a_340_);
v___y_343_ = v_b_321_;
goto v___jp_342_;
}
else
{
size_t v___x_352_; size_t v___x_353_; lean_object* v___x_354_; 
v___x_352_ = ((size_t)0ULL);
v___x_353_ = lean_usize_of_nat(v___x_349_);
v___x_354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_a_340_, v___x_352_, v___x_353_, v_b_321_);
lean_dec(v_a_340_);
v___y_343_ = v___x_354_;
goto v___jp_342_;
}
}
else
{
size_t v___x_355_; size_t v___x_356_; lean_object* v___x_357_; 
v___x_355_ = ((size_t)0ULL);
v___x_356_ = lean_usize_of_nat(v___x_349_);
v___x_357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_a_340_, v___x_355_, v___x_356_, v_b_321_);
lean_dec(v_a_340_);
v___y_343_ = v___x_357_;
goto v___jp_342_;
}
}
v___jp_342_:
{
lean_object* v___x_344_; size_t v___x_345_; size_t v___x_346_; 
lean_inc(v___x_330_);
v___x_344_ = l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(v___y_343_, v___x_330_);
v___x_345_ = ((size_t)1ULL);
v___x_346_ = lean_usize_add(v_i_319_, v___x_345_);
v_i_319_ = v___x_346_;
v_b_321_ = v___x_344_;
v___y_327_ = v_a_341_;
goto _start;
}
}
else
{
lean_object* v_a_358_; lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec_ref(v___y_322_);
lean_dec_ref(v_b_321_);
v_a_358_ = lean_ctor_get(v___x_339_, 0);
v_a_359_ = lean_ctor_get(v___x_339_, 1);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_339_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_inc(v_a_358_);
lean_dec(v___x_339_);
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
lean_object* v_a_367_; lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec_ref(v___y_322_);
lean_dec_ref(v_b_321_);
v_a_367_ = lean_ctor_get(v___x_336_, 0);
v_a_368_ = lean_ctor_get(v___x_336_, 1);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_336_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_inc(v_a_367_);
lean_dec(v___x_336_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_367_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
else
{
lean_object* v___x_376_; 
lean_dec_ref(v___y_322_);
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v_b_321_);
lean_ctor_set(v___x_376_, 1, v___y_327_);
return v___x_376_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_318_ = stack[0].m_obj;
size_t v_i_319_ = stack[1].m_num;
size_t v_stop_320_ = stack[2].m_num;
lean_object* v_b_321_ = stack[3].m_obj;
lean_object* v___y_322_ = stack[4].m_obj;
lean_object* v___y_323_ = stack[5].m_obj;
lean_object* v___y_324_ = stack[6].m_obj;
lean_object* v___y_325_ = stack[7].m_obj;
lean_object* v___y_326_ = stack[8].m_obj;
lean_object* v___y_327_ = stack[9].m_obj;
lean_object* v_res_377_;
v_res_377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_as_318_, v_i_319_, v_stop_320_, v_b_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
stack->m_obj
 = v_res_377_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3___boxed(lean_object* v_as_378_, lean_object* v_i_379_, lean_object* v_stop_380_, lean_object* v_b_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
size_t v_i_boxed_389_; size_t v_stop_boxed_390_; lean_object* v_res_391_; 
v_i_boxed_389_ = lean_unbox_usize(v_i_379_);
lean_dec(v_i_379_);
v_stop_boxed_390_ = lean_unbox_usize(v_stop_380_);
lean_dec(v_stop_380_);
v_res_391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_as_378_, v_i_boxed_389_, v_stop_boxed_390_, v_b_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v_as_378_);
return v_res_391_;
}
}
lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0(lean_object* v___x_392_, lean_object* v___x_393_, lean_object* v___x_394_, lean_object* v___x_395_, lean_object* v_depPkgs_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_a_405_; lean_object* v_a_406_; lean_object* v___y_426_; uint8_t v___x_438_; 
v___x_438_ = lean_nat_dec_lt(v___x_392_, v___x_394_);
if (v___x_438_ == 0)
{
lean_dec_ref(v___y_397_);
v_a_405_ = v___x_395_;
v_a_406_ = v___y_402_;
goto v___jp_404_;
}
else
{
uint8_t v___x_439_; 
v___x_439_ = lean_nat_dec_le(v___x_394_, v___x_394_);
if (v___x_439_ == 0)
{
if (v___x_438_ == 0)
{
lean_dec_ref(v___y_397_);
v_a_405_ = v___x_395_;
v_a_406_ = v___y_402_;
goto v___jp_404_;
}
else
{
size_t v___x_440_; size_t v___x_441_; lean_object* v___x_442_; 
v___x_440_ = ((size_t)0ULL);
v___x_441_ = lean_usize_of_nat(v___x_394_);
v___x_442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_depPkgs_396_, v___x_440_, v___x_441_, v___x_395_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
v___y_426_ = v___x_442_;
goto v___jp_425_;
}
}
else
{
size_t v___x_443_; size_t v___x_444_; lean_object* v___x_445_; 
v___x_443_ = ((size_t)0ULL);
v___x_444_ = lean_usize_of_nat(v___x_394_);
v___x_445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_depPkgs_396_, v___x_443_, v___x_444_, v___x_395_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
v___y_426_ = v___x_445_;
goto v___jp_425_;
}
}
v___jp_404_:
{
lean_object* v_toArray_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_423_; 
v_toArray_407_ = lean_ctor_get(v_a_405_, 1);
v_isSharedCheck_423_ = !lean_is_exclusive(v_a_405_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; 
v_unused_424_ = lean_ctor_get(v_a_405_, 0);
lean_dec(v_unused_424_);
v___x_409_ = v_a_405_;
v_isShared_410_ = v_isSharedCheck_423_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_toArray_407_);
lean_dec(v_a_405_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_423_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; uint8_t v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_411_ = lean_mk_empty_array_with_capacity(v___x_392_);
v___x_412_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_413_ = 0;
v___x_414_ = 0;
v___x_415_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_416_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_416_, 0, v___x_411_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
lean_ctor_set(v___x_416_, 2, v___x_392_);
lean_ctor_set_uint8(v___x_416_, sizeof(void*)*3, v___x_413_);
lean_ctor_set_uint8(v___x_416_, sizeof(void*)*3 + 1, v___x_414_);
lean_ctor_set_uint8(v___x_416_, sizeof(void*)*3 + 2, v___x_414_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 1, v___x_416_);
lean_ctor_set(v___x_409_, 0, v_toArray_407_);
v___x_418_ = v___x_409_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_toArray_407_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v___x_416_);
v___x_418_ = v_reuseFailAlloc_422_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = lean_task_pure(v___x_418_);
v___x_420_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v___x_393_);
lean_ctor_set(v___x_420_, 2, v___x_412_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*3, v___x_414_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v_a_406_);
return v___x_421_;
}
}
}
v___jp_425_:
{
if (lean_obj_tag(v___y_426_) == 0)
{
lean_object* v_a_427_; lean_object* v_a_428_; 
v_a_427_ = lean_ctor_get(v___y_426_, 0);
lean_inc(v_a_427_);
v_a_428_ = lean_ctor_get(v___y_426_, 1);
lean_inc(v_a_428_);
lean_dec_ref_known(v___y_426_, 2);
v_a_405_ = v_a_427_;
v_a_406_ = v_a_428_;
goto v___jp_404_;
}
else
{
lean_object* v_a_429_; lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec(v___x_393_);
lean_dec(v___x_392_);
v_a_429_ = lean_ctor_get(v___y_426_, 0);
v_a_430_ = lean_ctor_get(v___y_426_, 1);
v_isSharedCheck_437_ = !lean_is_exclusive(v___y_426_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___y_426_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_inc(v_a_429_);
lean_dec(v___y_426_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_429_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_392_ = stack[0].m_obj;
lean_object* v___x_393_ = stack[1].m_obj;
lean_object* v___x_394_ = stack[2].m_obj;
lean_object* v___x_395_ = stack[3].m_obj;
lean_object* v_depPkgs_396_ = stack[4].m_obj;
lean_object* v___y_397_ = stack[5].m_obj;
lean_object* v___y_398_ = stack[6].m_obj;
lean_object* v___y_399_ = stack[7].m_obj;
lean_object* v___y_400_ = stack[8].m_obj;
lean_object* v___y_401_ = stack[9].m_obj;
lean_object* v___y_402_ = stack[10].m_obj;
lean_object* v_res_446_;
v_res_446_ = l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0(v___x_392_, v___x_393_, v___x_394_, v___x_395_, v_depPkgs_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
stack->m_obj
 = v_res_446_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0___boxed(lean_object* v___x_447_, lean_object* v___x_448_, lean_object* v___x_449_, lean_object* v___x_450_, lean_object* v_depPkgs_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0(v___x_447_, v___x_448_, v___x_449_, v___x_450_, v_depPkgs_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v_depPkgs_451_);
lean_dec(v___x_449_);
return v_res_459_;
}
}
lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps(lean_object* v_self_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_depPkgs_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___f_473_; lean_object* v___x_474_; 
v_depPkgs_468_ = lean_ctor_get(v_self_460_, 14);
lean_inc_ref(v_depPkgs_468_);
lean_dec_ref(v_self_460_);
v___x_469_ = lean_box(0);
v___x_470_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2;
v___x_471_ = lean_unsigned_to_nat(0u);
v___x_472_ = lean_array_get_size(v_depPkgs_468_);
v___f_473_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0___boxed), 12, 5);
lean_closure_set(v___f_473_, 0, v___x_471_);
lean_closure_set(v___f_473_, 1, v___x_469_);
lean_closure_set(v___f_473_, 2, v___x_472_);
lean_closure_set(v___f_473_, 3, v___x_470_);
lean_closure_set(v___f_473_, 4, v_depPkgs_468_);
v___x_474_ = l_Lake_ensureJob___redArg(v___x_469_, v___f_473_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
return v___x_474_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_460_ = stack[0].m_obj;
lean_object* v_a_461_ = stack[1].m_obj;
lean_object* v_a_462_ = stack[2].m_obj;
lean_object* v_a_463_ = stack[3].m_obj;
lean_object* v_a_464_ = stack[4].m_obj;
lean_object* v_a_465_ = stack[5].m_obj;
lean_object* v_a_466_ = stack[6].m_obj;
lean_object* v_res_475_;
v_res_475_ = l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps(v_self_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
stack->m_obj
 = v_res_475_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___boxed(lean_object* v_self_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps(v_self_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec(v_a_479_);
lean_dec(v_a_478_);
return v_res_484_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0(lean_object* v_00_u03b2_485_, lean_object* v_m_486_, lean_object* v_a_487_){
_start:
{
uint8_t v___x_488_; 
v___x_488_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_m_486_, v_a_487_);
return v___x_488_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_486_ = stack[1].m_obj;
lean_object* v_a_487_ = stack[2].m_obj;
uint8_t v_res_489_;
v_res_489_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0(lean_box(0), v_m_486_, v_a_487_);
stack->m_num = v_res_489_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_490_, lean_object* v_m_491_, lean_object* v_a_492_){
_start:
{
uint8_t v_res_493_; lean_object* v_r_494_; 
v_res_493_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0(v_00_u03b2_490_, v_m_491_, v_a_492_);
lean_dec_ref(v_a_492_);
lean_dec_ref(v_m_491_);
v_r_494_ = lean_box(v_res_493_);
return v_r_494_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1(lean_object* v_00_u03b2_495_, lean_object* v_m_496_, lean_object* v_a_497_, lean_object* v_b_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(v_m_496_, v_a_497_, v_b_498_);
return v___x_499_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_500_, lean_object* v_a_501_, lean_object* v_x_502_){
_start:
{
uint8_t v___x_503_; 
v___x_503_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_501_, v_x_502_);
return v___x_503_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_501_ = stack[1].m_obj;
lean_object* v_x_502_ = stack[2].m_obj;
uint8_t v_res_504_;
v_res_504_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2(lean_box(0), v_a_501_, v_x_502_);
stack->m_num = v_res_504_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_505_, lean_object* v_a_506_, lean_object* v_x_507_){
_start:
{
uint8_t v_res_508_; lean_object* v_r_509_; 
v_res_508_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2(v_00_u03b2_505_, v_a_506_, v_x_507_);
lean_dec(v_x_507_);
lean_dec_ref(v_a_506_);
v_r_509_ = lean_box(v_res_508_);
return v_r_509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_510_, lean_object* v_data_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(v_data_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_513_, lean_object* v_i_514_, lean_object* v_source_515_, lean_object* v_target_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7___redArg(v_i_514_, v_source_515_, v_target_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_518_, lean_object* v_x_519_, lean_object* v_x_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8___redArg(v_x_519_, v_x_520_);
return v___x_521_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg(lean_object* v_a_522_, lean_object* v_x_523_){
_start:
{
if (lean_obj_tag(v_x_523_) == 0)
{
uint8_t v___x_524_; 
v___x_524_ = 0;
return v___x_524_;
}
else
{
lean_object* v_key_525_; lean_object* v_tail_526_; lean_object* v_name_527_; lean_object* v_name_528_; uint8_t v___x_529_; 
v_key_525_ = lean_ctor_get(v_x_523_, 0);
v_tail_526_ = lean_ctor_get(v_x_523_, 2);
v_name_527_ = lean_ctor_get(v_key_525_, 1);
v_name_528_ = lean_ctor_get(v_a_522_, 1);
v___x_529_ = lean_name_eq(v_name_527_, v_name_528_);
if (v___x_529_ == 0)
{
v_x_523_ = v_tail_526_;
goto _start;
}
else
{
return v___x_529_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_522_ = stack[0].m_obj;
lean_object* v_x_523_ = stack[1].m_obj;
uint8_t v_res_531_;
v_res_531_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg(v_a_522_, v_x_523_);
stack->m_num = v_res_531_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg___boxed(lean_object* v_a_532_, lean_object* v_x_533_){
_start:
{
uint8_t v_res_534_; lean_object* v_r_535_; 
v_res_534_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg(v_a_532_, v_x_533_);
lean_dec(v_x_533_);
lean_dec_ref(v_a_532_);
v_r_535_ = lean_box(v_res_534_);
return v_r_535_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___redArg(lean_object* v_m_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_buckets_538_; lean_object* v_name_539_; lean_object* v___x_540_; uint64_t v___y_542_; 
v_buckets_538_ = lean_ctor_get(v_m_536_, 1);
v_name_539_ = lean_ctor_get(v_a_537_, 1);
v___x_540_ = lean_array_get_size(v_buckets_538_);
if (lean_obj_tag(v_name_539_) == 0)
{
uint64_t v___x_556_; 
v___x_556_ = 1723ULL;
v___y_542_ = v___x_556_;
goto v___jp_541_;
}
else
{
uint64_t v_hash_557_; 
v_hash_557_ = lean_ctor_get_uint64(v_name_539_, sizeof(void*)*2);
v___y_542_ = v_hash_557_;
goto v___jp_541_;
}
v___jp_541_:
{
uint64_t v___x_543_; uint64_t v___x_544_; uint64_t v_fold_545_; uint64_t v___x_546_; uint64_t v___x_547_; uint64_t v___x_548_; size_t v___x_549_; size_t v___x_550_; size_t v___x_551_; size_t v___x_552_; size_t v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_543_ = 32ULL;
v___x_544_ = lean_uint64_shift_right(v___y_542_, v___x_543_);
v_fold_545_ = lean_uint64_xor(v___y_542_, v___x_544_);
v___x_546_ = 16ULL;
v___x_547_ = lean_uint64_shift_right(v_fold_545_, v___x_546_);
v___x_548_ = lean_uint64_xor(v_fold_545_, v___x_547_);
v___x_549_ = lean_uint64_to_usize(v___x_548_);
v___x_550_ = lean_usize_of_nat(v___x_540_);
v___x_551_ = ((size_t)1ULL);
v___x_552_ = lean_usize_sub(v___x_550_, v___x_551_);
v___x_553_ = lean_usize_land(v___x_549_, v___x_552_);
v___x_554_ = lean_array_uget_borrowed(v_buckets_538_, v___x_553_);
v___x_555_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg(v_a_537_, v___x_554_);
return v___x_555_;
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_536_ = stack[0].m_obj;
lean_object* v_a_537_ = stack[1].m_obj;
uint8_t v_res_558_;
v_res_558_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___redArg(v_m_536_, v_a_537_);
stack->m_num = v_res_558_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___redArg___boxed(lean_object* v_m_559_, lean_object* v_a_560_){
_start:
{
uint8_t v_res_561_; lean_object* v_r_562_; 
v_res_561_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___redArg(v_m_559_, v_a_560_);
lean_dec_ref(v_a_560_);
lean_dec_ref(v_m_559_);
v_r_562_ = lean_box(v_res_561_);
return v_r_562_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_x_563_, lean_object* v_x_564_){
_start:
{
if (lean_obj_tag(v_x_564_) == 0)
{
return v_x_563_;
}
else
{
lean_object* v_key_565_; lean_object* v_value_566_; lean_object* v_tail_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_594_; 
v_key_565_ = lean_ctor_get(v_x_564_, 0);
v_value_566_ = lean_ctor_get(v_x_564_, 1);
v_tail_567_ = lean_ctor_get(v_x_564_, 2);
v_isSharedCheck_594_ = !lean_is_exclusive(v_x_564_);
if (v_isSharedCheck_594_ == 0)
{
v___x_569_ = v_x_564_;
v_isShared_570_ = v_isSharedCheck_594_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_tail_567_);
lean_inc(v_value_566_);
lean_inc(v_key_565_);
lean_dec(v_x_564_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_594_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v_name_571_; lean_object* v___x_572_; uint64_t v___y_574_; 
v_name_571_ = lean_ctor_get(v_key_565_, 1);
v___x_572_ = lean_array_get_size(v_x_563_);
if (lean_obj_tag(v_name_571_) == 0)
{
uint64_t v___x_592_; 
v___x_592_ = 1723ULL;
v___y_574_ = v___x_592_;
goto v___jp_573_;
}
else
{
uint64_t v_hash_593_; 
v_hash_593_ = lean_ctor_get_uint64(v_name_571_, sizeof(void*)*2);
v___y_574_ = v_hash_593_;
goto v___jp_573_;
}
v___jp_573_:
{
uint64_t v___x_575_; uint64_t v___x_576_; uint64_t v_fold_577_; uint64_t v___x_578_; uint64_t v___x_579_; uint64_t v___x_580_; size_t v___x_581_; size_t v___x_582_; size_t v___x_583_; size_t v___x_584_; size_t v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_575_ = 32ULL;
v___x_576_ = lean_uint64_shift_right(v___y_574_, v___x_575_);
v_fold_577_ = lean_uint64_xor(v___y_574_, v___x_576_);
v___x_578_ = 16ULL;
v___x_579_ = lean_uint64_shift_right(v_fold_577_, v___x_578_);
v___x_580_ = lean_uint64_xor(v_fold_577_, v___x_579_);
v___x_581_ = lean_uint64_to_usize(v___x_580_);
v___x_582_ = lean_usize_of_nat(v___x_572_);
v___x_583_ = ((size_t)1ULL);
v___x_584_ = lean_usize_sub(v___x_582_, v___x_583_);
v___x_585_ = lean_usize_land(v___x_581_, v___x_584_);
v___x_586_ = lean_array_uget_borrowed(v_x_563_, v___x_585_);
lean_inc(v___x_586_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 2, v___x_586_);
v___x_588_ = v___x_569_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_key_565_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_value_566_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v___x_586_);
v___x_588_ = v_reuseFailAlloc_591_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_589_; 
v___x_589_ = lean_array_uset(v_x_563_, v___x_585_, v___x_588_);
v_x_563_ = v___x_589_;
v_x_564_ = v_tail_567_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3___redArg(lean_object* v_i_595_, lean_object* v_source_596_, lean_object* v_target_597_){
_start:
{
lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_598_ = lean_array_get_size(v_source_596_);
v___x_599_ = lean_nat_dec_lt(v_i_595_, v___x_598_);
if (v___x_599_ == 0)
{
lean_dec_ref(v_source_596_);
lean_dec(v_i_595_);
return v_target_597_;
}
else
{
lean_object* v_es_600_; lean_object* v___x_601_; lean_object* v_source_602_; lean_object* v_target_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v_es_600_ = lean_array_fget(v_source_596_, v_i_595_);
v___x_601_ = lean_box(0);
v_source_602_ = lean_array_fset(v_source_596_, v_i_595_, v___x_601_);
v_target_603_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3_spec__6___redArg(v_target_597_, v_es_600_);
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = lean_nat_add(v_i_595_, v___x_604_);
lean_dec(v_i_595_);
v_i_595_ = v___x_605_;
v_source_596_ = v_source_602_;
v_target_597_ = v_target_603_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2___redArg(lean_object* v_data_607_){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v_nbuckets_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_608_ = lean_array_get_size(v_data_607_);
v___x_609_ = lean_unsigned_to_nat(2u);
v_nbuckets_610_ = lean_nat_mul(v___x_608_, v___x_609_);
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = lean_box(0);
v___x_613_ = lean_mk_array(v_nbuckets_610_, v___x_612_);
v___x_614_ = lean_array_propagate_mark(v_data_607_, v___x_613_);
v___x_615_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3___redArg(v___x_611_, v_data_607_, v___x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1___redArg(lean_object* v_m_616_, lean_object* v_a_617_, lean_object* v_b_618_){
_start:
{
lean_object* v_size_619_; lean_object* v_buckets_620_; lean_object* v_name_621_; lean_object* v___x_622_; uint64_t v___y_624_; 
v_size_619_ = lean_ctor_get(v_m_616_, 0);
v_buckets_620_ = lean_ctor_get(v_m_616_, 1);
v_name_621_ = lean_ctor_get(v_a_617_, 1);
v___x_622_ = lean_array_get_size(v_buckets_620_);
if (lean_obj_tag(v_name_621_) == 0)
{
uint64_t v___x_661_; 
v___x_661_ = 1723ULL;
v___y_624_ = v___x_661_;
goto v___jp_623_;
}
else
{
uint64_t v_hash_662_; 
v_hash_662_ = lean_ctor_get_uint64(v_name_621_, sizeof(void*)*2);
v___y_624_ = v_hash_662_;
goto v___jp_623_;
}
v___jp_623_:
{
uint64_t v___x_625_; uint64_t v___x_626_; uint64_t v_fold_627_; uint64_t v___x_628_; uint64_t v___x_629_; uint64_t v___x_630_; size_t v___x_631_; size_t v___x_632_; size_t v___x_633_; size_t v___x_634_; size_t v___x_635_; lean_object* v_bkt_636_; uint8_t v___x_637_; 
v___x_625_ = 32ULL;
v___x_626_ = lean_uint64_shift_right(v___y_624_, v___x_625_);
v_fold_627_ = lean_uint64_xor(v___y_624_, v___x_626_);
v___x_628_ = 16ULL;
v___x_629_ = lean_uint64_shift_right(v_fold_627_, v___x_628_);
v___x_630_ = lean_uint64_xor(v_fold_627_, v___x_629_);
v___x_631_ = lean_uint64_to_usize(v___x_630_);
v___x_632_ = lean_usize_of_nat(v___x_622_);
v___x_633_ = ((size_t)1ULL);
v___x_634_ = lean_usize_sub(v___x_632_, v___x_633_);
v___x_635_ = lean_usize_land(v___x_631_, v___x_634_);
v_bkt_636_ = lean_array_uget_borrowed(v_buckets_620_, v___x_635_);
v___x_637_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg(v_a_617_, v_bkt_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_658_; 
lean_inc_ref(v_buckets_620_);
lean_inc(v_size_619_);
v_isSharedCheck_658_ = !lean_is_exclusive(v_m_616_);
if (v_isSharedCheck_658_ == 0)
{
lean_object* v_unused_659_; lean_object* v_unused_660_; 
v_unused_659_ = lean_ctor_get(v_m_616_, 1);
lean_dec(v_unused_659_);
v_unused_660_ = lean_ctor_get(v_m_616_, 0);
lean_dec(v_unused_660_);
v___x_639_ = v_m_616_;
v_isShared_640_ = v_isSharedCheck_658_;
goto v_resetjp_638_;
}
else
{
lean_dec(v_m_616_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_658_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v_size_x27_642_; lean_object* v___x_643_; lean_object* v_buckets_x27_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_641_ = lean_unsigned_to_nat(1u);
v_size_x27_642_ = lean_nat_add(v_size_619_, v___x_641_);
lean_dec(v_size_619_);
lean_inc(v_bkt_636_);
v___x_643_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_643_, 0, v_a_617_);
lean_ctor_set(v___x_643_, 1, v_b_618_);
lean_ctor_set(v___x_643_, 2, v_bkt_636_);
v_buckets_x27_644_ = lean_array_uset(v_buckets_620_, v___x_635_, v___x_643_);
v___x_645_ = lean_unsigned_to_nat(4u);
v___x_646_ = lean_nat_mul(v_size_x27_642_, v___x_645_);
v___x_647_ = lean_unsigned_to_nat(3u);
v___x_648_ = lean_nat_div(v___x_646_, v___x_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_array_get_size(v_buckets_x27_644_);
v___x_650_ = lean_nat_dec_le(v___x_648_, v___x_649_);
lean_dec(v___x_648_);
if (v___x_650_ == 0)
{
lean_object* v_val_651_; lean_object* v___x_653_; 
v_val_651_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2___redArg(v_buckets_x27_644_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 1, v_val_651_);
lean_ctor_set(v___x_639_, 0, v_size_x27_642_);
v___x_653_ = v___x_639_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_size_x27_642_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_val_651_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
else
{
lean_object* v___x_656_; 
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 1, v_buckets_x27_644_);
lean_ctor_set(v___x_639_, 0, v_size_x27_642_);
v___x_656_ = v___x_639_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_size_x27_642_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_buckets_x27_644_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
else
{
lean_dec(v_b_618_);
lean_dec_ref(v_a_617_);
return v_m_616_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___redArg(lean_object* v_as_663_, size_t v_sz_664_, size_t v_i_665_, lean_object* v_b_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_a_670_; lean_object* v_a_671_; uint8_t v___x_675_; 
v___x_675_ = lean_usize_dec_lt(v_i_665_, v_sz_664_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; 
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v_b_666_);
lean_ctor_set(v___x_676_, 1, v___y_667_);
return v___x_676_;
}
else
{
lean_object* v_fst_677_; lean_object* v_snd_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_693_; 
v_fst_677_ = lean_ctor_get(v_b_666_, 0);
v_snd_678_ = lean_ctor_get(v_b_666_, 1);
v_isSharedCheck_693_ = !lean_is_exclusive(v_b_666_);
if (v_isSharedCheck_693_ == 0)
{
v___x_680_ = v_b_666_;
v_isShared_681_ = v_isSharedCheck_693_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_snd_678_);
lean_inc(v_fst_677_);
lean_dec(v_b_666_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_693_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v_a_682_; uint8_t v___x_683_; 
v_a_682_ = lean_array_uget_borrowed(v_as_663_, v_i_665_);
v___x_683_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___redArg(v_snd_678_, v_a_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_684_ = lean_box(0);
lean_inc_n(v_a_682_, 2);
v___x_685_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1___redArg(v_snd_678_, v_a_682_, v___x_684_);
v___x_686_ = lean_array_push(v_fst_677_, v_a_682_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v___x_685_);
lean_ctor_set(v___x_680_, 0, v___x_686_);
v___x_688_ = v___x_680_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v___x_685_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
v_a_670_ = v___x_688_;
v_a_671_ = v___y_667_;
goto v___jp_669_;
}
}
else
{
lean_object* v___x_691_; 
if (v_isShared_681_ == 0)
{
v___x_691_ = v___x_680_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_fst_677_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_snd_678_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
v_a_670_ = v___x_691_;
v_a_671_ = v___y_667_;
goto v___jp_669_;
}
}
}
}
v___jp_669_:
{
size_t v___x_672_; size_t v___x_673_; 
v___x_672_ = ((size_t)1ULL);
v___x_673_ = lean_usize_add(v_i_665_, v___x_672_);
v_i_665_ = v___x_673_;
v_b_666_ = v_a_670_;
v___y_667_ = v_a_671_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_663_ = stack[0].m_obj;
size_t v_sz_664_ = stack[1].m_num;
size_t v_i_665_ = stack[2].m_num;
lean_object* v_b_666_ = stack[3].m_obj;
lean_object* v___y_667_ = stack[4].m_obj;
lean_object* v_res_694_;
v_res_694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___redArg(v_as_663_, v_sz_664_, v_i_665_, v_b_666_, v___y_667_);
stack->m_obj
 = v_res_694_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___redArg___boxed(lean_object* v_as_695_, lean_object* v_sz_696_, lean_object* v_i_697_, lean_object* v_b_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
size_t v_sz_boxed_701_; size_t v_i_boxed_702_; lean_object* v_res_703_; 
v_sz_boxed_701_ = lean_unbox_usize(v_sz_696_);
lean_dec(v_sz_696_);
v_i_boxed_702_ = lean_unbox_usize(v_i_697_);
lean_dec(v_i_697_);
v_res_703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___redArg(v_as_695_, v_sz_boxed_701_, v_i_boxed_702_, v_b_698_, v___y_699_);
lean_dec_ref(v_as_695_);
return v_res_703_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3(lean_object* v_self_709_, lean_object* v_as_710_, size_t v_sz_711_, size_t v_i_712_, lean_object* v_b_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v_a_722_; lean_object* v_a_723_; uint8_t v___x_725_; 
v___x_725_ = lean_usize_dec_lt(v_i_712_, v_sz_711_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; 
lean_dec_ref(v___y_714_);
lean_dec_ref(v_self_709_);
v___x_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_726_, 0, v_b_713_);
lean_ctor_set(v___x_726_, 1, v___y_719_);
return v___x_726_;
}
else
{
lean_object* v_fst_727_; lean_object* v_snd_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_828_; 
v_fst_727_ = lean_ctor_get(v_b_713_, 0);
v_snd_728_ = lean_ctor_get(v_b_713_, 1);
v_isSharedCheck_828_ = !lean_is_exclusive(v_b_713_);
if (v_isSharedCheck_828_ == 0)
{
v___x_730_ = v_b_713_;
v_isShared_731_ = v_isSharedCheck_828_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_snd_728_);
lean_inc(v_fst_727_);
lean_dec(v_b_713_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_828_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v_targetMods_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v_mods_762_; lean_object* v_a_763_; lean_object* v___x_799_; 
v_mods_762_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___closed__0));
v_a_763_ = lean_array_uget_borrowed(v_as_710_, v_i_712_);
v___x_799_ = l_Lake_Package_findTargetDecl_x3f(v_a_763_, v_self_709_);
if (lean_obj_tag(v___x_799_) == 0)
{
goto v___jp_764_;
}
else
{
lean_object* v_val_800_; lean_object* v_name_801_; lean_object* v_kind_802_; lean_object* v_config_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_826_; 
v_val_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_val_800_);
lean_dec_ref_known(v___x_799_, 1);
v_name_801_ = lean_ctor_get(v_val_800_, 1);
v_kind_802_ = lean_ctor_get(v_val_800_, 2);
v_config_803_ = lean_ctor_get(v_val_800_, 3);
v_isSharedCheck_826_ = !lean_is_exclusive(v_val_800_);
if (v_isSharedCheck_826_ == 0)
{
lean_object* v_unused_827_; 
v_unused_827_ = lean_ctor_get(v_val_800_, 0);
lean_dec(v_unused_827_);
v___x_805_ = v_val_800_;
v_isShared_806_ = v_isSharedCheck_826_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_config_803_);
lean_inc(v_kind_802_);
lean_inc(v_name_801_);
lean_dec(v_val_800_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_826_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_807_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___closed__2));
v___x_808_ = lean_name_eq(v_kind_802_, v___x_807_);
lean_dec(v_kind_802_);
if (v___x_808_ == 0)
{
lean_del_object(v___x_805_);
lean_dec(v_config_803_);
lean_dec(v_name_801_);
goto v___jp_764_;
}
else
{
lean_object* v_keyName_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_814_; 
v_keyName_809_ = lean_ctor_get(v_self_709_, 2);
lean_inc(v_name_801_);
lean_inc_ref(v_self_709_);
v___x_810_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_810_, 0, v_self_709_);
lean_ctor_set(v___x_810_, 1, v_name_801_);
lean_ctor_set(v___x_810_, 2, v_config_803_);
v___x_811_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_809_);
v___x_812_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_812_, 0, v_keyName_809_);
lean_ctor_set(v___x_812_, 1, v_name_801_);
if (v_isShared_806_ == 0)
{
lean_ctor_set_tag(v___x_805_, 1);
lean_ctor_set(v___x_805_, 3, v___x_811_);
lean_ctor_set(v___x_805_, 2, v___x_810_);
lean_ctor_set(v___x_805_, 1, v___x_807_);
lean_ctor_set(v___x_805_, 0, v___x_812_);
v___x_814_ = v___x_805_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_825_, 2, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_825_, 3, v___x_811_);
v___x_814_ = v_reuseFailAlloc_825_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; 
lean_inc_ref(v___y_714_);
lean_inc_ref(v___y_718_);
lean_inc(v___y_717_);
lean_inc(v___y_716_);
lean_inc(v___y_715_);
v___x_815_ = lean_apply_7(v___y_714_, v___x_814_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, lean_box(0));
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v_a_817_; lean_object* v___x_818_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_a_816_);
v_a_817_ = lean_ctor_get(v___x_815_, 1);
lean_inc(v_a_817_);
lean_dec_ref_known(v___x_815_, 2);
v___x_818_ = l_Lake_Job_await___redArg(v_a_816_, v_a_817_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v_a_820_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
v_a_820_ = lean_ctor_get(v___x_818_, 1);
lean_inc(v_a_820_);
lean_dec_ref_known(v___x_818_, 2);
lean_inc_ref(v___y_714_);
v_targetMods_733_ = v_a_819_;
v___y_734_ = v___y_714_;
v___y_735_ = v___y_715_;
v___y_736_ = v___y_716_;
v___y_737_ = v___y_717_;
v___y_738_ = v___y_718_;
v___y_739_ = v_a_820_;
goto v___jp_732_;
}
else
{
lean_object* v_a_821_; lean_object* v_a_822_; 
lean_del_object(v___x_730_);
lean_dec(v_snd_728_);
lean_dec(v_fst_727_);
lean_dec_ref(v___y_714_);
lean_dec_ref(v_self_709_);
v_a_821_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_821_);
v_a_822_ = lean_ctor_get(v___x_818_, 1);
lean_inc(v_a_822_);
lean_dec_ref_known(v___x_818_, 2);
v_a_722_ = v_a_821_;
v_a_723_ = v_a_822_;
goto v___jp_721_;
}
}
else
{
lean_object* v_a_823_; lean_object* v_a_824_; 
lean_del_object(v___x_730_);
lean_dec(v_snd_728_);
lean_dec(v_fst_727_);
lean_dec_ref(v___y_714_);
lean_dec_ref(v_self_709_);
v_a_823_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_a_823_);
v_a_824_ = lean_ctor_get(v___x_815_, 1);
lean_inc(v_a_824_);
lean_dec_ref_known(v___x_815_, 2);
v_a_722_ = v_a_823_;
v_a_723_ = v_a_824_;
goto v___jp_721_;
}
}
}
}
}
v___jp_732_:
{
lean_object* v___x_741_; 
lean_dec_ref(v___y_734_);
if (v_isShared_731_ == 0)
{
v___x_741_ = v___x_730_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_fst_727_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_snd_728_);
v___x_741_ = v_reuseFailAlloc_761_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
size_t v_sz_742_; size_t v___x_743_; lean_object* v___x_744_; 
v_sz_742_ = lean_array_size(v_targetMods_733_);
v___x_743_ = ((size_t)0ULL);
v___x_744_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___redArg(v_targetMods_733_, v_sz_742_, v___x_743_, v___x_741_, v___y_739_);
lean_dec_ref(v_targetMods_733_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v_a_746_; lean_object* v_fst_747_; lean_object* v_snd_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_758_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
v_a_746_ = lean_ctor_get(v___x_744_, 1);
lean_inc(v_a_746_);
lean_dec_ref_known(v___x_744_, 2);
v_fst_747_ = lean_ctor_get(v_a_745_, 0);
v_snd_748_ = lean_ctor_get(v_a_745_, 1);
v_isSharedCheck_758_ = !lean_is_exclusive(v_a_745_);
if (v_isSharedCheck_758_ == 0)
{
v___x_750_ = v_a_745_;
v_isShared_751_ = v_isSharedCheck_758_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_snd_748_);
lean_inc(v_fst_747_);
lean_dec(v_a_745_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_758_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_fst_747_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_snd_748_);
v___x_753_ = v_reuseFailAlloc_757_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
size_t v___x_754_; size_t v___x_755_; 
v___x_754_ = ((size_t)1ULL);
v___x_755_ = lean_usize_add(v_i_712_, v___x_754_);
v_i_712_ = v___x_755_;
v_b_713_ = v___x_753_;
v___y_719_ = v_a_746_;
goto _start;
}
}
}
else
{
lean_object* v_a_759_; lean_object* v_a_760_; 
lean_dec_ref(v___y_714_);
lean_dec_ref(v_self_709_);
v_a_759_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_759_);
v_a_760_ = lean_ctor_get(v___x_744_, 1);
lean_inc(v_a_760_);
lean_dec_ref_known(v___x_744_, 2);
v_a_722_ = v_a_759_;
v_a_723_ = v_a_760_;
goto v___jp_721_;
}
}
}
v___jp_764_:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lake_Package_findTargetDecl_x3f(v_a_763_, v_self_709_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_inc_ref(v___y_714_);
v_targetMods_733_ = v_mods_762_;
v___y_734_ = v___y_714_;
v___y_735_ = v___y_715_;
v___y_736_ = v___y_716_;
v___y_737_ = v___y_717_;
v___y_738_ = v___y_718_;
v___y_739_ = v___y_719_;
goto v___jp_732_;
}
else
{
lean_object* v_val_766_; lean_object* v_name_767_; lean_object* v_kind_768_; lean_object* v_config_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_797_; 
v_val_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_val_766_);
lean_dec_ref_known(v___x_765_, 1);
v_name_767_ = lean_ctor_get(v_val_766_, 1);
v_kind_768_ = lean_ctor_get(v_val_766_, 2);
v_config_769_ = lean_ctor_get(v_val_766_, 3);
v_isSharedCheck_797_ = !lean_is_exclusive(v_val_766_);
if (v_isSharedCheck_797_ == 0)
{
lean_object* v_unused_798_; 
v_unused_798_ = lean_ctor_get(v_val_766_, 0);
lean_dec(v_unused_798_);
v___x_771_ = v_val_766_;
v_isShared_772_ = v_isSharedCheck_797_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_config_769_);
lean_inc(v_kind_768_);
lean_inc(v_name_767_);
lean_dec(v_val_766_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_797_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_773_ = l_Lake_LeanExe_keyword;
v___x_774_ = lean_name_eq(v_kind_768_, v___x_773_);
lean_dec(v_kind_768_);
if (v___x_774_ == 0)
{
lean_del_object(v___x_771_);
lean_dec(v_config_769_);
lean_dec(v_name_767_);
lean_inc_ref(v___y_714_);
v_targetMods_733_ = v_mods_762_;
v___y_734_ = v___y_714_;
v___y_735_ = v___y_715_;
v___y_736_ = v___y_716_;
v___y_737_ = v___y_717_;
v___y_738_ = v___y_718_;
v___y_739_ = v___y_719_;
goto v___jp_732_;
}
else
{
lean_object* v_root_775_; lean_object* v_keyName_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_784_; 
v_root_775_ = lean_ctor_get(v_config_769_, 2);
lean_inc_n(v_root_775_, 2);
v_keyName_776_ = lean_ctor_get(v_self_709_, 2);
v___x_777_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_769_);
lean_dec(v_config_769_);
lean_inc_ref(v_self_709_);
v___x_778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_778_, 0, v_self_709_);
lean_ctor_set(v___x_778_, 1, v_name_767_);
lean_ctor_set(v___x_778_, 2, v___x_777_);
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
lean_ctor_set(v___x_779_, 1, v_root_775_);
v___x_780_ = l_Lake_Module_transImportsFacet;
lean_inc(v_keyName_776_);
v___x_781_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_781_, 0, v_keyName_776_);
lean_ctor_set(v___x_781_, 1, v_root_775_);
v___x_782_ = l_Lake_Module_keyword;
lean_inc_ref(v___x_779_);
if (v_isShared_772_ == 0)
{
lean_ctor_set_tag(v___x_771_, 1);
lean_ctor_set(v___x_771_, 3, v___x_780_);
lean_ctor_set(v___x_771_, 2, v___x_779_);
lean_ctor_set(v___x_771_, 1, v___x_782_);
lean_ctor_set(v___x_771_, 0, v___x_781_);
v___x_784_ = v___x_771_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_796_, 2, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_796_, 3, v___x_780_);
v___x_784_ = v_reuseFailAlloc_796_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_785_; 
lean_inc_ref(v___y_714_);
lean_inc_ref(v___y_718_);
lean_inc(v___y_717_);
lean_inc(v___y_716_);
lean_inc(v___y_715_);
v___x_785_ = lean_apply_7(v___y_714_, v___x_784_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, lean_box(0));
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v_a_787_; lean_object* v___x_788_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
v_a_787_ = lean_ctor_get(v___x_785_, 1);
lean_inc(v_a_787_);
lean_dec_ref_known(v___x_785_, 2);
v___x_788_ = l_Lake_Job_await___redArg(v_a_786_, v_a_787_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v_a_790_; lean_object* v___x_791_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
v_a_790_ = lean_ctor_get(v___x_788_, 1);
lean_inc(v_a_790_);
lean_dec_ref_known(v___x_788_, 2);
v___x_791_ = lean_array_push(v_a_789_, v___x_779_);
lean_inc_ref(v___y_714_);
v_targetMods_733_ = v___x_791_;
v___y_734_ = v___y_714_;
v___y_735_ = v___y_715_;
v___y_736_ = v___y_716_;
v___y_737_ = v___y_717_;
v___y_738_ = v___y_718_;
v___y_739_ = v_a_790_;
goto v___jp_732_;
}
else
{
lean_object* v_a_792_; lean_object* v_a_793_; 
lean_dec_ref_known(v___x_779_, 2);
lean_del_object(v___x_730_);
lean_dec(v_snd_728_);
lean_dec(v_fst_727_);
lean_dec_ref(v___y_714_);
lean_dec_ref(v_self_709_);
v_a_792_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_792_);
v_a_793_ = lean_ctor_get(v___x_788_, 1);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_788_, 2);
v_a_722_ = v_a_792_;
v_a_723_ = v_a_793_;
goto v___jp_721_;
}
}
else
{
lean_object* v_a_794_; lean_object* v_a_795_; 
lean_dec_ref_known(v___x_779_, 2);
lean_del_object(v___x_730_);
lean_dec(v_snd_728_);
lean_dec(v_fst_727_);
lean_dec_ref(v___y_714_);
lean_dec_ref(v_self_709_);
v_a_794_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_794_);
v_a_795_ = lean_ctor_get(v___x_785_, 1);
lean_inc(v_a_795_);
lean_dec_ref_known(v___x_785_, 2);
v_a_722_ = v_a_794_;
v_a_723_ = v_a_795_;
goto v___jp_721_;
}
}
}
}
}
}
}
}
v___jp_721_:
{
lean_object* v___x_724_; 
v___x_724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_724_, 0, v_a_722_);
lean_ctor_set(v___x_724_, 1, v_a_723_);
return v___x_724_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_709_ = stack[0].m_obj;
lean_object* v_as_710_ = stack[1].m_obj;
size_t v_sz_711_ = stack[2].m_num;
size_t v_i_712_ = stack[3].m_num;
lean_object* v_b_713_ = stack[4].m_obj;
lean_object* v___y_714_ = stack[5].m_obj;
lean_object* v___y_715_ = stack[6].m_obj;
lean_object* v___y_716_ = stack[7].m_obj;
lean_object* v___y_717_ = stack[8].m_obj;
lean_object* v___y_718_ = stack[9].m_obj;
lean_object* v___y_719_ = stack[10].m_obj;
lean_object* v_res_829_;
v_res_829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3(v_self_709_, v_as_710_, v_sz_711_, v_i_712_, v_b_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
stack->m_obj
 = v_res_829_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___boxed(lean_object* v_self_830_, lean_object* v_as_831_, lean_object* v_sz_832_, lean_object* v_i_833_, lean_object* v_b_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
size_t v_sz_boxed_842_; size_t v_i_boxed_843_; lean_object* v_res_844_; 
v_sz_boxed_842_ = lean_unbox_usize(v_sz_832_);
lean_dec(v_sz_832_);
v_i_boxed_843_ = lean_unbox_usize(v_i_833_);
lean_dec(v_i_833_);
v_res_844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3(v_self_830_, v_as_831_, v_sz_boxed_842_, v_i_boxed_843_, v_b_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v_as_831_);
return v_res_844_;
}
}
lean_object* l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___lam__0(lean_object* v_self_845_, lean_object* v_defaultTargets_846_, size_t v_sz_847_, size_t v___x_848_, lean_object* v___x_849_, lean_object* v___x_850_, lean_object* v___x_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3(v_self_845_, v_defaultTargets_846_, v_sz_847_, v___x_848_, v___x_849_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_885_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
v_a_861_ = lean_ctor_get(v___x_859_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_885_ == 0)
{
v___x_863_ = v___x_859_;
v_isShared_864_ = v_isSharedCheck_885_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_inc(v_a_860_);
lean_dec(v___x_859_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_885_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v_fst_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_883_; 
v_fst_865_ = lean_ctor_get(v_a_860_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v_a_860_);
if (v_isSharedCheck_883_ == 0)
{
lean_object* v_unused_884_; 
v_unused_884_ = lean_ctor_get(v_a_860_, 1);
lean_dec(v_unused_884_);
v___x_867_ = v_a_860_;
v_isShared_868_ = v_isSharedCheck_883_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_fst_865_);
lean_dec(v_a_860_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_883_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; uint8_t v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_869_ = lean_mk_empty_array_with_capacity(v___x_850_);
v___x_870_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_871_ = 0;
v___x_872_ = 0;
v___x_873_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_874_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_874_, 0, v___x_869_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
lean_ctor_set(v___x_874_, 2, v___x_850_);
lean_ctor_set_uint8(v___x_874_, sizeof(void*)*3, v___x_871_);
lean_ctor_set_uint8(v___x_874_, sizeof(void*)*3 + 1, v___x_872_);
lean_ctor_set_uint8(v___x_874_, sizeof(void*)*3 + 2, v___x_872_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 1, v___x_874_);
lean_ctor_set(v___x_863_, 0, v_fst_865_);
v___x_876_ = v___x_863_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_fst_865_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v___x_874_);
v___x_876_ = v_reuseFailAlloc_882_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_877_ = lean_task_pure(v___x_876_);
v___x_878_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_878_, 0, v___x_877_);
lean_ctor_set(v___x_878_, 1, v___x_851_);
lean_ctor_set(v___x_878_, 2, v___x_870_);
lean_ctor_set_uint8(v___x_878_, sizeof(void*)*3, v___x_872_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 1, v_a_861_);
lean_ctor_set(v___x_867_, 0, v___x_878_);
v___x_880_ = v___x_867_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_a_861_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
else
{
lean_object* v_a_886_; lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_dec(v___x_851_);
lean_dec(v___x_850_);
v_a_886_ = lean_ctor_get(v___x_859_, 0);
v_a_887_ = lean_ctor_get(v___x_859_, 1);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_859_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_inc(v_a_886_);
lean_dec(v___x_859_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_886_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_845_ = stack[0].m_obj;
lean_object* v_defaultTargets_846_ = stack[1].m_obj;
size_t v_sz_847_ = stack[2].m_num;
size_t v___x_848_ = stack[3].m_num;
lean_object* v___x_849_ = stack[4].m_obj;
lean_object* v___x_850_ = stack[5].m_obj;
lean_object* v___x_851_ = stack[6].m_obj;
lean_object* v___y_852_ = stack[7].m_obj;
lean_object* v___y_853_ = stack[8].m_obj;
lean_object* v___y_854_ = stack[9].m_obj;
lean_object* v___y_855_ = stack[10].m_obj;
lean_object* v___y_856_ = stack[11].m_obj;
lean_object* v___y_857_ = stack[12].m_obj;
lean_object* v_res_895_;
v_res_895_ = l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___lam__0(v_self_845_, v_defaultTargets_846_, v_sz_847_, v___x_848_, v___x_849_, v___x_850_, v___x_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
stack->m_obj
 = v_res_895_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___lam__0___boxed(lean_object* v_self_896_, lean_object* v_defaultTargets_897_, lean_object* v_sz_898_, lean_object* v___x_899_, lean_object* v___x_900_, lean_object* v___x_901_, lean_object* v___x_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
size_t v_sz_boxed_910_; size_t v___x_15622__boxed_911_; lean_object* v_res_912_; 
v_sz_boxed_910_ = lean_unbox_usize(v_sz_898_);
lean_dec(v_sz_898_);
v___x_15622__boxed_911_ = lean_unbox_usize(v___x_899_);
lean_dec(v___x_899_);
v_res_912_ = l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___lam__0(v_self_896_, v_defaultTargets_897_, v_sz_boxed_910_, v___x_15622__boxed_911_, v___x_900_, v___x_901_, v___x_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v_defaultTargets_897_);
return v_res_912_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__0(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = lean_box(0);
v___x_914_ = lean_unsigned_to_nat(16u);
v___x_915_ = lean_mk_array(v___x_914_, v___x_913_);
return v___x_915_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__1(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v_seen_918_; 
v___x_916_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__0);
v___x_917_ = lean_unsigned_to_nat(0u);
v_seen_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_seen_918_, 0, v___x_917_);
lean_ctor_set(v_seen_918_, 1, v___x_916_);
return v_seen_918_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__2(void){
_start:
{
lean_object* v_seen_919_; lean_object* v_mods_920_; lean_object* v___x_921_; 
v_seen_919_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__1, &l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__1_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__1);
v_mods_920_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___closed__0));
v___x_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_921_, 0, v_mods_920_);
lean_ctor_set(v___x_921_, 1, v_seen_919_);
return v___x_921_;
}
}
lean_object* l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules(lean_object* v_self_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
lean_object* v_defaultTargets_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; size_t v_sz_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___f_939_; lean_object* v___x_940_; 
v_defaultTargets_932_ = lean_ctor_get(v_self_924_, 17);
lean_inc_ref(v_defaultTargets_932_);
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_934_ = lean_box(0);
v___x_935_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__2, &l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__2_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__2);
v_sz_936_ = lean_array_size(v_defaultTargets_932_);
v___x_937_ = lean_box_usize(v_sz_936_);
v___x_938_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___boxed__const__1));
v___f_939_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___lam__0___boxed), 14, 7);
lean_closure_set(v___f_939_, 0, v_self_924_);
lean_closure_set(v___f_939_, 1, v_defaultTargets_932_);
lean_closure_set(v___f_939_, 2, v___x_937_);
lean_closure_set(v___f_939_, 3, v___x_938_);
lean_closure_set(v___f_939_, 4, v___x_935_);
lean_closure_set(v___f_939_, 5, v___x_933_);
lean_closure_set(v___f_939_, 6, v___x_934_);
v___x_940_ = l_Lake_ensureJob___redArg(v___x_934_, v___f_939_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
return v___x_940_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_924_ = stack[0].m_obj;
lean_object* v_a_925_ = stack[1].m_obj;
lean_object* v_a_926_ = stack[2].m_obj;
lean_object* v_a_927_ = stack[3].m_obj;
lean_object* v_a_928_ = stack[4].m_obj;
lean_object* v_a_929_ = stack[5].m_obj;
lean_object* v_a_930_ = stack[6].m_obj;
lean_object* v_res_941_;
v_res_941_ = l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules(v_self_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
stack->m_obj
 = v_res_941_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___boxed(lean_object* v_self_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules(v_self_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec(v_a_945_);
lean_dec(v_a_944_);
return v_res_950_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0(lean_object* v_00_u03b2_951_, lean_object* v_m_952_, lean_object* v_a_953_){
_start:
{
uint8_t v___x_954_; 
v___x_954_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___redArg(v_m_952_, v_a_953_);
return v___x_954_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_952_ = stack[1].m_obj;
lean_object* v_a_953_ = stack[2].m_obj;
uint8_t v_res_955_;
v_res_955_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0(lean_box(0), v_m_952_, v_a_953_);
stack->m_num = v_res_955_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___boxed(lean_object* v_00_u03b2_956_, lean_object* v_m_957_, lean_object* v_a_958_){
_start:
{
uint8_t v_res_959_; lean_object* v_r_960_; 
v_res_959_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0(v_00_u03b2_956_, v_m_957_, v_a_958_);
lean_dec_ref(v_a_958_);
lean_dec_ref(v_m_957_);
v_r_960_ = lean_box(v_res_959_);
return v_r_960_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1(lean_object* v_00_u03b2_961_, lean_object* v_m_962_, lean_object* v_a_963_, lean_object* v_b_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1___redArg(v_m_962_, v_a_963_, v_b_964_);
return v___x_965_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2(lean_object* v_as_966_, size_t v_sz_967_, size_t v_i_968_, lean_object* v_b_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___redArg(v_as_966_, v_sz_967_, v_i_968_, v_b_969_, v___y_975_);
return v___x_977_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_966_ = stack[0].m_obj;
size_t v_sz_967_ = stack[1].m_num;
size_t v_i_968_ = stack[2].m_num;
lean_object* v_b_969_ = stack[3].m_obj;
lean_object* v___y_970_ = stack[4].m_obj;
lean_object* v___y_971_ = stack[5].m_obj;
lean_object* v___y_972_ = stack[6].m_obj;
lean_object* v___y_973_ = stack[7].m_obj;
lean_object* v___y_974_ = stack[8].m_obj;
lean_object* v___y_975_ = stack[9].m_obj;
lean_object* v_res_978_;
v_res_978_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2(v_as_966_, v_sz_967_, v_i_968_, v_b_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
stack->m_obj
 = v_res_978_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___boxed(lean_object* v_as_979_, lean_object* v_sz_980_, lean_object* v_i_981_, lean_object* v_b_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
size_t v_sz_boxed_990_; size_t v_i_boxed_991_; lean_object* v_res_992_; 
v_sz_boxed_990_ = lean_unbox_usize(v_sz_980_);
lean_dec(v_sz_980_);
v_i_boxed_991_ = lean_unbox_usize(v_i_981_);
lean_dec(v_i_981_);
v_res_992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2(v_as_979_, v_sz_boxed_990_, v_i_boxed_991_, v_b_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec_ref(v_as_979_);
return v_res_992_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0(lean_object* v_00_u03b2_993_, lean_object* v_a_994_, lean_object* v_x_995_){
_start:
{
uint8_t v___x_996_; 
v___x_996_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg(v_a_994_, v_x_995_);
return v___x_996_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_994_ = stack[1].m_obj;
lean_object* v_x_995_ = stack[2].m_obj;
uint8_t v_res_997_;
v_res_997_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0(lean_box(0), v_a_994_, v_x_995_);
stack->m_num = v_res_997_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___boxed(lean_object* v_00_u03b2_998_, lean_object* v_a_999_, lean_object* v_x_1000_){
_start:
{
uint8_t v_res_1001_; lean_object* v_r_1002_; 
v_res_1001_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0(v_00_u03b2_998_, v_a_999_, v_x_1000_);
lean_dec(v_x_1000_);
lean_dec_ref(v_a_999_);
v_r_1002_ = lean_box(v_res_1001_);
return v_r_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2(lean_object* v_00_u03b2_1003_, lean_object* v_data_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2___redArg(v_data_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1006_, lean_object* v_i_1007_, lean_object* v_source_1008_, lean_object* v_target_1009_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3___redArg(v_i_1007_, v_source_1008_, v_target_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_1011_, lean_object* v_x_1012_, lean_object* v_x_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3_spec__6___redArg(v_x_1012_, v_x_1013_);
return v___x_1014_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__0(lean_object* v_as_1015_, size_t v_i_1016_, size_t v_stop_1017_, lean_object* v_b_1018_){
_start:
{
uint8_t v___x_1019_; 
v___x_1019_ = lean_usize_dec_eq(v_i_1016_, v_stop_1017_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; lean_object* v_name_1021_; uint8_t v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; size_t v___x_1027_; size_t v___x_1028_; 
v___x_1020_ = lean_array_uget_borrowed(v_as_1015_, v_i_1016_);
v_name_1021_ = lean_ctor_get(v___x_1020_, 1);
v___x_1022_ = 1;
lean_inc(v_name_1021_);
v___x_1023_ = l_Lean_Name_toString(v_name_1021_, v___x_1022_);
v___x_1024_ = lean_string_append(v_b_1018_, v___x_1023_);
lean_dec_ref(v___x_1023_);
v___x_1025_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0));
v___x_1026_ = lean_string_append(v___x_1024_, v___x_1025_);
v___x_1027_ = ((size_t)1ULL);
v___x_1028_ = lean_usize_add(v_i_1016_, v___x_1027_);
v_i_1016_ = v___x_1028_;
v_b_1018_ = v___x_1026_;
goto _start;
}
else
{
return v_b_1018_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1015_ = stack[0].m_obj;
size_t v_i_1016_ = stack[1].m_num;
size_t v_stop_1017_ = stack[2].m_num;
lean_object* v_b_1018_ = stack[3].m_obj;
lean_object* v_res_1030_;
v_res_1030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__0(v_as_1015_, v_i_1016_, v_stop_1017_, v_b_1018_);
stack->m_obj
 = v_res_1030_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__0___boxed(lean_object* v_as_1031_, lean_object* v_i_1032_, lean_object* v_stop_1033_, lean_object* v_b_1034_){
_start:
{
size_t v_i_boxed_1035_; size_t v_stop_boxed_1036_; lean_object* v_res_1037_; 
v_i_boxed_1035_ = lean_unbox_usize(v_i_1032_);
lean_dec(v_i_1032_);
v_stop_boxed_1036_ = lean_unbox_usize(v_stop_1033_);
lean_dec(v_stop_1033_);
v_res_1037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__0(v_as_1031_, v_i_boxed_1035_, v_stop_boxed_1036_, v_b_1034_);
lean_dec_ref(v_as_1031_);
return v_res_1037_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1_spec__2(size_t v_sz_1038_, size_t v_i_1039_, lean_object* v_bs_1040_){
_start:
{
uint8_t v___x_1041_; 
v___x_1041_ = lean_usize_dec_lt(v_i_1039_, v_sz_1038_);
if (v___x_1041_ == 0)
{
return v_bs_1040_;
}
else
{
lean_object* v_v_1042_; lean_object* v_name_1043_; lean_object* v___x_1044_; lean_object* v_bs_x27_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; size_t v___x_1048_; size_t v___x_1049_; lean_object* v___x_1050_; 
v_v_1042_ = lean_array_uget_borrowed(v_bs_1040_, v_i_1039_);
v_name_1043_ = lean_ctor_get(v_v_1042_, 1);
lean_inc(v_name_1043_);
v___x_1044_ = lean_unsigned_to_nat(0u);
v_bs_x27_1045_ = lean_array_uset(v_bs_1040_, v_i_1039_, v___x_1044_);
v___x_1046_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1043_, v___x_1041_);
v___x_1047_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
v___x_1048_ = ((size_t)1ULL);
v___x_1049_ = lean_usize_add(v_i_1039_, v___x_1048_);
v___x_1050_ = lean_array_uset(v_bs_x27_1045_, v_i_1039_, v___x_1047_);
v_i_1039_ = v___x_1049_;
v_bs_1040_ = v___x_1050_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1038_ = stack[0].m_num;
size_t v_i_1039_ = stack[1].m_num;
lean_object* v_bs_1040_ = stack[2].m_obj;
lean_object* v_res_1052_;
v_res_1052_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1_spec__2(v_sz_1038_, v_i_1039_, v_bs_1040_);
stack->m_obj
 = v_res_1052_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_1053_, lean_object* v_i_1054_, lean_object* v_bs_1055_){
_start:
{
size_t v_sz_boxed_1056_; size_t v_i_boxed_1057_; lean_object* v_res_1058_; 
v_sz_boxed_1056_ = lean_unbox_usize(v_sz_1053_);
lean_dec(v_sz_1053_);
v_i_boxed_1057_ = lean_unbox_usize(v_i_1054_);
lean_dec(v_i_1054_);
v_res_1058_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1_spec__2(v_sz_boxed_1056_, v_i_boxed_1057_, v_bs_1055_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1(lean_object* v_a_1059_){
_start:
{
size_t v_sz_1060_; size_t v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v_sz_1060_ = lean_array_size(v_a_1059_);
v___x_1061_ = ((size_t)0ULL);
v___x_1062_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1_spec__2(v_sz_1060_, v___x_1061_, v_a_1059_);
v___x_1063_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
return v___x_1063_;
}
}
lean_object* l_Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0(uint8_t v_fmt_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v___y_1067_; 
if (v_fmt_1064_ == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1074_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_1075_ = lean_unsigned_to_nat(0u);
v___x_1076_ = lean_array_get_size(v_a_1065_);
v___x_1077_ = lean_nat_dec_lt(v___x_1075_, v___x_1076_);
if (v___x_1077_ == 0)
{
lean_dec_ref(v_a_1065_);
v___y_1067_ = v___x_1074_;
goto v___jp_1066_;
}
else
{
size_t v___x_1078_; size_t v___x_1079_; lean_object* v___x_1080_; 
v___x_1078_ = ((size_t)0ULL);
v___x_1079_ = lean_usize_of_nat(v___x_1076_);
v___x_1080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__0(v_a_1065_, v___x_1078_, v___x_1079_, v___x_1074_);
lean_dec_ref(v_a_1065_);
v___y_1067_ = v___x_1080_;
goto v___jp_1066_;
}
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = l_Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1(v_a_1065_);
v___x_1082_ = l_Lean_Json_compress(v___x_1081_);
return v___x_1082_;
}
v___jp_1066_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1068_ = lean_unsigned_to_nat(1u);
v___x_1069_ = lean_unsigned_to_nat(0u);
v___x_1070_ = lean_string_utf8_byte_size(v___y_1067_);
lean_inc_ref(v___y_1067_);
v___x_1071_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1071_, 0, v___y_1067_);
lean_ctor_set(v___x_1071_, 1, v___x_1069_);
lean_ctor_set(v___x_1071_, 2, v___x_1070_);
v___x_1072_ = l_String_Slice_Pos_prevn(v___x_1071_, v___x_1070_, v___x_1068_);
lean_dec_ref_known(v___x_1071_, 3);
v___x_1073_ = lean_string_utf8_extract_fast(v___y_1067_, v___x_1069_, v___x_1072_);
lean_dec(v___x_1072_);
lean_dec_ref(v___y_1067_);
return v___x_1073_;
}
}
}
LEAN_EXPORT void l_Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_fmt_1064_ = stack[0].m_num;
lean_object* v_a_1065_ = stack[1].m_obj;
lean_object* v_res_1083_;
v_res_1083_ = l_Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0(v_fmt_1064_, v_a_1065_);
stack->m_obj
 = v_res_1083_;
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0___boxed(lean_object* v_fmt_1084_, lean_object* v_a_1085_){
_start:
{
uint8_t v_fmt_boxed_1086_; lean_object* v_res_1087_; 
v_fmt_boxed_1086_ = lean_unbox(v_fmt_1084_);
v_res_1087_ = l_Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0(v_fmt_boxed_1086_, v_a_1085_);
return v_res_1087_;
}
}
static lean_object* _init_l_Lake_Package_defaultModulesFacetConfig___closed__2(void){
_start:
{
uint8_t v___x_1090_; lean_object* v___f_1091_; uint8_t v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1090_ = 1;
v___f_1091_ = ((lean_object*)(l_Lake_Package_defaultModulesFacetConfig___closed__0));
v___x_1092_ = 0;
v___x_1093_ = lean_box(0);
v___x_1094_ = ((lean_object*)(l_Lake_Package_defaultModulesFacetConfig___closed__1));
v___x_1095_ = l_Lake_Package_keyword;
v___x_1096_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
lean_ctor_set(v___x_1096_, 1, v___x_1094_);
lean_ctor_set(v___x_1096_, 2, v___x_1093_);
lean_ctor_set(v___x_1096_, 3, v___f_1091_);
lean_ctor_set_uint8(v___x_1096_, sizeof(void*)*4, v___x_1092_);
lean_ctor_set_uint8(v___x_1096_, sizeof(void*)*4 + 1, v___x_1090_);
return v___x_1096_;
}
}
static lean_object* _init_l_Lake_Package_defaultModulesFacetConfig(void){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = lean_obj_once(&l_Lake_Package_defaultModulesFacetConfig___closed__2, &l_Lake_Package_defaultModulesFacetConfig___closed__2_once, _init_l_Lake_Package_defaultModulesFacetConfig___closed__2);
return v___x_1097_;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig___closed__1(void){
_start:
{
uint8_t v___x_1099_; lean_object* v___f_1100_; uint8_t v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1099_ = 1;
v___f_1100_ = ((lean_object*)(l_Lake_Package_depsFacetConfig___closed__0));
v___x_1101_ = 0;
v___x_1102_ = lean_box(0);
v___x_1103_ = ((lean_object*)(l_Lake_Package_transDepsFacetConfig___closed__0));
v___x_1104_ = l_Lake_Package_keyword;
v___x_1105_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
lean_ctor_set(v___x_1105_, 1, v___x_1103_);
lean_ctor_set(v___x_1105_, 2, v___x_1102_);
lean_ctor_set(v___x_1105_, 3, v___f_1100_);
lean_ctor_set_uint8(v___x_1105_, sizeof(void*)*4, v___x_1101_);
lean_ctor_set_uint8(v___x_1105_, sizeof(void*)*4 + 1, v___x_1099_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig(void){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_obj_once(&l_Lake_Package_transDepsFacetConfig___closed__1, &l_Lake_Package_transDepsFacetConfig___closed__1_once, _init_l_Lake_Package_transDepsFacetConfig___closed__1);
return v___x_1106_;
}
}
lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(lean_object* v_self_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v_config_1115_; uint8_t v_preferReleaseBuild_1116_; 
v_config_1115_ = lean_ctor_get(v_self_1107_, 6);
v_preferReleaseBuild_1116_ = lean_ctor_get_uint8(v_config_1115_, sizeof(void*)*28 + 2);
if (v_preferReleaseBuild_1116_ == 0)
{
lean_object* v_keyName_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v_keyName_1117_ = lean_ctor_get(v_self_1107_, 2);
v___x_1118_ = l_Lake_Package_optReservoirBarrelFacet;
lean_inc(v_keyName_1117_);
v___x_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1119_, 0, v_keyName_1117_);
v___x_1120_ = l_Lake_Package_keyword;
v___x_1121_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1119_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
lean_ctor_set(v___x_1121_, 2, v_self_1107_);
lean_ctor_set(v___x_1121_, 3, v___x_1118_);
lean_inc_ref(v_a_1112_);
lean_inc(v_a_1111_);
lean_inc(v_a_1110_);
lean_inc(v_a_1109_);
v___x_1122_ = lean_apply_7(v_a_1108_, v___x_1121_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, lean_box(0));
return v___x_1122_;
}
else
{
lean_object* v_keyName_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v_keyName_1123_ = lean_ctor_get(v_self_1107_, 2);
v___x_1124_ = l_Lake_Package_optGitHubReleaseFacet;
lean_inc(v_keyName_1123_);
v___x_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1125_, 0, v_keyName_1123_);
v___x_1126_ = l_Lake_Package_keyword;
v___x_1127_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1125_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
lean_ctor_set(v___x_1127_, 2, v_self_1107_);
lean_ctor_set(v___x_1127_, 3, v___x_1124_);
lean_inc_ref(v_a_1112_);
lean_inc(v_a_1111_);
lean_inc(v_a_1110_);
lean_inc(v_a_1109_);
v___x_1128_ = lean_apply_7(v_a_1108_, v___x_1127_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, lean_box(0));
return v___x_1128_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1107_ = stack[0].m_obj;
lean_object* v_a_1108_ = stack[1].m_obj;
lean_object* v_a_1109_ = stack[2].m_obj;
lean_object* v_a_1110_ = stack[3].m_obj;
lean_object* v_a_1111_ = stack[4].m_obj;
lean_object* v_a_1112_ = stack[5].m_obj;
lean_object* v_a_1113_ = stack[6].m_obj;
lean_object* v_res_1129_;
v_res_1129_ = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(v_self_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
stack->m_obj
 = v_res_1129_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___boxed(lean_object* v_self_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(v_self_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec(v_a_1133_);
lean_dec(v_a_1132_);
return v_res_1138_;
}
}
lean_object* l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0(uint8_t v_fmt_1141_, uint8_t v_a_1142_){
_start:
{
if (v_fmt_1141_ == 0)
{
if (v_a_1142_ == 0)
{
lean_object* v___x_1143_; 
v___x_1143_ = ((lean_object*)(l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0));
return v___x_1143_;
}
else
{
lean_object* v___x_1144_; 
v___x_1144_ = ((lean_object*)(l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1));
return v___x_1144_;
}
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1145_, 0, v_a_1142_);
v___x_1146_ = l_Lean_Json_compress(v___x_1145_);
return v___x_1146_;
}
}
}
LEAN_EXPORT void l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_fmt_1141_ = stack[0].m_num;
uint8_t v_a_1142_ = stack[1].m_num;
lean_object* v_res_1147_;
v_res_1147_ = l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0(v_fmt_1141_, v_a_1142_);
stack->m_obj
 = v_res_1147_;
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___boxed(lean_object* v_fmt_1148_, lean_object* v_a_1149_){
_start:
{
uint8_t v_fmt_boxed_1150_; uint8_t v_a_boxed_1151_; lean_object* v_res_1152_; 
v_fmt_boxed_1150_ = lean_unbox(v_fmt_1148_);
v_a_boxed_1151_ = lean_unbox(v_a_1149_);
v_res_1152_ = l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0(v_fmt_boxed_1150_, v_a_boxed_1151_);
return v_res_1152_;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_1155_; uint8_t v___x_1156_; lean_object* v___x_1157_; lean_object* v___f_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___f_1155_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_1156_ = 1;
v___x_1157_ = l_Lake_instDataKindBool;
v___f_1158_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__0));
v___x_1159_ = l_Lake_Package_keyword;
v___x_1160_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
lean_ctor_set(v___x_1160_, 1, v___f_1158_);
lean_ctor_set(v___x_1160_, 2, v___x_1157_);
lean_ctor_set(v___x_1160_, 3, v___f_1155_);
lean_ctor_set_uint8(v___x_1160_, sizeof(void*)*4, v___x_1156_);
lean_ctor_set_uint8(v___x_1160_, sizeof(void*)*4 + 1, v___x_1156_);
return v___x_1160_;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig(void){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_obj_once(&l_Lake_Package_optBuildCacheFacetConfig___closed__2, &l_Lake_Package_optBuildCacheFacetConfig___closed__2_once, _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2);
return v___x_1161_;
}
}
lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(lean_object* v_self_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v___y_1173_; uint8_t v___y_1174_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1197_; lean_object* v___y_1198_; uint8_t v___y_1199_; lean_object* v___y_1200_; lean_object* v_toContext_1204_; lean_object* v_lakeEnv_1205_; uint8_t v_noCache_1206_; lean_object* v_toolchain_1207_; uint8_t v_a_1209_; lean_object* v_a_1210_; 
v_toContext_1204_ = lean_ctor_get(v_a_1169_, 1);
v_lakeEnv_1205_ = lean_ctor_get(v_toContext_1204_, 0);
v_noCache_1206_ = lean_ctor_get_uint8(v_lakeEnv_1205_, sizeof(void*)*20);
v_toolchain_1207_ = lean_ctor_get(v_lakeEnv_1205_, 19);
if (v_noCache_1206_ == 0)
{
uint8_t v___x_1225_; 
v___x_1225_ = 1;
v_a_1209_ = v___x_1225_;
v_a_1210_ = v_a_1170_;
goto v___jp_1208_;
}
else
{
uint8_t v___x_1226_; 
v___x_1226_ = 0;
v_a_1209_ = v___x_1226_;
v_a_1210_ = v_a_1170_;
goto v___jp_1208_;
}
v___jp_1172_:
{
uint8_t v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1175_ = 1;
v___x_1176_ = lean_box(0);
v___x_1177_ = lean_unsigned_to_nat(0u);
v___x_1178_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_1179_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_1180_ = 0;
v___x_1181_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_1182_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1182_, 0, v___x_1178_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
lean_ctor_set(v___x_1182_, 2, v___x_1177_);
lean_ctor_set_uint8(v___x_1182_, sizeof(void*)*3, v___x_1180_);
lean_ctor_set_uint8(v___x_1182_, sizeof(void*)*3 + 1, v___y_1174_);
lean_ctor_set_uint8(v___x_1182_, sizeof(void*)*3 + 2, v___y_1174_);
v___x_1183_ = lean_box(v___x_1175_);
v___x_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set(v___x_1184_, 1, v___x_1182_);
v___x_1185_ = lean_task_pure(v___x_1184_);
v___x_1186_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
lean_ctor_set(v___x_1186_, 1, v___x_1176_);
lean_ctor_set(v___x_1186_, 2, v___x_1179_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*3, v___y_1174_);
v___x_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
lean_ctor_set(v___x_1187_, 1, v___y_1173_);
return v___x_1187_;
}
v___jp_1188_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1191_ = l_Lake_Package_optBuildCacheFacet;
v___x_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1192_, 0, v___y_1190_);
v___x_1193_ = l_Lake_Package_keyword;
v___x_1194_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1192_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
lean_ctor_set(v___x_1194_, 2, v_self_1164_);
lean_ctor_set(v___x_1194_, 3, v___x_1191_);
lean_inc_ref(v_a_1169_);
lean_inc(v_a_1168_);
lean_inc(v_a_1167_);
lean_inc(v_a_1166_);
v___x_1195_ = lean_apply_7(v_a_1165_, v___x_1194_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v___y_1189_, lean_box(0));
return v___x_1195_;
}
v___jp_1196_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1201_ = lean_string_utf8_byte_size(v___y_1198_);
v___x_1202_ = lean_unsigned_to_nat(0u);
v___x_1203_ = lean_nat_dec_eq(v___x_1201_, v___x_1202_);
if (v___x_1203_ == 0)
{
v___y_1189_ = v___y_1197_;
v___y_1190_ = v___y_1200_;
goto v___jp_1188_;
}
else
{
lean_dec(v___y_1200_);
lean_dec_ref(v_a_1165_);
lean_dec_ref(v_self_1164_);
v___y_1173_ = v___y_1197_;
v___y_1174_ = v___y_1199_;
goto v___jp_1172_;
}
}
v___jp_1208_:
{
lean_object* v_config_1211_; lean_object* v_keyName_1212_; lean_object* v_dir_1213_; lean_object* v_scope_1214_; lean_object* v_buildDir_1215_; uint8_t v_preferReleaseBuild_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; 
v_config_1211_ = lean_ctor_get(v_self_1164_, 6);
v_keyName_1212_ = lean_ctor_get(v_self_1164_, 2);
v_dir_1213_ = lean_ctor_get(v_self_1164_, 4);
v_scope_1214_ = lean_ctor_get(v_self_1164_, 10);
v_buildDir_1215_ = lean_ctor_get(v_config_1211_, 5);
v_preferReleaseBuild_1216_ = lean_ctor_get_uint8(v_config_1211_, sizeof(void*)*28 + 2);
lean_inc_ref(v_buildDir_1215_);
v___x_1217_ = l_System_FilePath_normalize(v_buildDir_1215_);
lean_inc_ref(v_dir_1213_);
v___x_1218_ = l_Lake_joinRelative(v_dir_1213_, v___x_1217_);
v___x_1219_ = l_System_FilePath_pathExists(v___x_1218_);
lean_dec_ref(v___x_1218_);
if (v_a_1209_ == 0)
{
lean_dec_ref(v_a_1165_);
lean_dec_ref(v_self_1164_);
v___y_1173_ = v_a_1210_;
v___y_1174_ = v_a_1209_;
goto v___jp_1172_;
}
else
{
if (v___x_1219_ == 0)
{
if (v_preferReleaseBuild_1216_ == 0)
{
lean_object* v___x_1220_; uint8_t v___x_1221_; 
v___x_1220_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__0));
v___x_1221_ = lean_string_dec_eq(v_scope_1214_, v___x_1220_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__1));
v___x_1223_ = lean_string_dec_eq(v_scope_1214_, v___x_1222_);
if (v___x_1223_ == 0)
{
lean_dec_ref(v_a_1165_);
lean_dec_ref(v_self_1164_);
v___y_1173_ = v_a_1210_;
v___y_1174_ = v___x_1223_;
goto v___jp_1172_;
}
else
{
lean_inc(v_keyName_1212_);
v___y_1197_ = v_a_1210_;
v___y_1198_ = v_toolchain_1207_;
v___y_1199_ = v_preferReleaseBuild_1216_;
v___y_1200_ = v_keyName_1212_;
goto v___jp_1196_;
}
}
else
{
lean_inc(v_keyName_1212_);
v___y_1197_ = v_a_1210_;
v___y_1198_ = v_toolchain_1207_;
v___y_1199_ = v_preferReleaseBuild_1216_;
v___y_1200_ = v_keyName_1212_;
goto v___jp_1196_;
}
}
else
{
lean_inc(v_keyName_1212_);
v___y_1189_ = v_a_1210_;
v___y_1190_ = v_keyName_1212_;
goto v___jp_1188_;
}
}
else
{
uint8_t v___x_1224_; 
lean_dec_ref(v_a_1165_);
lean_dec_ref(v_self_1164_);
v___x_1224_ = 0;
v___y_1173_ = v_a_1210_;
v___y_1174_ = v___x_1224_;
goto v___jp_1172_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1164_ = stack[0].m_obj;
lean_object* v_a_1165_ = stack[1].m_obj;
lean_object* v_a_1166_ = stack[2].m_obj;
lean_object* v_a_1167_ = stack[3].m_obj;
lean_object* v_a_1168_ = stack[4].m_obj;
lean_object* v_a_1169_ = stack[5].m_obj;
lean_object* v_a_1170_ = stack[6].m_obj;
lean_object* v_res_1227_;
v_res_1227_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_);
stack->m_obj
 = v_res_1227_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___boxed(lean_object* v_self_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec(v_a_1230_);
return v_res_1236_;
}
}
lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(lean_object* v_self_1241_, lean_object* v_facet_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_toBuildConfig_1246_; uint8_t v_verbosity_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v_toBuildConfig_1246_ = lean_ctor_get(v_a_1243_, 0);
v_verbosity_1247_ = lean_ctor_get_uint8(v_toBuildConfig_1246_, sizeof(void*)*5 + 4);
v___x_1248_ = lean_box(v_verbosity_1247_);
v___x_1249_ = lean_obj_tag_nat(v___x_1248_);
lean_dec(v___x_1248_);
v___x_1250_ = lean_unsigned_to_nat(2u);
v___x_1251_ = lean_nat_dec_eq(v___x_1249_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_dec(v_facet_1242_);
lean_dec_ref(v_self_1241_);
v___x_1252_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v___x_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
lean_ctor_set(v___x_1253_, 1, v_a_1244_);
return v___x_1253_;
}
else
{
lean_object* v_baseName_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v_baseName_1254_ = lean_ctor_get(v_self_1241_, 1);
lean_inc(v_baseName_1254_);
lean_dec_ref(v_self_1241_);
v___x_1255_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_1256_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1254_, v___x_1251_);
v___x_1257_ = lean_string_append(v___x_1255_, v___x_1256_);
lean_dec_ref(v___x_1256_);
v___x_1258_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1259_ = lean_string_append(v___x_1257_, v___x_1258_);
v___x_1260_ = l_Lake_Name_eraseHead(v_facet_1242_);
v___x_1261_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1260_, v___x_1251_);
v___x_1262_ = lean_string_append(v___x_1259_, v___x_1261_);
lean_dec_ref(v___x_1261_);
v___x_1263_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1264_ = lean_string_append(v___x_1262_, v___x_1263_);
v___x_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
lean_ctor_set(v___x_1265_, 1, v_a_1244_);
return v___x_1265_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1241_ = stack[0].m_obj;
lean_object* v_facet_1242_ = stack[1].m_obj;
lean_object* v_a_1243_ = stack[2].m_obj;
lean_object* v_a_1244_ = stack[3].m_obj;
lean_object* v_res_1266_;
v_res_1266_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(v_self_1241_, v_facet_1242_, v_a_1243_, v_a_1244_);
stack->m_obj
 = v_res_1266_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___boxed(lean_object* v_self_1267_, lean_object* v_facet_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(v_self_1267_, v_facet_1268_, v_a_1269_, v_a_1270_);
lean_dec_ref(v_a_1269_);
return v_res_1272_;
}
}
lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(lean_object* v_self_1273_, lean_object* v_facet_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v_toBuildConfig_1282_; uint8_t v_verbosity_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
v_toBuildConfig_1282_ = lean_ctor_get(v_a_1279_, 0);
v_verbosity_1283_ = lean_ctor_get_uint8(v_toBuildConfig_1282_, sizeof(void*)*5 + 4);
v___x_1284_ = lean_box(v_verbosity_1283_);
v___x_1285_ = lean_obj_tag_nat(v___x_1284_);
lean_dec(v___x_1284_);
v___x_1286_ = lean_unsigned_to_nat(2u);
v___x_1287_ = lean_nat_dec_eq(v___x_1285_, v___x_1286_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_dec(v_facet_1274_);
lean_dec_ref(v_self_1273_);
v___x_1288_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v___x_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
lean_ctor_set(v___x_1289_, 1, v_a_1280_);
return v___x_1289_;
}
else
{
lean_object* v_baseName_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v_baseName_1290_ = lean_ctor_get(v_self_1273_, 1);
lean_inc(v_baseName_1290_);
lean_dec_ref(v_self_1273_);
v___x_1291_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_1292_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1290_, v___x_1287_);
v___x_1293_ = lean_string_append(v___x_1291_, v___x_1292_);
lean_dec_ref(v___x_1292_);
v___x_1294_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1295_ = lean_string_append(v___x_1293_, v___x_1294_);
v___x_1296_ = l_Lake_Name_eraseHead(v_facet_1274_);
v___x_1297_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1296_, v___x_1287_);
v___x_1298_ = lean_string_append(v___x_1295_, v___x_1297_);
lean_dec_ref(v___x_1297_);
v___x_1299_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1300_ = lean_string_append(v___x_1298_, v___x_1299_);
v___x_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
lean_ctor_set(v___x_1301_, 1, v_a_1280_);
return v___x_1301_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1273_ = stack[0].m_obj;
lean_object* v_facet_1274_ = stack[1].m_obj;
lean_object* v_a_1275_ = stack[2].m_obj;
lean_object* v_a_1276_ = stack[3].m_obj;
lean_object* v_a_1277_ = stack[4].m_obj;
lean_object* v_a_1278_ = stack[5].m_obj;
lean_object* v_a_1279_ = stack[6].m_obj;
lean_object* v_a_1280_ = stack[7].m_obj;
lean_object* v_res_1302_;
v_res_1302_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(v_self_1273_, v_facet_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_);
stack->m_obj
 = v_res_1302_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___boxed(lean_object* v_self_1303_, lean_object* v_facet_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(v_self_1303_, v_facet_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
return v_res_1312_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_1316_ = l_Lake_Name_eraseHead(v___x_1315_);
return v___x_1316_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_1318_ = l_Lake_Name_eraseHead(v___x_1317_);
return v___x_1318_;
}
}
lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(lean_object* v_self_1319_, uint8_t v_success_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_a_1329_; lean_object* v_a_1330_; lean_object* v_a_1352_; lean_object* v_a_1353_; 
if (v_success_1320_ == 0)
{
lean_object* v_config_1374_; uint8_t v_preferReleaseBuild_1375_; 
v_config_1374_ = lean_ctor_get(v_self_1319_, 6);
v_preferReleaseBuild_1375_ = lean_ctor_get_uint8(v_config_1374_, sizeof(void*)*28 + 2);
if (v_preferReleaseBuild_1375_ == 0)
{
lean_object* v_toBuildConfig_1376_; lean_object* v_baseName_1377_; uint8_t v_verbosity_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v_toBuildConfig_1376_ = lean_ctor_get(v___y_1325_, 0);
v_baseName_1377_ = lean_ctor_get(v_self_1319_, 1);
lean_inc(v_baseName_1377_);
lean_dec_ref(v_self_1319_);
v_verbosity_1378_ = lean_ctor_get_uint8(v_toBuildConfig_1376_, sizeof(void*)*5 + 4);
v___x_1379_ = lean_box(v_verbosity_1378_);
v___x_1380_ = lean_obj_tag_nat(v___x_1379_);
lean_dec(v___x_1379_);
v___x_1381_ = lean_unsigned_to_nat(2u);
v___x_1382_ = lean_nat_dec_eq(v___x_1380_, v___x_1381_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; 
lean_dec(v_baseName_1377_);
v___x_1383_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_1329_ = v___x_1383_;
v_a_1330_ = v___y_1326_;
goto v___jp_1328_;
}
else
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1384_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_1385_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1377_, v___x_1382_);
v___x_1386_ = lean_string_append(v___x_1384_, v___x_1385_);
lean_dec_ref(v___x_1385_);
v___x_1387_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1388_ = lean_string_append(v___x_1386_, v___x_1387_);
v___x_1389_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2);
v___x_1390_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1389_, v___x_1382_);
v___x_1391_ = lean_string_append(v___x_1388_, v___x_1390_);
lean_dec_ref(v___x_1390_);
v___x_1392_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1393_ = lean_string_append(v___x_1391_, v___x_1392_);
v_a_1329_ = v___x_1393_;
v_a_1330_ = v___y_1326_;
goto v___jp_1328_;
}
}
else
{
lean_object* v_toBuildConfig_1394_; lean_object* v_baseName_1395_; uint8_t v_verbosity_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v_toBuildConfig_1394_ = lean_ctor_get(v___y_1325_, 0);
v_baseName_1395_ = lean_ctor_get(v_self_1319_, 1);
lean_inc(v_baseName_1395_);
lean_dec_ref(v_self_1319_);
v_verbosity_1396_ = lean_ctor_get_uint8(v_toBuildConfig_1394_, sizeof(void*)*5 + 4);
v___x_1397_ = lean_box(v_verbosity_1396_);
v___x_1398_ = lean_obj_tag_nat(v___x_1397_);
lean_dec(v___x_1397_);
v___x_1399_ = lean_unsigned_to_nat(2u);
v___x_1400_ = lean_nat_dec_eq(v___x_1398_, v___x_1399_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; 
lean_dec(v_baseName_1395_);
v___x_1401_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_1352_ = v___x_1401_;
v_a_1353_ = v___y_1326_;
goto v___jp_1351_;
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1402_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_1403_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1395_, v___x_1400_);
v___x_1404_ = lean_string_append(v___x_1402_, v___x_1403_);
lean_dec_ref(v___x_1403_);
v___x_1405_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1406_ = lean_string_append(v___x_1404_, v___x_1405_);
v___x_1407_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3);
v___x_1408_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1407_, v___x_1400_);
v___x_1409_ = lean_string_append(v___x_1406_, v___x_1408_);
lean_dec_ref(v___x_1408_);
v___x_1410_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1411_ = lean_string_append(v___x_1409_, v___x_1410_);
v_a_1352_ = v___x_1411_;
v_a_1353_ = v___y_1326_;
goto v___jp_1351_;
}
}
}
else
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
lean_dec_ref(v_self_1319_);
v___x_1412_ = lean_box(0);
v___x_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
lean_ctor_set(v___x_1413_, 1, v___y_1326_);
return v___x_1413_;
}
v___jp_1328_:
{
lean_object* v_log_1331_; uint8_t v_action_1332_; uint8_t v_wantsRebuild_1333_; uint8_t v_canceled_1334_; lean_object* v_trace_1335_; lean_object* v_buildTime_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1350_; 
v_log_1331_ = lean_ctor_get(v_a_1330_, 0);
v_action_1332_ = lean_ctor_get_uint8(v_a_1330_, sizeof(void*)*3);
v_wantsRebuild_1333_ = lean_ctor_get_uint8(v_a_1330_, sizeof(void*)*3 + 1);
v_canceled_1334_ = lean_ctor_get_uint8(v_a_1330_, sizeof(void*)*3 + 2);
v_trace_1335_ = lean_ctor_get(v_a_1330_, 1);
v_buildTime_1336_ = lean_ctor_get(v_a_1330_, 2);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_a_1330_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1338_ = v_a_1330_;
v_isShared_1339_ = v_isSharedCheck_1350_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_buildTime_1336_);
lean_inc(v_trace_1335_);
lean_inc(v_log_1331_);
lean_dec(v_a_1330_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1350_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1347_; 
v___x_1340_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0));
v___x_1341_ = lean_string_append(v___x_1340_, v_a_1329_);
lean_dec_ref(v_a_1329_);
v___x_1342_ = 0;
v___x_1343_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1343_, 0, v___x_1341_);
lean_ctor_set_uint8(v___x_1343_, sizeof(void*)*1, v___x_1342_);
v___x_1344_ = lean_box(0);
v___x_1345_ = lean_array_push(v_log_1331_, v___x_1343_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1345_);
v___x_1347_ = v___x_1338_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1345_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_trace_1335_);
lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_buildTime_1336_);
lean_ctor_set_uint8(v_reuseFailAlloc_1349_, sizeof(void*)*3, v_action_1332_);
lean_ctor_set_uint8(v_reuseFailAlloc_1349_, sizeof(void*)*3 + 1, v_wantsRebuild_1333_);
lean_ctor_set_uint8(v_reuseFailAlloc_1349_, sizeof(void*)*3 + 2, v_canceled_1334_);
v___x_1347_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1348_; 
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1344_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
return v___x_1348_;
}
}
}
v___jp_1351_:
{
lean_object* v_log_1354_; uint8_t v_action_1355_; uint8_t v_wantsRebuild_1356_; uint8_t v_canceled_1357_; lean_object* v_trace_1358_; lean_object* v_buildTime_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1373_; 
v_log_1354_ = lean_ctor_get(v_a_1353_, 0);
v_action_1355_ = lean_ctor_get_uint8(v_a_1353_, sizeof(void*)*3);
v_wantsRebuild_1356_ = lean_ctor_get_uint8(v_a_1353_, sizeof(void*)*3 + 1);
v_canceled_1357_ = lean_ctor_get_uint8(v_a_1353_, sizeof(void*)*3 + 2);
v_trace_1358_ = lean_ctor_get(v_a_1353_, 1);
v_buildTime_1359_ = lean_ctor_get(v_a_1353_, 2);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_a_1353_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1361_ = v_a_1353_;
v_isShared_1362_ = v_isSharedCheck_1373_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_buildTime_1359_);
lean_inc(v_trace_1358_);
lean_inc(v_log_1354_);
lean_dec(v_a_1353_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1373_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1363_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1));
v___x_1364_ = lean_string_append(v___x_1363_, v_a_1352_);
lean_dec_ref(v_a_1352_);
v___x_1365_ = 2;
v___x_1366_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1366_, 0, v___x_1364_);
lean_ctor_set_uint8(v___x_1366_, sizeof(void*)*1, v___x_1365_);
v___x_1367_ = lean_box(0);
v___x_1368_ = lean_array_push(v_log_1354_, v___x_1366_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1368_);
v___x_1370_ = v___x_1361_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_trace_1358_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v_buildTime_1359_);
lean_ctor_set_uint8(v_reuseFailAlloc_1372_, sizeof(void*)*3, v_action_1355_);
lean_ctor_set_uint8(v_reuseFailAlloc_1372_, sizeof(void*)*3 + 1, v_wantsRebuild_1356_);
lean_ctor_set_uint8(v_reuseFailAlloc_1372_, sizeof(void*)*3 + 2, v_canceled_1357_);
v___x_1370_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
lean_object* v___x_1371_; 
v___x_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1367_);
lean_ctor_set(v___x_1371_, 1, v___x_1370_);
return v___x_1371_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1319_ = stack[0].m_obj;
uint8_t v_success_1320_ = stack[1].m_num;
lean_object* v___y_1321_ = stack[2].m_obj;
lean_object* v___y_1322_ = stack[3].m_obj;
lean_object* v___y_1323_ = stack[4].m_obj;
lean_object* v___y_1324_ = stack[5].m_obj;
lean_object* v___y_1325_ = stack[6].m_obj;
lean_object* v___y_1326_ = stack[7].m_obj;
lean_object* v_res_1414_;
v_res_1414_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(v_self_1319_, v_success_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
stack->m_obj
 = v_res_1414_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed(lean_object* v_self_1415_, lean_object* v_success_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
uint8_t v_success_boxed_1424_; lean_object* v_res_1425_; 
v_success_boxed_1424_ = lean_unbox(v_success_1416_);
v_res_1425_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(v_self_1415_, v_success_boxed_1424_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
return v_res_1425_;
}
}
lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(lean_object* v_self_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_){
_start:
{
lean_object* v___f_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
lean_inc_ref(v_self_1426_);
v___f_1434_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed), 9, 1);
lean_closure_set(v___f_1434_, 0, v_self_1426_);
v___x_1435_ = l_Lake_instDataKindUnit;
lean_inc_ref(v_a_1427_);
v___x_1436_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1449_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_a_1438_ = lean_ctor_get(v___x_1436_, 1);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1440_ = v___x_1436_;
v_isShared_1441_ = v_isSharedCheck_1449_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1449_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; uint8_t v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1447_; 
v___x_1442_ = lean_unsigned_to_nat(0u);
v___x_1443_ = 0;
v___x_1444_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_1445_ = l_Lake_Job_mapM___redArg(v___x_1435_, v_a_1437_, v___f_1434_, v___x_1442_, v___x_1443_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v___x_1444_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v___x_1445_);
v___x_1447_ = v___x_1440_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_a_1438_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec_ref(v___f_1434_);
lean_dec_ref(v_a_1427_);
v_a_1450_ = lean_ctor_get(v___x_1436_, 0);
v_a_1451_ = lean_ctor_get(v___x_1436_, 1);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1436_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_inc(v_a_1450_);
lean_dec(v___x_1436_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1450_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1426_ = stack[0].m_obj;
lean_object* v_a_1427_ = stack[1].m_obj;
lean_object* v_a_1428_ = stack[2].m_obj;
lean_object* v_a_1429_ = stack[3].m_obj;
lean_object* v_a_1430_ = stack[4].m_obj;
lean_object* v_a_1431_ = stack[5].m_obj;
lean_object* v_a_1432_ = stack[6].m_obj;
lean_object* v_res_1459_;
v_res_1459_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
stack->m_obj
 = v_res_1459_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___boxed(lean_object* v_self_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
lean_dec_ref(v_a_1465_);
lean_dec(v_a_1464_);
lean_dec(v_a_1463_);
lean_dec(v_a_1462_);
return v_res_1468_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(lean_object* v_self_1469_, lean_object* v_as_1470_, size_t v_sz_1471_, size_t v_i_1472_, lean_object* v_b_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
uint8_t v___x_1481_; 
v___x_1481_ = lean_usize_dec_lt(v_i_1472_, v_sz_1471_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; 
lean_dec_ref(v___y_1474_);
lean_dec_ref(v_self_1469_);
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v_b_1473_);
lean_ctor_set(v___x_1482_, 1, v___y_1479_);
return v___x_1482_;
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1484_; 
v_a_1483_ = lean_array_uget_borrowed(v_as_1470_, v_i_1472_);
lean_inc_ref(v___y_1474_);
lean_inc(v_a_1483_);
lean_inc_ref(v_self_1469_);
v___x_1484_ = l_Lake_Package_fetchTargetJob(v_self_1469_, v_a_1483_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v_a_1486_; lean_object* v___x_1487_; size_t v___x_1488_; size_t v___x_1489_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1485_);
v_a_1486_ = lean_ctor_get(v___x_1484_, 1);
lean_inc(v_a_1486_);
lean_dec_ref_known(v___x_1484_, 2);
v___x_1487_ = l_Lake_Job_mix___redArg(v_b_1473_, v_a_1485_);
v___x_1488_ = ((size_t)1ULL);
v___x_1489_ = lean_usize_add(v_i_1472_, v___x_1488_);
v_i_1472_ = v___x_1489_;
v_b_1473_ = v___x_1487_;
v___y_1479_ = v_a_1486_;
goto _start;
}
else
{
lean_object* v_a_1491_; lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec_ref(v___y_1474_);
lean_dec_ref(v_b_1473_);
lean_dec_ref(v_self_1469_);
v_a_1491_ = lean_ctor_get(v___x_1484_, 0);
v_a_1492_ = lean_ctor_get(v___x_1484_, 1);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1484_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_inc(v_a_1491_);
lean_dec(v___x_1484_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1491_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1469_ = stack[0].m_obj;
lean_object* v_as_1470_ = stack[1].m_obj;
size_t v_sz_1471_ = stack[2].m_num;
size_t v_i_1472_ = stack[3].m_num;
lean_object* v_b_1473_ = stack[4].m_obj;
lean_object* v___y_1474_ = stack[5].m_obj;
lean_object* v___y_1475_ = stack[6].m_obj;
lean_object* v___y_1476_ = stack[7].m_obj;
lean_object* v___y_1477_ = stack[8].m_obj;
lean_object* v___y_1478_ = stack[9].m_obj;
lean_object* v___y_1479_ = stack[10].m_obj;
lean_object* v_res_1500_;
v_res_1500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_1469_, v_as_1470_, v_sz_1471_, v_i_1472_, v_b_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
stack->m_obj
 = v_res_1500_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0___boxed(lean_object* v_self_1501_, lean_object* v_as_1502_, lean_object* v_sz_1503_, lean_object* v_i_1504_, lean_object* v_b_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
size_t v_sz_boxed_1513_; size_t v_i_boxed_1514_; lean_object* v_res_1515_; 
v_sz_boxed_1513_ = lean_unbox_usize(v_sz_1503_);
lean_dec(v_sz_1503_);
v_i_boxed_1514_ = lean_unbox_usize(v_i_1504_);
lean_dec(v_i_1504_);
v_res_1515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_1501_, v_as_1502_, v_sz_boxed_1513_, v_i_boxed_1514_, v_b_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v_as_1502_);
return v_res_1515_;
}
}
lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(lean_object* v_config_1516_, lean_object* v_self_1517_, lean_object* v_____r_1518_, lean_object* v_job_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_extraDepTargets_1527_; size_t v_sz_1528_; size_t v___x_1529_; lean_object* v___x_1530_; 
v_extraDepTargets_1527_ = lean_ctor_get(v_config_1516_, 2);
v_sz_1528_ = lean_array_size(v_extraDepTargets_1527_);
v___x_1529_ = ((size_t)0ULL);
v___x_1530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_1517_, v_extraDepTargets_1527_, v_sz_1528_, v___x_1529_, v_job_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
return v___x_1530_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_1516_ = stack[0].m_obj;
lean_object* v_self_1517_ = stack[1].m_obj;
lean_object* v_____r_1518_ = stack[2].m_obj;
lean_object* v_job_1519_ = stack[3].m_obj;
lean_object* v___y_1520_ = stack[4].m_obj;
lean_object* v___y_1521_ = stack[5].m_obj;
lean_object* v___y_1522_ = stack[6].m_obj;
lean_object* v___y_1523_ = stack[7].m_obj;
lean_object* v___y_1524_ = stack[8].m_obj;
lean_object* v___y_1525_ = stack[9].m_obj;
lean_object* v_res_1531_;
v_res_1531_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(v_config_1516_, v_self_1517_, v_____r_1518_, v_job_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
stack->m_obj
 = v_res_1531_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed(lean_object* v_config_1532_, lean_object* v_self_1533_, lean_object* v_____r_1534_, lean_object* v_job_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(v_config_1532_, v_self_1533_, v_____r_1534_, v_job_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v_config_1532_);
return v_res_1543_;
}
}
lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(uint8_t v___x_1544_, lean_object* v_self_1545_, lean_object* v_job_1546_, lean_object* v___f_1547_, lean_object* v___x_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
if (v___x_1544_ == 0)
{
lean_object* v___x_1556_; 
lean_inc_ref(v___y_1549_);
v___x_1556_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_1545_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v_a_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
v_a_1558_ = lean_ctor_get(v___x_1556_, 1);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1556_, 2);
v___x_1559_ = l_Lake_Job_add___redArg(v_job_1546_, v_a_1557_);
lean_inc_ref(v___y_1553_);
lean_inc(v___y_1552_);
lean_inc(v___y_1551_);
lean_inc(v___y_1550_);
v___x_1560_ = lean_apply_9(v___f_1547_, v___x_1548_, v___x_1559_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v_a_1558_, lean_box(0));
return v___x_1560_;
}
else
{
lean_dec_ref(v___y_1549_);
lean_dec_ref(v___f_1547_);
lean_dec_ref(v_job_1546_);
return v___x_1556_;
}
}
else
{
lean_object* v___x_1561_; 
lean_dec_ref(v_self_1545_);
lean_inc_ref(v___y_1553_);
lean_inc(v___y_1552_);
lean_inc(v___y_1551_);
lean_inc(v___y_1550_);
v___x_1561_ = lean_apply_9(v___f_1547_, v___x_1548_, v_job_1546_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, lean_box(0));
return v___x_1561_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1544_ = stack[0].m_num;
lean_object* v_self_1545_ = stack[1].m_obj;
lean_object* v_job_1546_ = stack[2].m_obj;
lean_object* v___f_1547_ = stack[3].m_obj;
lean_object* v___x_1548_ = stack[4].m_obj;
lean_object* v___y_1549_ = stack[5].m_obj;
lean_object* v___y_1550_ = stack[6].m_obj;
lean_object* v___y_1551_ = stack[7].m_obj;
lean_object* v___y_1552_ = stack[8].m_obj;
lean_object* v___y_1553_ = stack[9].m_obj;
lean_object* v___y_1554_ = stack[10].m_obj;
lean_object* v_res_1562_;
v_res_1562_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(v___x_1544_, v_self_1545_, v_job_1546_, v___f_1547_, v___x_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
stack->m_obj
 = v_res_1562_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed(lean_object* v___x_1563_, lean_object* v_self_1564_, lean_object* v_job_1565_, lean_object* v___f_1566_, lean_object* v___x_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
uint8_t v___x_4176__boxed_1575_; lean_object* v_res_1576_; 
v___x_4176__boxed_1575_ = lean_unbox(v___x_1563_);
v_res_1576_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(v___x_4176__boxed_1575_, v_self_1564_, v_job_1565_, v___f_1566_, v___x_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec(v___y_1569_);
return v_res_1576_;
}
}
lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(lean_object* v_self_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v_wsIdx_1587_; lean_object* v_baseName_1588_; lean_object* v_config_1589_; lean_object* v___f_1590_; lean_object* v___x_1591_; uint8_t v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; uint8_t v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v_job_1610_; uint8_t v___x_1611_; lean_object* v___x_1612_; lean_object* v___y_1613_; lean_object* v___x_1614_; 
v_wsIdx_1587_ = lean_ctor_get(v_self_1579_, 0);
v_baseName_1588_ = lean_ctor_get(v_self_1579_, 1);
v_config_1589_ = lean_ctor_get(v_self_1579_, 6);
lean_inc_ref(v_self_1579_);
lean_inc_ref(v_config_1589_);
v___f_1590_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1590_, 0, v_config_1589_);
lean_closure_set(v___f_1590_, 1, v_self_1579_);
v___x_1591_ = l_Lake_instDataKindUnit;
v___x_1592_ = 1;
lean_inc(v_baseName_1588_);
v___x_1593_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1588_, v___x_1592_);
v___x_1594_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0));
lean_inc_ref(v___x_1593_);
v___x_1595_ = lean_string_append(v___x_1593_, v___x_1594_);
v___x_1596_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1));
v___x_1597_ = lean_string_append(v___x_1596_, v___x_1593_);
lean_dec_ref(v___x_1593_);
v___x_1598_ = lean_string_append(v___x_1597_, v___x_1594_);
v___x_1599_ = lean_box(0);
v___x_1600_ = lean_box(0);
v___x_1601_ = lean_unsigned_to_nat(0u);
v___x_1602_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_1603_ = 0;
v___x_1604_ = 0;
v___x_1605_ = l_Lake_BuildTrace_nil(v___x_1598_);
v___x_1606_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1606_, 0, v___x_1602_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
lean_ctor_set(v___x_1606_, 2, v___x_1601_);
lean_ctor_set_uint8(v___x_1606_, sizeof(void*)*3, v___x_1603_);
lean_ctor_set_uint8(v___x_1606_, sizeof(void*)*3 + 1, v___x_1604_);
lean_ctor_set_uint8(v___x_1606_, sizeof(void*)*3 + 2, v___x_1604_);
v___x_1607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1599_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
v___x_1608_ = lean_task_pure(v___x_1607_);
v___x_1609_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v_job_1610_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_1610_, 0, v___x_1608_);
lean_ctor_set(v_job_1610_, 1, v___x_1600_);
lean_ctor_set(v_job_1610_, 2, v___x_1609_);
lean_ctor_set_uint8(v_job_1610_, sizeof(void*)*3, v___x_1604_);
v___x_1611_ = lean_nat_dec_eq(v_wsIdx_1587_, v___x_1601_);
v___x_1612_ = lean_box(v___x_1611_);
v___y_1613_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed), 12, 5);
lean_closure_set(v___y_1613_, 0, v___x_1612_);
lean_closure_set(v___y_1613_, 1, v_self_1579_);
lean_closure_set(v___y_1613_, 2, v_job_1610_);
lean_closure_set(v___y_1613_, 3, v___f_1590_);
lean_closure_set(v___y_1613_, 4, v___x_1599_);
v___x_1614_ = l_Lake_ensureJob___redArg(v___x_1591_, v___y_1613_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1639_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
v_a_1616_ = lean_ctor_get(v___x_1614_, 1);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1618_ = v___x_1614_;
v_isShared_1619_ = v_isSharedCheck_1639_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_inc(v_a_1615_);
lean_dec(v___x_1614_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1639_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v_task_1620_; lean_object* v_kind_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1637_; 
v_task_1620_ = lean_ctor_get(v_a_1615_, 0);
v_kind_1621_ = lean_ctor_get(v_a_1615_, 1);
v_isSharedCheck_1637_ = !lean_is_exclusive(v_a_1615_);
if (v_isSharedCheck_1637_ == 0)
{
lean_object* v_unused_1638_; 
v_unused_1638_ = lean_ctor_get(v_a_1615_, 2);
lean_dec(v_unused_1638_);
v___x_1623_ = v_a_1615_;
v_isShared_1624_ = v_isSharedCheck_1637_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_kind_1621_);
lean_inc(v_task_1620_);
lean_dec(v_a_1615_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1637_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v_registeredJobs_1625_; lean_object* v_job_1627_; 
v_registeredJobs_1625_ = lean_ctor_get(v_a_1584_, 4);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 2, v___x_1595_);
v_job_1627_ = v___x_1623_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_task_1620_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_kind_1621_);
lean_ctor_set(v_reuseFailAlloc_1636_, 2, v___x_1595_);
v_job_1627_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1634_; 
lean_ctor_set_uint8(v_job_1627_, sizeof(void*)*3, v___x_1604_);
v___x_1628_ = lean_st_ref_take(v_registeredJobs_1625_);
lean_inc_ref(v_job_1627_);
v___x_1629_ = l_Lake_Job_toOpaque___redArg(v_job_1627_);
v___x_1630_ = lean_array_push(v___x_1628_, v___x_1629_);
v___x_1631_ = lean_st_ref_put(v_registeredJobs_1625_, v___x_1630_);
v___x_1632_ = l_Lake_Job_renew___redArg(v_job_1627_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v___x_1632_);
v___x_1634_ = v___x_1618_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_a_1616_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1595_);
return v___x_1614_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1579_ = stack[0].m_obj;
lean_object* v_a_1580_ = stack[1].m_obj;
lean_object* v_a_1581_ = stack[2].m_obj;
lean_object* v_a_1582_ = stack[3].m_obj;
lean_object* v_a_1583_ = stack[4].m_obj;
lean_object* v_a_1584_ = stack[5].m_obj;
lean_object* v_a_1585_ = stack[6].m_obj;
lean_object* v_res_1640_;
v_res_1640_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(v_self_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
stack->m_obj
 = v_res_1640_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___boxed(lean_object* v_self_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(v_self_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec(v_a_1644_);
lean_dec(v_a_1643_);
return v_res_1649_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = lean_box(0);
v___x_1651_ = l_Lean_Json_compress(v___x_1650_);
return v___x_1651_;
}
}
lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(uint8_t v_fmt_1652_){
_start:
{
if (v_fmt_1652_ == 0)
{
lean_object* v___x_1653_; 
v___x_1653_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
return v___x_1653_;
}
else
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0);
return v___x_1654_;
}
}
}
LEAN_EXPORT void l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_fmt_1652_ = stack[0].m_num;
lean_object* v_res_1655_;
v_res_1655_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_1652_);
stack->m_obj
 = v_res_1655_;
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_1656_){
_start:
{
uint8_t v_fmt_boxed_1657_; lean_object* v_res_1658_; 
v_fmt_boxed_1657_ = lean_unbox(v_fmt_1656_);
v_res_1658_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_boxed_1657_);
return v_res_1658_;
}
}
lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(uint8_t v_fmt_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_1659_);
return v___x_1661_;
}
}
LEAN_EXPORT void l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_fmt_1659_ = stack[0].m_num;
lean_object* v_a_1660_ = stack[1].m_obj;
lean_object* v_res_1662_;
v_res_1662_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(v_fmt_1659_, v_a_1660_);
stack->m_obj
 = v_res_1662_;
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___boxed(lean_object* v_fmt_1663_, lean_object* v_a_1664_){
_start:
{
uint8_t v_fmt_boxed_1665_; lean_object* v_res_1666_; 
v_fmt_boxed_1665_ = lean_unbox(v_fmt_1663_);
v_res_1666_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(v_fmt_boxed_1665_, v_a_1664_);
return v_res_1666_;
}
}
lean_object* l_Lake_Package_extraDepFacetConfig___lam__0(uint8_t v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v___y_1667_);
return v___x_1669_;
}
}
LEAN_EXPORT void l_Lake_Package_extraDepFacetConfig___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_1667_ = stack[0].m_num;
lean_object* v___y_1668_ = stack[1].m_obj;
lean_object* v_res_1670_;
v_res_1670_ = l_Lake_Package_extraDepFacetConfig___lam__0(v___y_1667_, v___y_1668_);
stack->m_obj
 = v_res_1670_;
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0___boxed(lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
uint8_t v___y_72__boxed_1673_; lean_object* v_res_1674_; 
v___y_72__boxed_1673_ = lean_unbox(v___y_1671_);
v_res_1674_ = l_Lake_Package_extraDepFacetConfig___lam__0(v___y_72__boxed_1673_, v___y_1672_);
return v_res_1674_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_1677_; uint8_t v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___f_1677_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_1678_ = 1;
v___x_1679_ = l_Lake_instDataKindUnit;
v___x_1680_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__1));
v___x_1681_ = l_Lake_Package_keyword;
v___x_1682_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1682_, 0, v___x_1681_);
lean_ctor_set(v___x_1682_, 1, v___x_1680_);
lean_ctor_set(v___x_1682_, 2, v___x_1679_);
lean_ctor_set(v___x_1682_, 3, v___f_1677_);
lean_ctor_set_uint8(v___x_1682_, sizeof(void*)*4, v___x_1678_);
lean_ctor_set_uint8(v___x_1682_, sizeof(void*)*4 + 1, v___x_1678_);
return v___x_1682_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = lean_obj_once(&l_Lake_Package_extraDepFacetConfig___closed__2, &l_Lake_Package_extraDepFacetConfig___closed__2_once, _init_l_Lake_Package_extraDepFacetConfig___closed__2);
return v___x_1683_;
}
}
lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(lean_object* v_self_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_){
_start:
{
lean_object* v_origName_1703_; lean_object* v_dir_1704_; lean_object* v_scope_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; uint8_t v___x_1708_; 
v_origName_1703_ = lean_ctor_get(v_self_1699_, 3);
lean_inc(v_origName_1703_);
v_dir_1704_ = lean_ctor_get(v_self_1699_, 4);
lean_inc_ref(v_dir_1704_);
v_scope_1705_ = lean_ctor_get(v_self_1699_, 10);
lean_inc_ref(v_scope_1705_);
lean_dec_ref(v_self_1699_);
v___x_1706_ = lean_string_utf8_byte_size(v_scope_1705_);
v___x_1707_ = lean_unsigned_to_nat(0u);
v___x_1708_ = lean_nat_dec_eq(v___x_1706_, v___x_1707_);
if (v___x_1708_ == 0)
{
lean_object* v_log_1709_; uint8_t v_action_1710_; uint8_t v_wantsRebuild_1711_; uint8_t v_canceled_1712_; lean_object* v_trace_1713_; lean_object* v_buildTime_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v_log_1709_ = lean_ctor_get(v_a_1701_, 0);
v_action_1710_ = lean_ctor_get_uint8(v_a_1701_, sizeof(void*)*3);
v_wantsRebuild_1711_ = lean_ctor_get_uint8(v_a_1701_, sizeof(void*)*3 + 1);
v_canceled_1712_ = lean_ctor_get_uint8(v_a_1701_, sizeof(void*)*3 + 2);
v_trace_1713_ = lean_ctor_get(v_a_1701_, 1);
v_buildTime_1714_ = lean_ctor_get(v_a_1701_, 2);
v___x_1715_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
v___x_1716_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1715_, v_dir_1704_);
if (lean_obj_tag(v___x_1716_) == 1)
{
lean_object* v_toContext_1717_; lean_object* v_lakeEnv_1718_; lean_object* v_val_1719_; lean_object* v_toolchain_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; 
v_toContext_1717_ = lean_ctor_get(v_a_1700_, 1);
v_lakeEnv_1718_ = lean_ctor_get(v_toContext_1717_, 0);
v_val_1719_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_val_1719_);
lean_dec_ref_known(v___x_1716_, 1);
v_toolchain_1720_ = lean_ctor_get(v_lakeEnv_1718_, 19);
v___x_1721_ = lean_string_utf8_byte_size(v_toolchain_1720_);
v___x_1722_ = lean_nat_dec_eq(v___x_1721_, v___x_1707_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1723_ = l_Lean_Name_toString(v_origName_1703_, v___x_1708_);
lean_inc_ref(v_lakeEnv_1718_);
v___x_1724_ = l_Lake_Reservoir_pkgApiUrl(v_lakeEnv_1718_, v_scope_1705_, v___x_1723_);
lean_dec_ref(v___x_1723_);
lean_dec_ref(v_scope_1705_);
v___x_1725_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1));
v___x_1726_ = lean_string_append(v___x_1724_, v___x_1725_);
v___x_1727_ = lean_string_append(v___x_1726_, v_val_1719_);
lean_dec(v_val_1719_);
v___x_1728_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2));
v___x_1729_ = lean_string_append(v___x_1727_, v___x_1728_);
v___x_1730_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_1731_ = l_Lake_uriEncode(v_toolchain_1720_, v___x_1730_);
v___x_1732_ = lean_string_append(v___x_1729_, v___x_1731_);
lean_dec_ref(v___x_1731_);
v___x_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
lean_ctor_set(v___x_1733_, 1, v_a_1701_);
return v___x_1733_;
}
else
{
lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1744_; 
lean_inc(v_buildTime_1714_);
lean_inc_ref(v_trace_1713_);
lean_inc_ref(v_log_1709_);
lean_dec(v_val_1719_);
lean_dec_ref(v_scope_1705_);
lean_dec(v_origName_1703_);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_a_1701_);
if (v_isSharedCheck_1744_ == 0)
{
lean_object* v_unused_1745_; lean_object* v_unused_1746_; lean_object* v_unused_1747_; 
v_unused_1745_ = lean_ctor_get(v_a_1701_, 2);
lean_dec(v_unused_1745_);
v_unused_1746_ = lean_ctor_get(v_a_1701_, 1);
lean_dec(v_unused_1746_);
v_unused_1747_ = lean_ctor_get(v_a_1701_, 0);
lean_dec(v_unused_1747_);
v___x_1735_ = v_a_1701_;
v_isShared_1736_ = v_isSharedCheck_1744_;
goto v_resetjp_1734_;
}
else
{
lean_dec(v_a_1701_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1744_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1737_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4));
v___x_1738_ = lean_array_get_size(v_log_1709_);
v___x_1739_ = lean_array_push(v_log_1709_, v___x_1737_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 0, v___x_1739_);
v___x_1741_ = v___x_1735_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1739_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v_trace_1713_);
lean_ctor_set(v_reuseFailAlloc_1743_, 2, v_buildTime_1714_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*3, v_action_1710_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*3 + 1, v_wantsRebuild_1711_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*3 + 2, v_canceled_1712_);
v___x_1741_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1742_; 
v___x_1742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1738_);
lean_ctor_set(v___x_1742_, 1, v___x_1741_);
return v___x_1742_;
}
}
}
}
else
{
lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1758_; 
lean_inc(v_buildTime_1714_);
lean_inc_ref(v_trace_1713_);
lean_inc_ref(v_log_1709_);
lean_dec(v___x_1716_);
lean_dec_ref(v_scope_1705_);
lean_dec(v_origName_1703_);
v_isSharedCheck_1758_ = !lean_is_exclusive(v_a_1701_);
if (v_isSharedCheck_1758_ == 0)
{
lean_object* v_unused_1759_; lean_object* v_unused_1760_; lean_object* v_unused_1761_; 
v_unused_1759_ = lean_ctor_get(v_a_1701_, 2);
lean_dec(v_unused_1759_);
v_unused_1760_ = lean_ctor_get(v_a_1701_, 1);
lean_dec(v_unused_1760_);
v_unused_1761_ = lean_ctor_get(v_a_1701_, 0);
lean_dec(v_unused_1761_);
v___x_1749_ = v_a_1701_;
v_isShared_1750_ = v_isSharedCheck_1758_;
goto v_resetjp_1748_;
}
else
{
lean_dec(v_a_1701_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1758_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1755_; 
v___x_1751_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6));
v___x_1752_ = lean_array_get_size(v_log_1709_);
v___x_1753_ = lean_array_push(v_log_1709_, v___x_1751_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1753_);
v___x_1755_ = v___x_1749_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1753_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v_trace_1713_);
lean_ctor_set(v_reuseFailAlloc_1757_, 2, v_buildTime_1714_);
lean_ctor_set_uint8(v_reuseFailAlloc_1757_, sizeof(void*)*3, v_action_1710_);
lean_ctor_set_uint8(v_reuseFailAlloc_1757_, sizeof(void*)*3 + 1, v_wantsRebuild_1711_);
lean_ctor_set_uint8(v_reuseFailAlloc_1757_, sizeof(void*)*3 + 2, v_canceled_1712_);
v___x_1755_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
lean_object* v___x_1756_; 
v___x_1756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1752_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
return v___x_1756_;
}
}
}
}
else
{
lean_object* v_log_1762_; uint8_t v_action_1763_; uint8_t v_wantsRebuild_1764_; uint8_t v_canceled_1765_; lean_object* v_trace_1766_; lean_object* v_buildTime_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1778_; 
lean_dec_ref(v_scope_1705_);
lean_dec_ref(v_dir_1704_);
lean_dec(v_origName_1703_);
v_log_1762_ = lean_ctor_get(v_a_1701_, 0);
v_action_1763_ = lean_ctor_get_uint8(v_a_1701_, sizeof(void*)*3);
v_wantsRebuild_1764_ = lean_ctor_get_uint8(v_a_1701_, sizeof(void*)*3 + 1);
v_canceled_1765_ = lean_ctor_get_uint8(v_a_1701_, sizeof(void*)*3 + 2);
v_trace_1766_ = lean_ctor_get(v_a_1701_, 1);
v_buildTime_1767_ = lean_ctor_get(v_a_1701_, 2);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_a_1701_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1769_ = v_a_1701_;
v_isShared_1770_ = v_isSharedCheck_1778_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_buildTime_1767_);
lean_inc(v_trace_1766_);
lean_inc(v_log_1762_);
lean_dec(v_a_1701_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1778_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1775_; 
v___x_1771_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8));
v___x_1772_ = lean_array_get_size(v_log_1762_);
v___x_1773_ = lean_array_push(v_log_1762_, v___x_1771_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v___x_1773_);
v___x_1775_ = v___x_1769_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1773_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_trace_1766_);
lean_ctor_set(v_reuseFailAlloc_1777_, 2, v_buildTime_1767_);
lean_ctor_set_uint8(v_reuseFailAlloc_1777_, sizeof(void*)*3, v_action_1763_);
lean_ctor_set_uint8(v_reuseFailAlloc_1777_, sizeof(void*)*3 + 1, v_wantsRebuild_1764_);
lean_ctor_set_uint8(v_reuseFailAlloc_1777_, sizeof(void*)*3 + 2, v_canceled_1765_);
v___x_1775_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1772_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
return v___x_1776_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1699_ = stack[0].m_obj;
lean_object* v_a_1700_ = stack[1].m_obj;
lean_object* v_a_1701_ = stack[2].m_obj;
lean_object* v_res_1779_;
v_res_1779_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1699_, v_a_1700_, v_a_1701_);
stack->m_obj
 = v_res_1779_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___boxed(lean_object* v_self_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1780_, v_a_1781_, v_a_1782_);
lean_dec_ref(v_a_1781_);
return v_res_1784_;
}
}
lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(lean_object* v_self_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1785_, v_a_1790_, v_a_1791_);
return v___x_1793_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1785_ = stack[0].m_obj;
lean_object* v_a_1786_ = stack[1].m_obj;
lean_object* v_a_1787_ = stack[2].m_obj;
lean_object* v_a_1788_ = stack[3].m_obj;
lean_object* v_a_1789_ = stack[4].m_obj;
lean_object* v_a_1790_ = stack[5].m_obj;
lean_object* v_a_1791_ = stack[6].m_obj;
lean_object* v_res_1794_;
v_res_1794_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(v_self_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
stack->m_obj
 = v_res_1794_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___boxed(lean_object* v_self_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(v_self_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_);
lean_dec_ref(v_a_1800_);
lean_dec(v_a_1799_);
lean_dec(v_a_1798_);
lean_dec(v_a_1797_);
lean_dec_ref(v_a_1796_);
return v_res_1803_;
}
}
lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(lean_object* v_self_1813_, lean_object* v_a_1814_){
_start:
{
lean_object* v_rev_1817_; lean_object* v_log_1818_; uint8_t v_action_1819_; uint8_t v_wantsRebuild_1820_; uint8_t v_canceled_1821_; lean_object* v_trace_1822_; lean_object* v_buildTime_1823_; lean_object* v_dir_1832_; lean_object* v_config_1833_; lean_object* v_remoteUrl_1834_; lean_object* v_buildArchive_1835_; lean_object* v___y_1837_; lean_object* v___y_1838_; uint8_t v___y_1839_; uint8_t v___y_1840_; uint8_t v___y_1841_; lean_object* v___y_1842_; lean_object* v_val_1843_; lean_object* v___y_1863_; lean_object* v_releaseRepo_1885_; 
v_dir_1832_ = lean_ctor_get(v_self_1813_, 4);
lean_inc_ref(v_dir_1832_);
v_config_1833_ = lean_ctor_get(v_self_1813_, 6);
lean_inc_ref(v_config_1833_);
v_remoteUrl_1834_ = lean_ctor_get(v_self_1813_, 11);
lean_inc_ref(v_remoteUrl_1834_);
v_buildArchive_1835_ = lean_ctor_get(v_self_1813_, 21);
lean_inc_ref(v_buildArchive_1835_);
lean_dec_ref(v_self_1813_);
v_releaseRepo_1885_ = lean_ctor_get(v_config_1833_, 10);
lean_inc(v_releaseRepo_1885_);
lean_dec_ref(v_config_1833_);
if (lean_obj_tag(v_releaseRepo_1885_) == 0)
{
lean_object* v___x_1886_; lean_object* v___x_1887_; uint8_t v___x_1888_; 
v___x_1886_ = lean_string_utf8_byte_size(v_remoteUrl_1834_);
v___x_1887_ = lean_unsigned_to_nat(0u);
v___x_1888_ = lean_nat_dec_eq(v___x_1886_, v___x_1887_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1889_, 0, v_remoteUrl_1834_);
v___y_1863_ = v___x_1889_;
goto v___jp_1862_;
}
else
{
lean_dec_ref(v_remoteUrl_1834_);
v___y_1863_ = v_releaseRepo_1885_;
goto v___jp_1862_;
}
}
else
{
lean_dec_ref(v_remoteUrl_1834_);
v___y_1863_ = v_releaseRepo_1885_;
goto v___jp_1862_;
}
v___jp_1816_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1824_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0));
v___x_1825_ = lean_string_append(v___x_1824_, v_rev_1817_);
lean_dec_ref(v_rev_1817_);
v___x_1826_ = 3;
v___x_1827_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1827_, 0, v___x_1825_);
lean_ctor_set_uint8(v___x_1827_, sizeof(void*)*1, v___x_1826_);
v___x_1828_ = lean_array_get_size(v_log_1818_);
v___x_1829_ = lean_array_push(v_log_1818_, v___x_1827_);
v___x_1830_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
lean_ctor_set(v___x_1830_, 1, v_trace_1822_);
lean_ctor_set(v___x_1830_, 2, v_buildTime_1823_);
lean_ctor_set_uint8(v___x_1830_, sizeof(void*)*3, v_action_1819_);
lean_ctor_set_uint8(v___x_1830_, sizeof(void*)*3 + 1, v_wantsRebuild_1820_);
lean_ctor_set_uint8(v___x_1830_, sizeof(void*)*3 + 2, v_canceled_1821_);
v___x_1831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1828_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
return v___x_1831_;
}
v___jp_1836_:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
lean_inc_ref(v_dir_1832_);
v___x_1845_ = l_Lake_GitRepo_findTag_x3f(v___x_1844_, v_dir_1832_);
if (lean_obj_tag(v___x_1845_) == 1)
{
lean_object* v_val_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
lean_dec_ref(v_dir_1832_);
v_val_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_val_1846_);
lean_dec_ref_known(v___x_1845_, 1);
v___x_1847_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1847_, 0, v___y_1837_);
lean_ctor_set(v___x_1847_, 1, v___y_1838_);
lean_ctor_set(v___x_1847_, 2, v___y_1842_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*3, v___y_1839_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*3 + 1, v___y_1840_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*3 + 2, v___y_1841_);
v___x_1848_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1));
v___x_1849_ = lean_string_append(v_val_1843_, v___x_1848_);
v___x_1850_ = lean_string_append(v___x_1849_, v_val_1846_);
lean_dec(v_val_1846_);
v___x_1851_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2));
v___x_1852_ = lean_string_append(v___x_1850_, v___x_1851_);
v___x_1853_ = lean_string_append(v___x_1852_, v_buildArchive_1835_);
lean_dec_ref(v_buildArchive_1835_);
v___x_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
lean_ctor_set(v___x_1854_, 1, v___x_1847_);
return v___x_1854_;
}
else
{
lean_object* v___x_1855_; 
lean_dec(v___x_1845_);
lean_dec_ref(v_val_1843_);
lean_dec_ref(v_buildArchive_1835_);
v___x_1855_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1844_, v_dir_1832_);
if (lean_obj_tag(v___x_1855_) == 1)
{
lean_object* v_val_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v_val_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_val_1856_);
lean_dec_ref_known(v___x_1855_, 1);
v___x_1857_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3));
v___x_1858_ = lean_string_append(v___x_1857_, v_val_1856_);
lean_dec(v_val_1856_);
v___x_1859_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4));
v___x_1860_ = lean_string_append(v___x_1858_, v___x_1859_);
v_rev_1817_ = v___x_1860_;
v_log_1818_ = v___y_1837_;
v_action_1819_ = v___y_1839_;
v_wantsRebuild_1820_ = v___y_1840_;
v_canceled_1821_ = v___y_1841_;
v_trace_1822_ = v___y_1838_;
v_buildTime_1823_ = v___y_1842_;
goto v___jp_1816_;
}
else
{
lean_object* v___x_1861_; 
lean_dec(v___x_1855_);
v___x_1861_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v_rev_1817_ = v___x_1861_;
v_log_1818_ = v___y_1837_;
v_action_1819_ = v___y_1839_;
v_wantsRebuild_1820_ = v___y_1840_;
v_canceled_1821_ = v___y_1841_;
v_trace_1822_ = v___y_1838_;
v_buildTime_1823_ = v___y_1842_;
goto v___jp_1816_;
}
}
}
v___jp_1862_:
{
lean_object* v_log_1864_; uint8_t v_action_1865_; uint8_t v_wantsRebuild_1866_; uint8_t v_canceled_1867_; lean_object* v_trace_1868_; lean_object* v_buildTime_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1884_; 
v_log_1864_ = lean_ctor_get(v_a_1814_, 0);
v_action_1865_ = lean_ctor_get_uint8(v_a_1814_, sizeof(void*)*3);
v_wantsRebuild_1866_ = lean_ctor_get_uint8(v_a_1814_, sizeof(void*)*3 + 1);
v_canceled_1867_ = lean_ctor_get_uint8(v_a_1814_, sizeof(void*)*3 + 2);
v_trace_1868_ = lean_ctor_get(v_a_1814_, 1);
v_buildTime_1869_ = lean_ctor_get(v_a_1814_, 2);
v_isSharedCheck_1884_ = !lean_is_exclusive(v_a_1814_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1871_ = v_a_1814_;
v_isShared_1872_ = v_isSharedCheck_1884_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_buildTime_1869_);
lean_inc(v_trace_1868_);
lean_inc(v_log_1864_);
lean_dec(v_a_1814_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1884_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = l_Lake_Git_defaultRemote;
lean_inc_ref(v_dir_1832_);
v___x_1874_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v___x_1873_, v_dir_1832_);
if (lean_obj_tag(v___y_1863_) == 0)
{
if (lean_obj_tag(v___x_1874_) == 1)
{
lean_object* v_val_1875_; 
lean_del_object(v___x_1871_);
v_val_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_val_1875_);
lean_dec_ref_known(v___x_1874_, 1);
v___y_1837_ = v_log_1864_;
v___y_1838_ = v_trace_1868_;
v___y_1839_ = v_action_1865_;
v___y_1840_ = v_wantsRebuild_1866_;
v___y_1841_ = v_canceled_1867_;
v___y_1842_ = v_buildTime_1869_;
v_val_1843_ = v_val_1875_;
goto v___jp_1836_;
}
else
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1880_; 
lean_dec(v___x_1874_);
lean_dec_ref(v_buildArchive_1835_);
lean_dec_ref(v_dir_1832_);
v___x_1876_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6));
v___x_1877_ = lean_array_get_size(v_log_1864_);
v___x_1878_ = lean_array_push(v_log_1864_, v___x_1876_);
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1878_);
v___x_1880_ = v___x_1871_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_trace_1868_);
lean_ctor_set(v_reuseFailAlloc_1882_, 2, v_buildTime_1869_);
lean_ctor_set_uint8(v_reuseFailAlloc_1882_, sizeof(void*)*3, v_action_1865_);
lean_ctor_set_uint8(v_reuseFailAlloc_1882_, sizeof(void*)*3 + 1, v_wantsRebuild_1866_);
lean_ctor_set_uint8(v_reuseFailAlloc_1882_, sizeof(void*)*3 + 2, v_canceled_1867_);
v___x_1880_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1877_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
return v___x_1881_;
}
}
}
else
{
lean_object* v_val_1883_; 
lean_dec(v___x_1874_);
lean_del_object(v___x_1871_);
v_val_1883_ = lean_ctor_get(v___y_1863_, 0);
lean_inc(v_val_1883_);
lean_dec_ref_known(v___y_1863_, 1);
v___y_1837_ = v_log_1864_;
v___y_1838_ = v_trace_1868_;
v___y_1839_ = v_action_1865_;
v___y_1840_ = v_wantsRebuild_1866_;
v___y_1841_ = v_canceled_1867_;
v___y_1842_ = v_buildTime_1869_;
v_val_1843_ = v_val_1883_;
goto v___jp_1836_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1813_ = stack[0].m_obj;
lean_object* v_a_1814_ = stack[1].m_obj;
lean_object* v_res_1890_;
v_res_1890_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1813_, v_a_1814_);
stack->m_obj
 = v_res_1890_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___boxed(lean_object* v_self_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1891_, v_a_1892_);
return v_res_1894_;
}
}
lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(lean_object* v_self_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1895_, v_a_1901_);
return v___x_1903_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1895_ = stack[0].m_obj;
lean_object* v_a_1896_ = stack[1].m_obj;
lean_object* v_a_1897_ = stack[2].m_obj;
lean_object* v_a_1898_ = stack[3].m_obj;
lean_object* v_a_1899_ = stack[4].m_obj;
lean_object* v_a_1900_ = stack[5].m_obj;
lean_object* v_a_1901_ = stack[6].m_obj;
lean_object* v_res_1904_;
v_res_1904_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(v_self_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
stack->m_obj
 = v_res_1904_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___boxed(lean_object* v_self_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(v_self_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
lean_dec_ref(v_a_1910_);
lean_dec(v_a_1909_);
lean_dec(v_a_1908_);
lean_dec(v_a_1907_);
lean_dec_ref(v_a_1906_);
return v_res_1913_;
}
}
lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(lean_object* v_val_1914_, lean_object* v_a_x3f_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_log_1918_; uint8_t v_action_1919_; uint8_t v_wantsRebuild_1920_; uint8_t v_canceled_1921_; lean_object* v_trace_1922_; lean_object* v_buildTime_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1935_; 
v_log_1918_ = lean_ctor_get(v___y_1916_, 0);
v_action_1919_ = lean_ctor_get_uint8(v___y_1916_, sizeof(void*)*3);
v_wantsRebuild_1920_ = lean_ctor_get_uint8(v___y_1916_, sizeof(void*)*3 + 1);
v_canceled_1921_ = lean_ctor_get_uint8(v___y_1916_, sizeof(void*)*3 + 2);
v_trace_1922_ = lean_ctor_get(v___y_1916_, 1);
v_buildTime_1923_ = lean_ctor_get(v___y_1916_, 2);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___y_1916_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1925_ = v___y_1916_;
v_isShared_1926_ = v_isSharedCheck_1935_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_buildTime_1923_);
lean_inc(v_trace_1922_);
lean_inc(v_log_1918_);
lean_dec(v___y_1916_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1935_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1932_; 
v___x_1927_ = lean_io_mono_ms_now();
v___x_1928_ = lean_nat_sub(v___x_1927_, v_val_1914_);
lean_dec(v___x_1927_);
v___x_1929_ = lean_box(0);
v___x_1930_ = lean_nat_add(v_buildTime_1923_, v___x_1928_);
lean_dec(v___x_1928_);
lean_dec(v_buildTime_1923_);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 2, v___x_1930_);
v___x_1932_ = v___x_1925_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_log_1918_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_trace_1922_);
lean_ctor_set(v_reuseFailAlloc_1934_, 2, v___x_1930_);
lean_ctor_set_uint8(v_reuseFailAlloc_1934_, sizeof(void*)*3, v_action_1919_);
lean_ctor_set_uint8(v_reuseFailAlloc_1934_, sizeof(void*)*3 + 1, v_wantsRebuild_1920_);
lean_ctor_set_uint8(v_reuseFailAlloc_1934_, sizeof(void*)*3 + 2, v_canceled_1921_);
v___x_1932_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1933_; 
v___x_1933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1929_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
return v___x_1933_;
}
}
}
}
LEAN_EXPORT void l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1914_ = stack[0].m_obj;
lean_object* v_a_x3f_1915_ = stack[1].m_obj;
lean_object* v___y_1916_ = stack[2].m_obj;
lean_object* v_res_1936_;
v_res_1936_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v_val_1914_, v_a_x3f_1915_, v___y_1916_);
stack->m_obj
 = v_res_1936_;
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0___boxed(lean_object* v_val_1937_, lean_object* v_a_x3f_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v_val_1937_, v_a_x3f_1938_, v___y_1939_);
lean_dec(v_a_x3f_1938_);
lean_dec(v_val_1937_);
return v_res_1941_;
}
}
lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(lean_object* v_url_1947_, lean_object* v_archiveFile_1948_, lean_object* v_headers_1949_, lean_object* v_depTrace_1950_, lean_object* v_traceFile_1951_, uint8_t v_action_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v_a_1957_; lean_object* v_a_1958_; lean_object* v_log_1961_; uint8_t v_action_1962_; uint8_t v_wantsRebuild_1963_; uint8_t v_canceled_1964_; lean_object* v_trace_1965_; lean_object* v_buildTime_1966_; lean_object* v_toBuildConfig_1972_; lean_object* v_log_1973_; uint8_t v_action_1974_; uint8_t v_wantsRebuild_1975_; uint8_t v_canceled_1976_; lean_object* v_trace_1977_; lean_object* v_buildTime_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_2068_; 
v_toBuildConfig_1972_ = lean_ctor_get(v_a_1953_, 0);
v_log_1973_ = lean_ctor_get(v_a_1954_, 0);
v_action_1974_ = lean_ctor_get_uint8(v_a_1954_, sizeof(void*)*3);
v_wantsRebuild_1975_ = lean_ctor_get_uint8(v_a_1954_, sizeof(void*)*3 + 1);
v_canceled_1976_ = lean_ctor_get_uint8(v_a_1954_, sizeof(void*)*3 + 2);
v_trace_1977_ = lean_ctor_get(v_a_1954_, 1);
v_buildTime_1978_ = lean_ctor_get(v_a_1954_, 2);
v_isSharedCheck_2068_ = !lean_is_exclusive(v_a_1954_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_1980_ = v_a_1954_;
v_isShared_1981_ = v_isSharedCheck_2068_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_buildTime_1978_);
lean_inc(v_trace_1977_);
lean_inc(v_log_1973_);
lean_dec(v_a_1954_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_2068_;
goto v_resetjp_1979_;
}
v___jp_1956_:
{
lean_object* v___x_1959_; 
v___x_1959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1959_, 0, v_a_1957_);
lean_ctor_set(v___x_1959_, 1, v_a_1958_);
return v___x_1959_;
}
v___jp_1960_:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1967_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__1));
v___x_1968_ = lean_array_get_size(v_log_1961_);
v___x_1969_ = lean_array_push(v_log_1961_, v___x_1967_);
v___x_1970_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
lean_ctor_set(v___x_1970_, 1, v_trace_1965_);
lean_ctor_set(v___x_1970_, 2, v_buildTime_1966_);
lean_ctor_set_uint8(v___x_1970_, sizeof(void*)*3, v_action_1962_);
lean_ctor_set_uint8(v___x_1970_, sizeof(void*)*3 + 1, v_wantsRebuild_1963_);
lean_ctor_set_uint8(v___x_1970_, sizeof(void*)*3 + 2, v_canceled_1964_);
v___x_1971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1968_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
return v___x_1971_;
}
v_resetjp_1979_:
{
uint8_t v_noBuild_1982_; uint8_t v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v_noBuild_1982_ = lean_ctor_get_uint8(v_toBuildConfig_1972_, sizeof(void*)*5 + 2);
v___x_1983_ = l_Lake_JobAction_merge(v_action_1974_, v_action_1952_);
v___x_1984_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__2));
lean_inc_ref(v_traceFile_1951_);
v___x_1985_ = l_System_FilePath_addExtension(v_traceFile_1951_, v___x_1984_);
if (v_noBuild_1982_ == 0)
{
lean_object* v___x_1986_; lean_object* v_a_1988_; lean_object* v_a_1989_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1986_ = lean_io_mono_ms_now();
v___x_1993_ = lean_array_get_size(v_log_1973_);
v___x_1994_ = l_Lake_download(v_url_1947_, v_archiveFile_1948_, v_headers_1949_, v_log_1973_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v_a_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_a_1995_);
v_a_1996_ = lean_ctor_get(v___x_1994_, 1);
lean_inc(v_a_1996_);
lean_dec_ref_known(v___x_1994_, 2);
v___x_1997_ = lean_array_get_size(v_a_1996_);
v___x_1998_ = l_Array_extract___redArg(v_a_1996_, v___x_1993_, v___x_1997_);
v___x_1999_ = lean_box(0);
v___x_2000_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1950_, v___x_1999_, v___x_1998_);
v___x_2001_ = l_Lake_BuildMetadata_writeFile(v_traceFile_1951_, v___x_2000_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2038_; 
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2038_ == 0)
{
lean_object* v_unused_2039_; 
v_unused_2039_ = lean_ctor_get(v___x_2001_, 0);
lean_dec(v_unused_2039_);
v___x_2003_ = v___x_2001_;
v_isShared_2004_ = v_isSharedCheck_2038_;
goto v_resetjp_2002_;
}
else
{
lean_dec(v___x_2001_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2038_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; 
v___x_2005_ = l_Lake_removeFileIfExists(v___x_1985_);
lean_dec_ref(v___x_1985_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2028_; 
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2028_ == 0)
{
lean_object* v_unused_2029_; 
v_unused_2029_ = lean_ctor_get(v___x_2005_, 0);
lean_dec(v_unused_2029_);
v___x_2007_ = v___x_2005_;
v_isShared_2008_ = v_isSharedCheck_2028_;
goto v_resetjp_2006_;
}
else
{
lean_dec(v___x_2005_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2028_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v_a_1996_);
v___x_2010_ = v___x_1980_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_1996_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_trace_1977_);
lean_ctor_set(v_reuseFailAlloc_2027_, 2, v_buildTime_1978_);
lean_ctor_set_uint8(v_reuseFailAlloc_2027_, sizeof(void*)*3 + 1, v_wantsRebuild_1975_);
lean_ctor_set_uint8(v_reuseFailAlloc_2027_, sizeof(void*)*3 + 2, v_canceled_1976_);
v___x_2010_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2012_; 
lean_ctor_set_uint8(v___x_2010_, sizeof(void*)*3, v___x_1983_);
lean_inc(v_a_1995_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v_a_1995_);
v___x_2012_ = v___x_2007_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_1995_);
v___x_2012_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2014_; 
if (v_isShared_2004_ == 0)
{
lean_ctor_set_tag(v___x_2003_, 1);
lean_ctor_set(v___x_2003_, 0, v___x_2012_);
v___x_2014_ = v___x_2003_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2012_);
v___x_2014_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2015_; lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
v___x_2015_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_1986_, v___x_2014_, v___x_2010_);
lean_dec_ref(v___x_2014_);
lean_dec(v___x_1986_);
v_a_2016_ = lean_ctor_get(v___x_2015_, 1);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2023_ == 0)
{
lean_object* v_unused_2024_; 
v_unused_2024_ = lean_ctor_get(v___x_2015_, 0);
lean_dec(v_unused_2024_);
v___x_2018_ = v___x_2015_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v_a_1995_);
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_1995_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2031_; uint8_t v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2036_; 
lean_del_object(v___x_2003_);
lean_dec(v_a_1995_);
v_a_2030_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___x_2005_, 1);
v___x_2031_ = lean_io_error_to_string(v_a_2030_);
v___x_2032_ = 3;
v___x_2033_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2033_, 0, v___x_2031_);
lean_ctor_set_uint8(v___x_2033_, sizeof(void*)*1, v___x_2032_);
v___x_2034_ = lean_array_push(v_a_1996_, v___x_2033_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_2034_);
v___x_2036_ = v___x_1980_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v_trace_1977_);
lean_ctor_set(v_reuseFailAlloc_2037_, 2, v_buildTime_1978_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*3 + 1, v_wantsRebuild_1975_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*3 + 2, v_canceled_1976_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*3, v___x_1983_);
v_a_1988_ = v___x_1997_;
v_a_1989_ = v___x_2036_;
goto v___jp_1987_;
}
}
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2046_; 
lean_dec(v_a_1995_);
lean_dec_ref(v___x_1985_);
v_a_2040_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2001_, 1);
v___x_2041_ = lean_io_error_to_string(v_a_2040_);
v___x_2042_ = 3;
v___x_2043_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2043_, 0, v___x_2041_);
lean_ctor_set_uint8(v___x_2043_, sizeof(void*)*1, v___x_2042_);
v___x_2044_ = lean_array_push(v_a_1996_, v___x_2043_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_2044_);
v___x_2046_ = v___x_1980_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2044_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v_trace_1977_);
lean_ctor_set(v_reuseFailAlloc_2047_, 2, v_buildTime_1978_);
lean_ctor_set_uint8(v_reuseFailAlloc_2047_, sizeof(void*)*3 + 1, v_wantsRebuild_1975_);
lean_ctor_set_uint8(v_reuseFailAlloc_2047_, sizeof(void*)*3 + 2, v_canceled_1976_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
lean_ctor_set_uint8(v___x_2046_, sizeof(void*)*3, v___x_1983_);
v_a_1988_ = v___x_1997_;
v_a_1989_ = v___x_2046_;
goto v___jp_1987_;
}
}
}
else
{
lean_object* v_a_2048_; lean_object* v_a_2049_; lean_object* v___x_2051_; 
lean_dec_ref(v___x_1985_);
lean_dec_ref(v_traceFile_1951_);
v_a_2048_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_a_2048_);
v_a_2049_ = lean_ctor_get(v___x_1994_, 1);
lean_inc(v_a_2049_);
lean_dec_ref_known(v___x_1994_, 2);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v_a_2049_);
v___x_2051_ = v___x_1980_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2049_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_trace_1977_);
lean_ctor_set(v_reuseFailAlloc_2052_, 2, v_buildTime_1978_);
lean_ctor_set_uint8(v_reuseFailAlloc_2052_, sizeof(void*)*3 + 1, v_wantsRebuild_1975_);
lean_ctor_set_uint8(v_reuseFailAlloc_2052_, sizeof(void*)*3 + 2, v_canceled_1976_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*3, v___x_1983_);
v_a_1988_ = v_a_2048_;
v_a_1989_ = v___x_2051_;
goto v___jp_1987_;
}
}
v___jp_1987_:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v_a_1992_; 
v___x_1990_ = lean_box(0);
v___x_1991_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_1986_, v___x_1990_, v_a_1989_);
lean_dec(v___x_1986_);
v_a_1992_ = lean_ctor_get(v___x_1991_, 1);
lean_inc(v_a_1992_);
lean_dec_ref(v___x_1991_);
v_a_1957_ = v_a_1988_;
v_a_1958_ = v_a_1992_;
goto v___jp_1956_;
}
}
else
{
uint8_t v___x_2053_; 
lean_dec_ref(v_archiveFile_1948_);
lean_dec_ref(v_url_1947_);
v___x_2053_ = l_System_FilePath_pathExists(v_traceFile_1951_);
lean_dec_ref(v_traceFile_1951_);
if (v___x_2053_ == 0)
{
lean_dec_ref(v___x_1985_);
lean_del_object(v___x_1980_);
v_log_1961_ = v_log_1973_;
v_action_1962_ = v___x_1983_;
v_wantsRebuild_1963_ = v_noBuild_1982_;
v_canceled_1964_ = v_canceled_1976_;
v_trace_1965_ = v_trace_1977_;
v_buildTime_1966_ = v_buildTime_1978_;
goto v___jp_1960_;
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2054_ = lean_box(0);
v___x_2055_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_2056_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1950_, v___x_2054_, v___x_2055_);
v___x_2057_ = l_Lake_BuildMetadata_writeFile(v___x_1985_, v___x_2056_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_dec_ref_known(v___x_2057_, 1);
lean_del_object(v___x_1980_);
v_log_1961_ = v_log_1973_;
v_action_1962_ = v___x_1983_;
v_wantsRebuild_1963_ = v_noBuild_1982_;
v_canceled_1964_ = v_canceled_1976_;
v_trace_1965_ = v_trace_1977_;
v_buildTime_1966_ = v_buildTime_1978_;
goto v___jp_1960_;
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2065_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2058_);
lean_dec_ref_known(v___x_2057_, 1);
v___x_2059_ = lean_io_error_to_string(v_a_2058_);
v___x_2060_ = 3;
v___x_2061_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2061_, 0, v___x_2059_);
lean_ctor_set_uint8(v___x_2061_, sizeof(void*)*1, v___x_2060_);
v___x_2062_ = lean_array_get_size(v_log_1973_);
v___x_2063_ = lean_array_push(v_log_1973_, v___x_2061_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_2063_);
v___x_2065_ = v___x_1980_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_trace_1977_);
lean_ctor_set(v_reuseFailAlloc_2067_, 2, v_buildTime_1978_);
lean_ctor_set_uint8(v_reuseFailAlloc_2067_, sizeof(void*)*3 + 2, v_canceled_1976_);
v___x_2065_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v___x_2066_; 
lean_ctor_set_uint8(v___x_2065_, sizeof(void*)*3, v___x_1983_);
lean_ctor_set_uint8(v___x_2065_, sizeof(void*)*3 + 1, v_noBuild_1982_);
v___x_2066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2062_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
return v___x_2066_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_url_1947_ = stack[0].m_obj;
lean_object* v_archiveFile_1948_ = stack[1].m_obj;
lean_object* v_headers_1949_ = stack[2].m_obj;
lean_object* v_depTrace_1950_ = stack[3].m_obj;
lean_object* v_traceFile_1951_ = stack[4].m_obj;
uint8_t v_action_1952_ = stack[5].m_num;
lean_object* v_a_1953_ = stack[6].m_obj;
lean_object* v_a_1954_ = stack[7].m_obj;
lean_object* v_res_2069_;
v_res_2069_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_1947_, v_archiveFile_1948_, v_headers_1949_, v_depTrace_1950_, v_traceFile_1951_, v_action_1952_, v_a_1953_, v_a_1954_);
stack->m_obj
 = v_res_2069_;
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___boxed(lean_object* v_url_2070_, lean_object* v_archiveFile_2071_, lean_object* v_headers_2072_, lean_object* v_depTrace_2073_, lean_object* v_traceFile_2074_, lean_object* v_action_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_){
_start:
{
uint8_t v_action_boxed_2079_; lean_object* v_res_2080_; 
v_action_boxed_2079_ = lean_unbox(v_action_2075_);
v_res_2080_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_2070_, v_archiveFile_2071_, v_headers_2072_, v_depTrace_2073_, v_traceFile_2074_, v_action_boxed_2079_, v_a_2076_, v_a_2077_);
lean_dec_ref(v_a_2076_);
lean_dec_ref(v_depTrace_2073_);
lean_dec_ref(v_headers_2072_);
return v_res_2080_;
}
}
lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(lean_object* v_url_2081_, lean_object* v_archiveFile_2082_, lean_object* v_headers_2083_, lean_object* v_a_2084_, lean_object* v_depTrace_2085_, lean_object* v_traceFile_2086_, uint8_t v_action_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_2081_, v_archiveFile_2082_, v_headers_2083_, v_depTrace_2085_, v_traceFile_2086_, v_action_2087_, v_a_2091_, v_a_2092_);
return v___x_2094_;
}
}
LEAN_EXPORT void l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_url_2081_ = stack[0].m_obj;
lean_object* v_archiveFile_2082_ = stack[1].m_obj;
lean_object* v_headers_2083_ = stack[2].m_obj;
lean_object* v_a_2084_ = stack[3].m_obj;
lean_object* v_depTrace_2085_ = stack[4].m_obj;
lean_object* v_traceFile_2086_ = stack[5].m_obj;
uint8_t v_action_2087_ = stack[6].m_num;
lean_object* v_a_2088_ = stack[7].m_obj;
lean_object* v_a_2089_ = stack[8].m_obj;
lean_object* v_a_2090_ = stack[9].m_obj;
lean_object* v_a_2091_ = stack[10].m_obj;
lean_object* v_a_2092_ = stack[11].m_obj;
lean_object* v_res_2095_;
v_res_2095_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(v_url_2081_, v_archiveFile_2082_, v_headers_2083_, v_a_2084_, v_depTrace_2085_, v_traceFile_2086_, v_action_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_);
stack->m_obj
 = v_res_2095_;
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___boxed(lean_object* v_url_2096_, lean_object* v_archiveFile_2097_, lean_object* v_headers_2098_, lean_object* v_a_2099_, lean_object* v_depTrace_2100_, lean_object* v_traceFile_2101_, lean_object* v_action_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_){
_start:
{
uint8_t v_action_boxed_2109_; lean_object* v_res_2110_; 
v_action_boxed_2109_ = lean_unbox(v_action_2102_);
v_res_2110_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(v_url_2096_, v_archiveFile_2097_, v_headers_2098_, v_a_2099_, v_depTrace_2100_, v_traceFile_2101_, v_action_boxed_2109_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_);
lean_dec_ref(v_a_2106_);
lean_dec(v_a_2105_);
lean_dec(v_a_2104_);
lean_dec(v_a_2103_);
lean_dec_ref(v_depTrace_2100_);
lean_dec_ref(v_a_2099_);
lean_dec_ref(v_headers_2098_);
return v_res_2110_;
}
}
uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(lean_object* v_info_2111_, lean_object* v_self_2112_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = lean_io_metadata(v_info_2111_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v_modified_2116_; uint8_t v___x_2117_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2114_, 1);
v_modified_2116_ = lean_ctor_get(v_a_2115_, 1);
lean_inc_ref(v_modified_2116_);
lean_dec(v_a_2115_);
v___x_2117_ = l_IO_FS_instOrdSystemTime_ord(v_self_2112_, v_modified_2116_);
lean_dec_ref(v_modified_2116_);
if (v___x_2117_ == 0)
{
uint8_t v___x_2118_; 
v___x_2118_ = 1;
return v___x_2118_;
}
else
{
uint8_t v___x_2119_; 
v___x_2119_ = 0;
return v___x_2119_;
}
}
else
{
uint8_t v___x_2120_; 
lean_dec_ref_known(v___x_2114_, 1);
v___x_2120_ = 0;
return v___x_2120_;
}
}
}
LEAN_EXPORT void l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_2111_ = stack[0].m_obj;
lean_object* v_self_2112_ = stack[1].m_obj;
uint8_t v_res_2121_;
v_res_2121_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_2111_, v_self_2112_);
stack->m_num = v_res_2121_;
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___boxed(lean_object* v_info_2122_, lean_object* v_self_2123_, lean_object* v_a_2124_){
_start:
{
uint8_t v_res_2125_; lean_object* v_r_2126_; 
v_res_2125_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_2122_, v_self_2123_);
lean_dec_ref(v_self_2123_);
lean_dec_ref(v_info_2122_);
v_r_2126_ = lean_box(v_res_2125_);
return v_r_2126_;
}
}
uint8_t l_instBEqOption_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(lean_object* v_x_2127_, lean_object* v_x_2128_){
_start:
{
if (lean_obj_tag(v_x_2127_) == 0)
{
if (lean_obj_tag(v_x_2128_) == 0)
{
uint8_t v___x_2129_; 
v___x_2129_ = 1;
return v___x_2129_;
}
else
{
uint8_t v___x_2130_; 
v___x_2130_ = 0;
return v___x_2130_;
}
}
else
{
if (lean_obj_tag(v_x_2128_) == 0)
{
uint8_t v___x_2131_; 
v___x_2131_ = 0;
return v___x_2131_;
}
else
{
lean_object* v_val_2132_; lean_object* v_val_2133_; uint64_t v___x_2134_; uint64_t v___x_2135_; uint8_t v___x_2136_; 
v_val_2132_ = lean_ctor_get(v_x_2127_, 0);
v_val_2133_ = lean_ctor_get(v_x_2128_, 0);
v___x_2134_ = lean_unbox_uint64(v_val_2132_);
v___x_2135_ = lean_unbox_uint64(v_val_2133_);
v___x_2136_ = lean_uint64_dec_eq(v___x_2134_, v___x_2135_);
return v___x_2136_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2127_ = stack[0].m_obj;
lean_object* v_x_2128_ = stack[1].m_obj;
uint8_t v_res_2137_;
v_res_2137_ = l_instBEqOption_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v_x_2127_, v_x_2128_);
stack->m_num = v_res_2137_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2138_, lean_object* v_x_2139_){
_start:
{
uint8_t v_res_2140_; lean_object* v_r_2141_; 
v_res_2140_ = l_instBEqOption_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v_x_2138_, v_x_2139_);
lean_dec(v_x_2139_);
lean_dec(v_x_2138_);
v_r_2141_ = lean_box(v_res_2140_);
return v_r_2141_;
}
}
lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(lean_object* v_info_2142_, lean_object* v_depTrace_2143_, lean_object* v_depHash_2144_, lean_object* v_oldTrace_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_){
_start:
{
uint64_t v_hash_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; uint8_t v___x_2152_; 
v_hash_2149_ = lean_ctor_get_uint64(v_depTrace_2143_, sizeof(void*)*3);
v___x_2150_ = lean_box_uint64(v_hash_2149_);
v___x_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
v___x_2152_ = l_instBEqOption_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v___x_2151_, v_depHash_2144_);
lean_dec_ref_known(v___x_2151_, 1);
if (v___x_2152_ == 0)
{
lean_object* v_toBuildConfig_2153_; uint8_t v_oldMode_2154_; 
v_toBuildConfig_2153_ = lean_ctor_get(v_a_2146_, 0);
v_oldMode_2154_ = lean_ctor_get_uint8(v_toBuildConfig_2153_, sizeof(void*)*5);
if (v_oldMode_2154_ == 0)
{
uint8_t v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2155_ = 0;
v___x_2156_ = lean_box(v___x_2155_);
v___x_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
lean_ctor_set(v___x_2157_, 1, v_a_2147_);
return v___x_2157_;
}
else
{
uint8_t v___x_2158_; 
v___x_2158_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_2142_, v_oldTrace_2145_);
if (v___x_2158_ == 0)
{
uint8_t v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2159_ = 0;
v___x_2160_ = lean_box(v___x_2159_);
v___x_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
lean_ctor_set(v___x_2161_, 1, v_a_2147_);
return v___x_2161_;
}
else
{
uint8_t v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2162_ = 1;
v___x_2163_ = lean_box(v___x_2162_);
v___x_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2163_);
lean_ctor_set(v___x_2164_, 1, v_a_2147_);
return v___x_2164_;
}
}
}
else
{
uint8_t v___x_2165_; 
v___x_2165_ = l_System_FilePath_pathExists(v_info_2142_);
if (v___x_2165_ == 0)
{
uint8_t v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2166_ = 0;
v___x_2167_ = lean_box(v___x_2166_);
v___x_2168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
lean_ctor_set(v___x_2168_, 1, v_a_2147_);
return v___x_2168_;
}
else
{
uint8_t v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2169_ = 2;
v___x_2170_ = lean_box(v___x_2169_);
v___x_2171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
lean_ctor_set(v___x_2171_, 1, v_a_2147_);
return v___x_2171_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_2142_ = stack[0].m_obj;
lean_object* v_depTrace_2143_ = stack[1].m_obj;
lean_object* v_depHash_2144_ = stack[2].m_obj;
lean_object* v_oldTrace_2145_ = stack[3].m_obj;
lean_object* v_a_2146_ = stack[4].m_obj;
lean_object* v_a_2147_ = stack[5].m_obj;
lean_object* v_res_2172_;
v_res_2172_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_2142_, v_depTrace_2143_, v_depHash_2144_, v_oldTrace_2145_, v_a_2146_, v_a_2147_);
stack->m_obj
 = v_res_2172_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg___boxed(lean_object* v_info_2173_, lean_object* v_depTrace_2174_, lean_object* v_depHash_2175_, lean_object* v_oldTrace_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_2173_, v_depTrace_2174_, v_depHash_2175_, v_oldTrace_2176_, v_a_2177_, v_a_2178_);
lean_dec_ref(v_a_2177_);
lean_dec_ref(v_oldTrace_2176_);
lean_dec(v_depHash_2175_);
lean_dec_ref(v_depTrace_2174_);
lean_dec_ref(v_info_2173_);
return v_res_2180_;
}
}
lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(lean_object* v_a_2181_, lean_object* v_info_2182_, lean_object* v_depTrace_2183_, lean_object* v_savedTrace_2184_, lean_object* v_oldTrace_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_){
_start:
{
if (lean_obj_tag(v_savedTrace_2184_) == 2)
{
lean_object* v_data_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2243_; 
v_data_2192_ = lean_ctor_get(v_savedTrace_2184_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v_savedTrace_2184_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2194_ = v_savedTrace_2184_;
v_isShared_2195_ = v_isSharedCheck_2243_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_data_2192_);
lean_dec(v_savedTrace_2184_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2243_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
uint64_t v_depHash_2196_; lean_object* v_log_2197_; lean_object* v___x_2198_; lean_object* v___x_2200_; 
v_depHash_2196_ = lean_ctor_get_uint64(v_data_2192_, sizeof(void*)*3);
v_log_2197_ = lean_ctor_get(v_data_2192_, 2);
lean_inc_ref(v_log_2197_);
lean_dec_ref(v_data_2192_);
v___x_2198_ = lean_box_uint64(v_depHash_2196_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set_tag(v___x_2194_, 1);
lean_ctor_set(v___x_2194_, 0, v___x_2198_);
v___x_2200_ = v___x_2194_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
lean_object* v___x_2201_; lean_object* v_a_2202_; lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2241_; 
v___x_2201_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_2182_, v_depTrace_2183_, v___x_2200_, v_oldTrace_2185_, v_a_2189_, v_a_2190_);
lean_dec_ref(v___x_2200_);
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
v_a_2203_ = lean_ctor_get(v___x_2201_, 1);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2205_ = v___x_2201_;
v_isShared_2206_ = v_isSharedCheck_2241_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_inc(v_a_2202_);
lean_dec(v___x_2201_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2241_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___y_2208_; lean_object* v___x_2212_; lean_object* v___x_2213_; uint8_t v___x_2214_; 
v___x_2212_ = lean_obj_tag_nat(v_a_2202_);
v___x_2213_ = lean_unsigned_to_nat(0u);
v___x_2214_ = lean_nat_dec_eq(v___x_2212_, v___x_2213_);
if (v___x_2214_ == 0)
{
lean_object* v_log_2215_; uint8_t v_action_2216_; uint8_t v_wantsRebuild_2217_; uint8_t v_canceled_2218_; lean_object* v_trace_2219_; lean_object* v_buildTime_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2240_; 
v_log_2215_ = lean_ctor_get(v_a_2203_, 0);
v_action_2216_ = lean_ctor_get_uint8(v_a_2203_, sizeof(void*)*3);
v_wantsRebuild_2217_ = lean_ctor_get_uint8(v_a_2203_, sizeof(void*)*3 + 1);
v_canceled_2218_ = lean_ctor_get_uint8(v_a_2203_, sizeof(void*)*3 + 2);
v_trace_2219_ = lean_ctor_get(v_a_2203_, 1);
v_buildTime_2220_ = lean_ctor_get(v_a_2203_, 2);
v_isSharedCheck_2240_ = !lean_is_exclusive(v_a_2203_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2222_ = v_a_2203_;
v_isShared_2223_ = v_isSharedCheck_2240_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_buildTime_2220_);
lean_inc(v_trace_2219_);
lean_inc(v_log_2215_);
lean_dec(v_a_2203_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2240_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
uint8_t v___x_2224_; uint8_t v___x_2225_; lean_object* v___x_2227_; 
v___x_2224_ = 2;
v___x_2225_ = l_Lake_JobAction_merge(v_action_2216_, v___x_2224_);
if (v_isShared_2223_ == 0)
{
v___x_2227_ = v___x_2222_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_log_2215_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v_trace_2219_);
lean_ctor_set(v_reuseFailAlloc_2239_, 2, v_buildTime_2220_);
lean_ctor_set_uint8(v_reuseFailAlloc_2239_, sizeof(void*)*3 + 1, v_wantsRebuild_2217_);
lean_ctor_set_uint8(v_reuseFailAlloc_2239_, sizeof(void*)*3 + 2, v_canceled_2218_);
v___x_2227_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
lean_object* v___x_2228_; 
lean_ctor_set_uint8(v___x_2227_, sizeof(void*)*3, v___x_2225_);
v___x_2228_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_2197_, v_a_2181_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v___x_2227_);
lean_dec_ref(v_log_2197_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 1);
lean_inc(v_a_2229_);
lean_dec_ref_known(v___x_2228_, 2);
v___y_2208_ = v_a_2229_;
goto v___jp_2207_;
}
else
{
lean_object* v_a_2230_; lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_del_object(v___x_2205_);
lean_dec(v_a_2202_);
v_a_2230_ = lean_ctor_get(v___x_2228_, 0);
v_a_2231_ = lean_ctor_get(v___x_2228_, 1);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2228_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_inc(v_a_2230_);
lean_dec(v___x_2228_);
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
}
else
{
lean_dec_ref(v_log_2197_);
v___y_2208_ = v_a_2203_;
goto v___jp_2207_;
}
v___jp_2207_:
{
lean_object* v___x_2210_; 
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 1, v___y_2208_);
v___x_2210_ = v___x_2205_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2202_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v___y_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
}
}
else
{
lean_object* v_toBuildConfig_2244_; uint8_t v_oldMode_2245_; 
lean_dec(v_savedTrace_2184_);
v_toBuildConfig_2244_ = lean_ctor_get(v_a_2189_, 0);
v_oldMode_2245_ = lean_ctor_get_uint8(v_toBuildConfig_2244_, sizeof(void*)*5);
if (v_oldMode_2245_ == 0)
{
uint8_t v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2246_ = 0;
v___x_2247_ = lean_box(v___x_2246_);
v___x_2248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
lean_ctor_set(v___x_2248_, 1, v_a_2190_);
return v___x_2248_;
}
else
{
uint8_t v___x_2249_; 
v___x_2249_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_2182_, v_oldTrace_2185_);
if (v___x_2249_ == 0)
{
uint8_t v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2250_ = 0;
v___x_2251_ = lean_box(v___x_2250_);
v___x_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
lean_ctor_set(v___x_2252_, 1, v_a_2190_);
return v___x_2252_;
}
else
{
uint8_t v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2253_ = 1;
v___x_2254_ = lean_box(v___x_2253_);
v___x_2255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
lean_ctor_set(v___x_2255_, 1, v_a_2190_);
return v___x_2255_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2181_ = stack[0].m_obj;
lean_object* v_info_2182_ = stack[1].m_obj;
lean_object* v_depTrace_2183_ = stack[2].m_obj;
lean_object* v_savedTrace_2184_ = stack[3].m_obj;
lean_object* v_oldTrace_2185_ = stack[4].m_obj;
lean_object* v_a_2186_ = stack[5].m_obj;
lean_object* v_a_2187_ = stack[6].m_obj;
lean_object* v_a_2188_ = stack[7].m_obj;
lean_object* v_a_2189_ = stack[8].m_obj;
lean_object* v_a_2190_ = stack[9].m_obj;
lean_object* v_res_2256_;
v_res_2256_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_2181_, v_info_2182_, v_depTrace_2183_, v_savedTrace_2184_, v_oldTrace_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
stack->m_obj
 = v_res_2256_;
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___boxed(lean_object* v_a_2257_, lean_object* v_info_2258_, lean_object* v_depTrace_2259_, lean_object* v_savedTrace_2260_, lean_object* v_oldTrace_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_2257_, v_info_2258_, v_depTrace_2259_, v_savedTrace_2260_, v_oldTrace_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
lean_dec_ref(v_a_2265_);
lean_dec(v_a_2264_);
lean_dec(v_a_2263_);
lean_dec(v_a_2262_);
lean_dec_ref(v_oldTrace_2261_);
lean_dec_ref(v_depTrace_2259_);
lean_dec_ref(v_info_2258_);
lean_dec_ref(v_a_2257_);
return v_res_2268_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3(void){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = lean_unsigned_to_nat(0u);
v___x_2274_ = lean_nat_to_int(v___x_2273_);
return v___x_2274_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4(void){
_start:
{
uint32_t v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2275_ = 0;
v___x_2276_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3);
v___x_2277_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
lean_ctor_set_uint32(v___x_2277_, sizeof(void*)*1, v___x_2275_);
return v___x_2277_;
}
}
lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(lean_object* v_self_2278_, lean_object* v_url_2279_, lean_object* v_archiveFile_2280_, lean_object* v_headers_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
uint8_t v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; uint8_t v___y_2294_; uint8_t v___y_2295_; lean_object* v___y_2296_; uint8_t v_a_2322_; lean_object* v_a_2323_; lean_object* v_a_2339_; lean_object* v_a_2340_; lean_object* v_log_2342_; uint8_t v_action_2343_; uint8_t v_wantsRebuild_2344_; uint8_t v_canceled_2345_; lean_object* v_trace_2346_; lean_object* v_buildTime_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2386_; 
v_log_2342_ = lean_ctor_get(v_a_2287_, 0);
v_action_2343_ = lean_ctor_get_uint8(v_a_2287_, sizeof(void*)*3);
v_wantsRebuild_2344_ = lean_ctor_get_uint8(v_a_2287_, sizeof(void*)*3 + 1);
v_canceled_2345_ = lean_ctor_get_uint8(v_a_2287_, sizeof(void*)*3 + 2);
v_trace_2346_ = lean_ctor_get(v_a_2287_, 1);
v_buildTime_2347_ = lean_ctor_get(v_a_2287_, 2);
v_isSharedCheck_2386_ = !lean_is_exclusive(v_a_2287_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2349_ = v_a_2287_;
v_isShared_2350_ = v_isSharedCheck_2386_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_buildTime_2347_);
lean_inc(v_trace_2346_);
lean_inc(v_log_2342_);
lean_dec(v_a_2287_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2386_;
goto v_resetjp_2348_;
}
v___jp_2289_:
{
uint8_t v___x_2297_; uint8_t v___x_2298_; uint8_t v___x_2299_; lean_object* v___x_2300_; 
v___x_2297_ = 1;
v___x_2298_ = 3;
v___x_2299_ = l_Lake_JobAction_merge(v___y_2290_, v___x_2298_);
v___x_2300_ = l_Lake_untar(v_archiveFile_2280_, v___y_2291_, v___x_2297_, v___y_2293_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2310_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
v_a_2302_ = lean_ctor_get(v___x_2300_, 1);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2304_ = v___x_2300_;
v_isShared_2305_ = v_isSharedCheck_2310_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_inc(v_a_2301_);
lean_dec(v___x_2300_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2310_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2306_; lean_object* v___x_2308_; 
v___x_2306_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2306_, 0, v_a_2302_);
lean_ctor_set(v___x_2306_, 1, v___y_2296_);
lean_ctor_set(v___x_2306_, 2, v___y_2292_);
lean_ctor_set_uint8(v___x_2306_, sizeof(void*)*3, v___x_2299_);
lean_ctor_set_uint8(v___x_2306_, sizeof(void*)*3 + 1, v___y_2295_);
lean_ctor_set_uint8(v___x_2306_, sizeof(void*)*3 + 2, v___y_2294_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 1, v___x_2306_);
v___x_2308_ = v___x_2304_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2301_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v___x_2306_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
else
{
lean_object* v_a_2311_; lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2320_; 
v_a_2311_ = lean_ctor_get(v___x_2300_, 0);
v_a_2312_ = lean_ctor_get(v___x_2300_, 1);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2314_ = v___x_2300_;
v_isShared_2315_ = v_isSharedCheck_2320_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_inc(v_a_2311_);
lean_dec(v___x_2300_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2320_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2316_; lean_object* v___x_2318_; 
v___x_2316_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2316_, 0, v_a_2312_);
lean_ctor_set(v___x_2316_, 1, v___y_2296_);
lean_ctor_set(v___x_2316_, 2, v___y_2292_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*3, v___x_2299_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*3 + 1, v___y_2295_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*3 + 2, v___y_2294_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 1, v___x_2316_);
v___x_2318_ = v___x_2314_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2311_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v___x_2316_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
v___jp_2321_:
{
lean_object* v_config_2324_; lean_object* v_dir_2325_; lean_object* v_buildDir_2326_; lean_object* v_log_2327_; uint8_t v_action_2328_; uint8_t v_wantsRebuild_2329_; uint8_t v_canceled_2330_; lean_object* v_trace_2331_; lean_object* v_buildTime_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; uint8_t v___x_2335_; 
v_config_2324_ = lean_ctor_get(v_self_2278_, 6);
lean_inc_ref(v_config_2324_);
v_dir_2325_ = lean_ctor_get(v_self_2278_, 4);
lean_inc_ref(v_dir_2325_);
lean_dec_ref(v_self_2278_);
v_buildDir_2326_ = lean_ctor_get(v_config_2324_, 5);
lean_inc_ref(v_buildDir_2326_);
lean_dec_ref(v_config_2324_);
v_log_2327_ = lean_ctor_get(v_a_2323_, 0);
v_action_2328_ = lean_ctor_get_uint8(v_a_2323_, sizeof(void*)*3);
v_wantsRebuild_2329_ = lean_ctor_get_uint8(v_a_2323_, sizeof(void*)*3 + 1);
v_canceled_2330_ = lean_ctor_get_uint8(v_a_2323_, sizeof(void*)*3 + 2);
v_trace_2331_ = lean_ctor_get(v_a_2323_, 1);
v_buildTime_2332_ = lean_ctor_get(v_a_2323_, 2);
v___x_2333_ = l_System_FilePath_normalize(v_buildDir_2326_);
v___x_2334_ = l_Lake_joinRelative(v_dir_2325_, v___x_2333_);
v___x_2335_ = l_System_FilePath_pathExists(v___x_2334_);
if (v_a_2322_ == 0)
{
lean_inc(v_buildTime_2332_);
lean_inc_ref(v_trace_2331_);
lean_inc_ref(v_log_2327_);
lean_dec_ref(v_a_2323_);
v___y_2290_ = v_action_2328_;
v___y_2291_ = v___x_2334_;
v___y_2292_ = v_buildTime_2332_;
v___y_2293_ = v_log_2327_;
v___y_2294_ = v_canceled_2330_;
v___y_2295_ = v_wantsRebuild_2329_;
v___y_2296_ = v_trace_2331_;
goto v___jp_2289_;
}
else
{
if (v___x_2335_ == 0)
{
lean_inc(v_buildTime_2332_);
lean_inc_ref(v_trace_2331_);
lean_inc_ref(v_log_2327_);
lean_dec_ref(v_a_2323_);
v___y_2290_ = v_action_2328_;
v___y_2291_ = v___x_2334_;
v___y_2292_ = v_buildTime_2332_;
v___y_2293_ = v_log_2327_;
v___y_2294_ = v_canceled_2330_;
v___y_2295_ = v_wantsRebuild_2329_;
v___y_2296_ = v_trace_2331_;
goto v___jp_2289_;
}
else
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_dec_ref(v___x_2334_);
lean_dec_ref(v_archiveFile_2280_);
v___x_2336_ = lean_box(0);
v___x_2337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
lean_ctor_set(v___x_2337_, 1, v_a_2323_);
return v___x_2337_;
}
}
}
v___jp_2338_:
{
lean_object* v___x_2341_; 
v___x_2341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2341_, 0, v_a_2339_);
lean_ctor_set(v___x_2341_, 1, v_a_2340_);
return v___x_2341_;
}
v_resetjp_2348_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; uint64_t v___x_2353_; uint64_t v___x_2354_; uint64_t v_depTrace_2355_; lean_object* v___x_2356_; lean_object* v_traceFile_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; uint8_t v___x_2361_; lean_object* v___x_2362_; 
v___x_2351_ = lean_unsigned_to_nat(0u);
v___x_2352_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0));
v___x_2353_ = l_Lake_Hash_nil;
v___x_2354_ = lean_string_hash(v_url_2279_);
v_depTrace_2355_ = lean_uint64_mix_hash(v___x_2353_, v___x_2354_);
v___x_2356_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1));
lean_inc_ref(v_archiveFile_2280_);
v_traceFile_2357_ = l_System_FilePath_addExtension(v_archiveFile_2280_, v___x_2356_);
v___x_2358_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2));
v___x_2359_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4, &l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4_once, _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4);
v___x_2360_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_2360_, 0, v___x_2358_);
lean_ctor_set(v___x_2360_, 1, v___x_2352_);
lean_ctor_set(v___x_2360_, 2, v___x_2359_);
lean_ctor_set_uint64(v___x_2360_, sizeof(void*)*3, v_depTrace_2355_);
v___x_2361_ = 4;
lean_inc_ref(v_traceFile_2357_);
v___x_2362_ = l_Lake_readTraceFile(v_traceFile_2357_, v_log_2342_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v_a_2364_; lean_object* v___x_2366_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2363_);
v_a_2364_ = lean_ctor_get(v___x_2362_, 1);
lean_inc(v_a_2364_);
lean_dec_ref_known(v___x_2362_, 2);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 0, v_a_2364_);
v___x_2366_ = v___x_2349_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2364_);
lean_ctor_set(v_reuseFailAlloc_2380_, 1, v_trace_2346_);
lean_ctor_set(v_reuseFailAlloc_2380_, 2, v_buildTime_2347_);
lean_ctor_set_uint8(v_reuseFailAlloc_2380_, sizeof(void*)*3, v_action_2343_);
lean_ctor_set_uint8(v_reuseFailAlloc_2380_, sizeof(void*)*3 + 1, v_wantsRebuild_2344_);
lean_ctor_set_uint8(v_reuseFailAlloc_2380_, sizeof(void*)*3 + 2, v_canceled_2345_);
v___x_2366_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_2282_, v_archiveFile_2280_, v___x_2360_, v_a_2363_, v___x_2359_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v___x_2366_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v_a_2368_; lean_object* v_a_2369_; lean_object* v___x_2370_; uint8_t v___x_2371_; 
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
lean_inc(v_a_2368_);
v_a_2369_ = lean_ctor_get(v___x_2367_, 1);
lean_inc(v_a_2369_);
lean_dec_ref_known(v___x_2367_, 2);
v___x_2370_ = lean_obj_tag_nat(v_a_2368_);
lean_dec(v_a_2368_);
v___x_2371_ = lean_nat_dec_eq(v___x_2370_, v___x_2351_);
if (v___x_2371_ == 0)
{
uint8_t v___x_2372_; 
lean_dec_ref_known(v___x_2360_, 3);
lean_dec_ref(v_traceFile_2357_);
lean_dec_ref(v_url_2279_);
v___x_2372_ = 1;
v_a_2322_ = v___x_2372_;
v_a_2323_ = v_a_2369_;
goto v___jp_2321_;
}
else
{
uint8_t v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = 0;
lean_inc_ref(v_archiveFile_2280_);
v___x_2374_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_2279_, v_archiveFile_2280_, v_headers_2281_, v___x_2360_, v_traceFile_2357_, v___x_2361_, v_a_2286_, v_a_2369_);
lean_dec_ref_known(v___x_2360_, 3);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 1);
lean_inc(v_a_2375_);
lean_dec_ref_known(v___x_2374_, 2);
v_a_2322_ = v___x_2373_;
v_a_2323_ = v_a_2375_;
goto v___jp_2321_;
}
else
{
lean_object* v_a_2376_; lean_object* v_a_2377_; 
lean_dec_ref(v_archiveFile_2280_);
lean_dec_ref(v_self_2278_);
v_a_2376_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2376_);
v_a_2377_ = lean_ctor_get(v___x_2374_, 1);
lean_inc(v_a_2377_);
lean_dec_ref_known(v___x_2374_, 2);
v_a_2339_ = v_a_2376_;
v_a_2340_ = v_a_2377_;
goto v___jp_2338_;
}
}
}
else
{
lean_object* v_a_2378_; lean_object* v_a_2379_; 
lean_dec_ref_known(v___x_2360_, 3);
lean_dec_ref(v_traceFile_2357_);
lean_dec_ref(v_archiveFile_2280_);
lean_dec_ref(v_url_2279_);
lean_dec_ref(v_self_2278_);
v_a_2378_ = lean_ctor_get(v___x_2367_, 0);
lean_inc(v_a_2378_);
v_a_2379_ = lean_ctor_get(v___x_2367_, 1);
lean_inc(v_a_2379_);
lean_dec_ref_known(v___x_2367_, 2);
v_a_2339_ = v_a_2378_;
v_a_2340_ = v_a_2379_;
goto v___jp_2338_;
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v_a_2382_; lean_object* v___x_2384_; 
lean_dec_ref_known(v___x_2360_, 3);
lean_dec_ref(v_traceFile_2357_);
lean_dec_ref(v_archiveFile_2280_);
lean_dec_ref(v_url_2279_);
lean_dec_ref(v_self_2278_);
v_a_2381_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2381_);
v_a_2382_ = lean_ctor_get(v___x_2362_, 1);
lean_inc(v_a_2382_);
lean_dec_ref_known(v___x_2362_, 2);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 0, v_a_2382_);
v___x_2384_ = v___x_2349_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2382_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_trace_2346_);
lean_ctor_set(v_reuseFailAlloc_2385_, 2, v_buildTime_2347_);
lean_ctor_set_uint8(v_reuseFailAlloc_2385_, sizeof(void*)*3, v_action_2343_);
lean_ctor_set_uint8(v_reuseFailAlloc_2385_, sizeof(void*)*3 + 1, v_wantsRebuild_2344_);
lean_ctor_set_uint8(v_reuseFailAlloc_2385_, sizeof(void*)*3 + 2, v_canceled_2345_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
v_a_2339_ = v_a_2381_;
v_a_2340_ = v___x_2384_;
goto v___jp_2338_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_2278_ = stack[0].m_obj;
lean_object* v_url_2279_ = stack[1].m_obj;
lean_object* v_archiveFile_2280_ = stack[2].m_obj;
lean_object* v_headers_2281_ = stack[3].m_obj;
lean_object* v_a_2282_ = stack[4].m_obj;
lean_object* v_a_2283_ = stack[5].m_obj;
lean_object* v_a_2284_ = stack[6].m_obj;
lean_object* v_a_2285_ = stack[7].m_obj;
lean_object* v_a_2286_ = stack[8].m_obj;
lean_object* v_a_2287_ = stack[9].m_obj;
lean_object* v_res_2387_;
v_res_2387_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_self_2278_, v_url_2279_, v_archiveFile_2280_, v_headers_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
stack->m_obj
 = v_res_2387_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___boxed(lean_object* v_self_2388_, lean_object* v_url_2389_, lean_object* v_archiveFile_2390_, lean_object* v_headers_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_self_2388_, v_url_2389_, v_archiveFile_2390_, v_headers_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_);
lean_dec_ref(v_a_2396_);
lean_dec(v_a_2395_);
lean_dec(v_a_2394_);
lean_dec(v_a_2393_);
lean_dec_ref(v_a_2392_);
lean_dec_ref(v_headers_2391_);
return v_res_2399_;
}
}
lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(lean_object* v_a_2400_, lean_object* v_info_2401_, lean_object* v_depTrace_2402_, lean_object* v_depHash_2403_, lean_object* v_oldTrace_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_2401_, v_depTrace_2402_, v_depHash_2403_, v_oldTrace_2404_, v_a_2408_, v_a_2409_);
return v___x_2411_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2400_ = stack[0].m_obj;
lean_object* v_info_2401_ = stack[1].m_obj;
lean_object* v_depTrace_2402_ = stack[2].m_obj;
lean_object* v_depHash_2403_ = stack[3].m_obj;
lean_object* v_oldTrace_2404_ = stack[4].m_obj;
lean_object* v_a_2405_ = stack[5].m_obj;
lean_object* v_a_2406_ = stack[6].m_obj;
lean_object* v_a_2407_ = stack[7].m_obj;
lean_object* v_a_2408_ = stack[8].m_obj;
lean_object* v_a_2409_ = stack[9].m_obj;
lean_object* v_res_2412_;
v_res_2412_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(v_a_2400_, v_info_2401_, v_depTrace_2402_, v_depHash_2403_, v_oldTrace_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_);
stack->m_obj
 = v_res_2412_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___boxed(lean_object* v_a_2413_, lean_object* v_info_2414_, lean_object* v_depTrace_2415_, lean_object* v_depHash_2416_, lean_object* v_oldTrace_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(v_a_2413_, v_info_2414_, v_depTrace_2415_, v_depHash_2416_, v_oldTrace_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
lean_dec_ref(v_a_2421_);
lean_dec(v_a_2420_);
lean_dec(v_a_2419_);
lean_dec(v_a_2418_);
lean_dec_ref(v_oldTrace_2417_);
lean_dec(v_depHash_2416_);
lean_dec_ref(v_depTrace_2415_);
lean_dec_ref(v_info_2414_);
lean_dec_ref(v_a_2413_);
return v_res_2424_;
}
}
lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(lean_object* v_getUrl_2425_, lean_object* v_pkg_2426_, lean_object* v_archiveFile_2427_, lean_object* v_headers_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
uint8_t v_r_2437_; lean_object* v___y_2438_; lean_object* v_a_2442_; lean_object* v___x_2459_; 
lean_inc_ref(v___y_2433_);
lean_inc(v___y_2432_);
lean_inc(v___y_2431_);
lean_inc(v___y_2430_);
lean_inc_ref(v___y_2429_);
lean_inc_ref(v_pkg_2426_);
v___x_2459_ = lean_apply_8(v_getUrl_2425_, v_pkg_2426_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, lean_box(0));
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; lean_object* v_a_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_a_2460_);
v_a_2461_ = lean_ctor_get(v___x_2459_, 1);
lean_inc(v_a_2461_);
lean_dec_ref_known(v___x_2459_, 2);
lean_inc_ref(v_pkg_2426_);
v___x_2462_ = lean_apply_1(v_archiveFile_2427_, v_pkg_2426_);
v___x_2463_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_2426_, v_a_2460_, v___x_2462_, v_headers_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v_a_2461_);
lean_dec_ref(v___y_2429_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; uint8_t v___x_2465_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 1);
lean_inc(v_a_2464_);
lean_dec_ref_known(v___x_2463_, 2);
v___x_2465_ = 1;
v_r_2437_ = v___x_2465_;
v___y_2438_ = v_a_2464_;
goto v___jp_2436_;
}
else
{
lean_object* v_a_2466_; 
v_a_2466_ = lean_ctor_get(v___x_2463_, 1);
lean_inc(v_a_2466_);
lean_dec_ref_known(v___x_2463_, 2);
v_a_2442_ = v_a_2466_;
goto v___jp_2441_;
}
}
else
{
lean_object* v_a_2467_; 
lean_dec_ref(v___y_2429_);
lean_dec_ref(v_archiveFile_2427_);
lean_dec_ref(v_pkg_2426_);
v_a_2467_ = lean_ctor_get(v___x_2459_, 1);
lean_inc(v_a_2467_);
lean_dec_ref_known(v___x_2459_, 2);
v_a_2442_ = v_a_2467_;
goto v___jp_2441_;
}
v___jp_2436_:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = lean_box(v_r_2437_);
v___x_2440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
lean_ctor_set(v___x_2440_, 1, v___y_2438_);
return v___x_2440_;
}
v___jp_2441_:
{
lean_object* v_log_2443_; uint8_t v_action_2444_; uint8_t v_wantsRebuild_2445_; uint8_t v_canceled_2446_; lean_object* v_trace_2447_; lean_object* v_buildTime_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2458_; 
v_log_2443_ = lean_ctor_get(v_a_2442_, 0);
v_action_2444_ = lean_ctor_get_uint8(v_a_2442_, sizeof(void*)*3);
v_wantsRebuild_2445_ = lean_ctor_get_uint8(v_a_2442_, sizeof(void*)*3 + 1);
v_canceled_2446_ = lean_ctor_get_uint8(v_a_2442_, sizeof(void*)*3 + 2);
v_trace_2447_ = lean_ctor_get(v_a_2442_, 1);
v_buildTime_2448_ = lean_ctor_get(v_a_2442_, 2);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_a_2442_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2450_ = v_a_2442_;
v_isShared_2451_ = v_isSharedCheck_2458_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_buildTime_2448_);
lean_inc(v_trace_2447_);
lean_inc(v_log_2443_);
lean_dec(v_a_2442_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2458_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
uint8_t v___x_2452_; uint8_t v___x_2453_; lean_object* v___x_2455_; 
v___x_2452_ = 4;
v___x_2453_ = l_Lake_JobAction_merge(v_action_2444_, v___x_2452_);
if (v_isShared_2451_ == 0)
{
v___x_2455_ = v___x_2450_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_log_2443_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_trace_2447_);
lean_ctor_set(v_reuseFailAlloc_2457_, 2, v_buildTime_2448_);
lean_ctor_set_uint8(v_reuseFailAlloc_2457_, sizeof(void*)*3 + 1, v_wantsRebuild_2445_);
lean_ctor_set_uint8(v_reuseFailAlloc_2457_, sizeof(void*)*3 + 2, v_canceled_2446_);
v___x_2455_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
uint8_t v___x_2456_; 
lean_ctor_set_uint8(v___x_2455_, sizeof(void*)*3, v___x_2453_);
v___x_2456_ = 0;
v_r_2437_ = v___x_2456_;
v___y_2438_ = v___x_2455_;
goto v___jp_2436_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_getUrl_2425_ = stack[0].m_obj;
lean_object* v_pkg_2426_ = stack[1].m_obj;
lean_object* v_archiveFile_2427_ = stack[2].m_obj;
lean_object* v_headers_2428_ = stack[3].m_obj;
lean_object* v___y_2429_ = stack[4].m_obj;
lean_object* v___y_2430_ = stack[5].m_obj;
lean_object* v___y_2431_ = stack[6].m_obj;
lean_object* v___y_2432_ = stack[7].m_obj;
lean_object* v___y_2433_ = stack[8].m_obj;
lean_object* v___y_2434_ = stack[9].m_obj;
lean_object* v_res_2468_;
v_res_2468_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(v_getUrl_2425_, v_pkg_2426_, v_archiveFile_2427_, v_headers_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
stack->m_obj
 = v_res_2468_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* v_getUrl_2469_, lean_object* v_pkg_2470_, lean_object* v_archiveFile_2471_, lean_object* v_headers_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(v_getUrl_2469_, v_pkg_2470_, v_archiveFile_2471_, v_headers_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec(v___y_2474_);
lean_dec_ref(v_headers_2472_);
return v_res_2480_;
}
}
lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(lean_object* v_getUrl_2481_, lean_object* v_archiveFile_2482_, lean_object* v_headers_2483_, lean_object* v_facet_2484_, lean_object* v___x_2485_, lean_object* v_pkg_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v_baseName_2494_; lean_object* v___f_2495_; uint8_t v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v_baseName_2494_ = lean_ctor_get(v_pkg_2486_, 1);
lean_inc(v_baseName_2494_);
v___f_2495_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2495_, 0, v_getUrl_2481_);
lean_closure_set(v___f_2495_, 1, v_pkg_2486_);
lean_closure_set(v___f_2495_, 2, v_archiveFile_2482_);
lean_closure_set(v___f_2495_, 3, v_headers_2483_);
v___x_2496_ = 1;
v___x_2497_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2494_, v___x_2496_);
v___x_2498_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2499_ = lean_string_append(v___x_2497_, v___x_2498_);
v___x_2500_ = l_Lake_Name_eraseHead(v_facet_2484_);
v___x_2501_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2500_, v___x_2496_);
v___x_2502_ = lean_string_append(v___x_2499_, v___x_2501_);
lean_dec_ref(v___x_2501_);
v___x_2503_ = lean_unsigned_to_nat(0u);
v___x_2504_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_2485_);
v___x_2505_ = lean_alloc_closure((void*)(l_Lake_Job_async___boxed), 12, 5);
lean_closure_set(v___x_2505_, 0, lean_box(0));
lean_closure_set(v___x_2505_, 1, v___x_2485_);
lean_closure_set(v___x_2505_, 2, v___f_2495_);
lean_closure_set(v___x_2505_, 3, v___x_2503_);
lean_closure_set(v___x_2505_, 4, v___x_2504_);
v___x_2506_ = lean_alloc_closure((void*)(l_Lake_JobM_runSpawnM___boxed), 9, 2);
lean_closure_set(v___x_2506_, 0, lean_box(0));
lean_closure_set(v___x_2506_, 1, v___x_2505_);
v___x_2507_ = lean_alloc_closure((void*)(l_Lake_FetchM_runJobM___boxed), 9, 2);
lean_closure_set(v___x_2507_, 0, lean_box(0));
lean_closure_set(v___x_2507_, 1, v___x_2506_);
v___x_2508_ = l_Lake_ensureJob___redArg(v___x_2485_, v___x_2507_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2533_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
v_a_2510_ = lean_ctor_get(v___x_2508_, 1);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2512_ = v___x_2508_;
v_isShared_2513_ = v_isSharedCheck_2533_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_inc(v_a_2509_);
lean_dec(v___x_2508_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2533_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v_task_2514_; lean_object* v_kind_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2531_; 
v_task_2514_ = lean_ctor_get(v_a_2509_, 0);
v_kind_2515_ = lean_ctor_get(v_a_2509_, 1);
v_isSharedCheck_2531_ = !lean_is_exclusive(v_a_2509_);
if (v_isSharedCheck_2531_ == 0)
{
lean_object* v_unused_2532_; 
v_unused_2532_ = lean_ctor_get(v_a_2509_, 2);
lean_dec(v_unused_2532_);
v___x_2517_ = v_a_2509_;
v_isShared_2518_ = v_isSharedCheck_2531_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_kind_2515_);
lean_inc(v_task_2514_);
lean_dec(v_a_2509_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2531_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v_registeredJobs_2519_; lean_object* v_job_2521_; 
v_registeredJobs_2519_ = lean_ctor_get(v___y_2491_, 4);
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 2, v___x_2502_);
v_job_2521_ = v___x_2517_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_task_2514_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v_kind_2515_);
lean_ctor_set(v_reuseFailAlloc_2530_, 2, v___x_2502_);
v_job_2521_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2528_; 
lean_ctor_set_uint8(v_job_2521_, sizeof(void*)*3, v___x_2496_);
v___x_2522_ = lean_st_ref_take(v_registeredJobs_2519_);
lean_inc_ref(v_job_2521_);
v___x_2523_ = l_Lake_Job_toOpaque___redArg(v_job_2521_);
v___x_2524_ = lean_array_push(v___x_2522_, v___x_2523_);
v___x_2525_ = lean_st_ref_put(v_registeredJobs_2519_, v___x_2524_);
v___x_2526_ = l_Lake_Job_renew___redArg(v_job_2521_);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 0, v___x_2526_);
v___x_2528_ = v___x_2512_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2526_);
lean_ctor_set(v_reuseFailAlloc_2529_, 1, v_a_2510_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2502_);
return v___x_2508_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_getUrl_2481_ = stack[0].m_obj;
lean_object* v_archiveFile_2482_ = stack[1].m_obj;
lean_object* v_headers_2483_ = stack[2].m_obj;
lean_object* v_facet_2484_ = stack[3].m_obj;
lean_object* v___x_2485_ = stack[4].m_obj;
lean_object* v_pkg_2486_ = stack[5].m_obj;
lean_object* v___y_2487_ = stack[6].m_obj;
lean_object* v___y_2488_ = stack[7].m_obj;
lean_object* v___y_2489_ = stack[8].m_obj;
lean_object* v___y_2490_ = stack[9].m_obj;
lean_object* v___y_2491_ = stack[10].m_obj;
lean_object* v___y_2492_ = stack[11].m_obj;
lean_object* v_res_2534_;
v_res_2534_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(v_getUrl_2481_, v_archiveFile_2482_, v_headers_2483_, v_facet_2484_, v___x_2485_, v_pkg_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
stack->m_obj
 = v_res_2534_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* v_getUrl_2535_, lean_object* v_archiveFile_2536_, lean_object* v_headers_2537_, lean_object* v_facet_2538_, lean_object* v___x_2539_, lean_object* v_pkg_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(v_getUrl_2535_, v_archiveFile_2536_, v_headers_2537_, v_facet_2538_, v___x_2539_, v_pkg_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec(v___y_2542_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg(lean_object* v_facet_2556_, lean_object* v_archiveFile_2557_, lean_object* v_getUrl_2558_, lean_object* v_headers_2559_){
_start:
{
lean_object* v___x_2560_; lean_object* v___f_2561_; lean_object* v___x_2562_; uint8_t v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2560_ = l_Lake_instDataKindBool;
v___f_2561_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2561_, 0, v_getUrl_2558_);
lean_closure_set(v___f_2561_, 1, v_archiveFile_2557_);
lean_closure_set(v___f_2561_, 2, v_headers_2559_);
lean_closure_set(v___f_2561_, 3, v_facet_2556_);
lean_closure_set(v___f_2561_, 4, v___x_2560_);
v___x_2562_ = l_Lake_Package_keyword;
v___x_2563_ = 1;
v___x_2564_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3));
v___x_2565_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2565_, 0, v___x_2562_);
lean_ctor_set(v___x_2565_, 1, v___f_2561_);
lean_ctor_set(v___x_2565_, 2, v___x_2560_);
lean_ctor_set(v___x_2565_, 3, v___x_2564_);
lean_ctor_set_uint8(v___x_2565_, sizeof(void*)*4, v___x_2563_);
lean_ctor_set_uint8(v___x_2565_, sizeof(void*)*4 + 1, v___x_2563_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig(lean_object* v_facet_2566_, lean_object* v_archiveFile_2567_, lean_object* v_getUrl_2568_, lean_object* v_headers_2569_, lean_object* v_inst_2570_){
_start:
{
lean_object* v___x_2571_; lean_object* v___f_2572_; lean_object* v___x_2573_; uint8_t v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2571_ = l_Lake_instDataKindBool;
v___f_2572_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2572_, 0, v_getUrl_2568_);
lean_closure_set(v___f_2572_, 1, v_archiveFile_2567_);
lean_closure_set(v___f_2572_, 2, v_headers_2569_);
lean_closure_set(v___f_2572_, 3, v_facet_2566_);
lean_closure_set(v___f_2572_, 4, v___x_2571_);
v___x_2573_ = l_Lake_Package_keyword;
v___x_2574_ = 1;
v___x_2575_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3));
v___x_2576_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2576_, 0, v___x_2573_);
lean_ctor_set(v___x_2576_, 1, v___f_2572_);
lean_ctor_set(v___x_2576_, 2, v___x_2571_);
lean_ctor_set(v___x_2576_, 3, v___x_2575_);
lean_ctor_set_uint8(v___x_2576_, sizeof(void*)*4, v___x_2574_);
lean_ctor_set_uint8(v___x_2576_, sizeof(void*)*4 + 1, v___x_2574_);
return v___x_2576_;
}
}
lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(lean_object* v_what_2578_, lean_object* v_baseName_2579_, lean_object* v_optFacet_2580_, uint8_t v_success_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v_a_2590_; lean_object* v_a_2591_; 
if (v_success_2581_ == 0)
{
lean_object* v_toBuildConfig_2613_; uint8_t v_verbosity_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; uint8_t v___x_2618_; 
v_toBuildConfig_2613_ = lean_ctor_get(v___y_2586_, 0);
v_verbosity_2614_ = lean_ctor_get_uint8(v_toBuildConfig_2613_, sizeof(void*)*5 + 4);
v___x_2615_ = lean_box(v_verbosity_2614_);
v___x_2616_ = lean_obj_tag_nat(v___x_2615_);
lean_dec(v___x_2615_);
v___x_2617_ = lean_unsigned_to_nat(2u);
v___x_2618_ = lean_nat_dec_eq(v___x_2616_, v___x_2617_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; 
lean_dec(v_optFacet_2580_);
lean_dec(v_baseName_2579_);
v___x_2619_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_2590_ = v___x_2619_;
v_a_2591_ = v___y_2587_;
goto v___jp_2589_;
}
else
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2620_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_2621_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2579_, v___x_2618_);
v___x_2622_ = lean_string_append(v___x_2620_, v___x_2621_);
lean_dec_ref(v___x_2621_);
v___x_2623_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2624_ = lean_string_append(v___x_2622_, v___x_2623_);
v___x_2625_ = l_Lake_Name_eraseHead(v_optFacet_2580_);
v___x_2626_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2625_, v___x_2618_);
v___x_2627_ = lean_string_append(v___x_2624_, v___x_2626_);
lean_dec_ref(v___x_2626_);
v___x_2628_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2629_ = lean_string_append(v___x_2627_, v___x_2628_);
v_a_2590_ = v___x_2629_;
v_a_2591_ = v___y_2587_;
goto v___jp_2589_;
}
}
else
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
lean_dec(v_optFacet_2580_);
lean_dec(v_baseName_2579_);
v___x_2630_ = lean_box(0);
v___x_2631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2630_);
lean_ctor_set(v___x_2631_, 1, v___y_2587_);
return v___x_2631_;
}
v___jp_2589_:
{
lean_object* v_log_2592_; uint8_t v_action_2593_; uint8_t v_wantsRebuild_2594_; uint8_t v_canceled_2595_; lean_object* v_trace_2596_; lean_object* v_buildTime_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2612_; 
v_log_2592_ = lean_ctor_get(v_a_2591_, 0);
v_action_2593_ = lean_ctor_get_uint8(v_a_2591_, sizeof(void*)*3);
v_wantsRebuild_2594_ = lean_ctor_get_uint8(v_a_2591_, sizeof(void*)*3 + 1);
v_canceled_2595_ = lean_ctor_get_uint8(v_a_2591_, sizeof(void*)*3 + 2);
v_trace_2596_ = lean_ctor_get(v_a_2591_, 1);
v_buildTime_2597_ = lean_ctor_get(v_a_2591_, 2);
v_isSharedCheck_2612_ = !lean_is_exclusive(v_a_2591_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2599_ = v_a_2591_;
v_isShared_2600_ = v_isSharedCheck_2612_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_buildTime_2597_);
lean_inc(v_trace_2596_);
lean_inc(v_log_2592_);
lean_dec(v_a_2591_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2612_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; uint8_t v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2609_; 
v___x_2601_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0));
v___x_2602_ = lean_string_append(v___x_2601_, v_what_2578_);
v___x_2603_ = lean_string_append(v___x_2602_, v_a_2590_);
lean_dec_ref(v_a_2590_);
v___x_2604_ = 3;
v___x_2605_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2605_, 0, v___x_2603_);
lean_ctor_set_uint8(v___x_2605_, sizeof(void*)*1, v___x_2604_);
v___x_2606_ = lean_array_get_size(v_log_2592_);
v___x_2607_ = lean_array_push(v_log_2592_, v___x_2605_);
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 0, v___x_2607_);
v___x_2609_ = v___x_2599_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2607_);
lean_ctor_set(v_reuseFailAlloc_2611_, 1, v_trace_2596_);
lean_ctor_set(v_reuseFailAlloc_2611_, 2, v_buildTime_2597_);
lean_ctor_set_uint8(v_reuseFailAlloc_2611_, sizeof(void*)*3, v_action_2593_);
lean_ctor_set_uint8(v_reuseFailAlloc_2611_, sizeof(void*)*3 + 1, v_wantsRebuild_2594_);
lean_ctor_set_uint8(v_reuseFailAlloc_2611_, sizeof(void*)*3 + 2, v_canceled_2595_);
v___x_2609_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
lean_object* v___x_2610_; 
v___x_2610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2606_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
return v___x_2610_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_what_2578_ = stack[0].m_obj;
lean_object* v_baseName_2579_ = stack[1].m_obj;
lean_object* v_optFacet_2580_ = stack[2].m_obj;
uint8_t v_success_2581_ = stack[3].m_num;
lean_object* v___y_2582_ = stack[4].m_obj;
lean_object* v___y_2583_ = stack[5].m_obj;
lean_object* v___y_2584_ = stack[6].m_obj;
lean_object* v___y_2585_ = stack[7].m_obj;
lean_object* v___y_2586_ = stack[8].m_obj;
lean_object* v___y_2587_ = stack[9].m_obj;
lean_object* v_res_2632_;
v_res_2632_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(v_what_2578_, v_baseName_2579_, v_optFacet_2580_, v_success_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
stack->m_obj
 = v_res_2632_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* v_what_2633_, lean_object* v_baseName_2634_, lean_object* v_optFacet_2635_, lean_object* v_success_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
uint8_t v_success_boxed_2644_; lean_object* v_res_2645_; 
v_success_boxed_2644_ = lean_unbox(v_success_2636_);
v_res_2645_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(v_what_2633_, v_baseName_2634_, v_optFacet_2635_, v_success_boxed_2644_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec_ref(v_what_2633_);
return v_res_2645_;
}
}
lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(lean_object* v___x_2646_, lean_object* v___x_2647_, lean_object* v___f_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v___x_2656_; 
lean_inc_ref(v___y_2649_);
lean_inc_ref(v___y_2653_);
lean_inc(v___y_2652_);
lean_inc(v___y_2651_);
lean_inc(v___y_2650_);
v___x_2656_ = lean_apply_7(v___y_2649_, v___x_2646_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, lean_box(0));
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2669_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
v_a_2658_ = lean_ctor_get(v___x_2656_, 1);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2660_ = v___x_2656_;
v_isShared_2661_ = v_isSharedCheck_2669_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_inc(v_a_2657_);
lean_dec(v___x_2656_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2669_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2662_; uint8_t v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2667_; 
v___x_2662_ = lean_unsigned_to_nat(0u);
v___x_2663_ = 0;
v___x_2664_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_2665_ = l_Lake_Job_mapM___redArg(v___x_2647_, v_a_2657_, v___f_2648_, v___x_2662_, v___x_2663_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___x_2664_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v___x_2665_);
v___x_2667_ = v___x_2660_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2665_);
lean_ctor_set(v_reuseFailAlloc_2668_, 1, v_a_2658_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
else
{
lean_object* v_a_2670_; lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2678_; 
lean_dec_ref(v___y_2649_);
lean_dec_ref(v___f_2648_);
lean_dec(v___x_2647_);
v_a_2670_ = lean_ctor_get(v___x_2656_, 0);
v_a_2671_ = lean_ctor_get(v___x_2656_, 1);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2673_ = v___x_2656_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_inc(v_a_2670_);
lean_dec(v___x_2656_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2676_; 
if (v_isShared_2674_ == 0)
{
v___x_2676_ = v___x_2673_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2670_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_a_2671_);
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
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2646_ = stack[0].m_obj;
lean_object* v___x_2647_ = stack[1].m_obj;
lean_object* v___f_2648_ = stack[2].m_obj;
lean_object* v___y_2649_ = stack[3].m_obj;
lean_object* v___y_2650_ = stack[4].m_obj;
lean_object* v___y_2651_ = stack[5].m_obj;
lean_object* v___y_2652_ = stack[6].m_obj;
lean_object* v___y_2653_ = stack[7].m_obj;
lean_object* v___y_2654_ = stack[8].m_obj;
lean_object* v_res_2679_;
v_res_2679_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(v___x_2646_, v___x_2647_, v___f_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
stack->m_obj
 = v_res_2679_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* v___x_2680_, lean_object* v___x_2681_, lean_object* v___f_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(v___x_2680_, v___x_2681_, v___f_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec(v___y_2684_);
return v_res_2690_;
}
}
lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(lean_object* v_what_2691_, lean_object* v_optFacet_2692_, lean_object* v_facet_2693_, lean_object* v___x_2694_, lean_object* v_pkg_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v_baseName_2703_; lean_object* v_keyName_2704_; lean_object* v___f_2705_; uint8_t v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___f_2716_; uint8_t v___x_2717_; lean_object* v___x_2718_; 
v_baseName_2703_ = lean_ctor_get(v_pkg_2695_, 1);
v_keyName_2704_ = lean_ctor_get(v_pkg_2695_, 2);
lean_inc(v_optFacet_2692_);
lean_inc_n(v_baseName_2703_, 2);
v___f_2705_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 3);
lean_closure_set(v___f_2705_, 0, v_what_2691_);
lean_closure_set(v___f_2705_, 1, v_baseName_2703_);
lean_closure_set(v___f_2705_, 2, v_optFacet_2692_);
v___x_2706_ = 1;
v___x_2707_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2703_, v___x_2706_);
v___x_2708_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2709_ = lean_string_append(v___x_2707_, v___x_2708_);
v___x_2710_ = l_Lake_Name_eraseHead(v_facet_2693_);
v___x_2711_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2710_, v___x_2706_);
v___x_2712_ = lean_string_append(v___x_2709_, v___x_2711_);
lean_dec_ref(v___x_2711_);
lean_inc(v_keyName_2704_);
v___x_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2713_, 0, v_keyName_2704_);
v___x_2714_ = l_Lake_Package_keyword;
v___x_2715_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2713_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
lean_ctor_set(v___x_2715_, 2, v_pkg_2695_);
lean_ctor_set(v___x_2715_, 3, v_optFacet_2692_);
lean_inc(v___x_2694_);
v___f_2716_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2716_, 0, v___x_2715_);
lean_closure_set(v___f_2716_, 1, v___x_2694_);
lean_closure_set(v___f_2716_, 2, v___f_2705_);
v___x_2717_ = 0;
v___x_2718_ = l_Lake_ensureJob___redArg(v___x_2694_, v___f_2716_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v_a_2719_; lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2743_; 
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
v_a_2720_ = lean_ctor_get(v___x_2718_, 1);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2722_ = v___x_2718_;
v_isShared_2723_ = v_isSharedCheck_2743_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_inc(v_a_2719_);
lean_dec(v___x_2718_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2743_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v_task_2724_; lean_object* v_kind_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2741_; 
v_task_2724_ = lean_ctor_get(v_a_2719_, 0);
v_kind_2725_ = lean_ctor_get(v_a_2719_, 1);
v_isSharedCheck_2741_ = !lean_is_exclusive(v_a_2719_);
if (v_isSharedCheck_2741_ == 0)
{
lean_object* v_unused_2742_; 
v_unused_2742_ = lean_ctor_get(v_a_2719_, 2);
lean_dec(v_unused_2742_);
v___x_2727_ = v_a_2719_;
v_isShared_2728_ = v_isSharedCheck_2741_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_kind_2725_);
lean_inc(v_task_2724_);
lean_dec(v_a_2719_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2741_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v_registeredJobs_2729_; lean_object* v_job_2731_; 
v_registeredJobs_2729_ = lean_ctor_get(v___y_2700_, 4);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 2, v___x_2712_);
v_job_2731_ = v___x_2727_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_task_2724_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v_kind_2725_);
lean_ctor_set(v_reuseFailAlloc_2740_, 2, v___x_2712_);
v_job_2731_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2738_; 
lean_ctor_set_uint8(v_job_2731_, sizeof(void*)*3, v___x_2717_);
v___x_2732_ = lean_st_ref_take(v_registeredJobs_2729_);
lean_inc_ref(v_job_2731_);
v___x_2733_ = l_Lake_Job_toOpaque___redArg(v_job_2731_);
v___x_2734_ = lean_array_push(v___x_2732_, v___x_2733_);
v___x_2735_ = lean_st_ref_put(v_registeredJobs_2729_, v___x_2734_);
v___x_2736_ = l_Lake_Job_renew___redArg(v_job_2731_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 0, v___x_2736_);
v___x_2738_ = v___x_2722_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2736_);
lean_ctor_set(v_reuseFailAlloc_2739_, 1, v_a_2720_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2712_);
return v___x_2718_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_what_2691_ = stack[0].m_obj;
lean_object* v_optFacet_2692_ = stack[1].m_obj;
lean_object* v_facet_2693_ = stack[2].m_obj;
lean_object* v___x_2694_ = stack[3].m_obj;
lean_object* v_pkg_2695_ = stack[4].m_obj;
lean_object* v___y_2696_ = stack[5].m_obj;
lean_object* v___y_2697_ = stack[6].m_obj;
lean_object* v___y_2698_ = stack[7].m_obj;
lean_object* v___y_2699_ = stack[8].m_obj;
lean_object* v___y_2700_ = stack[9].m_obj;
lean_object* v___y_2701_ = stack[10].m_obj;
lean_object* v_res_2744_;
v_res_2744_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(v_what_2691_, v_optFacet_2692_, v_facet_2693_, v___x_2694_, v_pkg_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
stack->m_obj
 = v_res_2744_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed(lean_object* v_what_2745_, lean_object* v_optFacet_2746_, lean_object* v_facet_2747_, lean_object* v___x_2748_, lean_object* v_pkg_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(v_what_2745_, v_optFacet_2746_, v_facet_2747_, v___x_2748_, v_pkg_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec(v___y_2751_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg(lean_object* v_facet_2765_, lean_object* v_optFacet_2766_, lean_object* v_what_2767_){
_start:
{
lean_object* v___x_2768_; lean_object* v___f_2769_; lean_object* v___x_2770_; uint8_t v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2768_ = l_Lake_instDataKindUnit;
v___f_2769_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2769_, 0, v_what_2767_);
lean_closure_set(v___f_2769_, 1, v_optFacet_2766_);
lean_closure_set(v___f_2769_, 2, v_facet_2765_);
lean_closure_set(v___f_2769_, 3, v___x_2768_);
v___x_2770_ = l_Lake_Package_keyword;
v___x_2771_ = 1;
v___x_2772_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3));
v___x_2773_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2773_, 0, v___x_2770_);
lean_ctor_set(v___x_2773_, 1, v___f_2769_);
lean_ctor_set(v___x_2773_, 2, v___x_2768_);
lean_ctor_set(v___x_2773_, 3, v___x_2772_);
lean_ctor_set_uint8(v___x_2773_, sizeof(void*)*4, v___x_2771_);
lean_ctor_set_uint8(v___x_2773_, sizeof(void*)*4 + 1, v___x_2771_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig(lean_object* v_facet_2774_, lean_object* v_optFacet_2775_, lean_object* v_what_2776_, lean_object* v_inst_2777_, lean_object* v_inst_2778_){
_start:
{
lean_object* v___x_2779_; lean_object* v___f_2780_; lean_object* v___x_2781_; uint8_t v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2779_ = l_Lake_instDataKindUnit;
v___f_2780_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2780_, 0, v_what_2776_);
lean_closure_set(v___f_2780_, 1, v_optFacet_2775_);
lean_closure_set(v___f_2780_, 2, v_facet_2774_);
lean_closure_set(v___f_2780_, 3, v___x_2779_);
v___x_2781_ = l_Lake_Package_keyword;
v___x_2782_ = 1;
v___x_2783_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3));
v___x_2784_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2784_, 0, v___x_2781_);
lean_ctor_set(v___x_2784_, 1, v___f_2780_);
lean_ctor_set(v___x_2784_, 2, v___x_2779_);
lean_ctor_set(v___x_2784_, 3, v___x_2783_);
lean_ctor_set_uint8(v___x_2784_, sizeof(void*)*4, v___x_2782_);
lean_ctor_set_uint8(v___x_2784_, sizeof(void*)*4 + 1, v___x_2782_);
return v___x_2784_;
}
}
lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1(lean_object* v_baseName_2786_, lean_object* v___x_2787_, uint8_t v_success_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
lean_object* v_a_2797_; lean_object* v_a_2798_; 
if (v_success_2788_ == 0)
{
lean_object* v_toBuildConfig_2819_; uint8_t v_verbosity_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; 
v_toBuildConfig_2819_ = lean_ctor_get(v___y_2793_, 0);
v_verbosity_2820_ = lean_ctor_get_uint8(v_toBuildConfig_2819_, sizeof(void*)*5 + 4);
v___x_2821_ = lean_box(v_verbosity_2820_);
v___x_2822_ = lean_obj_tag_nat(v___x_2821_);
lean_dec(v___x_2821_);
v___x_2823_ = lean_unsigned_to_nat(2u);
v___x_2824_ = lean_nat_dec_eq(v___x_2822_, v___x_2823_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; 
lean_dec(v___x_2787_);
lean_dec(v_baseName_2786_);
v___x_2825_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_2797_ = v___x_2825_;
v_a_2798_ = v___y_2794_;
goto v___jp_2796_;
}
else
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2826_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_2827_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2786_, v___x_2824_);
v___x_2828_ = lean_string_append(v___x_2826_, v___x_2827_);
lean_dec_ref(v___x_2827_);
v___x_2829_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2830_ = lean_string_append(v___x_2828_, v___x_2829_);
v___x_2831_ = l_Lake_Name_eraseHead(v___x_2787_);
v___x_2832_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2831_, v___x_2824_);
v___x_2833_ = lean_string_append(v___x_2830_, v___x_2832_);
lean_dec_ref(v___x_2832_);
v___x_2834_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2835_ = lean_string_append(v___x_2833_, v___x_2834_);
v_a_2797_ = v___x_2835_;
v_a_2798_ = v___y_2794_;
goto v___jp_2796_;
}
}
else
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
lean_dec(v___x_2787_);
lean_dec(v_baseName_2786_);
v___x_2836_ = lean_box(0);
v___x_2837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2836_);
lean_ctor_set(v___x_2837_, 1, v___y_2794_);
return v___x_2837_;
}
v___jp_2796_:
{
lean_object* v_log_2799_; uint8_t v_action_2800_; uint8_t v_wantsRebuild_2801_; uint8_t v_canceled_2802_; lean_object* v_trace_2803_; lean_object* v_buildTime_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2818_; 
v_log_2799_ = lean_ctor_get(v_a_2798_, 0);
v_action_2800_ = lean_ctor_get_uint8(v_a_2798_, sizeof(void*)*3);
v_wantsRebuild_2801_ = lean_ctor_get_uint8(v_a_2798_, sizeof(void*)*3 + 1);
v_canceled_2802_ = lean_ctor_get_uint8(v_a_2798_, sizeof(void*)*3 + 2);
v_trace_2803_ = lean_ctor_get(v_a_2798_, 1);
v_buildTime_2804_ = lean_ctor_get(v_a_2798_, 2);
v_isSharedCheck_2818_ = !lean_is_exclusive(v_a_2798_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2806_ = v_a_2798_;
v_isShared_2807_ = v_isSharedCheck_2818_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_buildTime_2804_);
lean_inc(v_trace_2803_);
lean_inc(v_log_2799_);
lean_dec(v_a_2798_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2818_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; uint8_t v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2815_; 
v___x_2808_ = ((lean_object*)(l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0));
v___x_2809_ = lean_string_append(v___x_2808_, v_a_2797_);
lean_dec_ref(v_a_2797_);
v___x_2810_ = 3;
v___x_2811_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2811_, 0, v___x_2809_);
lean_ctor_set_uint8(v___x_2811_, sizeof(void*)*1, v___x_2810_);
v___x_2812_ = lean_array_get_size(v_log_2799_);
v___x_2813_ = lean_array_push(v_log_2799_, v___x_2811_);
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 0, v___x_2813_);
v___x_2815_ = v___x_2806_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2813_);
lean_ctor_set(v_reuseFailAlloc_2817_, 1, v_trace_2803_);
lean_ctor_set(v_reuseFailAlloc_2817_, 2, v_buildTime_2804_);
lean_ctor_set_uint8(v_reuseFailAlloc_2817_, sizeof(void*)*3, v_action_2800_);
lean_ctor_set_uint8(v_reuseFailAlloc_2817_, sizeof(void*)*3 + 1, v_wantsRebuild_2801_);
lean_ctor_set_uint8(v_reuseFailAlloc_2817_, sizeof(void*)*3 + 2, v_canceled_2802_);
v___x_2815_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
lean_object* v___x_2816_; 
v___x_2816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2812_);
lean_ctor_set(v___x_2816_, 1, v___x_2815_);
return v___x_2816_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_Package_buildCacheFacetConfig___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_baseName_2786_ = stack[0].m_obj;
lean_object* v___x_2787_ = stack[1].m_obj;
uint8_t v_success_2788_ = stack[2].m_num;
lean_object* v___y_2789_ = stack[3].m_obj;
lean_object* v___y_2790_ = stack[4].m_obj;
lean_object* v___y_2791_ = stack[5].m_obj;
lean_object* v___y_2792_ = stack[6].m_obj;
lean_object* v___y_2793_ = stack[7].m_obj;
lean_object* v___y_2794_ = stack[8].m_obj;
lean_object* v_res_2838_;
v_res_2838_ = l_Lake_Package_buildCacheFacetConfig___lam__1(v_baseName_2786_, v___x_2787_, v_success_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
stack->m_obj
 = v_res_2838_;
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1___boxed(lean_object* v_baseName_2839_, lean_object* v___x_2840_, lean_object* v_success_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
uint8_t v_success_boxed_2849_; lean_object* v_res_2850_; 
v_success_boxed_2849_ = lean_unbox(v_success_2841_);
v_res_2850_ = l_Lake_Package_buildCacheFacetConfig___lam__1(v_baseName_2839_, v___x_2840_, v_success_boxed_2849_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
return v_res_2850_;
}
}
lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2(lean_object* v___x_2851_, lean_object* v___x_2852_, lean_object* v___x_2853_, lean_object* v_pkg_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
lean_object* v_baseName_2862_; lean_object* v_keyName_2863_; lean_object* v___f_2864_; uint8_t v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___f_2875_; uint8_t v___x_2876_; lean_object* v___x_2877_; 
v_baseName_2862_ = lean_ctor_get(v_pkg_2854_, 1);
v_keyName_2863_ = lean_ctor_get(v_pkg_2854_, 2);
lean_inc(v___x_2851_);
lean_inc_n(v_baseName_2862_, 2);
v___f_2864_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2864_, 0, v_baseName_2862_);
lean_closure_set(v___f_2864_, 1, v___x_2851_);
v___x_2865_ = 1;
v___x_2866_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2862_, v___x_2865_);
v___x_2867_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2868_ = lean_string_append(v___x_2866_, v___x_2867_);
v___x_2869_ = l_Lake_Name_eraseHead(v___x_2852_);
v___x_2870_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2869_, v___x_2865_);
v___x_2871_ = lean_string_append(v___x_2868_, v___x_2870_);
lean_dec_ref(v___x_2870_);
lean_inc(v_keyName_2863_);
v___x_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2872_, 0, v_keyName_2863_);
v___x_2873_ = l_Lake_Package_keyword;
v___x_2874_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2872_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
lean_ctor_set(v___x_2874_, 2, v_pkg_2854_);
lean_ctor_set(v___x_2874_, 3, v___x_2851_);
lean_inc(v___x_2853_);
v___f_2875_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2875_, 0, v___x_2874_);
lean_closure_set(v___f_2875_, 1, v___x_2853_);
lean_closure_set(v___f_2875_, 2, v___f_2864_);
v___x_2876_ = 0;
v___x_2877_ = l_Lake_ensureJob___redArg(v___x_2853_, v___f_2875_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2902_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
v_a_2879_ = lean_ctor_get(v___x_2877_, 1);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2881_ = v___x_2877_;
v_isShared_2882_ = v_isSharedCheck_2902_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_inc(v_a_2878_);
lean_dec(v___x_2877_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2902_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v_task_2883_; lean_object* v_kind_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2900_; 
v_task_2883_ = lean_ctor_get(v_a_2878_, 0);
v_kind_2884_ = lean_ctor_get(v_a_2878_, 1);
v_isSharedCheck_2900_ = !lean_is_exclusive(v_a_2878_);
if (v_isSharedCheck_2900_ == 0)
{
lean_object* v_unused_2901_; 
v_unused_2901_ = lean_ctor_get(v_a_2878_, 2);
lean_dec(v_unused_2901_);
v___x_2886_ = v_a_2878_;
v_isShared_2887_ = v_isSharedCheck_2900_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_kind_2884_);
lean_inc(v_task_2883_);
lean_dec(v_a_2878_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2900_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v_registeredJobs_2888_; lean_object* v_job_2890_; 
v_registeredJobs_2888_ = lean_ctor_get(v___y_2859_, 4);
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 2, v___x_2871_);
v_job_2890_ = v___x_2886_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_task_2883_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v_kind_2884_);
lean_ctor_set(v_reuseFailAlloc_2899_, 2, v___x_2871_);
v_job_2890_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2897_; 
lean_ctor_set_uint8(v_job_2890_, sizeof(void*)*3, v___x_2876_);
v___x_2891_ = lean_st_ref_take(v_registeredJobs_2888_);
lean_inc_ref(v_job_2890_);
v___x_2892_ = l_Lake_Job_toOpaque___redArg(v_job_2890_);
v___x_2893_ = lean_array_push(v___x_2891_, v___x_2892_);
v___x_2894_ = lean_st_ref_put(v_registeredJobs_2888_, v___x_2893_);
v___x_2895_ = l_Lake_Job_renew___redArg(v_job_2890_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 0, v___x_2895_);
v___x_2897_ = v___x_2881_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v___x_2895_);
lean_ctor_set(v_reuseFailAlloc_2898_, 1, v_a_2879_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2871_);
return v___x_2877_;
}
}
}
LEAN_EXPORT void l_Lake_Package_buildCacheFacetConfig___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2851_ = stack[0].m_obj;
lean_object* v___x_2852_ = stack[1].m_obj;
lean_object* v___x_2853_ = stack[2].m_obj;
lean_object* v_pkg_2854_ = stack[3].m_obj;
lean_object* v___y_2855_ = stack[4].m_obj;
lean_object* v___y_2856_ = stack[5].m_obj;
lean_object* v___y_2857_ = stack[6].m_obj;
lean_object* v___y_2858_ = stack[7].m_obj;
lean_object* v___y_2859_ = stack[8].m_obj;
lean_object* v___y_2860_ = stack[9].m_obj;
lean_object* v_res_2903_;
v_res_2903_ = l_Lake_Package_buildCacheFacetConfig___lam__2(v___x_2851_, v___x_2852_, v___x_2853_, v_pkg_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
stack->m_obj
 = v_res_2903_;
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2___boxed(lean_object* v___x_2904_, lean_object* v___x_2905_, lean_object* v___x_2906_, lean_object* v_pkg_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l_Lake_Package_buildCacheFacetConfig___lam__2(v___x_2904_, v___x_2905_, v___x_2906_, v_pkg_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec(v___y_2909_);
return v_res_2915_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___f_2919_; 
v___x_2916_ = l_Lake_instDataKindUnit;
v___x_2917_ = l_Lake_Package_buildCacheFacet;
v___x_2918_ = l_Lake_Package_optBuildCacheFacet;
v___f_2919_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2919_, 0, v___x_2918_);
lean_closure_set(v___f_2919_, 1, v___x_2917_);
lean_closure_set(v___f_2919_, 2, v___x_2916_);
return v___f_2919_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2920_; uint8_t v___x_2921_; lean_object* v___x_2922_; lean_object* v___f_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___f_2920_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_2921_ = 1;
v___x_2922_ = l_Lake_instDataKindUnit;
v___f_2923_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__0, &l_Lake_Package_buildCacheFacetConfig___closed__0_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__0);
v___x_2924_ = l_Lake_Package_keyword;
v___x_2925_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2925_, 0, v___x_2924_);
lean_ctor_set(v___x_2925_, 1, v___f_2923_);
lean_ctor_set(v___x_2925_, 2, v___x_2922_);
lean_ctor_set(v___x_2925_, 3, v___f_2920_);
lean_ctor_set_uint8(v___x_2925_, sizeof(void*)*4, v___x_2921_);
lean_ctor_set_uint8(v___x_2925_, sizeof(void*)*4 + 1, v___x_2921_);
return v___x_2925_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig(void){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__1, &l_Lake_Package_buildCacheFacetConfig___closed__1_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__1);
return v___x_2926_;
}
}
lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0(lean_object* v_pkg_2928_, lean_object* v_dir_2929_, lean_object* v___x_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
uint8_t v_r_2939_; lean_object* v___y_2940_; lean_object* v_a_2944_; lean_object* v___x_2961_; 
lean_inc_ref(v_pkg_2928_);
v___x_2961_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_pkg_2928_, v___y_2935_, v___y_2936_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v_a_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_a_2962_);
v_a_2963_ = lean_ctor_get(v___x_2961_, 1);
lean_inc(v_a_2963_);
lean_dec_ref_known(v___x_2961_, 2);
v___x_2964_ = l_Lake_defaultLakeDir;
v___x_2965_ = l_Lake_joinRelative(v_dir_2929_, v___x_2964_);
v___x_2966_ = ((lean_object*)(l_Lake_Package_optBarrelFacetConfig___lam__0___closed__0));
v___x_2967_ = l_Lake_joinRelative(v___x_2965_, v___x_2966_);
v___x_2968_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_2928_, v_a_2962_, v___x_2967_, v___x_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v_a_2963_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; uint8_t v___x_2970_; 
v_a_2969_ = lean_ctor_get(v___x_2968_, 1);
lean_inc(v_a_2969_);
lean_dec_ref_known(v___x_2968_, 2);
v___x_2970_ = 1;
v_r_2939_ = v___x_2970_;
v___y_2940_ = v_a_2969_;
goto v___jp_2938_;
}
else
{
lean_object* v_a_2971_; 
v_a_2971_ = lean_ctor_get(v___x_2968_, 1);
lean_inc(v_a_2971_);
lean_dec_ref_known(v___x_2968_, 2);
v_a_2944_ = v_a_2971_;
goto v___jp_2943_;
}
}
else
{
lean_object* v_a_2972_; 
lean_dec_ref(v_dir_2929_);
lean_dec_ref(v_pkg_2928_);
v_a_2972_ = lean_ctor_get(v___x_2961_, 1);
lean_inc(v_a_2972_);
lean_dec_ref_known(v___x_2961_, 2);
v_a_2944_ = v_a_2972_;
goto v___jp_2943_;
}
v___jp_2938_:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = lean_box(v_r_2939_);
v___x_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
lean_ctor_set(v___x_2942_, 1, v___y_2940_);
return v___x_2942_;
}
v___jp_2943_:
{
lean_object* v_log_2945_; uint8_t v_action_2946_; uint8_t v_wantsRebuild_2947_; uint8_t v_canceled_2948_; lean_object* v_trace_2949_; lean_object* v_buildTime_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2960_; 
v_log_2945_ = lean_ctor_get(v_a_2944_, 0);
v_action_2946_ = lean_ctor_get_uint8(v_a_2944_, sizeof(void*)*3);
v_wantsRebuild_2947_ = lean_ctor_get_uint8(v_a_2944_, sizeof(void*)*3 + 1);
v_canceled_2948_ = lean_ctor_get_uint8(v_a_2944_, sizeof(void*)*3 + 2);
v_trace_2949_ = lean_ctor_get(v_a_2944_, 1);
v_buildTime_2950_ = lean_ctor_get(v_a_2944_, 2);
v_isSharedCheck_2960_ = !lean_is_exclusive(v_a_2944_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2952_ = v_a_2944_;
v_isShared_2953_ = v_isSharedCheck_2960_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_buildTime_2950_);
lean_inc(v_trace_2949_);
lean_inc(v_log_2945_);
lean_dec(v_a_2944_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2960_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
uint8_t v___x_2954_; uint8_t v___x_2955_; lean_object* v___x_2957_; 
v___x_2954_ = 4;
v___x_2955_ = l_Lake_JobAction_merge(v_action_2946_, v___x_2954_);
if (v_isShared_2953_ == 0)
{
v___x_2957_ = v___x_2952_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_log_2945_);
lean_ctor_set(v_reuseFailAlloc_2959_, 1, v_trace_2949_);
lean_ctor_set(v_reuseFailAlloc_2959_, 2, v_buildTime_2950_);
lean_ctor_set_uint8(v_reuseFailAlloc_2959_, sizeof(void*)*3 + 1, v_wantsRebuild_2947_);
lean_ctor_set_uint8(v_reuseFailAlloc_2959_, sizeof(void*)*3 + 2, v_canceled_2948_);
v___x_2957_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
uint8_t v___x_2958_; 
lean_ctor_set_uint8(v___x_2957_, sizeof(void*)*3, v___x_2955_);
v___x_2958_ = 0;
v_r_2939_ = v___x_2958_;
v___y_2940_ = v___x_2957_;
goto v___jp_2938_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_Package_optBarrelFacetConfig___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkg_2928_ = stack[0].m_obj;
lean_object* v_dir_2929_ = stack[1].m_obj;
lean_object* v___x_2930_ = stack[2].m_obj;
lean_object* v___y_2931_ = stack[3].m_obj;
lean_object* v___y_2932_ = stack[4].m_obj;
lean_object* v___y_2933_ = stack[5].m_obj;
lean_object* v___y_2934_ = stack[6].m_obj;
lean_object* v___y_2935_ = stack[7].m_obj;
lean_object* v___y_2936_ = stack[8].m_obj;
lean_object* v_res_2973_;
v_res_2973_ = l_Lake_Package_optBarrelFacetConfig___lam__0(v_pkg_2928_, v_dir_2929_, v___x_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
stack->m_obj
 = v_res_2973_;
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0___boxed(lean_object* v_pkg_2974_, lean_object* v_dir_2975_, lean_object* v___x_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l_Lake_Package_optBarrelFacetConfig___lam__0(v_pkg_2974_, v_dir_2975_, v___x_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec(v___y_2979_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec_ref(v___x_2976_);
return v_res_2984_;
}
}
lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1(lean_object* v___x_2985_, lean_object* v___f_2986_, lean_object* v___x_2987_, lean_object* v___x_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2996_ = l_Lake_Job_async___redArg(v___x_2985_, v___f_2986_, v___x_2987_, v___x_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_);
v___x_2997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
lean_ctor_set(v___x_2997_, 1, v___y_2994_);
return v___x_2997_;
}
}
LEAN_EXPORT void l_Lake_Package_optBarrelFacetConfig___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2985_ = stack[0].m_obj;
lean_object* v___f_2986_ = stack[1].m_obj;
lean_object* v___x_2987_ = stack[2].m_obj;
lean_object* v___x_2988_ = stack[3].m_obj;
lean_object* v___y_2989_ = stack[4].m_obj;
lean_object* v___y_2990_ = stack[5].m_obj;
lean_object* v___y_2991_ = stack[6].m_obj;
lean_object* v___y_2992_ = stack[7].m_obj;
lean_object* v___y_2993_ = stack[8].m_obj;
lean_object* v___y_2994_ = stack[9].m_obj;
lean_object* v_res_2998_;
v_res_2998_ = l_Lake_Package_optBarrelFacetConfig___lam__1(v___x_2985_, v___f_2986_, v___x_2987_, v___x_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_);
stack->m_obj
 = v_res_2998_;
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1___boxed(lean_object* v___x_2999_, lean_object* v___f_3000_, lean_object* v___x_3001_, lean_object* v___x_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Lake_Package_optBarrelFacetConfig___lam__1(v___x_2999_, v___f_3000_, v___x_3001_, v___x_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec(v___y_3005_);
lean_dec(v___y_3004_);
return v_res_3010_;
}
}
lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2(lean_object* v___x_3011_, lean_object* v___x_3012_, lean_object* v___x_3013_, lean_object* v_pkg_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v_baseName_3022_; lean_object* v_dir_3023_; lean_object* v___f_3024_; uint8_t v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___f_3034_; lean_object* v___x_3035_; 
v_baseName_3022_ = lean_ctor_get(v_pkg_3014_, 1);
lean_inc(v_baseName_3022_);
v_dir_3023_ = lean_ctor_get(v_pkg_3014_, 4);
lean_inc_ref(v_dir_3023_);
v___f_3024_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3024_, 0, v_pkg_3014_);
lean_closure_set(v___f_3024_, 1, v_dir_3023_);
lean_closure_set(v___f_3024_, 2, v___x_3011_);
v___x_3025_ = 1;
v___x_3026_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3022_, v___x_3025_);
v___x_3027_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3028_ = lean_string_append(v___x_3026_, v___x_3027_);
v___x_3029_ = l_Lake_Name_eraseHead(v___x_3012_);
v___x_3030_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3029_, v___x_3025_);
v___x_3031_ = lean_string_append(v___x_3028_, v___x_3030_);
lean_dec_ref(v___x_3030_);
v___x_3032_ = lean_unsigned_to_nat(0u);
v___x_3033_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_3013_);
v___f_3034_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_3034_, 0, v___x_3013_);
lean_closure_set(v___f_3034_, 1, v___f_3024_);
lean_closure_set(v___f_3034_, 2, v___x_3032_);
lean_closure_set(v___f_3034_, 3, v___x_3033_);
v___x_3035_ = l_Lake_ensureJob___redArg(v___x_3013_, v___f_3034_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3060_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
v_a_3037_ = lean_ctor_get(v___x_3035_, 1);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3039_ = v___x_3035_;
v_isShared_3040_ = v_isSharedCheck_3060_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_inc(v_a_3036_);
lean_dec(v___x_3035_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3060_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v_task_3041_; lean_object* v_kind_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3058_; 
v_task_3041_ = lean_ctor_get(v_a_3036_, 0);
v_kind_3042_ = lean_ctor_get(v_a_3036_, 1);
v_isSharedCheck_3058_ = !lean_is_exclusive(v_a_3036_);
if (v_isSharedCheck_3058_ == 0)
{
lean_object* v_unused_3059_; 
v_unused_3059_ = lean_ctor_get(v_a_3036_, 2);
lean_dec(v_unused_3059_);
v___x_3044_ = v_a_3036_;
v_isShared_3045_ = v_isSharedCheck_3058_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_kind_3042_);
lean_inc(v_task_3041_);
lean_dec(v_a_3036_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3058_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v_registeredJobs_3046_; lean_object* v_job_3048_; 
v_registeredJobs_3046_ = lean_ctor_get(v___y_3019_, 4);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 2, v___x_3031_);
v_job_3048_ = v___x_3044_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_task_3041_);
lean_ctor_set(v_reuseFailAlloc_3057_, 1, v_kind_3042_);
lean_ctor_set(v_reuseFailAlloc_3057_, 2, v___x_3031_);
v_job_3048_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3055_; 
lean_ctor_set_uint8(v_job_3048_, sizeof(void*)*3, v___x_3025_);
v___x_3049_ = lean_st_ref_take(v_registeredJobs_3046_);
lean_inc_ref(v_job_3048_);
v___x_3050_ = l_Lake_Job_toOpaque___redArg(v_job_3048_);
v___x_3051_ = lean_array_push(v___x_3049_, v___x_3050_);
v___x_3052_ = lean_st_ref_put(v_registeredJobs_3046_, v___x_3051_);
v___x_3053_ = l_Lake_Job_renew___redArg(v_job_3048_);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 0, v___x_3053_);
v___x_3055_ = v___x_3039_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v___x_3053_);
lean_ctor_set(v_reuseFailAlloc_3056_, 1, v_a_3037_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3031_);
return v___x_3035_;
}
}
}
LEAN_EXPORT void l_Lake_Package_optBarrelFacetConfig___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3011_ = stack[0].m_obj;
lean_object* v___x_3012_ = stack[1].m_obj;
lean_object* v___x_3013_ = stack[2].m_obj;
lean_object* v_pkg_3014_ = stack[3].m_obj;
lean_object* v___y_3015_ = stack[4].m_obj;
lean_object* v___y_3016_ = stack[5].m_obj;
lean_object* v___y_3017_ = stack[6].m_obj;
lean_object* v___y_3018_ = stack[7].m_obj;
lean_object* v___y_3019_ = stack[8].m_obj;
lean_object* v___y_3020_ = stack[9].m_obj;
lean_object* v_res_3061_;
v_res_3061_ = l_Lake_Package_optBarrelFacetConfig___lam__2(v___x_3011_, v___x_3012_, v___x_3013_, v_pkg_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
stack->m_obj
 = v_res_3061_;
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2___boxed(lean_object* v___x_3062_, lean_object* v___x_3063_, lean_object* v___x_3064_, lean_object* v_pkg_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l_Lake_Package_optBarrelFacetConfig___lam__2(v___x_3062_, v___x_3063_, v___x_3064_, v_pkg_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_);
lean_dec_ref(v___y_3070_);
lean_dec(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec(v___y_3067_);
return v_res_3073_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___f_3077_; 
v___x_3074_ = l_Lake_instDataKindBool;
v___x_3075_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_3076_ = l_Lake_Reservoir_lakeHeaders;
v___f_3077_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_3077_, 0, v___x_3076_);
lean_closure_set(v___f_3077_, 1, v___x_3075_);
lean_closure_set(v___f_3077_, 2, v___x_3074_);
return v___f_3077_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3078_; uint8_t v___x_3079_; lean_object* v___x_3080_; lean_object* v___f_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___f_3078_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_3079_ = 1;
v___x_3080_ = l_Lake_instDataKindBool;
v___f_3081_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__0, &l_Lake_Package_optBarrelFacetConfig___closed__0_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__0);
v___x_3082_ = l_Lake_Package_keyword;
v___x_3083_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3083_, 0, v___x_3082_);
lean_ctor_set(v___x_3083_, 1, v___f_3081_);
lean_ctor_set(v___x_3083_, 2, v___x_3080_);
lean_ctor_set(v___x_3083_, 3, v___f_3078_);
lean_ctor_set_uint8(v___x_3083_, sizeof(void*)*4, v___x_3079_);
lean_ctor_set_uint8(v___x_3083_, sizeof(void*)*4 + 1, v___x_3079_);
return v___x_3083_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig(void){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__1, &l_Lake_Package_optBarrelFacetConfig___closed__1_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__1);
return v___x_3084_;
}
}
lean_object* l_Lake_Package_barrelFacetConfig___lam__1(lean_object* v_baseName_3086_, lean_object* v___x_3087_, uint8_t v_success_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v_a_3097_; lean_object* v_a_3098_; 
if (v_success_3088_ == 0)
{
lean_object* v_toBuildConfig_3119_; uint8_t v_verbosity_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; uint8_t v___x_3124_; 
v_toBuildConfig_3119_ = lean_ctor_get(v___y_3093_, 0);
v_verbosity_3120_ = lean_ctor_get_uint8(v_toBuildConfig_3119_, sizeof(void*)*5 + 4);
v___x_3121_ = lean_box(v_verbosity_3120_);
v___x_3122_ = lean_obj_tag_nat(v___x_3121_);
lean_dec(v___x_3121_);
v___x_3123_ = lean_unsigned_to_nat(2u);
v___x_3124_ = lean_nat_dec_eq(v___x_3122_, v___x_3123_);
if (v___x_3124_ == 0)
{
lean_object* v___x_3125_; 
lean_dec(v___x_3087_);
lean_dec(v_baseName_3086_);
v___x_3125_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_3097_ = v___x_3125_;
v_a_3098_ = v___y_3094_;
goto v___jp_3096_;
}
else
{
lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3126_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_3127_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3086_, v___x_3124_);
v___x_3128_ = lean_string_append(v___x_3126_, v___x_3127_);
lean_dec_ref(v___x_3127_);
v___x_3129_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3130_ = lean_string_append(v___x_3128_, v___x_3129_);
v___x_3131_ = l_Lake_Name_eraseHead(v___x_3087_);
v___x_3132_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3131_, v___x_3124_);
v___x_3133_ = lean_string_append(v___x_3130_, v___x_3132_);
lean_dec_ref(v___x_3132_);
v___x_3134_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_3135_ = lean_string_append(v___x_3133_, v___x_3134_);
v_a_3097_ = v___x_3135_;
v_a_3098_ = v___y_3094_;
goto v___jp_3096_;
}
}
else
{
lean_object* v___x_3136_; lean_object* v___x_3137_; 
lean_dec(v___x_3087_);
lean_dec(v_baseName_3086_);
v___x_3136_ = lean_box(0);
v___x_3137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
lean_ctor_set(v___x_3137_, 1, v___y_3094_);
return v___x_3137_;
}
v___jp_3096_:
{
lean_object* v_log_3099_; uint8_t v_action_3100_; uint8_t v_wantsRebuild_3101_; uint8_t v_canceled_3102_; lean_object* v_trace_3103_; lean_object* v_buildTime_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3118_; 
v_log_3099_ = lean_ctor_get(v_a_3098_, 0);
v_action_3100_ = lean_ctor_get_uint8(v_a_3098_, sizeof(void*)*3);
v_wantsRebuild_3101_ = lean_ctor_get_uint8(v_a_3098_, sizeof(void*)*3 + 1);
v_canceled_3102_ = lean_ctor_get_uint8(v_a_3098_, sizeof(void*)*3 + 2);
v_trace_3103_ = lean_ctor_get(v_a_3098_, 1);
v_buildTime_3104_ = lean_ctor_get(v_a_3098_, 2);
v_isSharedCheck_3118_ = !lean_is_exclusive(v_a_3098_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3106_ = v_a_3098_;
v_isShared_3107_ = v_isSharedCheck_3118_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_buildTime_3104_);
lean_inc(v_trace_3103_);
lean_inc(v_log_3099_);
lean_dec(v_a_3098_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3118_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; uint8_t v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3115_; 
v___x_3108_ = ((lean_object*)(l_Lake_Package_barrelFacetConfig___lam__1___closed__0));
v___x_3109_ = lean_string_append(v___x_3108_, v_a_3097_);
lean_dec_ref(v_a_3097_);
v___x_3110_ = 3;
v___x_3111_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3111_, 0, v___x_3109_);
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*1, v___x_3110_);
v___x_3112_ = lean_array_get_size(v_log_3099_);
v___x_3113_ = lean_array_push(v_log_3099_, v___x_3111_);
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 0, v___x_3113_);
v___x_3115_ = v___x_3106_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3113_);
lean_ctor_set(v_reuseFailAlloc_3117_, 1, v_trace_3103_);
lean_ctor_set(v_reuseFailAlloc_3117_, 2, v_buildTime_3104_);
lean_ctor_set_uint8(v_reuseFailAlloc_3117_, sizeof(void*)*3, v_action_3100_);
lean_ctor_set_uint8(v_reuseFailAlloc_3117_, sizeof(void*)*3 + 1, v_wantsRebuild_3101_);
lean_ctor_set_uint8(v_reuseFailAlloc_3117_, sizeof(void*)*3 + 2, v_canceled_3102_);
v___x_3115_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
lean_object* v___x_3116_; 
v___x_3116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3112_);
lean_ctor_set(v___x_3116_, 1, v___x_3115_);
return v___x_3116_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_Package_barrelFacetConfig___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_baseName_3086_ = stack[0].m_obj;
lean_object* v___x_3087_ = stack[1].m_obj;
uint8_t v_success_3088_ = stack[2].m_num;
lean_object* v___y_3089_ = stack[3].m_obj;
lean_object* v___y_3090_ = stack[4].m_obj;
lean_object* v___y_3091_ = stack[5].m_obj;
lean_object* v___y_3092_ = stack[6].m_obj;
lean_object* v___y_3093_ = stack[7].m_obj;
lean_object* v___y_3094_ = stack[8].m_obj;
lean_object* v_res_3138_;
v_res_3138_ = l_Lake_Package_barrelFacetConfig___lam__1(v_baseName_3086_, v___x_3087_, v_success_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
stack->m_obj
 = v_res_3138_;
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1___boxed(lean_object* v_baseName_3139_, lean_object* v___x_3140_, lean_object* v_success_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
uint8_t v_success_boxed_3149_; lean_object* v_res_3150_; 
v_success_boxed_3149_ = lean_unbox(v_success_3141_);
v_res_3150_ = l_Lake_Package_barrelFacetConfig___lam__1(v_baseName_3139_, v___x_3140_, v_success_boxed_3149_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
return v_res_3150_;
}
}
lean_object* l_Lake_Package_barrelFacetConfig___lam__2(lean_object* v___x_3151_, lean_object* v___x_3152_, lean_object* v___x_3153_, lean_object* v_pkg_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
lean_object* v_baseName_3162_; lean_object* v_keyName_3163_; lean_object* v___f_3164_; uint8_t v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___f_3175_; uint8_t v___x_3176_; lean_object* v___x_3177_; 
v_baseName_3162_ = lean_ctor_get(v_pkg_3154_, 1);
v_keyName_3163_ = lean_ctor_get(v_pkg_3154_, 2);
lean_inc(v___x_3151_);
lean_inc_n(v_baseName_3162_, 2);
v___f_3164_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_3164_, 0, v_baseName_3162_);
lean_closure_set(v___f_3164_, 1, v___x_3151_);
v___x_3165_ = 1;
v___x_3166_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3162_, v___x_3165_);
v___x_3167_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3168_ = lean_string_append(v___x_3166_, v___x_3167_);
v___x_3169_ = l_Lake_Name_eraseHead(v___x_3152_);
v___x_3170_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3169_, v___x_3165_);
v___x_3171_ = lean_string_append(v___x_3168_, v___x_3170_);
lean_dec_ref(v___x_3170_);
lean_inc(v_keyName_3163_);
v___x_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3172_, 0, v_keyName_3163_);
v___x_3173_ = l_Lake_Package_keyword;
v___x_3174_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3172_);
lean_ctor_set(v___x_3174_, 1, v___x_3173_);
lean_ctor_set(v___x_3174_, 2, v_pkg_3154_);
lean_ctor_set(v___x_3174_, 3, v___x_3151_);
lean_inc(v___x_3153_);
v___f_3175_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3175_, 0, v___x_3174_);
lean_closure_set(v___f_3175_, 1, v___x_3153_);
lean_closure_set(v___f_3175_, 2, v___f_3164_);
v___x_3176_ = 0;
v___x_3177_ = l_Lake_ensureJob___redArg(v___x_3153_, v___f_3175_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3202_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
v_a_3179_ = lean_ctor_get(v___x_3177_, 1);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3181_ = v___x_3177_;
v_isShared_3182_ = v_isSharedCheck_3202_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_inc(v_a_3178_);
lean_dec(v___x_3177_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3202_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v_task_3183_; lean_object* v_kind_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3200_; 
v_task_3183_ = lean_ctor_get(v_a_3178_, 0);
v_kind_3184_ = lean_ctor_get(v_a_3178_, 1);
v_isSharedCheck_3200_ = !lean_is_exclusive(v_a_3178_);
if (v_isSharedCheck_3200_ == 0)
{
lean_object* v_unused_3201_; 
v_unused_3201_ = lean_ctor_get(v_a_3178_, 2);
lean_dec(v_unused_3201_);
v___x_3186_ = v_a_3178_;
v_isShared_3187_ = v_isSharedCheck_3200_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_kind_3184_);
lean_inc(v_task_3183_);
lean_dec(v_a_3178_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3200_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v_registeredJobs_3188_; lean_object* v_job_3190_; 
v_registeredJobs_3188_ = lean_ctor_get(v___y_3159_, 4);
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 2, v___x_3171_);
v_job_3190_ = v___x_3186_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_task_3183_);
lean_ctor_set(v_reuseFailAlloc_3199_, 1, v_kind_3184_);
lean_ctor_set(v_reuseFailAlloc_3199_, 2, v___x_3171_);
v_job_3190_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3197_; 
lean_ctor_set_uint8(v_job_3190_, sizeof(void*)*3, v___x_3176_);
v___x_3191_ = lean_st_ref_take(v_registeredJobs_3188_);
lean_inc_ref(v_job_3190_);
v___x_3192_ = l_Lake_Job_toOpaque___redArg(v_job_3190_);
v___x_3193_ = lean_array_push(v___x_3191_, v___x_3192_);
v___x_3194_ = lean_st_ref_put(v_registeredJobs_3188_, v___x_3193_);
v___x_3195_ = l_Lake_Job_renew___redArg(v_job_3190_);
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 0, v___x_3195_);
v___x_3197_ = v___x_3181_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3195_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v_a_3179_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3171_);
return v___x_3177_;
}
}
}
LEAN_EXPORT void l_Lake_Package_barrelFacetConfig___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3151_ = stack[0].m_obj;
lean_object* v___x_3152_ = stack[1].m_obj;
lean_object* v___x_3153_ = stack[2].m_obj;
lean_object* v_pkg_3154_ = stack[3].m_obj;
lean_object* v___y_3155_ = stack[4].m_obj;
lean_object* v___y_3156_ = stack[5].m_obj;
lean_object* v___y_3157_ = stack[6].m_obj;
lean_object* v___y_3158_ = stack[7].m_obj;
lean_object* v___y_3159_ = stack[8].m_obj;
lean_object* v___y_3160_ = stack[9].m_obj;
lean_object* v_res_3203_;
v_res_3203_ = l_Lake_Package_barrelFacetConfig___lam__2(v___x_3151_, v___x_3152_, v___x_3153_, v_pkg_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
stack->m_obj
 = v_res_3203_;
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2___boxed(lean_object* v___x_3204_, lean_object* v___x_3205_, lean_object* v___x_3206_, lean_object* v_pkg_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l_Lake_Package_barrelFacetConfig___lam__2(v___x_3204_, v___x_3205_, v___x_3206_, v_pkg_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec(v___y_3211_);
lean_dec(v___y_3210_);
lean_dec(v___y_3209_);
return v_res_3215_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___f_3219_; 
v___x_3216_ = l_Lake_instDataKindUnit;
v___x_3217_ = l_Lake_Package_reservoirBarrelFacet;
v___x_3218_ = l_Lake_Package_optReservoirBarrelFacet;
v___f_3219_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_3219_, 0, v___x_3218_);
lean_closure_set(v___f_3219_, 1, v___x_3217_);
lean_closure_set(v___f_3219_, 2, v___x_3216_);
return v___f_3219_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3220_; uint8_t v___x_3221_; lean_object* v___x_3222_; lean_object* v___f_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___f_3220_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_3221_ = 1;
v___x_3222_ = l_Lake_instDataKindUnit;
v___f_3223_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__0, &l_Lake_Package_barrelFacetConfig___closed__0_once, _init_l_Lake_Package_barrelFacetConfig___closed__0);
v___x_3224_ = l_Lake_Package_keyword;
v___x_3225_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3225_, 0, v___x_3224_);
lean_ctor_set(v___x_3225_, 1, v___f_3223_);
lean_ctor_set(v___x_3225_, 2, v___x_3222_);
lean_ctor_set(v___x_3225_, 3, v___f_3220_);
lean_ctor_set_uint8(v___x_3225_, sizeof(void*)*4, v___x_3221_);
lean_ctor_set_uint8(v___x_3225_, sizeof(void*)*4 + 1, v___x_3221_);
return v___x_3225_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig(void){
_start:
{
lean_object* v___x_3226_; 
v___x_3226_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__1, &l_Lake_Package_barrelFacetConfig___closed__1_once, _init_l_Lake_Package_barrelFacetConfig___closed__1);
return v___x_3226_;
}
}
lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(lean_object* v_pkg_3227_, lean_object* v_dir_3228_, lean_object* v_buildArchive_3229_, lean_object* v___x_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
uint8_t v_r_3239_; lean_object* v___y_3240_; lean_object* v_a_3244_; lean_object* v___x_3261_; 
lean_inc_ref(v_pkg_3227_);
v___x_3261_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_pkg_3227_, v___y_3236_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_object* v_a_3262_; lean_object* v_a_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v_a_3262_ = lean_ctor_get(v___x_3261_, 0);
lean_inc(v_a_3262_);
v_a_3263_ = lean_ctor_get(v___x_3261_, 1);
lean_inc(v_a_3263_);
lean_dec_ref_known(v___x_3261_, 2);
v___x_3264_ = l_Lake_defaultLakeDir;
v___x_3265_ = l_Lake_joinRelative(v_dir_3228_, v___x_3264_);
v___x_3266_ = l_Lake_joinRelative(v___x_3265_, v_buildArchive_3229_);
v___x_3267_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_3227_, v_a_3262_, v___x_3266_, v___x_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v_a_3263_);
if (lean_obj_tag(v___x_3267_) == 0)
{
lean_object* v_a_3268_; uint8_t v___x_3269_; 
v_a_3268_ = lean_ctor_get(v___x_3267_, 1);
lean_inc(v_a_3268_);
lean_dec_ref_known(v___x_3267_, 2);
v___x_3269_ = 1;
v_r_3239_ = v___x_3269_;
v___y_3240_ = v_a_3268_;
goto v___jp_3238_;
}
else
{
lean_object* v_a_3270_; 
v_a_3270_ = lean_ctor_get(v___x_3267_, 1);
lean_inc(v_a_3270_);
lean_dec_ref_known(v___x_3267_, 2);
v_a_3244_ = v_a_3270_;
goto v___jp_3243_;
}
}
else
{
lean_object* v_a_3271_; 
lean_dec_ref(v_buildArchive_3229_);
lean_dec_ref(v_dir_3228_);
lean_dec_ref(v_pkg_3227_);
v_a_3271_ = lean_ctor_get(v___x_3261_, 1);
lean_inc(v_a_3271_);
lean_dec_ref_known(v___x_3261_, 2);
v_a_3244_ = v_a_3271_;
goto v___jp_3243_;
}
v___jp_3238_:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3241_ = lean_box(v_r_3239_);
v___x_3242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3241_);
lean_ctor_set(v___x_3242_, 1, v___y_3240_);
return v___x_3242_;
}
v___jp_3243_:
{
lean_object* v_log_3245_; uint8_t v_action_3246_; uint8_t v_wantsRebuild_3247_; uint8_t v_canceled_3248_; lean_object* v_trace_3249_; lean_object* v_buildTime_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3260_; 
v_log_3245_ = lean_ctor_get(v_a_3244_, 0);
v_action_3246_ = lean_ctor_get_uint8(v_a_3244_, sizeof(void*)*3);
v_wantsRebuild_3247_ = lean_ctor_get_uint8(v_a_3244_, sizeof(void*)*3 + 1);
v_canceled_3248_ = lean_ctor_get_uint8(v_a_3244_, sizeof(void*)*3 + 2);
v_trace_3249_ = lean_ctor_get(v_a_3244_, 1);
v_buildTime_3250_ = lean_ctor_get(v_a_3244_, 2);
v_isSharedCheck_3260_ = !lean_is_exclusive(v_a_3244_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3252_ = v_a_3244_;
v_isShared_3253_ = v_isSharedCheck_3260_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_buildTime_3250_);
lean_inc(v_trace_3249_);
lean_inc(v_log_3245_);
lean_dec(v_a_3244_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3260_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
uint8_t v___x_3254_; uint8_t v___x_3255_; lean_object* v___x_3257_; 
v___x_3254_ = 4;
v___x_3255_ = l_Lake_JobAction_merge(v_action_3246_, v___x_3254_);
if (v_isShared_3253_ == 0)
{
v___x_3257_ = v___x_3252_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_log_3245_);
lean_ctor_set(v_reuseFailAlloc_3259_, 1, v_trace_3249_);
lean_ctor_set(v_reuseFailAlloc_3259_, 2, v_buildTime_3250_);
lean_ctor_set_uint8(v_reuseFailAlloc_3259_, sizeof(void*)*3 + 1, v_wantsRebuild_3247_);
lean_ctor_set_uint8(v_reuseFailAlloc_3259_, sizeof(void*)*3 + 2, v_canceled_3248_);
v___x_3257_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
uint8_t v___x_3258_; 
lean_ctor_set_uint8(v___x_3257_, sizeof(void*)*3, v___x_3255_);
v___x_3258_ = 0;
v_r_3239_ = v___x_3258_;
v___y_3240_ = v___x_3257_;
goto v___jp_3238_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_Package_optGitHubReleaseFacetConfig___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkg_3227_ = stack[0].m_obj;
lean_object* v_dir_3228_ = stack[1].m_obj;
lean_object* v_buildArchive_3229_ = stack[2].m_obj;
lean_object* v___x_3230_ = stack[3].m_obj;
lean_object* v___y_3231_ = stack[4].m_obj;
lean_object* v___y_3232_ = stack[5].m_obj;
lean_object* v___y_3233_ = stack[6].m_obj;
lean_object* v___y_3234_ = stack[7].m_obj;
lean_object* v___y_3235_ = stack[8].m_obj;
lean_object* v___y_3236_ = stack[9].m_obj;
lean_object* v_res_3272_;
v_res_3272_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(v_pkg_3227_, v_dir_3228_, v_buildArchive_3229_, v___x_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
stack->m_obj
 = v_res_3272_;
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed(lean_object* v_pkg_3273_, lean_object* v_dir_3274_, lean_object* v_buildArchive_3275_, lean_object* v___x_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(v_pkg_3273_, v_dir_3274_, v_buildArchive_3275_, v___x_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec_ref(v___x_3276_);
return v_res_3284_;
}
}
lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(lean_object* v___x_3285_, lean_object* v___x_3286_, lean_object* v___x_3287_, lean_object* v___x_3288_, lean_object* v_pkg_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
lean_object* v_baseName_3297_; lean_object* v_dir_3298_; lean_object* v_buildArchive_3299_; lean_object* v___f_3300_; uint8_t v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___f_3309_; lean_object* v___x_3310_; 
v_baseName_3297_ = lean_ctor_get(v_pkg_3289_, 1);
lean_inc(v_baseName_3297_);
v_dir_3298_ = lean_ctor_get(v_pkg_3289_, 4);
lean_inc_ref(v_dir_3298_);
v_buildArchive_3299_ = lean_ctor_get(v_pkg_3289_, 21);
lean_inc_ref(v_buildArchive_3299_);
v___f_3300_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed), 11, 4);
lean_closure_set(v___f_3300_, 0, v_pkg_3289_);
lean_closure_set(v___f_3300_, 1, v_dir_3298_);
lean_closure_set(v___f_3300_, 2, v_buildArchive_3299_);
lean_closure_set(v___f_3300_, 3, v___x_3285_);
v___x_3301_ = 1;
v___x_3302_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3297_, v___x_3301_);
v___x_3303_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3304_ = lean_string_append(v___x_3302_, v___x_3303_);
v___x_3305_ = l_Lake_Name_eraseHead(v___x_3286_);
v___x_3306_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3305_, v___x_3301_);
v___x_3307_ = lean_string_append(v___x_3304_, v___x_3306_);
lean_dec_ref(v___x_3306_);
v___x_3308_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_3287_);
v___f_3309_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_3309_, 0, v___x_3287_);
lean_closure_set(v___f_3309_, 1, v___f_3300_);
lean_closure_set(v___f_3309_, 2, v___x_3288_);
lean_closure_set(v___f_3309_, 3, v___x_3308_);
v___x_3310_ = l_Lake_ensureJob___redArg(v___x_3287_, v___f_3309_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_object* v_a_3311_; lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3335_; 
v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
v_a_3312_ = lean_ctor_get(v___x_3310_, 1);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3314_ = v___x_3310_;
v_isShared_3315_ = v_isSharedCheck_3335_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_inc(v_a_3311_);
lean_dec(v___x_3310_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3335_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v_task_3316_; lean_object* v_kind_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3333_; 
v_task_3316_ = lean_ctor_get(v_a_3311_, 0);
v_kind_3317_ = lean_ctor_get(v_a_3311_, 1);
v_isSharedCheck_3333_ = !lean_is_exclusive(v_a_3311_);
if (v_isSharedCheck_3333_ == 0)
{
lean_object* v_unused_3334_; 
v_unused_3334_ = lean_ctor_get(v_a_3311_, 2);
lean_dec(v_unused_3334_);
v___x_3319_ = v_a_3311_;
v_isShared_3320_ = v_isSharedCheck_3333_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_kind_3317_);
lean_inc(v_task_3316_);
lean_dec(v_a_3311_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3333_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v_registeredJobs_3321_; lean_object* v_job_3323_; 
v_registeredJobs_3321_ = lean_ctor_get(v___y_3294_, 4);
if (v_isShared_3320_ == 0)
{
lean_ctor_set(v___x_3319_, 2, v___x_3307_);
v_job_3323_ = v___x_3319_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_task_3316_);
lean_ctor_set(v_reuseFailAlloc_3332_, 1, v_kind_3317_);
lean_ctor_set(v_reuseFailAlloc_3332_, 2, v___x_3307_);
v_job_3323_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3330_; 
lean_ctor_set_uint8(v_job_3323_, sizeof(void*)*3, v___x_3301_);
v___x_3324_ = lean_st_ref_take(v_registeredJobs_3321_);
lean_inc_ref(v_job_3323_);
v___x_3325_ = l_Lake_Job_toOpaque___redArg(v_job_3323_);
v___x_3326_ = lean_array_push(v___x_3324_, v___x_3325_);
v___x_3327_ = lean_st_ref_put(v_registeredJobs_3321_, v___x_3326_);
v___x_3328_ = l_Lake_Job_renew___redArg(v_job_3323_);
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 0, v___x_3328_);
v___x_3330_ = v___x_3314_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v___x_3328_);
lean_ctor_set(v_reuseFailAlloc_3331_, 1, v_a_3312_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3307_);
return v___x_3310_;
}
}
}
LEAN_EXPORT void l_Lake_Package_optGitHubReleaseFacetConfig___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3285_ = stack[0].m_obj;
lean_object* v___x_3286_ = stack[1].m_obj;
lean_object* v___x_3287_ = stack[2].m_obj;
lean_object* v___x_3288_ = stack[3].m_obj;
lean_object* v_pkg_3289_ = stack[4].m_obj;
lean_object* v___y_3290_ = stack[5].m_obj;
lean_object* v___y_3291_ = stack[6].m_obj;
lean_object* v___y_3292_ = stack[7].m_obj;
lean_object* v___y_3293_ = stack[8].m_obj;
lean_object* v___y_3294_ = stack[9].m_obj;
lean_object* v___y_3295_ = stack[10].m_obj;
lean_object* v_res_3336_;
v_res_3336_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(v___x_3285_, v___x_3286_, v___x_3287_, v___x_3288_, v_pkg_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
stack->m_obj
 = v_res_3336_;
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_3337_, lean_object* v___x_3338_, lean_object* v___x_3339_, lean_object* v___x_3340_, lean_object* v_pkg_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
lean_object* v_res_3349_; 
v_res_3349_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(v___x_3337_, v___x_3338_, v___x_3339_, v___x_3340_, v_pkg_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec(v___y_3343_);
return v_res_3349_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___f_3356_; 
v___x_3352_ = lean_unsigned_to_nat(0u);
v___x_3353_ = l_Lake_instDataKindBool;
v___x_3354_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_3355_ = ((lean_object*)(l_Lake_Package_optGitHubReleaseFacetConfig___closed__0));
v___f_3356_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed), 12, 4);
lean_closure_set(v___f_3356_, 0, v___x_3355_);
lean_closure_set(v___f_3356_, 1, v___x_3354_);
lean_closure_set(v___f_3356_, 2, v___x_3353_);
lean_closure_set(v___f_3356_, 3, v___x_3352_);
return v___f_3356_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_3357_; uint8_t v___x_3358_; lean_object* v___x_3359_; lean_object* v___f_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___f_3357_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_3358_ = 1;
v___x_3359_ = l_Lake_instDataKindBool;
v___f_3360_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__1, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1);
v___x_3361_ = l_Lake_Package_keyword;
v___x_3362_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3362_, 0, v___x_3361_);
lean_ctor_set(v___x_3362_, 1, v___f_3360_);
lean_ctor_set(v___x_3362_, 2, v___x_3359_);
lean_ctor_set(v___x_3362_, 3, v___f_3357_);
lean_ctor_set_uint8(v___x_3362_, sizeof(void*)*4, v___x_3358_);
lean_ctor_set_uint8(v___x_3362_, sizeof(void*)*4 + 1, v___x_3358_);
return v___x_3362_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_3363_; 
v___x_3363_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__2, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__2_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2);
return v___x_3363_;
}
}
lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1(lean_object* v_baseName_3365_, lean_object* v___x_3366_, uint8_t v_success_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_){
_start:
{
lean_object* v_a_3376_; lean_object* v_a_3377_; 
if (v_success_3367_ == 0)
{
lean_object* v_toBuildConfig_3398_; uint8_t v_verbosity_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; uint8_t v___x_3403_; 
v_toBuildConfig_3398_ = lean_ctor_get(v___y_3372_, 0);
v_verbosity_3399_ = lean_ctor_get_uint8(v_toBuildConfig_3398_, sizeof(void*)*5 + 4);
v___x_3400_ = lean_box(v_verbosity_3399_);
v___x_3401_ = lean_obj_tag_nat(v___x_3400_);
lean_dec(v___x_3400_);
v___x_3402_ = lean_unsigned_to_nat(2u);
v___x_3403_ = lean_nat_dec_eq(v___x_3401_, v___x_3402_);
if (v___x_3403_ == 0)
{
lean_object* v___x_3404_; 
lean_dec(v___x_3366_);
lean_dec(v_baseName_3365_);
v___x_3404_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_3376_ = v___x_3404_;
v_a_3377_ = v___y_3373_;
goto v___jp_3375_;
}
else
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3405_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_3406_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3365_, v___x_3403_);
v___x_3407_ = lean_string_append(v___x_3405_, v___x_3406_);
lean_dec_ref(v___x_3406_);
v___x_3408_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3409_ = lean_string_append(v___x_3407_, v___x_3408_);
v___x_3410_ = l_Lake_Name_eraseHead(v___x_3366_);
v___x_3411_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3410_, v___x_3403_);
v___x_3412_ = lean_string_append(v___x_3409_, v___x_3411_);
lean_dec_ref(v___x_3411_);
v___x_3413_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_3414_ = lean_string_append(v___x_3412_, v___x_3413_);
v_a_3376_ = v___x_3414_;
v_a_3377_ = v___y_3373_;
goto v___jp_3375_;
}
}
else
{
lean_object* v___x_3415_; lean_object* v___x_3416_; 
lean_dec(v___x_3366_);
lean_dec(v_baseName_3365_);
v___x_3415_ = lean_box(0);
v___x_3416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3415_);
lean_ctor_set(v___x_3416_, 1, v___y_3373_);
return v___x_3416_;
}
v___jp_3375_:
{
lean_object* v_log_3378_; uint8_t v_action_3379_; uint8_t v_wantsRebuild_3380_; uint8_t v_canceled_3381_; lean_object* v_trace_3382_; lean_object* v_buildTime_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3397_; 
v_log_3378_ = lean_ctor_get(v_a_3377_, 0);
v_action_3379_ = lean_ctor_get_uint8(v_a_3377_, sizeof(void*)*3);
v_wantsRebuild_3380_ = lean_ctor_get_uint8(v_a_3377_, sizeof(void*)*3 + 1);
v_canceled_3381_ = lean_ctor_get_uint8(v_a_3377_, sizeof(void*)*3 + 2);
v_trace_3382_ = lean_ctor_get(v_a_3377_, 1);
v_buildTime_3383_ = lean_ctor_get(v_a_3377_, 2);
v_isSharedCheck_3397_ = !lean_is_exclusive(v_a_3377_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3385_ = v_a_3377_;
v_isShared_3386_ = v_isSharedCheck_3397_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_buildTime_3383_);
lean_inc(v_trace_3382_);
lean_inc(v_log_3378_);
lean_dec(v_a_3377_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3397_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; uint8_t v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3394_; 
v___x_3387_ = ((lean_object*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0));
v___x_3388_ = lean_string_append(v___x_3387_, v_a_3376_);
lean_dec_ref(v_a_3376_);
v___x_3389_ = 3;
v___x_3390_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3390_, 0, v___x_3388_);
lean_ctor_set_uint8(v___x_3390_, sizeof(void*)*1, v___x_3389_);
v___x_3391_ = lean_array_get_size(v_log_3378_);
v___x_3392_ = lean_array_push(v_log_3378_, v___x_3390_);
if (v_isShared_3386_ == 0)
{
lean_ctor_set(v___x_3385_, 0, v___x_3392_);
v___x_3394_ = v___x_3385_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3392_);
lean_ctor_set(v_reuseFailAlloc_3396_, 1, v_trace_3382_);
lean_ctor_set(v_reuseFailAlloc_3396_, 2, v_buildTime_3383_);
lean_ctor_set_uint8(v_reuseFailAlloc_3396_, sizeof(void*)*3, v_action_3379_);
lean_ctor_set_uint8(v_reuseFailAlloc_3396_, sizeof(void*)*3 + 1, v_wantsRebuild_3380_);
lean_ctor_set_uint8(v_reuseFailAlloc_3396_, sizeof(void*)*3 + 2, v_canceled_3381_);
v___x_3394_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
lean_object* v___x_3395_; 
v___x_3395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3391_);
lean_ctor_set(v___x_3395_, 1, v___x_3394_);
return v___x_3395_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_Package_gitHubReleaseFacetConfig___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_baseName_3365_ = stack[0].m_obj;
lean_object* v___x_3366_ = stack[1].m_obj;
uint8_t v_success_3367_ = stack[2].m_num;
lean_object* v___y_3368_ = stack[3].m_obj;
lean_object* v___y_3369_ = stack[4].m_obj;
lean_object* v___y_3370_ = stack[5].m_obj;
lean_object* v___y_3371_ = stack[6].m_obj;
lean_object* v___y_3372_ = stack[7].m_obj;
lean_object* v___y_3373_ = stack[8].m_obj;
lean_object* v_res_3417_;
v_res_3417_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__1(v_baseName_3365_, v___x_3366_, v_success_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
stack->m_obj
 = v_res_3417_;
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed(lean_object* v_baseName_3418_, lean_object* v___x_3419_, lean_object* v_success_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
uint8_t v_success_boxed_3428_; lean_object* v_res_3429_; 
v_success_boxed_3428_ = lean_unbox(v_success_3420_);
v_res_3429_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__1(v_baseName_3418_, v___x_3419_, v_success_boxed_3428_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
return v_res_3429_;
}
}
lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2(lean_object* v___x_3430_, lean_object* v___x_3431_, lean_object* v___x_3432_, lean_object* v_pkg_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_){
_start:
{
lean_object* v_baseName_3441_; lean_object* v_keyName_3442_; lean_object* v___f_3443_; uint8_t v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___f_3454_; uint8_t v___x_3455_; lean_object* v___x_3456_; 
v_baseName_3441_ = lean_ctor_get(v_pkg_3433_, 1);
v_keyName_3442_ = lean_ctor_get(v_pkg_3433_, 2);
lean_inc(v___x_3430_);
lean_inc_n(v_baseName_3441_, 2);
v___f_3443_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_3443_, 0, v_baseName_3441_);
lean_closure_set(v___f_3443_, 1, v___x_3430_);
v___x_3444_ = 1;
v___x_3445_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3441_, v___x_3444_);
v___x_3446_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3447_ = lean_string_append(v___x_3445_, v___x_3446_);
v___x_3448_ = l_Lake_Name_eraseHead(v___x_3431_);
v___x_3449_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3448_, v___x_3444_);
v___x_3450_ = lean_string_append(v___x_3447_, v___x_3449_);
lean_dec_ref(v___x_3449_);
lean_inc(v_keyName_3442_);
v___x_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3451_, 0, v_keyName_3442_);
v___x_3452_ = l_Lake_Package_keyword;
v___x_3453_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3451_);
lean_ctor_set(v___x_3453_, 1, v___x_3452_);
lean_ctor_set(v___x_3453_, 2, v_pkg_3433_);
lean_ctor_set(v___x_3453_, 3, v___x_3430_);
lean_inc(v___x_3432_);
v___f_3454_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3454_, 0, v___x_3453_);
lean_closure_set(v___f_3454_, 1, v___x_3432_);
lean_closure_set(v___f_3454_, 2, v___f_3443_);
v___x_3455_ = 0;
v___x_3456_ = l_Lake_ensureJob___redArg(v___x_3432_, v___f_3454_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3481_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
v_a_3458_ = lean_ctor_get(v___x_3456_, 1);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3460_ = v___x_3456_;
v_isShared_3461_ = v_isSharedCheck_3481_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_inc(v_a_3457_);
lean_dec(v___x_3456_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3481_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v_task_3462_; lean_object* v_kind_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3479_; 
v_task_3462_ = lean_ctor_get(v_a_3457_, 0);
v_kind_3463_ = lean_ctor_get(v_a_3457_, 1);
v_isSharedCheck_3479_ = !lean_is_exclusive(v_a_3457_);
if (v_isSharedCheck_3479_ == 0)
{
lean_object* v_unused_3480_; 
v_unused_3480_ = lean_ctor_get(v_a_3457_, 2);
lean_dec(v_unused_3480_);
v___x_3465_ = v_a_3457_;
v_isShared_3466_ = v_isSharedCheck_3479_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_kind_3463_);
lean_inc(v_task_3462_);
lean_dec(v_a_3457_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3479_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v_registeredJobs_3467_; lean_object* v_job_3469_; 
v_registeredJobs_3467_ = lean_ctor_get(v___y_3438_, 4);
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 2, v___x_3450_);
v_job_3469_ = v___x_3465_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_task_3462_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v_kind_3463_);
lean_ctor_set(v_reuseFailAlloc_3478_, 2, v___x_3450_);
v_job_3469_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3476_; 
lean_ctor_set_uint8(v_job_3469_, sizeof(void*)*3, v___x_3455_);
v___x_3470_ = lean_st_ref_take(v_registeredJobs_3467_);
lean_inc_ref(v_job_3469_);
v___x_3471_ = l_Lake_Job_toOpaque___redArg(v_job_3469_);
v___x_3472_ = lean_array_push(v___x_3470_, v___x_3471_);
v___x_3473_ = lean_st_ref_put(v_registeredJobs_3467_, v___x_3472_);
v___x_3474_ = l_Lake_Job_renew___redArg(v_job_3469_);
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 0, v___x_3474_);
v___x_3476_ = v___x_3460_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v___x_3474_);
lean_ctor_set(v_reuseFailAlloc_3477_, 1, v_a_3458_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3450_);
return v___x_3456_;
}
}
}
LEAN_EXPORT void l_Lake_Package_gitHubReleaseFacetConfig___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3430_ = stack[0].m_obj;
lean_object* v___x_3431_ = stack[1].m_obj;
lean_object* v___x_3432_ = stack[2].m_obj;
lean_object* v_pkg_3433_ = stack[3].m_obj;
lean_object* v___y_3434_ = stack[4].m_obj;
lean_object* v___y_3435_ = stack[5].m_obj;
lean_object* v___y_3436_ = stack[6].m_obj;
lean_object* v___y_3437_ = stack[7].m_obj;
lean_object* v___y_3438_ = stack[8].m_obj;
lean_object* v___y_3439_ = stack[9].m_obj;
lean_object* v_res_3482_;
v_res_3482_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__2(v___x_3430_, v___x_3431_, v___x_3432_, v_pkg_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
stack->m_obj
 = v_res_3482_;
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_3483_, lean_object* v___x_3484_, lean_object* v___x_3485_, lean_object* v_pkg_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__2(v___x_3483_, v___x_3484_, v___x_3485_, v_pkg_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec(v___y_3488_);
return v_res_3494_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___f_3498_; 
v___x_3495_ = l_Lake_instDataKindUnit;
v___x_3496_ = l_Lake_Package_gitHubReleaseFacet;
v___x_3497_ = l_Lake_Package_optGitHubReleaseFacet;
v___f_3498_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_3498_, 0, v___x_3497_);
lean_closure_set(v___f_3498_, 1, v___x_3496_);
lean_closure_set(v___f_3498_, 2, v___x_3495_);
return v___f_3498_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3499_; uint8_t v___x_3500_; lean_object* v___x_3501_; lean_object* v___f_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___f_3499_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_3500_ = 1;
v___x_3501_ = l_Lake_instDataKindUnit;
v___f_3502_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__0, &l_Lake_Package_gitHubReleaseFacetConfig___closed__0_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0);
v___x_3503_ = l_Lake_Package_keyword;
v___x_3504_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3504_, 0, v___x_3503_);
lean_ctor_set(v___x_3504_, 1, v___f_3502_);
lean_ctor_set(v___x_3504_, 2, v___x_3501_);
lean_ctor_set(v___x_3504_, 3, v___f_3499_);
lean_ctor_set_uint8(v___x_3504_, sizeof(void*)*4, v___x_3500_);
lean_ctor_set_uint8(v___x_3504_, sizeof(void*)*4 + 1, v___x_3500_);
return v___x_3504_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_3505_; 
v___x_3505_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__1, &l_Lake_Package_gitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1);
return v___x_3505_;
}
}
lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(lean_object* v_build_3506_, uint8_t v_x_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
lean_object* v_log_3515_; uint8_t v_action_3516_; uint8_t v_wantsRebuild_3517_; uint8_t v_canceled_3518_; lean_object* v_buildTime_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3528_; 
v_log_3515_ = lean_ctor_get(v___y_3513_, 0);
v_action_3516_ = lean_ctor_get_uint8(v___y_3513_, sizeof(void*)*3);
v_wantsRebuild_3517_ = lean_ctor_get_uint8(v___y_3513_, sizeof(void*)*3 + 1);
v_canceled_3518_ = lean_ctor_get_uint8(v___y_3513_, sizeof(void*)*3 + 2);
v_buildTime_3519_ = lean_ctor_get(v___y_3513_, 2);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___y_3513_);
if (v_isSharedCheck_3528_ == 0)
{
lean_object* v_unused_3529_; 
v_unused_3529_ = lean_ctor_get(v___y_3513_, 1);
lean_dec(v_unused_3529_);
v___x_3521_ = v___y_3513_;
v_isShared_3522_ = v_isSharedCheck_3528_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_buildTime_3519_);
lean_inc(v_log_3515_);
lean_dec(v___y_3513_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3528_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3523_; lean_object* v___x_3525_; 
v___x_3523_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 1, v___x_3523_);
v___x_3525_ = v___x_3521_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_log_3515_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v___x_3523_);
lean_ctor_set(v_reuseFailAlloc_3527_, 2, v_buildTime_3519_);
lean_ctor_set_uint8(v_reuseFailAlloc_3527_, sizeof(void*)*3, v_action_3516_);
lean_ctor_set_uint8(v_reuseFailAlloc_3527_, sizeof(void*)*3 + 1, v_wantsRebuild_3517_);
lean_ctor_set_uint8(v_reuseFailAlloc_3527_, sizeof(void*)*3 + 2, v_canceled_3518_);
v___x_3525_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
lean_object* v___x_3526_; 
lean_inc_ref(v___y_3512_);
lean_inc(v___y_3511_);
lean_inc(v___y_3510_);
lean_inc(v___y_3509_);
v___x_3526_ = lean_apply_7(v_build_3506_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___x_3525_, lean_box(0));
return v___x_3526_;
}
}
}
}
LEAN_EXPORT void l_Lake_Package_afterBuildCacheAsync___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_build_3506_ = stack[0].m_obj;
uint8_t v_x_3507_ = stack[1].m_num;
lean_object* v___y_3508_ = stack[2].m_obj;
lean_object* v___y_3509_ = stack[3].m_obj;
lean_object* v___y_3510_ = stack[4].m_obj;
lean_object* v___y_3511_ = stack[5].m_obj;
lean_object* v___y_3512_ = stack[6].m_obj;
lean_object* v___y_3513_ = stack[7].m_obj;
lean_object* v_res_3530_;
v_res_3530_ = l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(v_build_3506_, v_x_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
stack->m_obj
 = v_res_3530_;
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed(lean_object* v_build_3531_, lean_object* v_x_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
uint8_t v_x_1627__boxed_3540_; lean_object* v_res_3541_; 
v_x_1627__boxed_3540_ = lean_unbox(v_x_3532_);
v_res_3541_ = l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(v_build_3531_, v_x_1627__boxed_3540_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec(v___y_3535_);
lean_dec(v___y_3534_);
return v_res_3541_;
}
}
lean_object* l_Lake_Package_afterBuildCacheAsync___redArg(lean_object* v_self_3542_, lean_object* v_build_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_){
_start:
{
lean_object* v_wsIdx_3551_; lean_object* v___x_3552_; uint8_t v___x_3553_; 
v_wsIdx_3551_ = lean_ctor_get(v_self_3542_, 0);
v___x_3552_ = lean_unsigned_to_nat(0u);
v___x_3553_ = lean_nat_dec_eq(v_wsIdx_3551_, v___x_3552_);
if (v___x_3553_ == 0)
{
lean_object* v___f_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___f_3554_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3554_, 0, v_build_3543_);
v___x_3555_ = lean_box(0);
lean_inc_ref(v_a_3544_);
v___x_3556_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_3542_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v_a_3557_; lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3567_; 
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
v_a_3558_ = lean_ctor_get(v___x_3556_, 1);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3560_ = v___x_3556_;
v_isShared_3561_ = v_isSharedCheck_3567_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_inc(v_a_3557_);
lean_dec(v___x_3556_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3567_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3565_; 
v___x_3562_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3563_ = l_Lake_Job_bindM___redArg(v___x_3555_, v_a_3557_, v___f_3554_, v___x_3552_, v___x_3553_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v___x_3562_);
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 0, v___x_3563_);
v___x_3565_ = v___x_3560_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v___x_3563_);
lean_ctor_set(v_reuseFailAlloc_3566_, 1, v_a_3558_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
}
else
{
lean_object* v_a_3568_; lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec_ref(v___f_3554_);
lean_dec_ref(v_a_3544_);
v_a_3568_ = lean_ctor_get(v___x_3556_, 0);
v_a_3569_ = lean_ctor_get(v___x_3556_, 1);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3556_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_inc(v_a_3568_);
lean_dec(v___x_3556_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3568_);
lean_ctor_set(v_reuseFailAlloc_3575_, 1, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
else
{
uint8_t v___x_3577_; uint8_t v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
lean_dec_ref(v_self_3542_);
v___x_3577_ = 0;
v___x_3578_ = 0;
v___x_3579_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3580_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3580_, 0, v_a_3549_);
lean_ctor_set(v___x_3580_, 1, v___x_3579_);
lean_ctor_set(v___x_3580_, 2, v___x_3552_);
lean_ctor_set_uint8(v___x_3580_, sizeof(void*)*3, v___x_3577_);
lean_ctor_set_uint8(v___x_3580_, sizeof(void*)*3 + 1, v___x_3578_);
lean_ctor_set_uint8(v___x_3580_, sizeof(void*)*3 + 2, v___x_3578_);
lean_inc_ref(v_a_3548_);
lean_inc(v_a_3547_);
lean_inc(v_a_3546_);
lean_inc(v_a_3545_);
v___x_3581_ = lean_apply_7(v_build_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v___x_3580_, lean_box(0));
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3591_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 1);
v_a_3583_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3585_ = v___x_3581_;
v_isShared_3586_ = v_isSharedCheck_3591_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3582_);
lean_inc(v_a_3583_);
lean_dec(v___x_3581_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3591_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v_log_3587_; lean_object* v___x_3589_; 
v_log_3587_ = lean_ctor_get(v_a_3582_, 0);
lean_inc_ref(v_log_3587_);
lean_dec(v_a_3582_);
if (v_isShared_3586_ == 0)
{
lean_ctor_set(v___x_3585_, 1, v_log_3587_);
v___x_3589_ = v___x_3585_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3583_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_log_3587_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
else
{
lean_object* v_a_3592_; lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3601_; 
v_a_3592_ = lean_ctor_get(v___x_3581_, 1);
v_a_3593_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3595_ = v___x_3581_;
v_isShared_3596_ = v_isSharedCheck_3601_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_a_3592_);
lean_inc(v_a_3593_);
lean_dec(v___x_3581_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3601_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v_log_3597_; lean_object* v___x_3599_; 
v_log_3597_ = lean_ctor_get(v_a_3592_, 0);
lean_inc_ref(v_log_3597_);
lean_dec(v_a_3592_);
if (v_isShared_3596_ == 0)
{
lean_ctor_set(v___x_3595_, 1, v_log_3597_);
v___x_3599_ = v___x_3595_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3593_);
lean_ctor_set(v_reuseFailAlloc_3600_, 1, v_log_3597_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_Package_afterBuildCacheAsync___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_3542_ = stack[0].m_obj;
lean_object* v_build_3543_ = stack[1].m_obj;
lean_object* v_a_3544_ = stack[2].m_obj;
lean_object* v_a_3545_ = stack[3].m_obj;
lean_object* v_a_3546_ = stack[4].m_obj;
lean_object* v_a_3547_ = stack[5].m_obj;
lean_object* v_a_3548_ = stack[6].m_obj;
lean_object* v_a_3549_ = stack[7].m_obj;
lean_object* v_res_3602_;
v_res_3602_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_3542_, v_build_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_);
stack->m_obj
 = v_res_3602_;
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___boxed(lean_object* v_self_3603_, lean_object* v_build_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_3603_, v_build_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_);
lean_dec_ref(v_a_3609_);
lean_dec(v_a_3608_);
lean_dec(v_a_3607_);
lean_dec(v_a_3606_);
return v_res_3612_;
}
}
lean_object* l_Lake_Package_afterBuildCacheAsync(lean_object* v_00_u03b1_3613_, lean_object* v_self_3614_, lean_object* v_build_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_){
_start:
{
lean_object* v___x_3623_; 
v___x_3623_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_3614_, v_build_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_);
return v___x_3623_;
}
}
LEAN_EXPORT void l_Lake_Package_afterBuildCacheAsync_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_3614_ = stack[1].m_obj;
lean_object* v_build_3615_ = stack[2].m_obj;
lean_object* v_a_3616_ = stack[3].m_obj;
lean_object* v_a_3617_ = stack[4].m_obj;
lean_object* v_a_3618_ = stack[5].m_obj;
lean_object* v_a_3619_ = stack[6].m_obj;
lean_object* v_a_3620_ = stack[7].m_obj;
lean_object* v_a_3621_ = stack[8].m_obj;
lean_object* v_res_3624_;
v_res_3624_ = l_Lake_Package_afterBuildCacheAsync(lean_box(0), v_self_3614_, v_build_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_);
stack->m_obj
 = v_res_3624_;
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___boxed(lean_object* v_00_u03b1_3625_, lean_object* v_self_3626_, lean_object* v_build_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l_Lake_Package_afterBuildCacheAsync(v_00_u03b1_3625_, v_self_3626_, v_build_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_);
lean_dec_ref(v_a_3632_);
lean_dec(v_a_3631_);
lean_dec(v_a_3630_);
lean_dec(v_a_3629_);
return v_res_3635_;
}
}
lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0(lean_object* v_build_3636_, uint8_t v_x_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
lean_object* v_log_3645_; uint8_t v_action_3646_; uint8_t v_wantsRebuild_3647_; uint8_t v_canceled_3648_; lean_object* v_buildTime_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3658_; 
v_log_3645_ = lean_ctor_get(v___y_3643_, 0);
v_action_3646_ = lean_ctor_get_uint8(v___y_3643_, sizeof(void*)*3);
v_wantsRebuild_3647_ = lean_ctor_get_uint8(v___y_3643_, sizeof(void*)*3 + 1);
v_canceled_3648_ = lean_ctor_get_uint8(v___y_3643_, sizeof(void*)*3 + 2);
v_buildTime_3649_ = lean_ctor_get(v___y_3643_, 2);
v_isSharedCheck_3658_ = !lean_is_exclusive(v___y_3643_);
if (v_isSharedCheck_3658_ == 0)
{
lean_object* v_unused_3659_; 
v_unused_3659_ = lean_ctor_get(v___y_3643_, 1);
lean_dec(v_unused_3659_);
v___x_3651_ = v___y_3643_;
v_isShared_3652_ = v_isSharedCheck_3658_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_buildTime_3649_);
lean_inc(v_log_3645_);
lean_dec(v___y_3643_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3658_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3653_; lean_object* v___x_3655_; 
v___x_3653_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 1, v___x_3653_);
v___x_3655_ = v___x_3651_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_log_3645_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v___x_3653_);
lean_ctor_set(v_reuseFailAlloc_3657_, 2, v_buildTime_3649_);
lean_ctor_set_uint8(v_reuseFailAlloc_3657_, sizeof(void*)*3, v_action_3646_);
lean_ctor_set_uint8(v_reuseFailAlloc_3657_, sizeof(void*)*3 + 1, v_wantsRebuild_3647_);
lean_ctor_set_uint8(v_reuseFailAlloc_3657_, sizeof(void*)*3 + 2, v_canceled_3648_);
v___x_3655_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
lean_object* v___x_3656_; 
lean_inc_ref(v___y_3642_);
lean_inc(v___y_3641_);
lean_inc(v___y_3640_);
lean_inc(v___y_3639_);
v___x_3656_ = lean_apply_7(v_build_3636_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___x_3655_, lean_box(0));
return v___x_3656_;
}
}
}
}
LEAN_EXPORT void l_Lake_Package_afterBuildCacheSync___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_build_3636_ = stack[0].m_obj;
uint8_t v_x_3637_ = stack[1].m_num;
lean_object* v___y_3638_ = stack[2].m_obj;
lean_object* v___y_3639_ = stack[3].m_obj;
lean_object* v___y_3640_ = stack[4].m_obj;
lean_object* v___y_3641_ = stack[5].m_obj;
lean_object* v___y_3642_ = stack[6].m_obj;
lean_object* v___y_3643_ = stack[7].m_obj;
lean_object* v_res_3660_;
v_res_3660_ = l_Lake_Package_afterBuildCacheSync___redArg___lam__0(v_build_3636_, v_x_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_);
stack->m_obj
 = v_res_3660_;
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed(lean_object* v_build_3661_, lean_object* v_x_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
uint8_t v_x_1657__boxed_3670_; lean_object* v_res_3671_; 
v_x_1657__boxed_3670_ = lean_unbox(v_x_3662_);
v_res_3671_ = l_Lake_Package_afterBuildCacheSync___redArg___lam__0(v_build_3661_, v_x_1657__boxed_3670_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v___y_3666_);
lean_dec(v___y_3665_);
lean_dec(v___y_3664_);
return v_res_3671_;
}
}
lean_object* l_Lake_Package_afterBuildCacheSync___redArg(lean_object* v_self_3672_, lean_object* v_build_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_){
_start:
{
lean_object* v_wsIdx_3681_; lean_object* v___x_3682_; uint8_t v___x_3683_; lean_object* v___x_3684_; 
v_wsIdx_3681_ = lean_ctor_get(v_self_3672_, 0);
v___x_3682_ = lean_unsigned_to_nat(0u);
v___x_3683_ = lean_nat_dec_eq(v_wsIdx_3681_, v___x_3682_);
v___x_3684_ = lean_box(0);
if (v___x_3683_ == 0)
{
lean_object* v___f_3685_; lean_object* v___x_3686_; 
v___f_3685_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3685_, 0, v_build_3673_);
lean_inc_ref(v_a_3674_);
v___x_3686_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_3672_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3697_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
v_a_3688_ = lean_ctor_get(v___x_3686_, 1);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3690_ = v___x_3686_;
v_isShared_3691_ = v_isSharedCheck_3697_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_inc(v_a_3687_);
lean_dec(v___x_3686_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3697_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3695_; 
v___x_3692_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3693_ = l_Lake_Job_mapM___redArg(v___x_3684_, v_a_3687_, v___f_3685_, v___x_3682_, v___x_3683_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v___x_3692_);
if (v_isShared_3691_ == 0)
{
lean_ctor_set(v___x_3690_, 0, v___x_3693_);
v___x_3695_ = v___x_3690_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3693_);
lean_ctor_set(v_reuseFailAlloc_3696_, 1, v_a_3688_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
else
{
lean_object* v_a_3698_; lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
lean_dec_ref(v___f_3685_);
lean_dec_ref(v_a_3674_);
v_a_3698_ = lean_ctor_get(v___x_3686_, 0);
v_a_3699_ = lean_ctor_get(v___x_3686_, 1);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3686_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_inc(v_a_3698_);
lean_dec(v___x_3686_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3698_);
lean_ctor_set(v_reuseFailAlloc_3705_, 1, v_a_3699_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
}
else
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
lean_dec_ref(v_self_3672_);
v___x_3707_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_3708_ = l_Lake_Job_async___redArg(v___x_3684_, v_build_3673_, v___x_3682_, v___x_3707_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_);
v___x_3709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3708_);
lean_ctor_set(v___x_3709_, 1, v_a_3679_);
return v___x_3709_;
}
}
}
LEAN_EXPORT void l_Lake_Package_afterBuildCacheSync___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_3672_ = stack[0].m_obj;
lean_object* v_build_3673_ = stack[1].m_obj;
lean_object* v_a_3674_ = stack[2].m_obj;
lean_object* v_a_3675_ = stack[3].m_obj;
lean_object* v_a_3676_ = stack[4].m_obj;
lean_object* v_a_3677_ = stack[5].m_obj;
lean_object* v_a_3678_ = stack[6].m_obj;
lean_object* v_a_3679_ = stack[7].m_obj;
lean_object* v_res_3710_;
v_res_3710_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3672_, v_build_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_);
stack->m_obj
 = v_res_3710_;
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___boxed(lean_object* v_self_3711_, lean_object* v_build_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3711_, v_build_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_);
lean_dec_ref(v_a_3717_);
lean_dec(v_a_3716_);
lean_dec(v_a_3715_);
lean_dec(v_a_3714_);
return v_res_3720_;
}
}
lean_object* l_Lake_Package_afterBuildCacheSync(lean_object* v_00_u03b1_3721_, lean_object* v_self_3722_, lean_object* v_build_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_){
_start:
{
lean_object* v___x_3731_; 
v___x_3731_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3722_, v_build_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_);
return v___x_3731_;
}
}
LEAN_EXPORT void l_Lake_Package_afterBuildCacheSync_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_3722_ = stack[1].m_obj;
lean_object* v_build_3723_ = stack[2].m_obj;
lean_object* v_a_3724_ = stack[3].m_obj;
lean_object* v_a_3725_ = stack[4].m_obj;
lean_object* v_a_3726_ = stack[5].m_obj;
lean_object* v_a_3727_ = stack[6].m_obj;
lean_object* v_a_3728_ = stack[7].m_obj;
lean_object* v_a_3729_ = stack[8].m_obj;
lean_object* v_res_3732_;
v_res_3732_ = l_Lake_Package_afterBuildCacheSync(lean_box(0), v_self_3722_, v_build_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_);
stack->m_obj
 = v_res_3732_;
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___boxed(lean_object* v_00_u03b1_3733_, lean_object* v_self_3734_, lean_object* v_build_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_){
_start:
{
lean_object* v_res_3743_; 
v_res_3743_ = l_Lake_Package_afterBuildCacheSync(v_00_u03b1_3733_, v_self_3734_, v_build_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_);
lean_dec_ref(v_a_3740_);
lean_dec(v_a_3739_);
lean_dec(v_a_3738_);
lean_dec(v_a_3737_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(lean_object* v_k_3744_, lean_object* v_v_3745_, lean_object* v_t_3746_){
_start:
{
if (lean_obj_tag(v_t_3746_) == 0)
{
lean_object* v_size_3747_; lean_object* v_k_3748_; lean_object* v_v_3749_; lean_object* v_l_3750_; lean_object* v_r_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_4031_; 
v_size_3747_ = lean_ctor_get(v_t_3746_, 0);
v_k_3748_ = lean_ctor_get(v_t_3746_, 1);
v_v_3749_ = lean_ctor_get(v_t_3746_, 2);
v_l_3750_ = lean_ctor_get(v_t_3746_, 3);
v_r_3751_ = lean_ctor_get(v_t_3746_, 4);
v_isSharedCheck_4031_ = !lean_is_exclusive(v_t_3746_);
if (v_isSharedCheck_4031_ == 0)
{
v___x_3753_ = v_t_3746_;
v_isShared_3754_ = v_isSharedCheck_4031_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_r_3751_);
lean_inc(v_l_3750_);
lean_inc(v_v_3749_);
lean_inc(v_k_3748_);
lean_inc(v_size_3747_);
lean_dec(v_t_3746_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_4031_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
uint8_t v___x_3755_; 
v___x_3755_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3744_, v_k_3748_);
switch(v___x_3755_)
{
case 0:
{
lean_object* v_impl_3756_; lean_object* v___x_3757_; 
lean_dec(v_size_3747_);
v_impl_3756_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3744_, v_v_3745_, v_l_3750_);
v___x_3757_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3751_) == 0)
{
lean_object* v_size_3758_; lean_object* v_size_3759_; lean_object* v_k_3760_; lean_object* v_v_3761_; lean_object* v_l_3762_; lean_object* v_r_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; uint8_t v___x_3766_; 
v_size_3758_ = lean_ctor_get(v_r_3751_, 0);
v_size_3759_ = lean_ctor_get(v_impl_3756_, 0);
v_k_3760_ = lean_ctor_get(v_impl_3756_, 1);
v_v_3761_ = lean_ctor_get(v_impl_3756_, 2);
v_l_3762_ = lean_ctor_get(v_impl_3756_, 3);
v_r_3763_ = lean_ctor_get(v_impl_3756_, 4);
lean_inc(v_r_3763_);
v___x_3764_ = lean_unsigned_to_nat(3u);
v___x_3765_ = lean_nat_mul(v___x_3764_, v_size_3758_);
v___x_3766_ = lean_nat_dec_lt(v___x_3765_, v_size_3759_);
lean_dec(v___x_3765_);
if (v___x_3766_ == 0)
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3770_; 
lean_dec(v_r_3763_);
v___x_3767_ = lean_nat_add(v___x_3757_, v_size_3759_);
v___x_3768_ = lean_nat_add(v___x_3767_, v_size_3758_);
lean_dec(v___x_3767_);
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 3, v_impl_3756_);
lean_ctor_set(v___x_3753_, 0, v___x_3768_);
v___x_3770_ = v___x_3753_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3768_);
lean_ctor_set(v_reuseFailAlloc_3771_, 1, v_k_3748_);
lean_ctor_set(v_reuseFailAlloc_3771_, 2, v_v_3749_);
lean_ctor_set(v_reuseFailAlloc_3771_, 3, v_impl_3756_);
lean_ctor_set(v_reuseFailAlloc_3771_, 4, v_r_3751_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
else
{
lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3837_; 
lean_inc(v_l_3762_);
lean_inc(v_v_3761_);
lean_inc(v_k_3760_);
lean_inc(v_size_3759_);
v_isSharedCheck_3837_ = !lean_is_exclusive(v_impl_3756_);
if (v_isSharedCheck_3837_ == 0)
{
lean_object* v_unused_3838_; lean_object* v_unused_3839_; lean_object* v_unused_3840_; lean_object* v_unused_3841_; lean_object* v_unused_3842_; 
v_unused_3838_ = lean_ctor_get(v_impl_3756_, 4);
lean_dec(v_unused_3838_);
v_unused_3839_ = lean_ctor_get(v_impl_3756_, 3);
lean_dec(v_unused_3839_);
v_unused_3840_ = lean_ctor_get(v_impl_3756_, 2);
lean_dec(v_unused_3840_);
v_unused_3841_ = lean_ctor_get(v_impl_3756_, 1);
lean_dec(v_unused_3841_);
v_unused_3842_ = lean_ctor_get(v_impl_3756_, 0);
lean_dec(v_unused_3842_);
v___x_3773_ = v_impl_3756_;
v_isShared_3774_ = v_isSharedCheck_3837_;
goto v_resetjp_3772_;
}
else
{
lean_dec(v_impl_3756_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3837_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v_size_3775_; lean_object* v_size_3776_; lean_object* v_k_3777_; lean_object* v_v_3778_; lean_object* v_l_3779_; lean_object* v_r_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; uint8_t v___x_3783_; 
v_size_3775_ = lean_ctor_get(v_l_3762_, 0);
v_size_3776_ = lean_ctor_get(v_r_3763_, 0);
v_k_3777_ = lean_ctor_get(v_r_3763_, 1);
v_v_3778_ = lean_ctor_get(v_r_3763_, 2);
v_l_3779_ = lean_ctor_get(v_r_3763_, 3);
v_r_3780_ = lean_ctor_get(v_r_3763_, 4);
v___x_3781_ = lean_unsigned_to_nat(2u);
v___x_3782_ = lean_nat_mul(v___x_3781_, v_size_3775_);
v___x_3783_ = lean_nat_dec_lt(v_size_3776_, v___x_3782_);
lean_dec(v___x_3782_);
if (v___x_3783_ == 0)
{
lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3812_; 
lean_inc(v_r_3780_);
lean_inc(v_l_3779_);
lean_inc(v_v_3778_);
lean_inc(v_k_3777_);
v_isSharedCheck_3812_ = !lean_is_exclusive(v_r_3763_);
if (v_isSharedCheck_3812_ == 0)
{
lean_object* v_unused_3813_; lean_object* v_unused_3814_; lean_object* v_unused_3815_; lean_object* v_unused_3816_; lean_object* v_unused_3817_; 
v_unused_3813_ = lean_ctor_get(v_r_3763_, 4);
lean_dec(v_unused_3813_);
v_unused_3814_ = lean_ctor_get(v_r_3763_, 3);
lean_dec(v_unused_3814_);
v_unused_3815_ = lean_ctor_get(v_r_3763_, 2);
lean_dec(v_unused_3815_);
v_unused_3816_ = lean_ctor_get(v_r_3763_, 1);
lean_dec(v_unused_3816_);
v_unused_3817_ = lean_ctor_get(v_r_3763_, 0);
lean_dec(v_unused_3817_);
v___x_3785_ = v_r_3763_;
v_isShared_3786_ = v_isSharedCheck_3812_;
goto v_resetjp_3784_;
}
else
{
lean_dec(v_r_3763_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3812_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___x_3800_; lean_object* v___y_3802_; 
v___x_3787_ = lean_nat_add(v___x_3757_, v_size_3759_);
lean_dec(v_size_3759_);
v___x_3788_ = lean_nat_add(v___x_3787_, v_size_3758_);
lean_dec(v___x_3787_);
v___x_3800_ = lean_nat_add(v___x_3757_, v_size_3775_);
if (lean_obj_tag(v_l_3779_) == 0)
{
lean_object* v_size_3810_; 
v_size_3810_ = lean_ctor_get(v_l_3779_, 0);
lean_inc(v_size_3810_);
v___y_3802_ = v_size_3810_;
goto v___jp_3801_;
}
else
{
lean_object* v___x_3811_; 
v___x_3811_ = lean_unsigned_to_nat(0u);
v___y_3802_ = v___x_3811_;
goto v___jp_3801_;
}
v___jp_3789_:
{
lean_object* v___x_3793_; lean_object* v___x_3795_; 
v___x_3793_ = lean_nat_add(v___y_3791_, v___y_3792_);
lean_dec(v___y_3792_);
lean_dec(v___y_3791_);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 4, v_r_3751_);
lean_ctor_set(v___x_3785_, 3, v_r_3780_);
lean_ctor_set(v___x_3785_, 2, v_v_3749_);
lean_ctor_set(v___x_3785_, 1, v_k_3748_);
lean_ctor_set(v___x_3785_, 0, v___x_3793_);
v___x_3795_ = v___x_3785_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3793_);
lean_ctor_set(v_reuseFailAlloc_3799_, 1, v_k_3748_);
lean_ctor_set(v_reuseFailAlloc_3799_, 2, v_v_3749_);
lean_ctor_set(v_reuseFailAlloc_3799_, 3, v_r_3780_);
lean_ctor_set(v_reuseFailAlloc_3799_, 4, v_r_3751_);
v___x_3795_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
lean_object* v___x_3797_; 
if (v_isShared_3774_ == 0)
{
lean_ctor_set(v___x_3773_, 4, v___x_3795_);
lean_ctor_set(v___x_3773_, 3, v___y_3790_);
lean_ctor_set(v___x_3773_, 2, v_v_3778_);
lean_ctor_set(v___x_3773_, 1, v_k_3777_);
lean_ctor_set(v___x_3773_, 0, v___x_3788_);
v___x_3797_ = v___x_3773_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3788_);
lean_ctor_set(v_reuseFailAlloc_3798_, 1, v_k_3777_);
lean_ctor_set(v_reuseFailAlloc_3798_, 2, v_v_3778_);
lean_ctor_set(v_reuseFailAlloc_3798_, 3, v___y_3790_);
lean_ctor_set(v_reuseFailAlloc_3798_, 4, v___x_3795_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
v___jp_3801_:
{
lean_object* v___x_3803_; lean_object* v___x_3805_; 
v___x_3803_ = lean_nat_add(v___x_3800_, v___y_3802_);
lean_dec(v___y_3802_);
lean_dec(v___x_3800_);
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 4, v_l_3779_);
lean_ctor_set(v___x_3753_, 3, v_l_3762_);
lean_ctor_set(v___x_3753_, 2, v_v_3761_);
lean_ctor_set(v___x_3753_, 1, v_k_3760_);
lean_ctor_set(v___x_3753_, 0, v___x_3803_);
v___x_3805_ = v___x_3753_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3803_);
lean_ctor_set(v_reuseFailAlloc_3809_, 1, v_k_3760_);
lean_ctor_set(v_reuseFailAlloc_3809_, 2, v_v_3761_);
lean_ctor_set(v_reuseFailAlloc_3809_, 3, v_l_3762_);
lean_ctor_set(v_reuseFailAlloc_3809_, 4, v_l_3779_);
v___x_3805_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
lean_object* v___x_3806_; 
v___x_3806_ = lean_nat_add(v___x_3757_, v_size_3758_);
if (lean_obj_tag(v_r_3780_) == 0)
{
lean_object* v_size_3807_; 
v_size_3807_ = lean_ctor_get(v_r_3780_, 0);
lean_inc(v_size_3807_);
v___y_3790_ = v___x_3805_;
v___y_3791_ = v___x_3806_;
v___y_3792_ = v_size_3807_;
goto v___jp_3789_;
}
else
{
lean_object* v___x_3808_; 
v___x_3808_ = lean_unsigned_to_nat(0u);
v___y_3790_ = v___x_3805_;
v___y_3791_ = v___x_3806_;
v___y_3792_ = v___x_3808_;
goto v___jp_3789_;
}
}
}
}
}
else
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3823_; 
lean_del_object(v___x_3753_);
v___x_3818_ = lean_nat_add(v___x_3757_, v_size_3759_);
lean_dec(v_size_3759_);
v___x_3819_ = lean_nat_add(v___x_3818_, v_size_3758_);
lean_dec(v___x_3818_);
v___x_3820_ = lean_nat_add(v___x_3757_, v_size_3758_);
v___x_3821_ = lean_nat_add(v___x_3820_, v_size_3776_);
lean_dec(v___x_3820_);
lean_inc_ref(v_r_3751_);
if (v_isShared_3774_ == 0)
{
lean_ctor_set(v___x_3773_, 4, v_r_3751_);
lean_ctor_set(v___x_3773_, 3, v_r_3763_);
lean_ctor_set(v___x_3773_, 2, v_v_3749_);
lean_ctor_set(v___x_3773_, 1, v_k_3748_);
lean_ctor_set(v___x_3773_, 0, v___x_3821_);
v___x_3823_ = v___x_3773_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3821_);
lean_ctor_set(v_reuseFailAlloc_3836_, 1, v_k_3748_);
lean_ctor_set(v_reuseFailAlloc_3836_, 2, v_v_3749_);
lean_ctor_set(v_reuseFailAlloc_3836_, 3, v_r_3763_);
lean_ctor_set(v_reuseFailAlloc_3836_, 4, v_r_3751_);
v___x_3823_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
v_isSharedCheck_3830_ = !lean_is_exclusive(v_r_3751_);
if (v_isSharedCheck_3830_ == 0)
{
lean_object* v_unused_3831_; lean_object* v_unused_3832_; lean_object* v_unused_3833_; lean_object* v_unused_3834_; lean_object* v_unused_3835_; 
v_unused_3831_ = lean_ctor_get(v_r_3751_, 4);
lean_dec(v_unused_3831_);
v_unused_3832_ = lean_ctor_get(v_r_3751_, 3);
lean_dec(v_unused_3832_);
v_unused_3833_ = lean_ctor_get(v_r_3751_, 2);
lean_dec(v_unused_3833_);
v_unused_3834_ = lean_ctor_get(v_r_3751_, 1);
lean_dec(v_unused_3834_);
v_unused_3835_ = lean_ctor_get(v_r_3751_, 0);
lean_dec(v_unused_3835_);
v___x_3825_ = v_r_3751_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_dec(v_r_3751_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 4, v___x_3823_);
lean_ctor_set(v___x_3825_, 3, v_l_3762_);
lean_ctor_set(v___x_3825_, 2, v_v_3761_);
lean_ctor_set(v___x_3825_, 1, v_k_3760_);
lean_ctor_set(v___x_3825_, 0, v___x_3819_);
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v___x_3819_);
lean_ctor_set(v_reuseFailAlloc_3829_, 1, v_k_3760_);
lean_ctor_set(v_reuseFailAlloc_3829_, 2, v_v_3761_);
lean_ctor_set(v_reuseFailAlloc_3829_, 3, v_l_3762_);
lean_ctor_set(v_reuseFailAlloc_3829_, 4, v___x_3823_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3843_; 
v_l_3843_ = lean_ctor_get(v_impl_3756_, 3);
if (lean_obj_tag(v_l_3843_) == 0)
{
lean_object* v_r_3844_; lean_object* v_k_3845_; lean_object* v_v_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3857_; 
lean_inc_ref(v_l_3843_);
v_r_3844_ = lean_ctor_get(v_impl_3756_, 4);
v_k_3845_ = lean_ctor_get(v_impl_3756_, 1);
v_v_3846_ = lean_ctor_get(v_impl_3756_, 2);
v_isSharedCheck_3857_ = !lean_is_exclusive(v_impl_3756_);
if (v_isSharedCheck_3857_ == 0)
{
lean_object* v_unused_3858_; lean_object* v_unused_3859_; 
v_unused_3858_ = lean_ctor_get(v_impl_3756_, 3);
lean_dec(v_unused_3858_);
v_unused_3859_ = lean_ctor_get(v_impl_3756_, 0);
lean_dec(v_unused_3859_);
v___x_3848_ = v_impl_3756_;
v_isShared_3849_ = v_isSharedCheck_3857_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_r_3844_);
lean_inc(v_v_3846_);
lean_inc(v_k_3845_);
lean_dec(v_impl_3756_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3857_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3850_; lean_object* v___x_3852_; 
v___x_3850_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3844_);
if (v_isShared_3849_ == 0)
{
lean_ctor_set(v___x_3848_, 3, v_r_3844_);
lean_ctor_set(v___x_3848_, 2, v_v_3749_);
lean_ctor_set(v___x_3848_, 1, v_k_3748_);
lean_ctor_set(v___x_3848_, 0, v___x_3757_);
v___x_3852_ = v___x_3848_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3757_);
lean_ctor_set(v_reuseFailAlloc_3856_, 1, v_k_3748_);
lean_ctor_set(v_reuseFailAlloc_3856_, 2, v_v_3749_);
lean_ctor_set(v_reuseFailAlloc_3856_, 3, v_r_3844_);
lean_ctor_set(v_reuseFailAlloc_3856_, 4, v_r_3844_);
v___x_3852_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
lean_object* v___x_3854_; 
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 4, v___x_3852_);
lean_ctor_set(v___x_3753_, 3, v_l_3843_);
lean_ctor_set(v___x_3753_, 2, v_v_3846_);
lean_ctor_set(v___x_3753_, 1, v_k_3845_);
lean_ctor_set(v___x_3753_, 0, v___x_3850_);
v___x_3854_ = v___x_3753_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v___x_3850_);
lean_ctor_set(v_reuseFailAlloc_3855_, 1, v_k_3845_);
lean_ctor_set(v_reuseFailAlloc_3855_, 2, v_v_3846_);
lean_ctor_set(v_reuseFailAlloc_3855_, 3, v_l_3843_);
lean_ctor_set(v_reuseFailAlloc_3855_, 4, v___x_3852_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
else
{
lean_object* v_r_3860_; 
v_r_3860_ = lean_ctor_get(v_impl_3756_, 4);
lean_inc(v_r_3860_);
if (lean_obj_tag(v_r_3860_) == 0)
{
lean_object* v_k_3861_; lean_object* v_v_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3885_; 
lean_inc(v_l_3843_);
v_k_3861_ = lean_ctor_get(v_impl_3756_, 1);
v_v_3862_ = lean_ctor_get(v_impl_3756_, 2);
v_isSharedCheck_3885_ = !lean_is_exclusive(v_impl_3756_);
if (v_isSharedCheck_3885_ == 0)
{
lean_object* v_unused_3886_; lean_object* v_unused_3887_; lean_object* v_unused_3888_; 
v_unused_3886_ = lean_ctor_get(v_impl_3756_, 4);
lean_dec(v_unused_3886_);
v_unused_3887_ = lean_ctor_get(v_impl_3756_, 3);
lean_dec(v_unused_3887_);
v_unused_3888_ = lean_ctor_get(v_impl_3756_, 0);
lean_dec(v_unused_3888_);
v___x_3864_ = v_impl_3756_;
v_isShared_3865_ = v_isSharedCheck_3885_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_v_3862_);
lean_inc(v_k_3861_);
lean_dec(v_impl_3756_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3885_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v_k_3866_; lean_object* v_v_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3881_; 
v_k_3866_ = lean_ctor_get(v_r_3860_, 1);
v_v_3867_ = lean_ctor_get(v_r_3860_, 2);
v_isSharedCheck_3881_ = !lean_is_exclusive(v_r_3860_);
if (v_isSharedCheck_3881_ == 0)
{
lean_object* v_unused_3882_; lean_object* v_unused_3883_; lean_object* v_unused_3884_; 
v_unused_3882_ = lean_ctor_get(v_r_3860_, 4);
lean_dec(v_unused_3882_);
v_unused_3883_ = lean_ctor_get(v_r_3860_, 3);
lean_dec(v_unused_3883_);
v_unused_3884_ = lean_ctor_get(v_r_3860_, 0);
lean_dec(v_unused_3884_);
v___x_3869_ = v_r_3860_;
v_isShared_3870_ = v_isSharedCheck_3881_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_v_3867_);
lean_inc(v_k_3866_);
lean_dec(v_r_3860_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3881_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v___x_3871_; lean_object* v___x_3873_; 
v___x_3871_ = lean_unsigned_to_nat(3u);
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 4, v_l_3843_);
lean_ctor_set(v___x_3869_, 3, v_l_3843_);
lean_ctor_set(v___x_3869_, 2, v_v_3862_);
lean_ctor_set(v___x_3869_, 1, v_k_3861_);
lean_ctor_set(v___x_3869_, 0, v___x_3757_);
v___x_3873_ = v___x_3869_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3757_);
lean_ctor_set(v_reuseFailAlloc_3880_, 1, v_k_3861_);
lean_ctor_set(v_reuseFailAlloc_3880_, 2, v_v_3862_);
lean_ctor_set(v_reuseFailAlloc_3880_, 3, v_l_3843_);
lean_ctor_set(v_reuseFailAlloc_3880_, 4, v_l_3843_);
v___x_3873_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
lean_object* v___x_3875_; 
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 4, v_l_3843_);
lean_ctor_set(v___x_3864_, 2, v_v_3749_);
lean_ctor_set(v___x_3864_, 1, v_k_3748_);
lean_ctor_set(v___x_3864_, 0, v___x_3757_);
v___x_3875_ = v___x_3864_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___x_3757_);
lean_ctor_set(v_reuseFailAlloc_3879_, 1, v_k_3748_);
lean_ctor_set(v_reuseFailAlloc_3879_, 2, v_v_3749_);
lean_ctor_set(v_reuseFailAlloc_3879_, 3, v_l_3843_);
lean_ctor_set(v_reuseFailAlloc_3879_, 4, v_l_3843_);
v___x_3875_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
lean_object* v___x_3877_; 
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 4, v___x_3875_);
lean_ctor_set(v___x_3753_, 3, v___x_3873_);
lean_ctor_set(v___x_3753_, 2, v_v_3867_);
lean_ctor_set(v___x_3753_, 1, v_k_3866_);
lean_ctor_set(v___x_3753_, 0, v___x_3871_);
v___x_3877_ = v___x_3753_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v___x_3871_);
lean_ctor_set(v_reuseFailAlloc_3878_, 1, v_k_3866_);
lean_ctor_set(v_reuseFailAlloc_3878_, 2, v_v_3867_);
lean_ctor_set(v_reuseFailAlloc_3878_, 3, v___x_3873_);
lean_ctor_set(v_reuseFailAlloc_3878_, 4, v___x_3875_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
}
}
}
else
{
lean_object* v___x_3889_; lean_object* v___x_3891_; 
v___x_3889_ = lean_unsigned_to_nat(2u);
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 4, v_r_3860_);
lean_ctor_set(v___x_3753_, 3, v_impl_3756_);
lean_ctor_set(v___x_3753_, 0, v___x_3889_);
v___x_3891_ = v___x_3753_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v___x_3889_);
lean_ctor_set(v_reuseFailAlloc_3892_, 1, v_k_3748_);
lean_ctor_set(v_reuseFailAlloc_3892_, 2, v_v_3749_);
lean_ctor_set(v_reuseFailAlloc_3892_, 3, v_impl_3756_);
lean_ctor_set(v_reuseFailAlloc_3892_, 4, v_r_3860_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3894_; 
lean_dec(v_v_3749_);
lean_dec(v_k_3748_);
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 2, v_v_3745_);
lean_ctor_set(v___x_3753_, 1, v_k_3744_);
v___x_3894_ = v___x_3753_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_size_3747_);
lean_ctor_set(v_reuseFailAlloc_3895_, 1, v_k_3744_);
lean_ctor_set(v_reuseFailAlloc_3895_, 2, v_v_3745_);
lean_ctor_set(v_reuseFailAlloc_3895_, 3, v_l_3750_);
lean_ctor_set(v_reuseFailAlloc_3895_, 4, v_r_3751_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
default: 
{
lean_object* v_impl_3896_; lean_object* v___x_3897_; 
lean_dec(v_size_3747_);
v_impl_3896_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3744_, v_v_3745_, v_r_3751_);
v___x_3897_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3750_) == 0)
{
lean_object* v_size_3898_; lean_object* v_size_3899_; lean_object* v_k_3900_; lean_object* v_v_3901_; lean_object* v_l_3902_; lean_object* v_r_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; uint8_t v___x_3906_; 
v_size_3898_ = lean_ctor_get(v_l_3750_, 0);
v_size_3899_ = lean_ctor_get(v_impl_3896_, 0);
v_k_3900_ = lean_ctor_get(v_impl_3896_, 1);
v_v_3901_ = lean_ctor_get(v_impl_3896_, 2);
v_l_3902_ = lean_ctor_get(v_impl_3896_, 3);
lean_inc(v_l_3902_);
v_r_3903_ = lean_ctor_get(v_impl_3896_, 4);
v___x_3904_ = lean_unsigned_to_nat(3u);
v___x_3905_ = lean_nat_mul(v___x_3904_, v_size_3898_);
v___x_3906_ = lean_nat_dec_lt(v___x_3905_, v_size_3899_);
lean_dec(v___x_3905_);
if (v___x_3906_ == 0)
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3910_; 
lean_dec(v_l_3902_);
v___x_3907_ = lean_nat_add(v___x_3897_, v_size_3898_);
v___x_3908_ = lean_nat_add(v___x_3907_, v_size_3899_);
lean_dec(v___x_3907_);
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 4, v_impl_3896_);
lean_ctor_set(v___x_3753_, 0, v___x_3908_);
v___x_3910_ = v___x_3753_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3908_);
lean_ctor_set(v_reuseFailAlloc_3911_, 1, v_k_3748_);
lean_ctor_set(v_reuseFailAlloc_3911_, 2, v_v_3749_);
lean_ctor_set(v_reuseFailAlloc_3911_, 3, v_l_3750_);
lean_ctor_set(v_reuseFailAlloc_3911_, 4, v_impl_3896_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
else
{
lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3975_; 
lean_inc(v_r_3903_);
lean_inc(v_v_3901_);
lean_inc(v_k_3900_);
lean_inc(v_size_3899_);
v_isSharedCheck_3975_ = !lean_is_exclusive(v_impl_3896_);
if (v_isSharedCheck_3975_ == 0)
{
lean_object* v_unused_3976_; lean_object* v_unused_3977_; lean_object* v_unused_3978_; lean_object* v_unused_3979_; lean_object* v_unused_3980_; 
v_unused_3976_ = lean_ctor_get(v_impl_3896_, 4);
lean_dec(v_unused_3976_);
v_unused_3977_ = lean_ctor_get(v_impl_3896_, 3);
lean_dec(v_unused_3977_);
v_unused_3978_ = lean_ctor_get(v_impl_3896_, 2);
lean_dec(v_unused_3978_);
v_unused_3979_ = lean_ctor_get(v_impl_3896_, 1);
lean_dec(v_unused_3979_);
v_unused_3980_ = lean_ctor_get(v_impl_3896_, 0);
lean_dec(v_unused_3980_);
v___x_3913_ = v_impl_3896_;
v_isShared_3914_ = v_isSharedCheck_3975_;
goto v_resetjp_3912_;
}
else
{
lean_dec(v_impl_3896_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3975_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v_size_3915_; lean_object* v_k_3916_; lean_object* v_v_3917_; lean_object* v_l_3918_; lean_object* v_r_3919_; lean_object* v_size_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; uint8_t v___x_3923_; 
v_size_3915_ = lean_ctor_get(v_l_3902_, 0);
v_k_3916_ = lean_ctor_get(v_l_3902_, 1);
v_v_3917_ = lean_ctor_get(v_l_3902_, 2);
v_l_3918_ = lean_ctor_get(v_l_3902_, 3);
v_r_3919_ = lean_ctor_get(v_l_3902_, 4);
v_size_3920_ = lean_ctor_get(v_r_3903_, 0);
v___x_3921_ = lean_unsigned_to_nat(2u);
v___x_3922_ = lean_nat_mul(v___x_3921_, v_size_3920_);
v___x_3923_ = lean_nat_dec_lt(v_size_3915_, v___x_3922_);
lean_dec(v___x_3922_);
if (v___x_3923_ == 0)
{
lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3951_; 
lean_inc(v_r_3919_);
lean_inc(v_l_3918_);
lean_inc(v_v_3917_);
lean_inc(v_k_3916_);
v_isSharedCheck_3951_ = !lean_is_exclusive(v_l_3902_);
if (v_isSharedCheck_3951_ == 0)
{
lean_object* v_unused_3952_; lean_object* v_unused_3953_; lean_object* v_unused_3954_; lean_object* v_unused_3955_; lean_object* v_unused_3956_; 
v_unused_3952_ = lean_ctor_get(v_l_3902_, 4);
lean_dec(v_unused_3952_);
v_unused_3953_ = lean_ctor_get(v_l_3902_, 3);
lean_dec(v_unused_3953_);
v_unused_3954_ = lean_ctor_get(v_l_3902_, 2);
lean_dec(v_unused_3954_);
v_unused_3955_ = lean_ctor_get(v_l_3902_, 1);
lean_dec(v_unused_3955_);
v_unused_3956_ = lean_ctor_get(v_l_3902_, 0);
lean_dec(v_unused_3956_);
v___x_3925_ = v_l_3902_;
v_isShared_3926_ = v_isSharedCheck_3951_;
goto v_resetjp_3924_;
}
else
{
lean_dec(v_l_3902_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3951_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3941_; 
v___x_3927_ = lean_nat_add(v___x_3897_, v_size_3898_);
v___x_3928_ = lean_nat_add(v___x_3927_, v_size_3899_);
lean_dec(v_size_3899_);
if (lean_obj_tag(v_l_3918_) == 0)
{
lean_object* v_size_3949_; 
v_size_3949_ = lean_ctor_get(v_l_3918_, 0);
lean_inc(v_size_3949_);
v___y_3941_ = v_size_3949_;
goto v___jp_3940_;
}
else
{
lean_object* v___x_3950_; 
v___x_3950_ = lean_unsigned_to_nat(0u);
v___y_3941_ = v___x_3950_;
goto v___jp_3940_;
}
v___jp_3929_:
{
lean_object* v___x_3933_; lean_object* v___x_3935_; 
v___x_3933_ = lean_nat_add(v___y_3931_, v___y_3932_);
lean_dec(v___y_3932_);
lean_dec(v___y_3931_);
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 4, v_r_3903_);
lean_ctor_set(v___x_3925_, 3, v_r_3919_);
lean_ctor_set(v___x_3925_, 2, v_v_3901_);
lean_ctor_set(v___x_3925_, 1, v_k_3900_);
lean_ctor_set(v___x_3925_, 0, v___x_3933_);
v___x_3935_ = v___x_3925_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v___x_3933_);
lean_ctor_set(v_reuseFailAlloc_3939_, 1, v_k_3900_);
lean_ctor_set(v_reuseFailAlloc_3939_, 2, v_v_3901_);
lean_ctor_set(v_reuseFailAlloc_3939_, 3, v_r_3919_);
lean_ctor_set(v_reuseFailAlloc_3939_, 4, v_r_3903_);
v___x_3935_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
lean_object* v___x_3937_; 
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 4, v___x_3935_);
lean_ctor_set(v___x_3913_, 3, v___y_3930_);
lean_ctor_set(v___x_3913_, 2, v_v_3917_);
lean_ctor_set(v___x_3913_, 1, v_k_3916_);
lean_ctor_set(v___x_3913_, 0, v___x_3928_);
v___x_3937_ = v___x_3913_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v___x_3928_);
lean_ctor_set(v_reuseFailAlloc_3938_, 1, v_k_3916_);
lean_ctor_set(v_reuseFailAlloc_3938_, 2, v_v_3917_);
lean_ctor_set(v_reuseFailAlloc_3938_, 3, v___y_3930_);
lean_ctor_set(v_reuseFailAlloc_3938_, 4, v___x_3935_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
v___jp_3940_:
{
lean_object* v___x_3942_; lean_object* v___x_3944_; 
v___x_3942_ = lean_nat_add(v___x_3927_, v___y_3941_);
lean_dec(v___y_3941_);
lean_dec(v___x_3927_);
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 4, v_l_3918_);
lean_ctor_set(v___x_3753_, 0, v___x_3942_);
v___x_3944_ = v___x_3753_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3942_);
lean_ctor_set(v_reuseFailAlloc_3948_, 1, v_k_3748_);
lean_ctor_set(v_reuseFailAlloc_3948_, 2, v_v_3749_);
lean_ctor_set(v_reuseFailAlloc_3948_, 3, v_l_3750_);
lean_ctor_set(v_reuseFailAlloc_3948_, 4, v_l_3918_);
v___x_3944_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
lean_object* v___x_3945_; 
v___x_3945_ = lean_nat_add(v___x_3897_, v_size_3920_);
if (lean_obj_tag(v_r_3919_) == 0)
{
lean_object* v_size_3946_; 
v_size_3946_ = lean_ctor_get(v_r_3919_, 0);
lean_inc(v_size_3946_);
v___y_3930_ = v___x_3944_;
v___y_3931_ = v___x_3945_;
v___y_3932_ = v_size_3946_;
goto v___jp_3929_;
}
else
{
lean_object* v___x_3947_; 
v___x_3947_ = lean_unsigned_to_nat(0u);
v___y_3930_ = v___x_3944_;
v___y_3931_ = v___x_3945_;
v___y_3932_ = v___x_3947_;
goto v___jp_3929_;
}
}
}
}
}
else
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3961_; 
lean_del_object(v___x_3753_);
v___x_3957_ = lean_nat_add(v___x_3897_, v_size_3898_);
v___x_3958_ = lean_nat_add(v___x_3957_, v_size_3899_);
lean_dec(v_size_3899_);
v___x_3959_ = lean_nat_add(v___x_3957_, v_size_3915_);
lean_dec(v___x_3957_);
lean_inc_ref(v_l_3750_);
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 4, v_l_3902_);
lean_ctor_set(v___x_3913_, 3, v_l_3750_);
lean_ctor_set(v___x_3913_, 2, v_v_3749_);
lean_ctor_set(v___x_3913_, 1, v_k_3748_);
lean_ctor_set(v___x_3913_, 0, v___x_3959_);
v___x_3961_ = v___x_3913_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v___x_3959_);
lean_ctor_set(v_reuseFailAlloc_3974_, 1, v_k_3748_);
lean_ctor_set(v_reuseFailAlloc_3974_, 2, v_v_3749_);
lean_ctor_set(v_reuseFailAlloc_3974_, 3, v_l_3750_);
lean_ctor_set(v_reuseFailAlloc_3974_, 4, v_l_3902_);
v___x_3961_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3968_; 
v_isSharedCheck_3968_ = !lean_is_exclusive(v_l_3750_);
if (v_isSharedCheck_3968_ == 0)
{
lean_object* v_unused_3969_; lean_object* v_unused_3970_; lean_object* v_unused_3971_; lean_object* v_unused_3972_; lean_object* v_unused_3973_; 
v_unused_3969_ = lean_ctor_get(v_l_3750_, 4);
lean_dec(v_unused_3969_);
v_unused_3970_ = lean_ctor_get(v_l_3750_, 3);
lean_dec(v_unused_3970_);
v_unused_3971_ = lean_ctor_get(v_l_3750_, 2);
lean_dec(v_unused_3971_);
v_unused_3972_ = lean_ctor_get(v_l_3750_, 1);
lean_dec(v_unused_3972_);
v_unused_3973_ = lean_ctor_get(v_l_3750_, 0);
lean_dec(v_unused_3973_);
v___x_3963_ = v_l_3750_;
v_isShared_3964_ = v_isSharedCheck_3968_;
goto v_resetjp_3962_;
}
else
{
lean_dec(v_l_3750_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3968_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___x_3966_; 
if (v_isShared_3964_ == 0)
{
lean_ctor_set(v___x_3963_, 4, v_r_3903_);
lean_ctor_set(v___x_3963_, 3, v___x_3961_);
lean_ctor_set(v___x_3963_, 2, v_v_3901_);
lean_ctor_set(v___x_3963_, 1, v_k_3900_);
lean_ctor_set(v___x_3963_, 0, v___x_3958_);
v___x_3966_ = v___x_3963_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v___x_3958_);
lean_ctor_set(v_reuseFailAlloc_3967_, 1, v_k_3900_);
lean_ctor_set(v_reuseFailAlloc_3967_, 2, v_v_3901_);
lean_ctor_set(v_reuseFailAlloc_3967_, 3, v___x_3961_);
lean_ctor_set(v_reuseFailAlloc_3967_, 4, v_r_3903_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3981_; 
v_l_3981_ = lean_ctor_get(v_impl_3896_, 3);
lean_inc(v_l_3981_);
if (lean_obj_tag(v_l_3981_) == 0)
{
lean_object* v_r_3982_; lean_object* v_k_3983_; lean_object* v_v_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_4007_; 
v_r_3982_ = lean_ctor_get(v_impl_3896_, 4);
v_k_3983_ = lean_ctor_get(v_impl_3896_, 1);
v_v_3984_ = lean_ctor_get(v_impl_3896_, 2);
v_isSharedCheck_4007_ = !lean_is_exclusive(v_impl_3896_);
if (v_isSharedCheck_4007_ == 0)
{
lean_object* v_unused_4008_; lean_object* v_unused_4009_; 
v_unused_4008_ = lean_ctor_get(v_impl_3896_, 3);
lean_dec(v_unused_4008_);
v_unused_4009_ = lean_ctor_get(v_impl_3896_, 0);
lean_dec(v_unused_4009_);
v___x_3986_ = v_impl_3896_;
v_isShared_3987_ = v_isSharedCheck_4007_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_r_3982_);
lean_inc(v_v_3984_);
lean_inc(v_k_3983_);
lean_dec(v_impl_3896_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_4007_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v_k_3988_; lean_object* v_v_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_4003_; 
v_k_3988_ = lean_ctor_get(v_l_3981_, 1);
v_v_3989_ = lean_ctor_get(v_l_3981_, 2);
v_isSharedCheck_4003_ = !lean_is_exclusive(v_l_3981_);
if (v_isSharedCheck_4003_ == 0)
{
lean_object* v_unused_4004_; lean_object* v_unused_4005_; lean_object* v_unused_4006_; 
v_unused_4004_ = lean_ctor_get(v_l_3981_, 4);
lean_dec(v_unused_4004_);
v_unused_4005_ = lean_ctor_get(v_l_3981_, 3);
lean_dec(v_unused_4005_);
v_unused_4006_ = lean_ctor_get(v_l_3981_, 0);
lean_dec(v_unused_4006_);
v___x_3991_ = v_l_3981_;
v_isShared_3992_ = v_isSharedCheck_4003_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_v_3989_);
lean_inc(v_k_3988_);
lean_dec(v_l_3981_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_4003_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3993_; lean_object* v___x_3995_; 
v___x_3993_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3982_, 2);
if (v_isShared_3992_ == 0)
{
lean_ctor_set(v___x_3991_, 4, v_r_3982_);
lean_ctor_set(v___x_3991_, 3, v_r_3982_);
lean_ctor_set(v___x_3991_, 2, v_v_3749_);
lean_ctor_set(v___x_3991_, 1, v_k_3748_);
lean_ctor_set(v___x_3991_, 0, v___x_3897_);
v___x_3995_ = v___x_3991_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v___x_3897_);
lean_ctor_set(v_reuseFailAlloc_4002_, 1, v_k_3748_);
lean_ctor_set(v_reuseFailAlloc_4002_, 2, v_v_3749_);
lean_ctor_set(v_reuseFailAlloc_4002_, 3, v_r_3982_);
lean_ctor_set(v_reuseFailAlloc_4002_, 4, v_r_3982_);
v___x_3995_ = v_reuseFailAlloc_4002_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
lean_object* v___x_3997_; 
lean_inc(v_r_3982_);
if (v_isShared_3987_ == 0)
{
lean_ctor_set(v___x_3986_, 3, v_r_3982_);
lean_ctor_set(v___x_3986_, 0, v___x_3897_);
v___x_3997_ = v___x_3986_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v___x_3897_);
lean_ctor_set(v_reuseFailAlloc_4001_, 1, v_k_3983_);
lean_ctor_set(v_reuseFailAlloc_4001_, 2, v_v_3984_);
lean_ctor_set(v_reuseFailAlloc_4001_, 3, v_r_3982_);
lean_ctor_set(v_reuseFailAlloc_4001_, 4, v_r_3982_);
v___x_3997_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
lean_object* v___x_3999_; 
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 4, v___x_3997_);
lean_ctor_set(v___x_3753_, 3, v___x_3995_);
lean_ctor_set(v___x_3753_, 2, v_v_3989_);
lean_ctor_set(v___x_3753_, 1, v_k_3988_);
lean_ctor_set(v___x_3753_, 0, v___x_3993_);
v___x_3999_ = v___x_3753_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v___x_3993_);
lean_ctor_set(v_reuseFailAlloc_4000_, 1, v_k_3988_);
lean_ctor_set(v_reuseFailAlloc_4000_, 2, v_v_3989_);
lean_ctor_set(v_reuseFailAlloc_4000_, 3, v___x_3995_);
lean_ctor_set(v_reuseFailAlloc_4000_, 4, v___x_3997_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
}
}
}
else
{
lean_object* v_r_4010_; 
v_r_4010_ = lean_ctor_get(v_impl_3896_, 4);
lean_inc(v_r_4010_);
if (lean_obj_tag(v_r_4010_) == 0)
{
lean_object* v_k_4011_; lean_object* v_v_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4023_; 
v_k_4011_ = lean_ctor_get(v_impl_3896_, 1);
v_v_4012_ = lean_ctor_get(v_impl_3896_, 2);
v_isSharedCheck_4023_ = !lean_is_exclusive(v_impl_3896_);
if (v_isSharedCheck_4023_ == 0)
{
lean_object* v_unused_4024_; lean_object* v_unused_4025_; lean_object* v_unused_4026_; 
v_unused_4024_ = lean_ctor_get(v_impl_3896_, 4);
lean_dec(v_unused_4024_);
v_unused_4025_ = lean_ctor_get(v_impl_3896_, 3);
lean_dec(v_unused_4025_);
v_unused_4026_ = lean_ctor_get(v_impl_3896_, 0);
lean_dec(v_unused_4026_);
v___x_4014_ = v_impl_3896_;
v_isShared_4015_ = v_isSharedCheck_4023_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_v_4012_);
lean_inc(v_k_4011_);
lean_dec(v_impl_3896_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4023_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4016_; lean_object* v___x_4018_; 
v___x_4016_ = lean_unsigned_to_nat(3u);
if (v_isShared_4015_ == 0)
{
lean_ctor_set(v___x_4014_, 4, v_l_3981_);
lean_ctor_set(v___x_4014_, 2, v_v_3749_);
lean_ctor_set(v___x_4014_, 1, v_k_3748_);
lean_ctor_set(v___x_4014_, 0, v___x_3897_);
v___x_4018_ = v___x_4014_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v___x_3897_);
lean_ctor_set(v_reuseFailAlloc_4022_, 1, v_k_3748_);
lean_ctor_set(v_reuseFailAlloc_4022_, 2, v_v_3749_);
lean_ctor_set(v_reuseFailAlloc_4022_, 3, v_l_3981_);
lean_ctor_set(v_reuseFailAlloc_4022_, 4, v_l_3981_);
v___x_4018_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
lean_object* v___x_4020_; 
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 4, v_r_4010_);
lean_ctor_set(v___x_3753_, 3, v___x_4018_);
lean_ctor_set(v___x_3753_, 2, v_v_4012_);
lean_ctor_set(v___x_3753_, 1, v_k_4011_);
lean_ctor_set(v___x_3753_, 0, v___x_4016_);
v___x_4020_ = v___x_3753_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v___x_4016_);
lean_ctor_set(v_reuseFailAlloc_4021_, 1, v_k_4011_);
lean_ctor_set(v_reuseFailAlloc_4021_, 2, v_v_4012_);
lean_ctor_set(v_reuseFailAlloc_4021_, 3, v___x_4018_);
lean_ctor_set(v_reuseFailAlloc_4021_, 4, v_r_4010_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
}
else
{
lean_object* v___x_4027_; lean_object* v___x_4029_; 
v___x_4027_ = lean_unsigned_to_nat(2u);
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 4, v_impl_3896_);
lean_ctor_set(v___x_3753_, 3, v_r_4010_);
lean_ctor_set(v___x_3753_, 0, v___x_4027_);
v___x_4029_ = v___x_3753_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v___x_4027_);
lean_ctor_set(v_reuseFailAlloc_4030_, 1, v_k_3748_);
lean_ctor_set(v_reuseFailAlloc_4030_, 2, v_v_3749_);
lean_ctor_set(v_reuseFailAlloc_4030_, 3, v_r_4010_);
lean_ctor_set(v_reuseFailAlloc_4030_, 4, v_impl_3896_);
v___x_4029_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
return v___x_4029_;
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
lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4032_ = lean_unsigned_to_nat(1u);
v___x_4033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4032_);
lean_ctor_set(v___x_4033_, 1, v_k_3744_);
lean_ctor_set(v___x_4033_, 2, v_v_3745_);
lean_ctor_set(v___x_4033_, 3, v_t_3746_);
lean_ctor_set(v___x_4033_, 4, v_t_3746_);
return v___x_4033_;
}
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4034_ = lean_box(1);
v___x_4035_ = l_Lake_Package_depsFacetConfig;
v___x_4036_ = l_Lake_Package_depsFacet;
v___x_4037_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_4036_, v___x_4035_, v___x_4034_);
return v___x_4037_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
v___x_4038_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__0, &l_Lake_Package_initFacetConfigs___closed__0_once, _init_l_Lake_Package_initFacetConfigs___closed__0);
v___x_4039_ = l_Lake_Package_transDepsFacetConfig;
v___x_4040_ = l_Lake_Package_transDepsFacet;
v___x_4041_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_4040_, v___x_4039_, v___x_4038_);
return v___x_4041_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4042_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__1, &l_Lake_Package_initFacetConfigs___closed__1_once, _init_l_Lake_Package_initFacetConfigs___closed__1);
v___x_4043_ = l_Lake_Package_defaultModulesFacetConfig;
v___x_4044_ = l_Lake_Package_defaultModulesFacet;
v___x_4045_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_4044_, v___x_4043_, v___x_4042_);
return v___x_4045_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4046_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__2, &l_Lake_Package_initFacetConfigs___closed__2_once, _init_l_Lake_Package_initFacetConfigs___closed__2);
v___x_4047_ = l_Lake_Package_extraDepFacetConfig;
v___x_4048_ = l_Lake_Package_extraDepFacet;
v___x_4049_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_4048_, v___x_4047_, v___x_4046_);
return v___x_4049_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4050_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__3, &l_Lake_Package_initFacetConfigs___closed__3_once, _init_l_Lake_Package_initFacetConfigs___closed__3);
v___x_4051_ = l_Lake_Package_optBuildCacheFacetConfig;
v___x_4052_ = l_Lake_Package_optBuildCacheFacet;
v___x_4053_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_4052_, v___x_4051_, v___x_4050_);
return v___x_4053_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; 
v___x_4054_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__4, &l_Lake_Package_initFacetConfigs___closed__4_once, _init_l_Lake_Package_initFacetConfigs___closed__4);
v___x_4055_ = l_Lake_Package_buildCacheFacetConfig;
v___x_4056_ = l_Lake_Package_buildCacheFacet;
v___x_4057_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_4056_, v___x_4055_, v___x_4054_);
return v___x_4057_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4058_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__5, &l_Lake_Package_initFacetConfigs___closed__5_once, _init_l_Lake_Package_initFacetConfigs___closed__5);
v___x_4059_ = l_Lake_Package_optBarrelFacetConfig;
v___x_4060_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_4061_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_4060_, v___x_4059_, v___x_4058_);
return v___x_4061_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__7(void){
_start:
{
lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4062_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__6, &l_Lake_Package_initFacetConfigs___closed__6_once, _init_l_Lake_Package_initFacetConfigs___closed__6);
v___x_4063_ = l_Lake_Package_barrelFacetConfig;
v___x_4064_ = l_Lake_Package_reservoirBarrelFacet;
v___x_4065_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_4064_, v___x_4063_, v___x_4062_);
return v___x_4065_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__8(void){
_start:
{
lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
v___x_4066_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__7, &l_Lake_Package_initFacetConfigs___closed__7_once, _init_l_Lake_Package_initFacetConfigs___closed__7);
v___x_4067_ = l_Lake_Package_optGitHubReleaseFacetConfig;
v___x_4068_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_4069_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_4068_, v___x_4067_, v___x_4066_);
return v___x_4069_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__9(void){
_start:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4070_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__8, &l_Lake_Package_initFacetConfigs___closed__8_once, _init_l_Lake_Package_initFacetConfigs___closed__8);
v___x_4071_ = l_Lake_Package_gitHubReleaseFacetConfig;
v___x_4072_ = l_Lake_Package_gitHubReleaseFacet;
v___x_4073_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_4072_, v___x_4071_, v___x_4070_);
return v___x_4073_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs(void){
_start:
{
lean_object* v___x_4074_; 
v___x_4074_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__9, &l_Lake_Package_initFacetConfigs___closed__9_once, _init_l_Lake_Package_initFacetConfigs___closed__9);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0(lean_object* v_00_u03b2_4075_, lean_object* v_k_4076_, lean_object* v_v_4077_, lean_object* v_t_4078_, lean_object* v_hl_4079_){
_start:
{
lean_object* v___x_4080_; 
v___x_4080_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_4076_, v_v_4077_, v_t_4078_);
return v___x_4080_;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs(void){
_start:
{
lean_object* v___x_4081_; 
v___x_4081_ = l_Lake_Package_initFacetConfigs;
return v___x_4081_;
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
