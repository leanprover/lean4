// Lean compiler output
// Module: Lake.Build.Common
// Imports: public import Lake.Build.Job.Monad public import Lake.Config.Monad public import Lake.Util.JsonObject public import Lake.Util.IO public import Lake.Build.Actions
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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_instMonadST(lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object*);
lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instAlternativeELogTOfMonad___redArg(lean_object*);
lean_object* l_ReaderT_instAlternativeOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_read(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(lean_object*, lean_object*);
lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(lean_object*, lean_object*);
lean_object* l_instMonadST___lam__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EquipT_instFunctor___redArg(lean_object*);
lean_object* l_Lake_EquipT_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobM_runFetchM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_Hash_hex(uint64_t);
lean_object* l_String_decidableLT___boxed(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
extern lean_object* l_System_Platform_target;
uint64_t lean_string_hash(lean_object*);
extern uint64_t l_Lake_Hash_nil;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lake_compileStaticLib(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lake_Artifact_trace(lean_object*);
lean_object* lean_io_metadata(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lake_Hash_ofJsonNumber_x3f(lean_object*);
lean_object* l_Lake_JsonObject_getJson_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_Lake_instFromJsonLogEntry_fromJson(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lake_Hash_ofDecimal_x3f(lean_object*);
lean_object* l_Lake_Hash_fromJson_x3f(lean_object*);
lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(uint64_t, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* lean_io_hard_link(lean_object*, lean_object*);
lean_object* l_Lake_copyFile(lean_object*, lean_object*);
lean_object* l_IO_setAccessRights(lean_object*, lean_object*);
lean_object* l_Lake_JsonObject_insertJson(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instToJsonLogEntry_toJson(lean_object*);
uint8_t l_Lake_JobAction_merge(uint8_t, uint8_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* l_Lake_removeFileIfExists(lean_object*);
lean_object* l_Lake_Package_cacheScope(lean_object*);
lean_object* l_Lake_Cache_readOutputs_x3f(lean_object*, lean_object*, uint64_t, lean_object*);
lean_object* l_Lake_ArtifactDescr_fromJson_x3f(lean_object*);
lean_object* l_Lean_Json_render(lean_object*);
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lake_CacheService_artifactUrl(uint64_t, lean_object*, lean_object*);
lean_object* l_Lake_downloadArtifactCore(uint64_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now();
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lake_computeBinFileHash(lean_object*);
lean_object* l_Lake_computeTextFileHash(lean_object*);
lean_object* l_Lake_Hash_load_x3f(lean_object*);
uint8_t l_IO_FS_instOrdSystemTime_ord(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*);
uint64_t lean_byte_array_hash(lean_object*);
lean_object* l_IO_FS_writeBinFile(lean_object*, lean_object*);
lean_object* l_String_crlfToLf(lean_object*);
extern lean_object* l_Lake_instDataKindFilePath;
lean_object* l_Lake_Job_collectArray___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Job_mapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instDecidableEqHash___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_MTime_checkUpToDate___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lake_compileO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_Job_async___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_System_FilePath_walkDir(lean_object*, lean_object*);
lean_object* l_Lake_Job_bindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Dynlib_dir_x3f(lean_object*);
lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t, lean_object*);
lean_object* l_Lake_compileExe(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_sharedLibExt;
extern lean_object* l_System_FilePath_exeExtension;
extern lean_object* l_Lake_instDataKindDynlib;
static lean_once_cell_t l_Lake_instMonadWorkspaceJobM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__0;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__1 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__1_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__2 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__2_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__3 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__3_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__4 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__4_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__5 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__5_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__6 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__6_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__7 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__7_value;
static const lean_ctor_object l_Lake_instMonadWorkspaceJobM___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__1_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__2_value)}};
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__8 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__8_value;
static const lean_ctor_object l_Lake_instMonadWorkspaceJobM___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__8_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__3_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__4_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__5_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__6_value)}};
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__9 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__9_value;
static const lean_ctor_object l_Lake_instMonadWorkspaceJobM___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__9_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__7_value)}};
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__10 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__10_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instFunctorOfMonad___redArg___lam__0, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__8_value)} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__11 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__11_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instFunctorOfMonad___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__8_value)} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__12 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__12_value;
static const lean_ctor_object l_Lake_instMonadWorkspaceJobM___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__11_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__12_value)}};
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__13 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__13_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_read, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__10_value)} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__14 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__14_value;
static lean_once_cell_t l_Lake_instMonadWorkspaceJobM___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__15;
static lean_once_cell_t l_Lake_instMonadWorkspaceJobM___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__16;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadST___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__17 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__17_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_EStateT_instPure___redArg___lam__0, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__17_value)} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__18 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__18_value;
static lean_once_cell_t l_Lake_instMonadWorkspaceJobM___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__19;
static lean_once_cell_t l_Lake_instMonadWorkspaceJobM___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__20;
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceJobM;
static lean_once_cell_t l_Lake_platformTrace___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lake_platformTrace___closed__0;
static lean_once_cell_t l_Lake_platformTrace___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lake_platformTrace___closed__1;
static const lean_array_object l_Lake_platformTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_platformTrace___closed__2 = (const lean_object*)&l_Lake_platformTrace___closed__2_value;
static lean_once_cell_t l_Lake_platformTrace___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_platformTrace___closed__3;
static lean_once_cell_t l_Lake_platformTrace___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_platformTrace___closed__4;
static lean_once_cell_t l_Lake_platformTrace___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_platformTrace___closed__5;
LEAN_EXPORT lean_object* l_Lake_platformTrace;
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addLeanTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_addPureTrace___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lake_addPureTrace___redArg___closed__0 = (const lean_object*)&l_Lake_addPureTrace___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPureTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPureTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "2025-09-10"};
static const lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0_value;
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2(lean_object*);
static const lean_string_object l_Lake_BuildMetadata_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "schemaVersion"};
static const lean_object* l_Lake_BuildMetadata_toJson___closed__0 = (const lean_object*)&l_Lake_BuildMetadata_toJson___closed__0_value;
static const lean_ctor_object l_Lake_BuildMetadata_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0_value)}};
static const lean_object* l_Lake_BuildMetadata_toJson___closed__1 = (const lean_object*)&l_Lake_BuildMetadata_toJson___closed__1_value;
static lean_once_cell_t l_Lake_BuildMetadata_toJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_BuildMetadata_toJson___closed__2;
static const lean_string_object l_Lake_BuildMetadata_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "depHash"};
static const lean_object* l_Lake_BuildMetadata_toJson___closed__3 = (const lean_object*)&l_Lake_BuildMetadata_toJson___closed__3_value;
static const lean_string_object l_Lake_BuildMetadata_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "inputs"};
static const lean_object* l_Lake_BuildMetadata_toJson___closed__4 = (const lean_object*)&l_Lake_BuildMetadata_toJson___closed__4_value;
static const lean_string_object l_Lake_BuildMetadata_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "outputs"};
static const lean_object* l_Lake_BuildMetadata_toJson___closed__5 = (const lean_object*)&l_Lake_BuildMetadata_toJson___closed__5_value;
static const lean_string_object l_Lake_BuildMetadata_toJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "log"};
static const lean_object* l_Lake_BuildMetadata_toJson___closed__6 = (const lean_object*)&l_Lake_BuildMetadata_toJson___closed__6_value;
static const lean_string_object l_Lake_BuildMetadata_toJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "synthetic"};
static const lean_object* l_Lake_BuildMetadata_toJson___closed__7 = (const lean_object*)&l_Lake_BuildMetadata_toJson___closed__7_value;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_toJson(lean_object*);
static const lean_closure_object l_Lake_instToJsonBuildMetadata___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_BuildMetadata_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToJsonBuildMetadata___closed__0 = (const lean_object*)&l_Lake_instToJsonBuildMetadata___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToJsonBuildMetadata = (const lean_object*)&l_Lake_instToJsonBuildMetadata___closed__0_value;
static const lean_array_object l_Lake_BuildMetadata_ofStub___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_BuildMetadata_ofStub___closed__0 = (const lean_object*)&l_Lake_BuildMetadata_ofStub___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub(uint64_t);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub___boxed(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___boxed(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0_value;
static const lean_string_object l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1(lean_object*);
static const lean_string_object l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected pair, got '"};
static const lean_object* l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0 = (const lean_object*)&l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0_value;
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3(lean_object*);
static const lean_string_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "synthetic: "};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__0 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__0_value;
static const lean_array_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1_value;
static const lean_string_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "log: "};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2_value;
static const lean_string_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "outputs: "};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3_value;
static const lean_array_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4_value;
static const lean_string_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "inputs: "};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5_value;
static const lean_string_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "property not found: depHash"};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__6 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__6_value;
static const lean_ctor_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__6_value)}};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7_value;
static const lean_string_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "depHash: "};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8_value;
static const lean_string_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "invalid trace: expected string 'depHash' of decimal digits"};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__9 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__9_value;
static const lean_ctor_object l_Lake_BuildMetadata_fromJsonObject_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__9_value)}};
static const lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__10 = (const lean_object*)&l_Lake_BuildMetadata_fromJsonObject_x3f___closed__10_value;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___boxed(lean_object*);
static const lean_string_object l_Lake_BuildMetadata_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid trace stub: "};
static const lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__0 = (const lean_object*)&l_Lake_BuildMetadata_fromJson_x3f___closed__0_value;
static const lean_string_object l_Lake_BuildMetadata_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "unknown trace format: "};
static const lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__1 = (const lean_object*)&l_Lake_BuildMetadata_fromJson_x3f___closed__1_value;
static const lean_string_object l_Lake_BuildMetadata_fromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "invalid trace: "};
static const lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__2 = (const lean_object*)&l_Lake_BuildMetadata_fromJson_x3f___closed__2_value;
static const lean_string_object l_Lake_BuildMetadata_fromJson_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "unknown trace format: expected JSON number or object"};
static const lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__3 = (const lean_object*)&l_Lake_BuildMetadata_fromJson_x3f___closed__3_value;
static const lean_ctor_object l_Lake_BuildMetadata_fromJson_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_BuildMetadata_fromJson_x3f___closed__3_value)}};
static const lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__4 = (const lean_object*)&l_Lake_BuildMetadata_fromJson_x3f___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f___boxed(lean_object*);
static const lean_closure_object l_Lake_instFromJsonBuildMetadata___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_BuildMetadata_fromJson_x3f___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instFromJsonBuildMetadata___closed__0 = (const lean_object*)&l_Lake_instFromJsonBuildMetadata___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instFromJsonBuildMetadata = (const lean_object*)&l_Lake_instFromJsonBuildMetadata___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_parse(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_missing_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_missing_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_invalid_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_invalid_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ok_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ok_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_readTraceFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = ": read failed: "};
static const lean_object* l_Lake_readTraceFile___closed__0 = (const lean_object*)&l_Lake_readTraceFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_readTraceFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_readTraceFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqOutputStatus(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqOutputStatus___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofHashCheck(uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofHashCheck___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofMTimeCheck(uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofMTimeCheck___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isUpToDate(uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isUpToDate___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isCacheable(uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isCacheable___boxed(lean_object*);
static lean_once_cell_t l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonPUnit___lam__0(lean_object*);
static const lean_closure_object l_Lake_instToOutputJsonPUnit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToOutputJsonPUnit___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToOutputJsonPUnit___closed__0 = (const lean_object*)&l_Lake_instToOutputJsonPUnit___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToOutputJsonPUnit = (const lean_object*)&l_Lake_instToOutputJsonPUnit___closed__0_value;
static const lean_string_object l_Lake_instToOutputJsonArtifact___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_instToOutputJsonArtifact___lam__0___closed__0 = (const lean_object*)&l_Lake_instToOutputJsonArtifact___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instToOutputJsonArtifact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instToOutputJsonArtifact___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instToOutputJsonArtifact___closed__0 = (const lean_object*)&l_Lake_instToOutputJsonArtifact___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToOutputJsonArtifact = (const lean_object*)&l_Lake_instToOutputJsonArtifact___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildAction___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "target is out-of-date and needs to be rebuilt"};
static const lean_object* l_Lake_buildAction___redArg___closed__0 = (const lean_object*)&l_Lake_buildAction___redArg___closed__0_value;
static const lean_ctor_object l_Lake_buildAction___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_buildAction___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_buildAction___redArg___closed__1 = (const lean_object*)&l_Lake_buildAction___redArg___closed__1_value;
static const lean_string_object l_Lake_buildAction___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "nobuild"};
static const lean_object* l_Lake_buildAction___redArg___closed__2 = (const lean_object*)&l_Lake_buildAction___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_writeFileHash___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ".hash"};
static const lean_object* l_Lake_writeFileHash___closed__0 = (const lean_object*)&l_Lake_writeFileHash___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_writeFileHash(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lake_writeFileHash___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_cacheFileHash___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_clearFileHash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_clearFileHash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildFileUnlessUpToDate_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ".trace"};
static const lean_object* l_Lake_buildFileUnlessUpToDate_x27___closed__0 = (const lean_object*)&l_Lake_buildFileUnlessUpToDate_x27___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0(lean_object*, uint64_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__1(lean_object*, uint64_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Cache_saveArtifact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "failed to cache artifact: "};
static const lean_object* l_Lake_Cache_saveArtifact___closed__0 = (const lean_object*)&l_Lake_Cache_saveArtifact___closed__0_value;
static const lean_string_object l_Lake_Cache_saveArtifact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "artifacts"};
static const lean_object* l_Lake_Cache_saveArtifact___closed__1 = (const lean_object*)&l_Lake_Cache_saveArtifact___closed__1_value;
static const lean_ctor_object l_Lake_Cache_saveArtifact___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_Cache_saveArtifact___closed__2 = (const lean_object*)&l_Lake_Cache_saveArtifact___closed__2_value;
static lean_once_cell_t l_Lake_Cache_saveArtifact___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Cache_saveArtifact___closed__3;
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_cacheArtifact___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_cacheArtifact___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_cacheArtifact___redArg___closed__0 = (const lean_object*)&l_Lake_cacheArtifact___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\n- "};
static const lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "input '"};
static const lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0_value;
static const lean_string_object l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "' found in package artifact cache, but some output(s) have issues:"};
static const lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1_value;
static const lean_closure_object l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "could not write outputs to cache: "};
static const lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0 = (const lean_object*)&l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_resolveArtifact___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "downloaded succeeded, but artifact failed to resolve: "};
static const lean_object* l_Lake_resolveArtifact___redArg___closed__0 = (const lean_object*)&l_Lake_resolveArtifact___redArg___closed__0_value;
static const lean_string_object l_Lake_resolveArtifact___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "downloaded artifact "};
static const lean_object* l_Lake_resolveArtifact___redArg___closed__1 = (const lean_object*)&l_Lake_resolveArtifact___redArg___closed__1_value;
static const lean_string_object l_Lake_resolveArtifact___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\n  local path: "};
static const lean_object* l_Lake_resolveArtifact___redArg___closed__2 = (const lean_object*)&l_Lake_resolveArtifact___redArg___closed__2_value;
static const lean_string_object l_Lake_resolveArtifact___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\n  remote URL: "};
static const lean_object* l_Lake_resolveArtifact___redArg___closed__3 = (const lean_object*)&l_Lake_resolveArtifact___redArg___closed__3_value;
static const lean_string_object l_Lake_resolveArtifact___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "could not mark downloaded artifact read-only: "};
static const lean_object* l_Lake_resolveArtifact___redArg___closed__4 = (const lean_object*)&l_Lake_resolveArtifact___redArg___closed__4_value;
static const lean_string_object l_Lake_resolveArtifact___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "artifact with associated cache service but no scope"};
static const lean_object* l_Lake_resolveArtifact___redArg___closed__5 = (const lean_object*)&l_Lake_resolveArtifact___redArg___closed__5_value;
static const lean_ctor_object l_Lake_resolveArtifact___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_resolveArtifact___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_resolveArtifact___redArg___closed__6 = (const lean_object*)&l_Lake_resolveArtifact___redArg___closed__6_value;
static const lean_string_object l_Lake_resolveArtifact___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "artifact cache service is not configured: "};
static const lean_object* l_Lake_resolveArtifact___redArg___closed__7 = (const lean_object*)&l_Lake_resolveArtifact___redArg___closed__7_value;
static const lean_string_object l_Lake_resolveArtifact___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "artifact not found in cache:\n  "};
static const lean_object* l_Lake_resolveArtifact___redArg___closed__8 = (const lean_object*)&l_Lake_resolveArtifact___redArg___closed__8_value;
static const lean_string_object l_Lake_resolveArtifact___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "failed to retrieve artifact from cache: "};
static const lean_object* l_Lake_resolveArtifact___redArg___closed__9 = (const lean_object*)&l_Lake_resolveArtifact___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifact(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_resolveArtifactOutput___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "ill-formed artifact output:\n"};
static const lean_object* l_Lake_resolveArtifactOutput___redArg___closed__0 = (const lean_object*)&l_Lake_resolveArtifactOutput___redArg___closed__0_value;
static const lean_string_object l_Lake_resolveArtifactOutput___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lake_resolveArtifactOutput___redArg___closed__1 = (const lean_object*)&l_Lake_resolveArtifactOutput___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArtifact(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_restoreArtifact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "restored artifact from cache to: "};
static const lean_object* l_Lake_restoreArtifact___closed__0 = (const lean_object*)&l_Lake_restoreArtifact___closed__0_value;
static const lean_string_object l_Lake_restoreArtifact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "found artifact in cache: "};
static const lean_object* l_Lake_restoreArtifact___closed__1 = (const lean_object*)&l_Lake_restoreArtifact___closed__1_value;
static const lean_string_object l_Lake_restoreArtifact___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "could not hard link artifact, copying from cache instead; error: "};
static const lean_object* l_Lake_restoreArtifact___closed__2 = (const lean_object*)&l_Lake_restoreArtifact___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_restoreArtifact(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_restoreArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "failed to retrieve artifact modification time: "};
static const lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(uint8_t, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___redArg(uint8_t, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(uint8_t, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(uint8_t, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildFileAfterDep___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "art"};
static const lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___closed__0 = (const lean_object*)&l_Lake_buildFileAfterDep___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_inputBinFile___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_inputBinFile___redArg___closed__0 = (const lean_object*)&l_Lake_inputBinFile___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decidableLT___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_inputDir___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_inputDir___lam__1___closed__0 = (const lean_object*)&l_Lake_inputDir___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_inputDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_inputDir___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_inputDir___closed__0 = (const lean_object*)&l_Lake_inputDir___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_inputDir(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_buildO___lam__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildO___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "traceArgs: "};
static const lean_object* l_Lake_buildO___lam__2___closed__0 = (const lean_object*)&l_Lake_buildO___lam__2___closed__0_value;
static const lean_string_object l_Lake_buildO___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Lake_buildO___lam__2___closed__1 = (const lean_object*)&l_Lake_buildO___lam__2___closed__1_value;
static const lean_string_object l_Lake_buildO___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "o"};
static const lean_object* l_Lake_buildO___lam__2___closed__2 = (const lean_object*)&l_Lake_buildO___lam__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_buildO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_buildO___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_buildO___closed__0 = (const lean_object*)&l_Lake_buildO___closed__0_value;
static const lean_closure_object l_Lake_buildO___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_buildO___closed__1 = (const lean_object*)&l_Lake_buildO___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildLeanO___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-I"};
static const lean_object* l_Lake_buildLeanO___lam__0___closed__0 = (const lean_object*)&l_Lake_buildLeanO___lam__0___closed__0_value;
static lean_once_cell_t l_Lake_buildLeanO___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_buildLeanO___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0 = (const lean_object*)&l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0_value;
static const lean_string_object l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1 = (const lean_object*)&l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1_value;
static const lean_string_object l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2 = (const lean_object*)&l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildStaticLib___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_Lake_buildStaticLib___lam__1___closed__0 = (const lean_object*)&l_Lake_buildStaticLib___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildStaticLib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "objs"};
static const lean_object* l_Lake_buildStaticLib___closed__0 = (const lean_object*)&l_Lake_buildStaticLib___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-l"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-L"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "  "};
static const lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "library dependency cycle:\n"};
static const lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0_value;
static const lean_array_object l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1_value;
static const lean_ctor_object l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1_value)}};
static const lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildSharedLib___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "linkLibs"};
static const lean_object* l_Lake_buildSharedLib___lam__3___closed__0 = (const lean_object*)&l_Lake_buildSharedLib___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3___boxed(lean_object**);
static const lean_string_object l_Lake_buildSharedLib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "linkObjs"};
static const lean_object* l_Lake_buildSharedLib___closed__0 = (const lean_object*)&l_Lake_buildSharedLib___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___boxed(lean_object**);
static lean_once_cell_t l_Lake_buildLeanSharedLib___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_buildLeanSharedLib___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_instMonadST(lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__15(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__13));
v___x_31_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__14));
v___x_32_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_31_, v___x_30_);
return v___x_32_;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__16(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__0, &l_Lake_instMonadWorkspaceJobM___closed__0_once, _init_l_Lake_instMonadWorkspaceJobM___closed__0);
v___x_34_ = l_Lake_instAlternativeELogTOfMonad___redArg(v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__19(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__13));
v___x_39_ = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__15, &l_Lake_instMonadWorkspaceJobM___closed__15_once, _init_l_Lake_instMonadWorkspaceJobM___closed__15);
v___x_40_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v___x_39_, v___x_38_);
return v___x_40_;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__20(void){
_start:
{
lean_object* v___x_41_; lean_object* v___f_42_; lean_object* v___x_43_; 
v___x_41_ = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__19, &l_Lake_instMonadWorkspaceJobM___closed__19_once, _init_l_Lake_instMonadWorkspaceJobM___closed__19);
v___f_42_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__18));
v___x_43_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0), 4, 3);
lean_closure_set(v___x_43_, 0, v___f_42_);
lean_closure_set(v___x_43_, 1, lean_box(0));
lean_closure_set(v___x_43_, 2, v___x_41_);
return v___x_43_;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM(void){
_start:
{
lean_object* v___x_44_; lean_object* v_toApplicative_45_; lean_object* v_toBind_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_123_; 
v___x_44_ = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__0, &l_Lake_instMonadWorkspaceJobM___closed__0_once, _init_l_Lake_instMonadWorkspaceJobM___closed__0);
v_toApplicative_45_ = lean_ctor_get(v___x_44_, 0);
v_toBind_46_ = lean_ctor_get(v___x_44_, 1);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_123_ == 0)
{
v___x_48_ = v___x_44_;
v_isShared_49_ = v_isSharedCheck_123_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_toBind_46_);
lean_inc(v_toApplicative_45_);
lean_dec(v___x_44_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_123_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v_toFunctor_50_; lean_object* v_toPure_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_119_; 
v_toFunctor_50_ = lean_ctor_get(v_toApplicative_45_, 0);
v_toPure_51_ = lean_ctor_get(v_toApplicative_45_, 1);
v_isSharedCheck_119_ = !lean_is_exclusive(v_toApplicative_45_);
if (v_isSharedCheck_119_ == 0)
{
lean_object* v_unused_120_; lean_object* v_unused_121_; lean_object* v_unused_122_; 
v_unused_120_ = lean_ctor_get(v_toApplicative_45_, 4);
lean_dec(v_unused_120_);
v_unused_121_ = lean_ctor_get(v_toApplicative_45_, 3);
lean_dec(v_unused_121_);
v_unused_122_ = lean_ctor_get(v_toApplicative_45_, 2);
lean_dec(v_unused_122_);
v___x_53_ = v_toApplicative_45_;
v_isShared_54_ = v_isSharedCheck_119_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_toPure_51_);
lean_inc(v_toFunctor_50_);
lean_dec(v_toApplicative_45_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_119_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___f_55_; lean_object* v___f_56_; lean_object* v___f_57_; lean_object* v___f_58_; lean_object* v___x_59_; lean_object* v___f_60_; lean_object* v___x_62_; 
lean_inc(v_toBind_46_);
lean_inc(v_toPure_51_);
v___f_55_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_55_, 0, v_toPure_51_);
lean_closure_set(v___f_55_, 1, v_toBind_46_);
lean_inc(v_toBind_46_);
lean_inc(v_toPure_51_);
v___f_56_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_56_, 0, v_toPure_51_);
lean_closure_set(v___f_56_, 1, v_toBind_46_);
lean_inc_ref(v___f_55_);
lean_inc(v_toPure_51_);
v___f_57_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_57_, 0, v_toPure_51_);
lean_closure_set(v___f_57_, 1, v___f_55_);
lean_inc(v_toPure_51_);
lean_inc_ref(v_toFunctor_50_);
v___f_58_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_58_, 0, v_toFunctor_50_);
lean_closure_set(v___f_58_, 1, v_toPure_51_);
lean_closure_set(v___f_58_, 2, v_toBind_46_);
v___x_59_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_50_);
v___f_60_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_60_, 0, v_toPure_51_);
lean_inc_ref(v___x_59_);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 4, v___f_56_);
lean_ctor_set(v___x_53_, 3, v___f_57_);
lean_ctor_set(v___x_53_, 2, v___f_58_);
lean_ctor_set(v___x_53_, 1, v___f_60_);
lean_ctor_set(v___x_53_, 0, v___x_59_);
v___x_62_ = v___x_53_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_59_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v___f_60_);
lean_ctor_set(v_reuseFailAlloc_118_, 2, v___f_58_);
lean_ctor_set(v_reuseFailAlloc_118_, 3, v___f_57_);
lean_ctor_set(v_reuseFailAlloc_118_, 4, v___f_56_);
v___x_62_ = v_reuseFailAlloc_118_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
lean_object* v___x_64_; 
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 1, v___f_55_);
lean_ctor_set(v___x_48_, 0, v___x_62_);
v___x_64_ = v___x_48_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_62_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v___f_55_);
v___x_64_ = v_reuseFailAlloc_117_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___f_65_; lean_object* v___f_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v_toApplicative_72_; lean_object* v_toFunctor_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v_toApplicative_77_; lean_object* v_toFunctor_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___f_82_; lean_object* v___f_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v_toApplicative_86_; lean_object* v_toFunctor_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___f_93_; lean_object* v___f_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v_toApplicative_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_115_; 
lean_inc_ref(v___x_59_);
v___f_65_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_65_, 0, v___x_59_);
v___f_66_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_66_, 0, v___x_59_);
v___x_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_67_, 0, v___f_65_);
lean_ctor_set(v___x_67_, 1, v___f_66_);
v___x_68_ = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__16, &l_Lake_instMonadWorkspaceJobM___closed__16_once, _init_l_Lake_instMonadWorkspaceJobM___closed__16);
lean_inc_ref(v___x_64_);
v___x_69_ = l_ReaderT_instAlternativeOfMonad___redArg(v___x_68_, v___x_64_);
v___x_70_ = l_ReaderT_instMonad___redArg(v___x_64_);
lean_inc_ref(v___x_70_);
v___x_71_ = l_ReaderT_instAlternativeOfMonad___redArg(v___x_69_, v___x_70_);
v_toApplicative_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc_ref(v_toApplicative_72_);
lean_dec_ref(v___x_71_);
v_toFunctor_73_ = lean_ctor_get(v_toApplicative_72_, 0);
lean_inc_ref(v_toFunctor_73_);
lean_dec_ref(v_toApplicative_72_);
v___x_74_ = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__20, &l_Lake_instMonadWorkspaceJobM___closed__20_once, _init_l_Lake_instMonadWorkspaceJobM___closed__20);
lean_inc_ref(v___x_67_);
v___x_75_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_74_, v___x_67_);
v___x_76_ = l_ReaderT_instMonad___redArg(v___x_70_);
v_toApplicative_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc_ref(v_toApplicative_77_);
v_toFunctor_78_ = lean_ctor_get(v_toApplicative_77_, 0);
lean_inc_ref(v_toFunctor_78_);
lean_dec_ref(v_toApplicative_77_);
v___x_79_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v___x_75_, v___x_67_);
v___x_80_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_80_, 0, lean_box(0));
lean_closure_set(v___x_80_, 1, lean_box(0));
lean_closure_set(v___x_80_, 2, lean_box(0));
lean_closure_set(v___x_80_, 3, lean_box(0));
lean_closure_set(v___x_80_, 4, v___x_79_);
lean_inc_ref(v_toFunctor_73_);
v___x_81_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_80_, v_toFunctor_73_);
lean_inc_ref(v_toFunctor_78_);
v___f_82_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_82_, 0, v_toFunctor_78_);
v___f_83_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_83_, 0, v_toFunctor_78_);
v___x_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_84_, 0, v___f_82_);
lean_ctor_set(v___x_84_, 1, v___f_83_);
v___x_85_ = l_ReaderT_instMonad___redArg(v___x_76_);
v_toApplicative_86_ = lean_ctor_get(v___x_85_, 0);
lean_inc_ref(v_toApplicative_86_);
v_toFunctor_87_ = lean_ctor_get(v_toApplicative_86_, 0);
lean_inc_ref(v_toFunctor_87_);
lean_dec_ref(v_toApplicative_86_);
v___x_88_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v___x_81_, v_toFunctor_73_);
v___x_89_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(v___x_89_, 0, lean_box(0));
lean_closure_set(v___x_89_, 1, v___x_88_);
lean_inc_ref(v___x_84_);
v___x_90_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_89_, v___x_84_);
v___x_91_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v___x_90_, v___x_84_);
v___x_92_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(v___x_92_, 0, lean_box(0));
lean_closure_set(v___x_92_, 1, v___x_91_);
lean_inc_ref(v_toFunctor_87_);
v___f_93_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_93_, 0, v_toFunctor_87_);
v___f_94_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_94_, 0, v_toFunctor_87_);
v___x_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_95_, 0, v___f_93_);
lean_ctor_set(v___x_95_, 1, v___f_94_);
lean_inc_ref(v___x_95_);
v___x_96_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_92_, v___x_95_);
lean_inc_ref(v___x_95_);
v___x_97_ = l_Lake_EquipT_instFunctor___redArg(v___x_95_);
v_toApplicative_98_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_115_ == 0)
{
lean_object* v_unused_116_; 
v_unused_116_ = lean_ctor_get(v___x_85_, 1);
lean_dec(v_unused_116_);
v___x_100_ = v___x_85_;
v_isShared_101_ = v_isSharedCheck_115_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_toApplicative_98_);
lean_dec(v___x_85_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_115_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v_toFunctor_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___f_108_; lean_object* v___f_109_; lean_object* v___x_111_; 
v_toFunctor_102_ = lean_ctor_get(v_toApplicative_98_, 0);
lean_inc_ref(v_toFunctor_102_);
lean_dec_ref(v_toApplicative_98_);
v___x_103_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v___x_96_, v___x_95_);
v___x_104_ = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(v___x_104_, 0, lean_box(0));
lean_closure_set(v___x_104_, 1, lean_box(0));
lean_closure_set(v___x_104_, 2, lean_box(0));
lean_closure_set(v___x_104_, 3, v___x_103_);
lean_inc_ref(v___x_97_);
v___x_105_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_104_, v___x_97_);
v___x_106_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v___x_105_, v___x_97_);
v___x_107_ = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM___boxed), 9, 2);
lean_closure_set(v___x_107_, 0, lean_box(0));
lean_closure_set(v___x_107_, 1, v___x_106_);
lean_inc_ref(v_toFunctor_102_);
v___f_108_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_108_, 0, v_toFunctor_102_);
v___f_109_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_109_, 0, v_toFunctor_102_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 1, v___f_109_);
lean_ctor_set(v___x_100_, 0, v___f_108_);
v___x_111_ = v___x_100_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___f_108_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v___f_109_);
v___x_111_ = v_reuseFailAlloc_114_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = l_Lake_EquipT_instFunctor___redArg(v___x_111_);
v___x_113_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_107_, v___x_112_);
return v___x_113_;
}
}
}
}
}
}
}
}
static uint64_t _init_l_Lake_platformTrace___closed__0(void){
_start:
{
lean_object* v___x_124_; uint64_t v___x_125_; 
v___x_124_ = l_System_Platform_target;
v___x_125_ = lean_string_hash(v___x_124_);
return v___x_125_;
}
}
static uint64_t _init_l_Lake_platformTrace___closed__1(void){
_start:
{
uint64_t v___x_126_; uint64_t v___x_127_; uint64_t v___x_128_; 
v___x_126_ = lean_uint64_once(&l_Lake_platformTrace___closed__0, &l_Lake_platformTrace___closed__0_once, _init_l_Lake_platformTrace___closed__0);
v___x_127_ = l_Lake_Hash_nil;
v___x_128_ = lean_uint64_mix_hash(v___x_127_, v___x_126_);
return v___x_128_;
}
}
static lean_object* _init_l_Lake_platformTrace___closed__3(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(0u);
v___x_132_ = lean_nat_to_int(v___x_131_);
return v___x_132_;
}
}
static lean_object* _init_l_Lake_platformTrace___closed__4(void){
_start:
{
uint32_t v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = 0;
v___x_134_ = lean_obj_once(&l_Lake_platformTrace___closed__3, &l_Lake_platformTrace___closed__3_once, _init_l_Lake_platformTrace___closed__3);
v___x_135_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set_uint32(v___x_135_, sizeof(void*)*1, v___x_133_);
return v___x_135_;
}
}
static lean_object* _init_l_Lake_platformTrace___closed__5(void){
_start:
{
lean_object* v___x_136_; uint64_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_136_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_137_ = lean_uint64_once(&l_Lake_platformTrace___closed__1, &l_Lake_platformTrace___closed__1_once, _init_l_Lake_platformTrace___closed__1);
v___x_138_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_139_ = l_System_Platform_target;
v___x_140_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v___x_138_);
lean_ctor_set(v___x_140_, 2, v___x_136_);
lean_ctor_set_uint64(v___x_140_, sizeof(void*)*3, v___x_137_);
return v___x_140_;
}
}
static lean_object* _init_l_Lake_platformTrace(void){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lean_obj_once(&l_Lake_platformTrace___closed__5, &l_Lake_platformTrace___closed__5_once, _init_l_Lake_platformTrace___closed__5);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg(lean_object* v_a_142_){
_start:
{
lean_object* v_log_144_; uint8_t v_action_145_; uint8_t v_wantsRebuild_146_; lean_object* v_trace_147_; lean_object* v_buildTime_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_159_; 
v_log_144_ = lean_ctor_get(v_a_142_, 0);
v_action_145_ = lean_ctor_get_uint8(v_a_142_, sizeof(void*)*3);
v_wantsRebuild_146_ = lean_ctor_get_uint8(v_a_142_, sizeof(void*)*3 + 1);
v_trace_147_ = lean_ctor_get(v_a_142_, 1);
v_buildTime_148_ = lean_ctor_get(v_a_142_, 2);
v_isSharedCheck_159_ = !lean_is_exclusive(v_a_142_);
if (v_isSharedCheck_159_ == 0)
{
v___x_150_ = v_a_142_;
v_isShared_151_ = v_isSharedCheck_159_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_buildTime_148_);
lean_inc(v_trace_147_);
lean_inc(v_log_144_);
lean_dec(v_a_142_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_159_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_156_; 
v___x_152_ = l_Lake_platformTrace;
v___x_153_ = lean_box(0);
v___x_154_ = l_Lake_BuildTrace_mix(v_trace_147_, v___x_152_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 1, v___x_154_);
v___x_156_ = v___x_150_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_log_144_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_158_, 2, v_buildTime_148_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, sizeof(void*)*3, v_action_145_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, sizeof(void*)*3 + 1, v_wantsRebuild_146_);
v___x_156_ = v_reuseFailAlloc_158_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_157_; 
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_153_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
return v___x_157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg___boxed(lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lake_addPlatformTrace___redArg(v_a_160_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace(lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_log_170_; uint8_t v_action_171_; uint8_t v_wantsRebuild_172_; lean_object* v_trace_173_; lean_object* v_buildTime_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_185_; 
v_log_170_ = lean_ctor_get(v_a_168_, 0);
v_action_171_ = lean_ctor_get_uint8(v_a_168_, sizeof(void*)*3);
v_wantsRebuild_172_ = lean_ctor_get_uint8(v_a_168_, sizeof(void*)*3 + 1);
v_trace_173_ = lean_ctor_get(v_a_168_, 1);
v_buildTime_174_ = lean_ctor_get(v_a_168_, 2);
v_isSharedCheck_185_ = !lean_is_exclusive(v_a_168_);
if (v_isSharedCheck_185_ == 0)
{
v___x_176_ = v_a_168_;
v_isShared_177_ = v_isSharedCheck_185_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_buildTime_174_);
lean_inc(v_trace_173_);
lean_inc(v_log_170_);
lean_dec(v_a_168_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_185_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_182_; 
v___x_178_ = l_Lake_platformTrace;
v___x_179_ = lean_box(0);
v___x_180_ = l_Lake_BuildTrace_mix(v_trace_173_, v___x_178_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 1, v___x_180_);
v___x_182_ = v___x_176_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_log_170_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v___x_180_);
lean_ctor_set(v_reuseFailAlloc_184_, 2, v_buildTime_174_);
lean_ctor_set_uint8(v_reuseFailAlloc_184_, sizeof(void*)*3, v_action_171_);
lean_ctor_set_uint8(v_reuseFailAlloc_184_, sizeof(void*)*3 + 1, v_wantsRebuild_172_);
v___x_182_ = v_reuseFailAlloc_184_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___x_183_; 
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_179_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
return v___x_183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___boxed(lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lake_addPlatformTrace(v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec(v_a_188_);
lean_dec(v_a_187_);
lean_dec_ref(v_a_186_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg(lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_log_197_; uint8_t v_action_198_; uint8_t v_wantsRebuild_199_; lean_object* v_trace_200_; lean_object* v_buildTime_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_212_; 
v_log_197_ = lean_ctor_get(v_a_195_, 0);
v_action_198_ = lean_ctor_get_uint8(v_a_195_, sizeof(void*)*3);
v_wantsRebuild_199_ = lean_ctor_get_uint8(v_a_195_, sizeof(void*)*3 + 1);
v_trace_200_ = lean_ctor_get(v_a_195_, 1);
v_buildTime_201_ = lean_ctor_get(v_a_195_, 2);
v_isSharedCheck_212_ = !lean_is_exclusive(v_a_195_);
if (v_isSharedCheck_212_ == 0)
{
v___x_203_ = v_a_195_;
v_isShared_204_ = v_isSharedCheck_212_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_buildTime_201_);
lean_inc(v_trace_200_);
lean_inc(v_log_197_);
lean_dec(v_a_195_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_212_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v_leanTrace_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_209_; 
v_leanTrace_205_ = lean_ctor_get(v_a_194_, 2);
lean_inc_ref(v_leanTrace_205_);
lean_dec_ref(v_a_194_);
v___x_206_ = lean_box(0);
v___x_207_ = l_Lake_BuildTrace_mix(v_trace_200_, v_leanTrace_205_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 1, v___x_207_);
v___x_209_ = v___x_203_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_log_197_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v___x_207_);
lean_ctor_set(v_reuseFailAlloc_211_, 2, v_buildTime_201_);
lean_ctor_set_uint8(v_reuseFailAlloc_211_, sizeof(void*)*3, v_action_198_);
lean_ctor_set_uint8(v_reuseFailAlloc_211_, sizeof(void*)*3 + 1, v_wantsRebuild_199_);
v___x_209_ = v_reuseFailAlloc_211_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_210_; 
v___x_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_206_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
return v___x_210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg___boxed(lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lake_addLeanTrace___redArg(v_a_213_, v_a_214_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace(lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_log_224_; uint8_t v_action_225_; uint8_t v_wantsRebuild_226_; lean_object* v_trace_227_; lean_object* v_buildTime_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_239_; 
v_log_224_ = lean_ctor_get(v_a_222_, 0);
v_action_225_ = lean_ctor_get_uint8(v_a_222_, sizeof(void*)*3);
v_wantsRebuild_226_ = lean_ctor_get_uint8(v_a_222_, sizeof(void*)*3 + 1);
v_trace_227_ = lean_ctor_get(v_a_222_, 1);
v_buildTime_228_ = lean_ctor_get(v_a_222_, 2);
v_isSharedCheck_239_ = !lean_is_exclusive(v_a_222_);
if (v_isSharedCheck_239_ == 0)
{
v___x_230_ = v_a_222_;
v_isShared_231_ = v_isSharedCheck_239_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_buildTime_228_);
lean_inc(v_trace_227_);
lean_inc(v_log_224_);
lean_dec(v_a_222_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_239_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v_leanTrace_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v_leanTrace_232_ = lean_ctor_get(v_a_221_, 2);
lean_inc_ref(v_leanTrace_232_);
lean_dec_ref(v_a_221_);
v___x_233_ = lean_box(0);
v___x_234_ = l_Lake_BuildTrace_mix(v_trace_227_, v_leanTrace_232_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 1, v___x_234_);
v___x_236_ = v___x_230_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_log_224_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_238_, 2, v_buildTime_228_);
lean_ctor_set_uint8(v_reuseFailAlloc_238_, sizeof(void*)*3, v_action_225_);
lean_ctor_set_uint8(v_reuseFailAlloc_238_, sizeof(void*)*3 + 1, v_wantsRebuild_226_);
v___x_236_ = v_reuseFailAlloc_238_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_237_; 
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_233_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
return v___x_237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___boxed(lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lake_addLeanTrace(v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
lean_dec(v_a_243_);
lean_dec(v_a_242_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg(lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_a_251_, lean_object* v_caption_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_log_255_; uint8_t v_action_256_; uint8_t v_wantsRebuild_257_; lean_object* v_trace_258_; lean_object* v_buildTime_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_278_; 
v_log_255_ = lean_ctor_get(v_a_253_, 0);
v_action_256_ = lean_ctor_get_uint8(v_a_253_, sizeof(void*)*3);
v_wantsRebuild_257_ = lean_ctor_get_uint8(v_a_253_, sizeof(void*)*3 + 1);
v_trace_258_ = lean_ctor_get(v_a_253_, 1);
v_buildTime_259_ = lean_ctor_get(v_a_253_, 2);
v_isSharedCheck_278_ = !lean_is_exclusive(v_a_253_);
if (v_isSharedCheck_278_ == 0)
{
v___x_261_ = v_a_253_;
v_isShared_262_ = v_isSharedCheck_278_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_buildTime_259_);
lean_inc(v_trace_258_);
lean_inc(v_log_255_);
lean_dec(v_a_253_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_278_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; uint64_t v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
lean_inc(v_a_251_);
v___x_263_ = lean_apply_1(v_inst_250_, v_a_251_);
v___x_264_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_265_ = ((lean_object*)(l_Lake_addPureTrace___redArg___closed__0));
v___x_266_ = lean_string_append(v_caption_252_, v___x_265_);
v___x_267_ = lean_apply_1(v_inst_249_, v_a_251_);
v___x_268_ = lean_string_append(v___x_266_, v___x_267_);
lean_dec_ref(v___x_267_);
v___x_269_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_270_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_270_, 0, v___x_268_);
lean_ctor_set(v___x_270_, 1, v___x_264_);
lean_ctor_set(v___x_270_, 2, v___x_269_);
v___x_271_ = lean_unbox_uint64(v___x_263_);
lean_dec_ref(v___x_263_);
lean_ctor_set_uint64(v___x_270_, sizeof(void*)*3, v___x_271_);
v___x_272_ = lean_box(0);
v___x_273_ = l_Lake_BuildTrace_mix(v_trace_258_, v___x_270_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v___x_273_);
v___x_275_ = v___x_261_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_log_255_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v_buildTime_259_);
lean_ctor_set_uint8(v_reuseFailAlloc_277_, sizeof(void*)*3, v_action_256_);
lean_ctor_set_uint8(v_reuseFailAlloc_277_, sizeof(void*)*3 + 1, v_wantsRebuild_257_);
v___x_275_ = v_reuseFailAlloc_277_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_276_; 
v___x_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_272_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
return v___x_276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg___boxed(lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_a_281_, lean_object* v_caption_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lake_addPureTrace___redArg(v_inst_279_, v_inst_280_, v_a_281_, v_caption_282_, v_a_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace(lean_object* v_00_u03b1_286_, lean_object* v_inst_287_, lean_object* v_inst_288_, lean_object* v_a_289_, lean_object* v_caption_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_log_298_; uint8_t v_action_299_; uint8_t v_wantsRebuild_300_; lean_object* v_trace_301_; lean_object* v_buildTime_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_321_; 
v_log_298_ = lean_ctor_get(v_a_296_, 0);
v_action_299_ = lean_ctor_get_uint8(v_a_296_, sizeof(void*)*3);
v_wantsRebuild_300_ = lean_ctor_get_uint8(v_a_296_, sizeof(void*)*3 + 1);
v_trace_301_ = lean_ctor_get(v_a_296_, 1);
v_buildTime_302_ = lean_ctor_get(v_a_296_, 2);
v_isSharedCheck_321_ = !lean_is_exclusive(v_a_296_);
if (v_isSharedCheck_321_ == 0)
{
v___x_304_ = v_a_296_;
v_isShared_305_ = v_isSharedCheck_321_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_buildTime_302_);
lean_inc(v_trace_301_);
lean_inc(v_log_298_);
lean_dec(v_a_296_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_321_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; uint64_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_318_; 
lean_inc(v_a_289_);
v___x_306_ = lean_apply_1(v_inst_288_, v_a_289_);
v___x_307_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_308_ = ((lean_object*)(l_Lake_addPureTrace___redArg___closed__0));
v___x_309_ = lean_string_append(v_caption_290_, v___x_308_);
v___x_310_ = lean_apply_1(v_inst_287_, v_a_289_);
v___x_311_ = lean_string_append(v___x_309_, v___x_310_);
lean_dec_ref(v___x_310_);
v___x_312_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_313_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_313_, 0, v___x_311_);
lean_ctor_set(v___x_313_, 1, v___x_307_);
lean_ctor_set(v___x_313_, 2, v___x_312_);
v___x_314_ = lean_unbox_uint64(v___x_306_);
lean_dec_ref(v___x_306_);
lean_ctor_set_uint64(v___x_313_, sizeof(void*)*3, v___x_314_);
v___x_315_ = lean_box(0);
v___x_316_ = l_Lake_BuildTrace_mix(v_trace_301_, v___x_313_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 1, v___x_316_);
v___x_318_ = v___x_304_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_log_298_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v___x_316_);
lean_ctor_set(v_reuseFailAlloc_320_, 2, v_buildTime_302_);
lean_ctor_set_uint8(v_reuseFailAlloc_320_, sizeof(void*)*3, v_action_299_);
lean_ctor_set_uint8(v_reuseFailAlloc_320_, sizeof(void*)*3 + 1, v_wantsRebuild_300_);
v___x_318_ = v_reuseFailAlloc_320_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_319_; 
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_315_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
return v___x_319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace___boxed(lean_object* v_00_u03b1_322_, lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_a_325_, lean_object* v_caption_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lake_addPureTrace(v_00_u03b1_322_, v_inst_323_, v_inst_324_, v_a_325_, v_caption_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(lean_object* v_x_337_){
_start:
{
if (lean_obj_tag(v_x_337_) == 0)
{
lean_object* v___x_338_; 
v___x_338_ = lean_box(0);
return v___x_338_;
}
else
{
lean_object* v_val_339_; 
v_val_339_ = lean_ctor_get(v_x_337_, 0);
lean_inc(v_val_339_);
return v_val_339_;
}
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1___boxed(lean_object* v_x_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(v_x_340_);
lean_dec(v_x_340_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0(lean_object* v_x_342_){
_start:
{
lean_object* v_fst_343_; lean_object* v_snd_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_fst_343_ = lean_ctor_get(v_x_342_, 0);
lean_inc(v_fst_343_);
v_snd_344_ = lean_ctor_get(v_x_342_, 1);
lean_inc(v_snd_344_);
lean_dec_ref(v_x_342_);
v___x_345_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_345_, 0, v_fst_343_);
v___x_346_ = lean_unsigned_to_nat(2u);
v___x_347_ = lean_mk_empty_array_with_capacity(v___x_346_);
v___x_348_ = lean_array_push(v___x_347_, v___x_345_);
v___x_349_ = lean_array_push(v___x_348_, v_snd_344_);
v___x_350_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(size_t v_sz_351_, size_t v_i_352_, lean_object* v_bs_353_){
_start:
{
uint8_t v___x_354_; 
v___x_354_ = lean_usize_dec_lt(v_i_352_, v_sz_351_);
if (v___x_354_ == 0)
{
return v_bs_353_;
}
else
{
lean_object* v_v_355_; lean_object* v___x_356_; lean_object* v_bs_x27_357_; lean_object* v___x_358_; size_t v___x_359_; size_t v___x_360_; lean_object* v___x_361_; 
v_v_355_ = lean_array_uget(v_bs_353_, v_i_352_);
v___x_356_ = lean_unsigned_to_nat(0u);
v_bs_x27_357_ = lean_array_uset(v_bs_353_, v_i_352_, v___x_356_);
v___x_358_ = l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0(v_v_355_);
v___x_359_ = ((size_t)1ULL);
v___x_360_ = lean_usize_add(v_i_352_, v___x_359_);
v___x_361_ = lean_array_uset(v_bs_x27_357_, v_i_352_, v___x_358_);
v_i_352_ = v___x_360_;
v_bs_353_ = v___x_361_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1___boxed(lean_object* v_sz_363_, lean_object* v_i_364_, lean_object* v_bs_365_){
_start:
{
size_t v_sz_boxed_366_; size_t v_i_boxed_367_; lean_object* v_res_368_; 
v_sz_boxed_366_ = lean_unbox_usize(v_sz_363_);
lean_dec(v_sz_363_);
v_i_boxed_367_ = lean_unbox_usize(v_i_364_);
lean_dec(v_i_364_);
v_res_368_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(v_sz_boxed_366_, v_i_boxed_367_, v_bs_365_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(lean_object* v_a_369_){
_start:
{
size_t v_sz_370_; size_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_sz_370_ = lean_array_size(v_a_369_);
v___x_371_ = ((size_t)0ULL);
v___x_372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(v_sz_370_, v___x_371_, v_a_369_);
v___x_373_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(size_t v_sz_374_, size_t v_i_375_, lean_object* v_bs_376_){
_start:
{
uint8_t v___x_377_; 
v___x_377_ = lean_usize_dec_lt(v_i_375_, v_sz_374_);
if (v___x_377_ == 0)
{
return v_bs_376_;
}
else
{
lean_object* v_v_378_; lean_object* v___x_379_; lean_object* v_bs_x27_380_; lean_object* v___x_381_; size_t v___x_382_; size_t v___x_383_; lean_object* v___x_384_; 
v_v_378_ = lean_array_uget(v_bs_376_, v_i_375_);
v___x_379_ = lean_unsigned_to_nat(0u);
v_bs_x27_380_ = lean_array_uset(v_bs_376_, v_i_375_, v___x_379_);
v___x_381_ = l_Lake_instToJsonLogEntry_toJson(v_v_378_);
lean_dec(v_v_378_);
v___x_382_ = ((size_t)1ULL);
v___x_383_ = lean_usize_add(v_i_375_, v___x_382_);
v___x_384_ = lean_array_uset(v_bs_x27_380_, v_i_375_, v___x_381_);
v_i_375_ = v___x_383_;
v_bs_376_ = v___x_384_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4___boxed(lean_object* v_sz_386_, lean_object* v_i_387_, lean_object* v_bs_388_){
_start:
{
size_t v_sz_boxed_389_; size_t v_i_boxed_390_; lean_object* v_res_391_; 
v_sz_boxed_389_ = lean_unbox_usize(v_sz_386_);
lean_dec(v_sz_386_);
v_i_boxed_390_ = lean_unbox_usize(v_i_387_);
lean_dec(v_i_387_);
v_res_391_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(v_sz_boxed_389_, v_i_boxed_390_, v_bs_388_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2(lean_object* v_a_392_){
_start:
{
size_t v_sz_393_; size_t v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_sz_393_ = lean_array_size(v_a_392_);
v___x_394_ = ((size_t)0ULL);
v___x_395_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(v_sz_393_, v___x_394_, v_a_392_);
v___x_396_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
return v___x_396_;
}
}
static lean_object* _init_l_Lake_BuildMetadata_toJson___closed__2(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_400_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__1));
v___x_401_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__0));
v___x_402_ = lean_box(1);
v___x_403_ = l_Lake_JsonObject_insertJson(v___x_402_, v___x_401_, v___x_400_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_toJson(lean_object* v_self_409_){
_start:
{
uint64_t v_depHash_410_; lean_object* v_inputs_411_; lean_object* v_outputs_x3f_412_; lean_object* v_log_413_; uint8_t v_synthetic_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v_depHash_410_ = lean_ctor_get_uint64(v_self_409_, sizeof(void*)*3);
v_inputs_411_ = lean_ctor_get(v_self_409_, 0);
lean_inc_ref(v_inputs_411_);
v_outputs_x3f_412_ = lean_ctor_get(v_self_409_, 1);
lean_inc(v_outputs_x3f_412_);
v_log_413_ = lean_ctor_get(v_self_409_, 2);
lean_inc_ref(v_log_413_);
v_synthetic_414_ = lean_ctor_get_uint8(v_self_409_, sizeof(void*)*3 + 8);
lean_dec_ref(v_self_409_);
v___x_415_ = lean_obj_once(&l_Lake_BuildMetadata_toJson___closed__2, &l_Lake_BuildMetadata_toJson___closed__2_once, _init_l_Lake_BuildMetadata_toJson___closed__2);
v___x_416_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__3));
v___x_417_ = l_Lake_Hash_hex(v_depHash_410_);
v___x_418_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
v___x_419_ = l_Lake_JsonObject_insertJson(v___x_415_, v___x_416_, v___x_418_);
v___x_420_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__4));
v___x_421_ = l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(v_inputs_411_);
v___x_422_ = l_Lake_JsonObject_insertJson(v___x_419_, v___x_420_, v___x_421_);
v___x_423_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__5));
v___x_424_ = l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(v_outputs_x3f_412_);
lean_dec(v_outputs_x3f_412_);
v___x_425_ = l_Lake_JsonObject_insertJson(v___x_422_, v___x_423_, v___x_424_);
v___x_426_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__6));
v___x_427_ = l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2(v_log_413_);
v___x_428_ = l_Lake_JsonObject_insertJson(v___x_425_, v___x_426_, v___x_427_);
v___x_429_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__7));
v___x_430_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_430_, 0, v_synthetic_414_);
v___x_431_ = l_Lake_JsonObject_insertJson(v___x_428_, v___x_429_, v___x_430_);
v___x_432_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub(uint64_t v_hash_437_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; lean_object* v___x_441_; 
v___x_438_ = ((lean_object*)(l_Lake_BuildMetadata_ofStub___closed__0));
v___x_439_ = lean_box(0);
v___x_440_ = 0;
v___x_441_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_441_, 0, v___x_438_);
lean_ctor_set(v___x_441_, 1, v___x_439_);
lean_ctor_set(v___x_441_, 2, v___x_438_);
lean_ctor_set_uint64(v___x_441_, sizeof(void*)*3, v_hash_437_);
lean_ctor_set_uint8(v___x_441_, sizeof(void*)*3 + 8, v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub___boxed(lean_object* v_hash_442_){
_start:
{
uint64_t v_hash_boxed_443_; lean_object* v_res_444_; 
v_hash_boxed_443_ = lean_unbox_uint64(v_hash_442_);
lean_dec_ref(v_hash_442_);
v_res_444_ = l_Lake_BuildMetadata_ofStub(v_hash_boxed_443_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(lean_object* v_x_447_){
_start:
{
if (lean_obj_tag(v_x_447_) == 0)
{
lean_object* v___x_448_; 
v___x_448_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0));
return v___x_448_;
}
else
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_Json_getBool_x3f(v_x_447_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_466_; 
v_a_458_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_466_ == 0)
{
v___x_460_ = v___x_449_;
v_isShared_461_ = v_isSharedCheck_466_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_449_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_466_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_462_, 0, v_a_458_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v___x_462_);
v___x_464_ = v___x_460_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___boxed(lean_object* v_x_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(v_x_467_);
lean_dec(v_x_467_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3(lean_object* v_x_471_){
_start:
{
if (lean_obj_tag(v_x_471_) == 0)
{
lean_object* v___x_472_; 
v___x_472_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0));
return v___x_472_;
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_473_, 0, v_x_471_);
v___x_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2(lean_object* v_x_477_){
_start:
{
if (lean_obj_tag(v_x_477_) == 0)
{
lean_object* v___x_478_; 
v___x_478_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0));
return v___x_478_;
}
else
{
lean_object* v___x_479_; lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_488_; 
v___x_479_ = l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3(v_x_477_);
v_a_480_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_488_ == 0)
{
v___x_482_ = v___x_479_;
v_isShared_483_ = v_isSharedCheck_488_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_488_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_484_, 0, v_a_480_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_484_);
v___x_486_ = v___x_482_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(size_t v_sz_489_, size_t v_i_490_, lean_object* v_bs_491_){
_start:
{
uint8_t v___x_492_; 
v___x_492_ = lean_usize_dec_lt(v_i_490_, v_sz_489_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; 
v___x_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_493_, 0, v_bs_491_);
return v___x_493_;
}
else
{
lean_object* v_v_494_; lean_object* v___x_495_; 
v_v_494_ = lean_array_uget_borrowed(v_bs_491_, v_i_490_);
lean_inc(v_v_494_);
v___x_495_ = l_Lake_instFromJsonLogEntry_fromJson(v_v_494_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec_ref(v_bs_491_);
v_a_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
else
{
lean_object* v_a_504_; lean_object* v___x_505_; lean_object* v_bs_x27_506_; size_t v___x_507_; size_t v___x_508_; lean_object* v___x_509_; 
v_a_504_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_504_);
lean_dec_ref(v___x_495_);
v___x_505_ = lean_unsigned_to_nat(0u);
v_bs_x27_506_ = lean_array_uset(v_bs_491_, v_i_490_, v___x_505_);
v___x_507_ = ((size_t)1ULL);
v___x_508_ = lean_usize_add(v_i_490_, v___x_507_);
v___x_509_ = lean_array_uset(v_bs_x27_506_, v_i_490_, v_a_504_);
v_i_490_ = v___x_508_;
v_bs_491_ = v___x_509_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_511_, lean_object* v_i_512_, lean_object* v_bs_513_){
_start:
{
size_t v_sz_boxed_514_; size_t v_i_boxed_515_; lean_object* v_res_516_; 
v_sz_boxed_514_ = lean_unbox_usize(v_sz_511_);
lean_dec(v_sz_511_);
v_i_boxed_515_ = lean_unbox_usize(v_i_512_);
lean_dec(v_i_512_);
v_res_516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(v_sz_boxed_514_, v_i_boxed_515_, v_bs_513_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(lean_object* v_x_519_){
_start:
{
if (lean_obj_tag(v_x_519_) == 4)
{
lean_object* v_elems_520_; size_t v_sz_521_; size_t v___x_522_; lean_object* v___x_523_; 
v_elems_520_ = lean_ctor_get(v_x_519_, 0);
lean_inc_ref(v_elems_520_);
lean_dec_ref(v_x_519_);
v_sz_521_ = lean_array_size(v_elems_520_);
v___x_522_ = ((size_t)0ULL);
v___x_523_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(v_sz_521_, v___x_522_, v_elems_520_);
return v___x_523_;
}
else
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_524_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0));
v___x_525_ = lean_unsigned_to_nat(80u);
v___x_526_ = l_Lean_Json_pretty(v_x_519_, v___x_525_);
v___x_527_ = lean_string_append(v___x_524_, v___x_526_);
lean_dec_ref(v___x_526_);
v___x_528_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1));
v___x_529_ = lean_string_append(v___x_527_, v___x_528_);
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1(lean_object* v_x_533_){
_start:
{
if (lean_obj_tag(v_x_533_) == 0)
{
lean_object* v___x_534_; 
v___x_534_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0));
return v___x_534_;
}
else
{
lean_object* v___x_535_; 
v___x_535_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(v_x_533_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_535_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_535_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_552_; 
v_a_544_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_552_ == 0)
{
v___x_546_ = v___x_535_;
v_isShared_547_ = v_isSharedCheck_552_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_535_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_552_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v_a_544_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_548_);
v___x_550_ = v___x_546_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7(lean_object* v_x_554_){
_start:
{
lean_object* v_j_556_; 
if (lean_obj_tag(v_x_554_) == 4)
{
lean_object* v_elems_564_; lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v_elems_564_ = lean_ctor_get(v_x_554_, 0);
v___x_565_ = lean_array_get_size(v_elems_564_);
v___x_566_ = lean_unsigned_to_nat(2u);
v___x_567_ = lean_nat_dec_eq(v___x_565_, v___x_566_);
if (v___x_567_ == 0)
{
v_j_556_ = v_x_554_;
goto v___jp_555_;
}
else
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
lean_inc_ref(v_elems_564_);
lean_dec_ref(v_x_554_);
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = lean_array_fget_borrowed(v_elems_564_, v___x_568_);
lean_inc(v___x_569_);
v___x_570_ = l_Lean_Json_getStr_x3f(v___x_569_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
lean_dec_ref(v_elems_564_);
v_a_571_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_570_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_570_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
else
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_589_; 
v_a_579_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_589_ == 0)
{
v___x_581_ = v___x_570_;
v_isShared_582_ = v_isSharedCheck_589_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_570_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_589_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_583_ = lean_unsigned_to_nat(1u);
v___x_584_ = lean_array_fget(v_elems_564_, v___x_583_);
lean_dec_ref(v_elems_564_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v_a_579_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___x_585_);
v___x_587_ = v___x_581_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
else
{
v_j_556_ = v_x_554_;
goto v___jp_555_;
}
v___jp_555_:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_557_ = ((lean_object*)(l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0));
v___x_558_ = lean_unsigned_to_nat(80u);
v___x_559_ = l_Lean_Json_pretty(v_j_556_, v___x_558_);
v___x_560_ = lean_string_append(v___x_557_, v___x_559_);
lean_dec_ref(v___x_559_);
v___x_561_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1));
v___x_562_ = lean_string_append(v___x_560_, v___x_561_);
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(size_t v_sz_590_, size_t v_i_591_, lean_object* v_bs_592_){
_start:
{
uint8_t v___x_593_; 
v___x_593_ = lean_usize_dec_lt(v_i_591_, v_sz_590_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; 
v___x_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_594_, 0, v_bs_592_);
return v___x_594_;
}
else
{
lean_object* v_v_595_; lean_object* v___x_596_; 
v_v_595_ = lean_array_uget_borrowed(v_bs_592_, v_i_591_);
lean_inc(v_v_595_);
v___x_596_ = l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7(v_v_595_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_dec_ref(v_bs_592_);
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_596_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
else
{
lean_object* v_a_605_; lean_object* v___x_606_; lean_object* v_bs_x27_607_; size_t v___x_608_; size_t v___x_609_; lean_object* v___x_610_; 
v_a_605_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_605_);
lean_dec_ref(v___x_596_);
v___x_606_ = lean_unsigned_to_nat(0u);
v_bs_x27_607_ = lean_array_uset(v_bs_592_, v_i_591_, v___x_606_);
v___x_608_ = ((size_t)1ULL);
v___x_609_ = lean_usize_add(v_i_591_, v___x_608_);
v___x_610_ = lean_array_uset(v_bs_x27_607_, v_i_591_, v_a_605_);
v_i_591_ = v___x_609_;
v_bs_592_ = v___x_610_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8___boxed(lean_object* v_sz_612_, lean_object* v_i_613_, lean_object* v_bs_614_){
_start:
{
size_t v_sz_boxed_615_; size_t v_i_boxed_616_; lean_object* v_res_617_; 
v_sz_boxed_615_ = lean_unbox_usize(v_sz_612_);
lean_dec(v_sz_612_);
v_i_boxed_616_ = lean_unbox_usize(v_i_613_);
lean_dec(v_i_613_);
v_res_617_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(v_sz_boxed_615_, v_i_boxed_616_, v_bs_614_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5(lean_object* v_x_618_){
_start:
{
if (lean_obj_tag(v_x_618_) == 4)
{
lean_object* v_elems_619_; size_t v_sz_620_; size_t v___x_621_; lean_object* v___x_622_; 
v_elems_619_ = lean_ctor_get(v_x_618_, 0);
lean_inc_ref(v_elems_619_);
lean_dec_ref(v_x_618_);
v_sz_620_ = lean_array_size(v_elems_619_);
v___x_621_ = ((size_t)0ULL);
v___x_622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(v_sz_620_, v___x_621_, v_elems_619_);
return v___x_622_;
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_623_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0));
v___x_624_ = lean_unsigned_to_nat(80u);
v___x_625_ = l_Lean_Json_pretty(v_x_618_, v___x_624_);
v___x_626_ = lean_string_append(v___x_623_, v___x_625_);
lean_dec_ref(v___x_625_);
v___x_627_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1));
v___x_628_ = lean_string_append(v___x_626_, v___x_627_);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
return v___x_629_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3(lean_object* v_x_632_){
_start:
{
if (lean_obj_tag(v_x_632_) == 0)
{
lean_object* v___x_633_; 
v___x_633_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0));
return v___x_633_;
}
else
{
lean_object* v___x_634_; 
v___x_634_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5(v_x_632_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_634_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_634_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_651_; 
v_a_643_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_651_ == 0)
{
v___x_645_ = v___x_634_;
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_634_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_647_, 0, v_a_643_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v___x_647_);
v___x_649_ = v___x_645_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f(lean_object* v_obj_667_){
_start:
{
lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; uint64_t v___y_672_; uint8_t v_a_673_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; uint64_t v___y_680_; lean_object* v___y_683_; lean_object* v___y_684_; uint64_t v___y_685_; lean_object* v_a_686_; lean_object* v___y_713_; lean_object* v___y_714_; uint64_t v___y_715_; lean_object* v___y_718_; uint64_t v___y_719_; lean_object* v_a_720_; lean_object* v___y_746_; uint64_t v___y_747_; uint64_t v___y_750_; lean_object* v_a_751_; uint64_t v___y_777_; uint64_t v_depHash_780_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__0));
v___x_806_ = l_Lake_JsonObject_getJson_x3f(v_obj_667_, v___x_805_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__3));
v___x_808_ = l_Lake_JsonObject_getJson_x3f(v_obj_667_, v___x_807_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v___x_809_; 
v___x_809_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7));
return v___x_809_;
}
else
{
lean_object* v_val_810_; lean_object* v___x_811_; 
v_val_810_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_val_810_);
lean_dec_ref(v___x_808_);
v___x_811_ = l_Lean_Json_getStr_x3f(v_val_810_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_821_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_821_ == 0)
{
v___x_814_ = v___x_811_;
v_isShared_815_ = v_isSharedCheck_821_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_821_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_816_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8));
v___x_817_ = lean_string_append(v___x_816_, v_a_812_);
lean_dec(v_a_812_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_817_);
v___x_819_ = v___x_814_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
else
{
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
v_a_822_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_811_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_811_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set_tag(v___x_824_, 0);
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_831_; 
v_a_830_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_830_);
lean_dec_ref(v___x_811_);
v___x_831_ = l_Lake_Hash_ofDecimal_x3f(v_a_830_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v___x_832_; 
v___x_832_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__10));
return v___x_832_;
}
else
{
lean_object* v_val_833_; uint64_t v___x_834_; 
v_val_833_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_val_833_);
lean_dec_ref(v___x_831_);
v___x_834_ = lean_unbox_uint64(v_val_833_);
lean_dec(v_val_833_);
v_depHash_780_ = v___x_834_;
goto v___jp_779_;
}
}
}
}
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; 
lean_dec_ref(v___x_806_);
v___x_835_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__3));
v___x_836_ = l_Lake_JsonObject_getJson_x3f(v_obj_667_, v___x_835_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v___x_837_; 
v___x_837_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7));
return v___x_837_;
}
else
{
lean_object* v_val_838_; lean_object* v___x_839_; 
v_val_838_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_val_838_);
lean_dec_ref(v___x_836_);
v___x_839_ = l_Lake_Hash_fromJson_x3f(v_val_838_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_849_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_849_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_849_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_849_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_844_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8));
v___x_845_ = lean_string_append(v___x_844_, v_a_840_);
lean_dec(v_a_840_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_845_);
v___x_847_ = v___x_842_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
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
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
v_a_850_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_839_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_839_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
lean_ctor_set_tag(v___x_852_, 0);
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
else
{
lean_object* v_a_858_; uint64_t v___x_859_; 
v_a_858_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_858_);
lean_dec_ref(v___x_839_);
v___x_859_ = lean_unbox_uint64(v_a_858_);
lean_dec(v_a_858_);
v_depHash_780_ = v___x_859_;
goto v___jp_779_;
}
}
}
}
v___jp_668_:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_674_, 0, v___y_669_);
lean_ctor_set(v___x_674_, 1, v___y_671_);
lean_ctor_set(v___x_674_, 2, v___y_670_);
lean_ctor_set_uint64(v___x_674_, sizeof(void*)*3, v___y_672_);
lean_ctor_set_uint8(v___x_674_, sizeof(void*)*3 + 8, v_a_673_);
v___x_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
return v___x_675_;
}
v___jp_676_:
{
uint8_t v___x_681_; 
v___x_681_ = 0;
v___y_669_ = v___y_677_;
v___y_670_ = v___y_679_;
v___y_671_ = v___y_678_;
v___y_672_ = v___y_680_;
v_a_673_ = v___x_681_;
goto v___jp_668_;
}
v___jp_682_:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__7));
v___x_688_ = l_Lake_JsonObject_getJson_x3f(v_obj_667_, v___x_687_);
if (lean_obj_tag(v___x_688_) == 0)
{
v___y_677_ = v___y_683_;
v___y_678_ = v___y_684_;
v___y_679_ = v_a_686_;
v___y_680_ = v___y_685_;
goto v___jp_676_;
}
else
{
lean_object* v_val_689_; lean_object* v___x_690_; 
v_val_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_val_689_);
lean_dec_ref(v___x_688_);
v___x_690_ = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(v_val_689_);
lean_dec(v_val_689_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_700_; 
lean_dec_ref(v_a_686_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
v_a_691_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_700_ == 0)
{
v___x_693_ = v___x_690_;
v_isShared_694_ = v_isSharedCheck_700_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_690_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_700_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_695_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__0));
v___x_696_ = lean_string_append(v___x_695_, v_a_691_);
lean_dec(v_a_691_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_696_);
v___x_698_ = v___x_693_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
else
{
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_dec_ref(v_a_686_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
v_a_701_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_690_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_690_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set_tag(v___x_703_, 0);
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
else
{
lean_object* v_a_709_; 
v_a_709_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_709_);
lean_dec_ref(v___x_690_);
if (lean_obj_tag(v_a_709_) == 0)
{
v___y_677_ = v___y_683_;
v___y_678_ = v___y_684_;
v___y_679_ = v_a_686_;
v___y_680_ = v___y_685_;
goto v___jp_676_;
}
else
{
lean_object* v_val_710_; uint8_t v___x_711_; 
v_val_710_ = lean_ctor_get(v_a_709_, 0);
lean_inc(v_val_710_);
lean_dec_ref(v_a_709_);
v___x_711_ = lean_unbox(v_val_710_);
lean_dec(v_val_710_);
v___y_669_ = v___y_683_;
v___y_670_ = v_a_686_;
v___y_671_ = v___y_684_;
v___y_672_ = v___y_685_;
v_a_673_ = v___x_711_;
goto v___jp_668_;
}
}
}
}
}
v___jp_712_:
{
lean_object* v___x_716_; 
v___x_716_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___y_683_ = v___y_713_;
v___y_684_ = v___y_714_;
v___y_685_ = v___y_715_;
v_a_686_ = v___x_716_;
goto v___jp_682_;
}
v___jp_717_:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__6));
v___x_722_ = l_Lake_JsonObject_getJson_x3f(v_obj_667_, v___x_721_);
if (lean_obj_tag(v___x_722_) == 0)
{
v___y_713_ = v___y_718_;
v___y_714_ = v_a_720_;
v___y_715_ = v___y_719_;
goto v___jp_712_;
}
else
{
lean_object* v_val_723_; lean_object* v___x_724_; 
v_val_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_val_723_);
lean_dec_ref(v___x_722_);
v___x_724_ = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1(v_val_723_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_734_; 
lean_dec(v_a_720_);
lean_dec_ref(v___y_718_);
v_a_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_734_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_734_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_734_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_729_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2));
v___x_730_ = lean_string_append(v___x_729_, v_a_725_);
lean_dec(v_a_725_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_730_);
v___x_732_ = v___x_727_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
else
{
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec(v_a_720_);
lean_dec_ref(v___y_718_);
v_a_735_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_724_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_724_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
lean_ctor_set_tag(v___x_737_, 0);
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
else
{
lean_object* v_a_743_; 
v_a_743_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_a_743_);
lean_dec_ref(v___x_724_);
if (lean_obj_tag(v_a_743_) == 0)
{
v___y_713_ = v___y_718_;
v___y_714_ = v_a_720_;
v___y_715_ = v___y_719_;
goto v___jp_712_;
}
else
{
lean_object* v_val_744_; 
v_val_744_ = lean_ctor_get(v_a_743_, 0);
lean_inc(v_val_744_);
lean_dec_ref(v_a_743_);
v___y_683_ = v___y_718_;
v___y_684_ = v_a_720_;
v___y_685_ = v___y_719_;
v_a_686_ = v_val_744_;
goto v___jp_682_;
}
}
}
}
}
v___jp_745_:
{
lean_object* v___x_748_; 
v___x_748_ = lean_box(0);
v___y_718_ = v___y_746_;
v___y_719_ = v___y_747_;
v_a_720_ = v___x_748_;
goto v___jp_717_;
}
v___jp_749_:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__5));
v___x_753_ = l_Lake_JsonObject_getJson_x3f(v_obj_667_, v___x_752_);
if (lean_obj_tag(v___x_753_) == 0)
{
v___y_746_ = v_a_751_;
v___y_747_ = v___y_750_;
goto v___jp_745_;
}
else
{
lean_object* v_val_754_; lean_object* v___x_755_; 
v_val_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_val_754_);
lean_dec_ref(v___x_753_);
v___x_755_ = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2(v_val_754_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_765_; 
lean_dec_ref(v_a_751_);
v_a_756_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_765_ == 0)
{
v___x_758_ = v___x_755_;
v_isShared_759_ = v_isSharedCheck_765_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_755_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_765_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_760_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3));
v___x_761_ = lean_string_append(v___x_760_, v_a_756_);
lean_dec(v_a_756_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v___x_761_);
v___x_763_ = v___x_758_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
else
{
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec_ref(v_a_751_);
v_a_766_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_755_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_755_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
lean_ctor_set_tag(v___x_768_, 0);
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
else
{
lean_object* v_a_774_; 
v_a_774_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_774_);
lean_dec_ref(v___x_755_);
if (lean_obj_tag(v_a_774_) == 0)
{
v___y_746_ = v_a_751_;
v___y_747_ = v___y_750_;
goto v___jp_745_;
}
else
{
lean_object* v_val_775_; 
v_val_775_ = lean_ctor_get(v_a_774_, 0);
lean_inc(v_val_775_);
lean_dec_ref(v_a_774_);
v___y_718_ = v_a_751_;
v___y_719_ = v___y_750_;
v_a_720_ = v_val_775_;
goto v___jp_717_;
}
}
}
}
}
v___jp_776_:
{
lean_object* v___x_778_; 
v___x_778_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4));
v___y_750_ = v___y_777_;
v_a_751_ = v___x_778_;
goto v___jp_749_;
}
v___jp_779_:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__4));
v___x_782_ = l_Lake_JsonObject_getJson_x3f(v_obj_667_, v___x_781_);
if (lean_obj_tag(v___x_782_) == 0)
{
v___y_777_ = v_depHash_780_;
goto v___jp_776_;
}
else
{
lean_object* v_val_783_; lean_object* v___x_784_; 
v_val_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_val_783_);
lean_dec_ref(v___x_782_);
v___x_784_ = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3(v_val_783_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_794_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_794_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_794_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_794_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_789_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5));
v___x_790_ = lean_string_append(v___x_789_, v_a_785_);
lean_dec(v_a_785_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_790_);
v___x_792_ = v___x_787_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
else
{
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
v_a_795_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_784_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_784_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
lean_ctor_set_tag(v___x_797_, 0);
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
else
{
lean_object* v_a_803_; 
v_a_803_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_803_);
lean_dec_ref(v___x_784_);
if (lean_obj_tag(v_a_803_) == 0)
{
v___y_777_ = v_depHash_780_;
goto v___jp_776_;
}
else
{
lean_object* v_val_804_; 
v_val_804_ = lean_ctor_get(v_a_803_, 0);
lean_inc(v_val_804_);
lean_dec_ref(v_a_803_);
v___y_750_ = v_depHash_780_;
v_a_751_ = v_val_804_;
goto v___jp_749_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___boxed(lean_object* v_obj_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lake_BuildMetadata_fromJsonObject_x3f(v_obj_860_);
lean_dec(v_obj_860_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f(lean_object* v_json_868_){
_start:
{
switch(lean_obj_tag(v_json_868_))
{
case 2:
{
lean_object* v_n_869_; lean_object* v___x_870_; 
v_n_869_ = lean_ctor_get(v_json_868_, 0);
v___x_870_ = l_Lake_Hash_ofJsonNumber_x3f(v_n_869_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_880_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_880_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_880_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_880_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_875_ = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__0));
v___x_876_ = lean_string_append(v___x_875_, v_a_871_);
lean_dec(v_a_871_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_876_);
v___x_878_ = v___x_873_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_890_; 
v_a_881_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_890_ == 0)
{
v___x_883_ = v___x_870_;
v_isShared_884_ = v_isSharedCheck_890_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_870_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_890_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
uint64_t v___x_885_; lean_object* v___x_886_; lean_object* v___x_888_; 
v___x_885_ = lean_unbox_uint64(v_a_881_);
lean_dec(v_a_881_);
v___x_886_ = l_Lake_BuildMetadata_ofStub(v___x_885_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_886_);
v___x_888_ = v___x_883_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
case 5:
{
lean_object* v_kvPairs_891_; lean_object* v___x_892_; 
v_kvPairs_891_ = lean_ctor_get(v_json_868_, 0);
v___x_892_ = l_Lake_BuildMetadata_fromJsonObject_x3f(v_kvPairs_891_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_918_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_918_ == 0)
{
v___x_895_ = v___x_892_;
v_isShared_896_ = v_isSharedCheck_918_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_892_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_918_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__0));
v___x_904_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_891_, v___x_903_);
if (lean_obj_tag(v___x_904_) == 1)
{
lean_object* v_val_905_; 
v_val_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_val_905_);
lean_dec_ref(v___x_904_);
if (lean_obj_tag(v_val_905_) == 3)
{
lean_object* v_s_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_917_; 
v_s_906_ = lean_ctor_get(v_val_905_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v_val_905_);
if (v_isSharedCheck_917_ == 0)
{
v___x_908_ = v_val_905_;
v_isShared_909_ = v_isSharedCheck_917_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_s_906_);
lean_dec(v_val_905_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_917_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_910_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0));
v___x_911_ = lean_string_dec_eq(v_s_906_, v___x_910_);
lean_dec_ref(v_s_906_);
if (v___x_911_ == 0)
{
lean_del_object(v___x_908_);
goto v___jp_897_;
}
else
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_915_; 
lean_del_object(v___x_895_);
v___x_912_ = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__2));
v___x_913_ = lean_string_append(v___x_912_, v_a_893_);
lean_dec(v_a_893_);
if (v_isShared_909_ == 0)
{
lean_ctor_set_tag(v___x_908_, 0);
lean_ctor_set(v___x_908_, 0, v___x_913_);
v___x_915_ = v___x_908_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_913_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
else
{
lean_dec(v_val_905_);
goto v___jp_897_;
}
}
else
{
lean_dec(v___x_904_);
goto v___jp_897_;
}
v___jp_897_:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_898_ = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__1));
v___x_899_ = lean_string_append(v___x_898_, v_a_893_);
lean_dec(v_a_893_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 0, v___x_899_);
v___x_901_ = v___x_895_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
else
{
return v___x_892_;
}
}
default: 
{
lean_object* v___x_919_; 
v___x_919_ = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__4));
return v___x_919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f___boxed(lean_object* v_json_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lake_BuildMetadata_fromJson_x3f(v_json_920_);
lean_dec(v_json_920_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_parse(lean_object* v_contents_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Lean_Json_parse(v_contents_924_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_925_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_925_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_935_; 
v_a_934_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_934_);
lean_dec_ref(v___x_925_);
v___x_935_ = l_Lake_BuildMetadata_fromJson_x3f(v_a_934_);
lean_dec(v_a_934_);
return v___x_935_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch(uint64_t v_inputHash_936_, lean_object* v_outputs_937_){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; lean_object* v___x_941_; 
v___x_938_ = ((lean_object*)(l_Lake_BuildMetadata_ofStub___closed__0));
v___x_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_939_, 0, v_outputs_937_);
v___x_940_ = 1;
v___x_941_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_941_, 0, v___x_938_);
lean_ctor_set(v___x_941_, 1, v___x_939_);
lean_ctor_set(v___x_941_, 2, v___x_938_);
lean_ctor_set_uint64(v___x_941_, sizeof(void*)*3, v_inputHash_936_);
lean_ctor_set_uint8(v___x_941_, sizeof(void*)*3 + 8, v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch___boxed(lean_object* v_inputHash_942_, lean_object* v_outputs_943_){
_start:
{
uint64_t v_inputHash_boxed_944_; lean_object* v_res_945_; 
v_inputHash_boxed_944_ = lean_unbox_uint64(v_inputHash_942_);
lean_dec_ref(v_inputHash_942_);
v_res_945_ = l_Lake_BuildMetadata_ofFetch(v_inputHash_boxed_944_, v_outputs_943_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(lean_object* v_as_946_, size_t v_i_947_, size_t v_stop_948_, lean_object* v_b_949_){
_start:
{
uint8_t v___x_950_; 
v___x_950_ = lean_usize_dec_eq(v_i_947_, v_stop_948_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; lean_object* v___y_953_; lean_object* v_inputs_960_; uint64_t v_hash_961_; lean_object* v___x_962_; lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_951_ = lean_array_uget_borrowed(v_as_946_, v_i_947_);
v_inputs_960_ = lean_ctor_get(v___x_951_, 1);
v_hash_961_ = lean_ctor_get_uint64(v___x_951_, sizeof(void*)*3);
v___x_962_ = lean_array_get_size(v_inputs_960_);
v___x_963_ = lean_unsigned_to_nat(0u);
v___x_964_ = lean_nat_dec_eq(v___x_962_, v___x_963_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = l___private_Lake_Build_Common_0__Lake_serializeInputs(v_inputs_960_);
v___x_966_ = l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(v___x_965_);
v___y_953_ = v___x_966_;
goto v___jp_952_;
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = l_Lake_Hash_hex(v_hash_961_);
v___x_968_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
v___y_953_ = v___x_968_;
goto v___jp_952_;
}
v___jp_952_:
{
lean_object* v_caption_954_; lean_object* v___x_955_; lean_object* v___x_956_; size_t v___x_957_; size_t v___x_958_; 
v_caption_954_ = lean_ctor_get(v___x_951_, 0);
lean_inc_ref(v_caption_954_);
v___x_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_955_, 0, v_caption_954_);
lean_ctor_set(v___x_955_, 1, v___y_953_);
v___x_956_ = lean_array_push(v_b_949_, v___x_955_);
v___x_957_ = ((size_t)1ULL);
v___x_958_ = lean_usize_add(v_i_947_, v___x_957_);
v_i_947_ = v___x_958_;
v_b_949_ = v___x_956_;
goto _start;
}
}
else
{
return v_b_949_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs(lean_object* v_inputs_969_){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_970_ = lean_unsigned_to_nat(0u);
v___x_971_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4));
v___x_972_ = lean_array_get_size(v_inputs_969_);
v___x_973_ = lean_nat_dec_lt(v___x_970_, v___x_972_);
if (v___x_973_ == 0)
{
return v___x_971_;
}
else
{
uint8_t v___x_974_; 
v___x_974_ = lean_nat_dec_le(v___x_972_, v___x_972_);
if (v___x_974_ == 0)
{
if (v___x_973_ == 0)
{
return v___x_971_;
}
else
{
size_t v___x_975_; size_t v___x_976_; lean_object* v___x_977_; 
v___x_975_ = ((size_t)0ULL);
v___x_976_ = lean_usize_of_nat(v___x_972_);
v___x_977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(v_inputs_969_, v___x_975_, v___x_976_, v___x_971_);
return v___x_977_;
}
}
else
{
size_t v___x_978_; size_t v___x_979_; lean_object* v___x_980_; 
v___x_978_ = ((size_t)0ULL);
v___x_979_ = lean_usize_of_nat(v___x_972_);
v___x_980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(v_inputs_969_, v___x_978_, v___x_979_, v___x_971_);
return v___x_980_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs___boxed(lean_object* v_inputs_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l___private_Lake_Build_Common_0__Lake_serializeInputs(v_inputs_981_);
lean_dec_ref(v_inputs_981_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0___boxed(lean_object* v_as_983_, lean_object* v_i_984_, lean_object* v_stop_985_, lean_object* v_b_986_){
_start:
{
size_t v_i_boxed_987_; size_t v_stop_boxed_988_; lean_object* v_res_989_; 
v_i_boxed_987_ = lean_unbox_usize(v_i_984_);
lean_dec(v_i_984_);
v_stop_boxed_988_ = lean_unbox_usize(v_stop_985_);
lean_dec(v_stop_985_);
v_res_989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(v_as_983_, v_i_boxed_987_, v_stop_boxed_988_, v_b_986_);
lean_dec_ref(v_as_983_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(lean_object* v_depTrace_990_, lean_object* v_outputs_991_, lean_object* v_log_992_){
_start:
{
lean_object* v_inputs_993_; uint64_t v_hash_994_; lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; lean_object* v___x_998_; 
v_inputs_993_ = lean_ctor_get(v_depTrace_990_, 1);
v_hash_994_ = lean_ctor_get_uint64(v_depTrace_990_, sizeof(void*)*3);
v___x_995_ = l___private_Lake_Build_Common_0__Lake_serializeInputs(v_inputs_993_);
v___x_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_996_, 0, v_outputs_991_);
v___x_997_ = 0;
v___x_998_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_998_, 0, v___x_995_);
lean_ctor_set(v___x_998_, 1, v___x_996_);
lean_ctor_set(v___x_998_, 2, v_log_992_);
lean_ctor_set_uint64(v___x_998_, sizeof(void*)*3, v_hash_994_);
lean_ctor_set_uint8(v___x_998_, sizeof(void*)*3 + 8, v___x_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore___boxed(lean_object* v_depTrace_999_, lean_object* v_outputs_1000_, lean_object* v_log_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_999_, v_outputs_1000_, v_log_1001_);
lean_dec_ref(v_depTrace_999_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg(lean_object* v_inst_1003_, lean_object* v_depTrace_1004_, lean_object* v_outputs_1005_, lean_object* v_log_1006_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = lean_apply_1(v_inst_1003_, v_outputs_1005_);
v___x_1008_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1004_, v___x_1007_, v_log_1006_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg___boxed(lean_object* v_inst_1009_, lean_object* v_depTrace_1010_, lean_object* v_outputs_1011_, lean_object* v_log_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lake_BuildMetadata_ofBuild___redArg(v_inst_1009_, v_depTrace_1010_, v_outputs_1011_, v_log_1012_);
lean_dec_ref(v_depTrace_1010_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild(lean_object* v_00_u03b1_1014_, lean_object* v_inst_1015_, lean_object* v_depTrace_1016_, lean_object* v_outputs_1017_, lean_object* v_log_1018_){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = lean_apply_1(v_inst_1015_, v_outputs_1017_);
v___x_1020_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1016_, v___x_1019_, v_log_1018_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___boxed(lean_object* v_00_u03b1_1021_, lean_object* v_inst_1022_, lean_object* v_depTrace_1023_, lean_object* v_outputs_1024_, lean_object* v_log_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lake_BuildMetadata_ofBuild(v_00_u03b1_1021_, v_inst_1022_, v_depTrace_1023_, v_outputs_1024_, v_log_1025_);
lean_dec_ref(v_depTrace_1023_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorIdx(lean_object* v_x_1027_){
_start:
{
switch(lean_obj_tag(v_x_1027_))
{
case 0:
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_unsigned_to_nat(0u);
return v___x_1028_;
}
case 1:
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_unsigned_to_nat(1u);
return v___x_1029_;
}
default: 
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_unsigned_to_nat(2u);
return v___x_1030_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorIdx___boxed(lean_object* v_x_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lake_SavedTrace_ctorIdx(v_x_1031_);
lean_dec(v_x_1031_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim___redArg(lean_object* v_t_1033_, lean_object* v_k_1034_){
_start:
{
if (lean_obj_tag(v_t_1033_) == 2)
{
lean_object* v_data_1035_; lean_object* v___x_1036_; 
v_data_1035_ = lean_ctor_get(v_t_1033_, 0);
lean_inc_ref(v_data_1035_);
lean_dec_ref(v_t_1033_);
v___x_1036_ = lean_apply_1(v_k_1034_, v_data_1035_);
return v___x_1036_;
}
else
{
lean_dec(v_t_1033_);
return v_k_1034_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim(lean_object* v_motive_1037_, lean_object* v_ctorIdx_1038_, lean_object* v_t_1039_, lean_object* v_h_1040_, lean_object* v_k_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1039_, v_k_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim___boxed(lean_object* v_motive_1043_, lean_object* v_ctorIdx_1044_, lean_object* v_t_1045_, lean_object* v_h_1046_, lean_object* v_k_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lake_SavedTrace_ctorElim(v_motive_1043_, v_ctorIdx_1044_, v_t_1045_, v_h_1046_, v_k_1047_);
lean_dec(v_ctorIdx_1044_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_missing_elim___redArg(lean_object* v_t_1049_, lean_object* v_missing_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1049_, v_missing_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_missing_elim(lean_object* v_motive_1052_, lean_object* v_t_1053_, lean_object* v_h_1054_, lean_object* v_missing_1055_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1053_, v_missing_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_invalid_elim___redArg(lean_object* v_t_1057_, lean_object* v_invalid_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1057_, v_invalid_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_invalid_elim(lean_object* v_motive_1060_, lean_object* v_t_1061_, lean_object* v_h_1062_, lean_object* v_invalid_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1061_, v_invalid_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ok_elim___redArg(lean_object* v_t_1065_, lean_object* v_ok_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1065_, v_ok_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ok_elim(lean_object* v_motive_1068_, lean_object* v_t_1069_, lean_object* v_h_1070_, lean_object* v_ok_1071_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1069_, v_ok_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lake_readTraceFile(lean_object* v_path_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_IO_FS_readFile(v_path_1074_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v_a_1080_; lean_object* v___x_1089_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1078_);
lean_dec_ref(v___x_1077_);
v___x_1089_ = l_Lean_Json_parse(v_a_1078_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_a_1090_);
lean_dec_ref(v___x_1089_);
v_a_1080_ = v_a_1090_;
goto v___jp_1079_;
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1092_; 
v_a_1091_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_a_1091_);
lean_dec_ref(v___x_1089_);
v___x_1092_ = l_Lake_BuildMetadata_fromJson_x3f(v_a_1091_);
lean_dec(v_a_1091_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1093_);
lean_dec_ref(v___x_1092_);
v_a_1080_ = v_a_1093_;
goto v___jp_1079_;
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1102_; 
lean_dec_ref(v_path_1074_);
v_a_1094_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1096_ = v___x_1092_;
v_isShared_1097_ = v_isSharedCheck_1102_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1092_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1102_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
lean_ctor_set_tag(v___x_1096_, 2);
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v___x_1100_; 
v___x_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
lean_ctor_set(v___x_1100_, 1, v_a_1075_);
return v___x_1100_;
}
}
}
}
v___jp_1079_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1081_ = ((lean_object*)(l_Lake_addPureTrace___redArg___closed__0));
v___x_1082_ = lean_string_append(v_path_1074_, v___x_1081_);
v___x_1083_ = lean_string_append(v___x_1082_, v_a_1080_);
lean_dec_ref(v_a_1080_);
v___x_1084_ = 2;
v___x_1085_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set_uint8(v___x_1085_, sizeof(void*)*1, v___x_1084_);
v___x_1086_ = lean_array_push(v_a_1075_, v___x_1085_);
v___x_1087_ = lean_box(1);
v___x_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
lean_ctor_set(v___x_1088_, 1, v___x_1086_);
return v___x_1088_;
}
}
else
{
lean_object* v_a_1103_; 
v_a_1103_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1103_);
lean_dec_ref(v___x_1077_);
if (lean_obj_tag(v_a_1103_) == 11)
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_dec_ref(v_a_1103_);
lean_dec_ref(v_path_1074_);
v___x_1104_ = lean_box(0);
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
lean_ctor_set(v___x_1105_, 1, v_a_1075_);
return v___x_1105_;
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1106_ = ((lean_object*)(l_Lake_readTraceFile___closed__0));
v___x_1107_ = lean_string_append(v_path_1074_, v___x_1106_);
v___x_1108_ = lean_io_error_to_string(v_a_1103_);
v___x_1109_ = lean_string_append(v___x_1107_, v___x_1108_);
lean_dec_ref(v___x_1108_);
v___x_1110_ = 3;
v___x_1111_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1111_, 0, v___x_1109_);
lean_ctor_set_uint8(v___x_1111_, sizeof(void*)*1, v___x_1110_);
v___x_1112_ = lean_array_get_size(v_a_1075_);
v___x_1113_ = lean_array_push(v_a_1075_, v___x_1111_);
v___x_1114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1112_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
return v___x_1114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_readTraceFile___boxed(lean_object* v_path_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lake_readTraceFile(v_path_1115_, v_a_1116_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile(lean_object* v_path_1119_, lean_object* v_data_1120_){
_start:
{
lean_object* v___x_1122_; 
lean_inc_ref(v_path_1119_);
v___x_1122_ = l_Lake_createParentDirs(v_path_1119_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
lean_dec_ref(v___x_1122_);
v___x_1123_ = l_Lake_BuildMetadata_toJson(v_data_1120_);
v___x_1124_ = lean_unsigned_to_nat(80u);
v___x_1125_ = l_Lean_Json_pretty(v___x_1123_, v___x_1124_);
v___x_1126_ = l_IO_FS_writeFile(v_path_1119_, v___x_1125_);
lean_dec_ref(v___x_1125_);
lean_dec_ref(v_path_1119_);
return v___x_1126_;
}
else
{
lean_dec_ref(v_data_1120_);
lean_dec_ref(v_path_1119_);
return v___x_1122_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile___boxed(lean_object* v_path_1127_, lean_object* v_data_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lake_BuildMetadata_writeFile(v_path_1127_, v_data_1128_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace(lean_object* v_path_1131_, uint64_t v_inputHash_1132_, lean_object* v_outputs_1133_){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = l_Lake_BuildMetadata_ofFetch(v_inputHash_1132_, v_outputs_1133_);
v___x_1136_ = l_Lake_BuildMetadata_writeFile(v_path_1131_, v___x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace___boxed(lean_object* v_path_1137_, lean_object* v_inputHash_1138_, lean_object* v_outputs_1139_, lean_object* v_a_1140_){
_start:
{
uint64_t v_inputHash_boxed_1141_; lean_object* v_res_1142_; 
v_inputHash_boxed_1141_ = lean_unbox_uint64(v_inputHash_1138_);
lean_dec_ref(v_inputHash_1138_);
v_res_1142_ = l_Lake_writeFetchTrace(v_path_1137_, v_inputHash_boxed_1141_, v_outputs_1139_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg(lean_object* v_inst_1143_, lean_object* v_path_1144_, lean_object* v_depTrace_1145_, lean_object* v_outputs_1146_, lean_object* v_log_1147_){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1149_ = lean_apply_1(v_inst_1143_, v_outputs_1146_);
v___x_1150_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1145_, v___x_1149_, v_log_1147_);
v___x_1151_ = l_Lake_BuildMetadata_writeFile(v_path_1144_, v___x_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg___boxed(lean_object* v_inst_1152_, lean_object* v_path_1153_, lean_object* v_depTrace_1154_, lean_object* v_outputs_1155_, lean_object* v_log_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lake_writeBuildTrace___redArg(v_inst_1152_, v_path_1153_, v_depTrace_1154_, v_outputs_1155_, v_log_1156_);
lean_dec_ref(v_depTrace_1154_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace(lean_object* v_00_u03b1_1159_, lean_object* v_inst_1160_, lean_object* v_path_1161_, lean_object* v_depTrace_1162_, lean_object* v_outputs_1163_, lean_object* v_log_1164_){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = lean_apply_1(v_inst_1160_, v_outputs_1163_);
v___x_1167_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1162_, v___x_1166_, v_log_1164_);
v___x_1168_ = l_Lake_BuildMetadata_writeFile(v_path_1161_, v___x_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___boxed(lean_object* v_00_u03b1_1169_, lean_object* v_inst_1170_, lean_object* v_path_1171_, lean_object* v_depTrace_1172_, lean_object* v_outputs_1173_, lean_object* v_log_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lake_writeBuildTrace(v_00_u03b1_1169_, v_inst_1170_, v_path_1171_, v_depTrace_1172_, v_outputs_1173_, v_log_1174_);
lean_dec_ref(v_depTrace_1172_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorIdx(uint8_t v_x_1177_){
_start:
{
switch(v_x_1177_)
{
case 0:
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_unsigned_to_nat(0u);
return v___x_1178_;
}
case 1:
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_unsigned_to_nat(1u);
return v___x_1179_;
}
default: 
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_unsigned_to_nat(2u);
return v___x_1180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorIdx___boxed(lean_object* v_x_1181_){
_start:
{
uint8_t v_x_boxed_1182_; lean_object* v_res_1183_; 
v_x_boxed_1182_ = lean_unbox(v_x_1181_);
v_res_1183_ = l_Lake_OutputStatus_ctorIdx(v_x_boxed_1182_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_toCtorIdx(uint8_t v_x_1184_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lake_OutputStatus_ctorIdx(v_x_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_toCtorIdx___boxed(lean_object* v_x_1186_){
_start:
{
uint8_t v_x_4__boxed_1187_; lean_object* v_res_1188_; 
v_x_4__boxed_1187_ = lean_unbox(v_x_1186_);
v_res_1188_ = l_Lake_OutputStatus_toCtorIdx(v_x_4__boxed_1187_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg(lean_object* v_k_1189_){
_start:
{
lean_inc(v_k_1189_);
return v_k_1189_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg___boxed(lean_object* v_k_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lake_OutputStatus_ctorElim___redArg(v_k_1190_);
lean_dec(v_k_1190_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim(lean_object* v_motive_1192_, lean_object* v_ctorIdx_1193_, uint8_t v_t_1194_, lean_object* v_h_1195_, lean_object* v_k_1196_){
_start:
{
lean_inc(v_k_1196_);
return v_k_1196_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___boxed(lean_object* v_motive_1197_, lean_object* v_ctorIdx_1198_, lean_object* v_t_1199_, lean_object* v_h_1200_, lean_object* v_k_1201_){
_start:
{
uint8_t v_t_boxed_1202_; lean_object* v_res_1203_; 
v_t_boxed_1202_ = lean_unbox(v_t_1199_);
v_res_1203_ = l_Lake_OutputStatus_ctorElim(v_motive_1197_, v_ctorIdx_1198_, v_t_boxed_1202_, v_h_1200_, v_k_1201_);
lean_dec(v_k_1201_);
lean_dec(v_ctorIdx_1198_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg(lean_object* v_outOfDate_1204_){
_start:
{
lean_inc(v_outOfDate_1204_);
return v_outOfDate_1204_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg___boxed(lean_object* v_outOfDate_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lake_OutputStatus_outOfDate_elim___redArg(v_outOfDate_1205_);
lean_dec(v_outOfDate_1205_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim(lean_object* v_motive_1207_, uint8_t v_t_1208_, lean_object* v_h_1209_, lean_object* v_outOfDate_1210_){
_start:
{
lean_inc(v_outOfDate_1210_);
return v_outOfDate_1210_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___boxed(lean_object* v_motive_1211_, lean_object* v_t_1212_, lean_object* v_h_1213_, lean_object* v_outOfDate_1214_){
_start:
{
uint8_t v_t_boxed_1215_; lean_object* v_res_1216_; 
v_t_boxed_1215_ = lean_unbox(v_t_1212_);
v_res_1216_ = l_Lake_OutputStatus_outOfDate_elim(v_motive_1211_, v_t_boxed_1215_, v_h_1213_, v_outOfDate_1214_);
lean_dec(v_outOfDate_1214_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg(lean_object* v_mtimeUpToDate_1217_){
_start:
{
lean_inc(v_mtimeUpToDate_1217_);
return v_mtimeUpToDate_1217_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg___boxed(lean_object* v_mtimeUpToDate_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Lake_OutputStatus_mtimeUpToDate_elim___redArg(v_mtimeUpToDate_1218_);
lean_dec(v_mtimeUpToDate_1218_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim(lean_object* v_motive_1220_, uint8_t v_t_1221_, lean_object* v_h_1222_, lean_object* v_mtimeUpToDate_1223_){
_start:
{
lean_inc(v_mtimeUpToDate_1223_);
return v_mtimeUpToDate_1223_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___boxed(lean_object* v_motive_1224_, lean_object* v_t_1225_, lean_object* v_h_1226_, lean_object* v_mtimeUpToDate_1227_){
_start:
{
uint8_t v_t_boxed_1228_; lean_object* v_res_1229_; 
v_t_boxed_1228_ = lean_unbox(v_t_1225_);
v_res_1229_ = l_Lake_OutputStatus_mtimeUpToDate_elim(v_motive_1224_, v_t_boxed_1228_, v_h_1226_, v_mtimeUpToDate_1227_);
lean_dec(v_mtimeUpToDate_1227_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg(lean_object* v_hashUpToDate_1230_){
_start:
{
lean_inc(v_hashUpToDate_1230_);
return v_hashUpToDate_1230_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg___boxed(lean_object* v_hashUpToDate_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lake_OutputStatus_hashUpToDate_elim___redArg(v_hashUpToDate_1231_);
lean_dec(v_hashUpToDate_1231_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim(lean_object* v_motive_1233_, uint8_t v_t_1234_, lean_object* v_h_1235_, lean_object* v_hashUpToDate_1236_){
_start:
{
lean_inc(v_hashUpToDate_1236_);
return v_hashUpToDate_1236_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___boxed(lean_object* v_motive_1237_, lean_object* v_t_1238_, lean_object* v_h_1239_, lean_object* v_hashUpToDate_1240_){
_start:
{
uint8_t v_t_boxed_1241_; lean_object* v_res_1242_; 
v_t_boxed_1241_ = lean_unbox(v_t_1238_);
v_res_1242_ = l_Lake_OutputStatus_hashUpToDate_elim(v_motive_1237_, v_t_boxed_1241_, v_h_1239_, v_hashUpToDate_1240_);
lean_dec(v_hashUpToDate_1240_);
return v_res_1242_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofNat(lean_object* v_n_1243_){
_start:
{
lean_object* v___x_1244_; uint8_t v___x_1245_; 
v___x_1244_ = lean_unsigned_to_nat(0u);
v___x_1245_ = lean_nat_dec_le(v_n_1243_, v___x_1244_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; uint8_t v___x_1247_; 
v___x_1246_ = lean_unsigned_to_nat(1u);
v___x_1247_ = lean_nat_dec_le(v_n_1243_, v___x_1246_);
if (v___x_1247_ == 0)
{
uint8_t v___x_1248_; 
v___x_1248_ = 2;
return v___x_1248_;
}
else
{
uint8_t v___x_1249_; 
v___x_1249_ = 1;
return v___x_1249_;
}
}
else
{
uint8_t v___x_1250_; 
v___x_1250_ = 0;
return v___x_1250_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofNat___boxed(lean_object* v_n_1251_){
_start:
{
uint8_t v_res_1252_; lean_object* v_r_1253_; 
v_res_1252_ = l_Lake_OutputStatus_ofNat(v_n_1251_);
lean_dec(v_n_1251_);
v_r_1253_ = lean_box(v_res_1252_);
return v_r_1253_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqOutputStatus(uint8_t v_x_1254_, uint8_t v_y_1255_){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v___x_1256_ = l_Lake_OutputStatus_ctorIdx(v_x_1254_);
v___x_1257_ = l_Lake_OutputStatus_ctorIdx(v_y_1255_);
v___x_1258_ = lean_nat_dec_eq(v___x_1256_, v___x_1257_);
lean_dec(v___x_1257_);
lean_dec(v___x_1256_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqOutputStatus___boxed(lean_object* v_x_1259_, lean_object* v_y_1260_){
_start:
{
uint8_t v_x_13__boxed_1261_; uint8_t v_y_14__boxed_1262_; uint8_t v_res_1263_; lean_object* v_r_1264_; 
v_x_13__boxed_1261_ = lean_unbox(v_x_1259_);
v_y_14__boxed_1262_ = lean_unbox(v_y_1260_);
v_res_1263_ = l_Lake_instDecidableEqOutputStatus(v_x_13__boxed_1261_, v_y_14__boxed_1262_);
v_r_1264_ = lean_box(v_res_1263_);
return v_r_1264_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofHashCheck(uint8_t v_upToDate_1265_){
_start:
{
if (v_upToDate_1265_ == 0)
{
uint8_t v___x_1266_; 
v___x_1266_ = 0;
return v___x_1266_;
}
else
{
uint8_t v___x_1267_; 
v___x_1267_ = 2;
return v___x_1267_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofHashCheck___boxed(lean_object* v_upToDate_1268_){
_start:
{
uint8_t v_upToDate_boxed_1269_; uint8_t v_res_1270_; lean_object* v_r_1271_; 
v_upToDate_boxed_1269_ = lean_unbox(v_upToDate_1268_);
v_res_1270_ = l_Lake_OutputStatus_ofHashCheck(v_upToDate_boxed_1269_);
v_r_1271_ = lean_box(v_res_1270_);
return v_r_1271_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofMTimeCheck(uint8_t v_upToDate_1272_){
_start:
{
if (v_upToDate_1272_ == 0)
{
uint8_t v___x_1273_; 
v___x_1273_ = 0;
return v___x_1273_;
}
else
{
uint8_t v___x_1274_; 
v___x_1274_ = 1;
return v___x_1274_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofMTimeCheck___boxed(lean_object* v_upToDate_1275_){
_start:
{
uint8_t v_upToDate_boxed_1276_; uint8_t v_res_1277_; lean_object* v_r_1278_; 
v_upToDate_boxed_1276_ = lean_unbox(v_upToDate_1275_);
v_res_1277_ = l_Lake_OutputStatus_ofMTimeCheck(v_upToDate_boxed_1276_);
v_r_1278_ = lean_box(v_res_1277_);
return v_r_1278_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isUpToDate(uint8_t v_status_1279_){
_start:
{
uint8_t v___x_1280_; uint8_t v___x_1281_; 
v___x_1280_ = 0;
v___x_1281_ = l_Lake_instDecidableEqOutputStatus(v_status_1279_, v___x_1280_);
if (v___x_1281_ == 0)
{
uint8_t v___x_1282_; 
v___x_1282_ = 1;
return v___x_1282_;
}
else
{
uint8_t v___x_1283_; 
v___x_1283_ = 0;
return v___x_1283_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isUpToDate___boxed(lean_object* v_status_1284_){
_start:
{
uint8_t v_status_boxed_1285_; uint8_t v_res_1286_; lean_object* v_r_1287_; 
v_status_boxed_1285_ = lean_unbox(v_status_1284_);
v_res_1286_ = l_Lake_OutputStatus_isUpToDate(v_status_boxed_1285_);
v_r_1287_ = lean_box(v_res_1286_);
return v_r_1287_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isCacheable(uint8_t v_status_1288_){
_start:
{
uint8_t v___x_1289_; uint8_t v___x_1290_; 
v___x_1289_ = 1;
v___x_1290_ = l_Lake_instDecidableEqOutputStatus(v_status_1288_, v___x_1289_);
if (v___x_1290_ == 0)
{
uint8_t v___x_1291_; 
v___x_1291_ = 1;
return v___x_1291_;
}
else
{
uint8_t v___x_1292_; 
v___x_1292_ = 0;
return v___x_1292_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isCacheable___boxed(lean_object* v_status_1293_){
_start:
{
uint8_t v_status_boxed_1294_; uint8_t v_res_1295_; lean_object* v_r_1296_; 
v_status_boxed_1294_ = lean_unbox(v_status_1293_);
v_res_1295_ = l_Lake_OutputStatus_isCacheable(v_status_boxed_1294_);
v_r_1296_ = lean_box(v_res_1295_);
return v_r_1296_;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___f_1298_; 
v___x_1297_ = lean_alloc_closure((void*)(l_Lake_instDecidableEqHash___boxed), 2, 0);
v___f_1298_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1298_, 0, v___x_1297_);
return v___f_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(lean_object* v_inst_1299_, lean_object* v_inst_1300_, lean_object* v_info_1301_, lean_object* v_depTrace_1302_, lean_object* v_depHash_1303_, lean_object* v_oldTrace_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
uint64_t v_hash_1308_; lean_object* v___f_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v_hash_1308_ = lean_ctor_get_uint64(v_depTrace_1302_, sizeof(void*)*3);
v___f_1309_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0);
v___x_1310_ = lean_box_uint64(v_hash_1308_);
v___x_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
v___x_1312_ = l_Option_instBEq_beq___redArg(v___f_1309_, v___x_1311_, v_depHash_1303_);
if (v___x_1312_ == 0)
{
lean_object* v_toBuildConfig_1313_; uint8_t v_oldMode_1314_; 
lean_dec_ref(v_inst_1299_);
v_toBuildConfig_1313_ = lean_ctor_get(v_a_1305_, 0);
v_oldMode_1314_ = lean_ctor_get_uint8(v_toBuildConfig_1313_, sizeof(void*)*2);
if (v_oldMode_1314_ == 0)
{
uint8_t v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_dec(v_info_1301_);
lean_dec_ref(v_inst_1300_);
v___x_1315_ = 0;
v___x_1316_ = lean_box(v___x_1315_);
v___x_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
lean_ctor_set(v___x_1317_, 1, v_a_1306_);
return v___x_1317_;
}
else
{
uint8_t v___x_1318_; 
v___x_1318_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1300_, v_info_1301_, v_oldTrace_1304_);
if (v___x_1318_ == 0)
{
uint8_t v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1319_ = 0;
v___x_1320_ = lean_box(v___x_1319_);
v___x_1321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
lean_ctor_set(v___x_1321_, 1, v_a_1306_);
return v___x_1321_;
}
else
{
uint8_t v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1322_ = 1;
v___x_1323_ = lean_box(v___x_1322_);
v___x_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
lean_ctor_set(v___x_1324_, 1, v_a_1306_);
return v___x_1324_;
}
}
}
else
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
lean_dec_ref(v_inst_1300_);
v___x_1325_ = lean_apply_2(v_inst_1299_, v_info_1301_, lean_box(0));
v___x_1326_ = lean_unbox(v___x_1325_);
if (v___x_1326_ == 0)
{
uint8_t v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1327_ = 0;
v___x_1328_ = lean_box(v___x_1327_);
v___x_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
lean_ctor_set(v___x_1329_, 1, v_a_1306_);
return v___x_1329_;
}
else
{
uint8_t v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1330_ = 2;
v___x_1331_ = lean_box(v___x_1330_);
v___x_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
lean_ctor_set(v___x_1332_, 1, v_a_1306_);
return v___x_1332_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___boxed(lean_object* v_inst_1333_, lean_object* v_inst_1334_, lean_object* v_info_1335_, lean_object* v_depTrace_1336_, lean_object* v_depHash_1337_, lean_object* v_oldTrace_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1333_, v_inst_1334_, v_info_1335_, v_depTrace_1336_, v_depHash_1337_, v_oldTrace_1338_, v_a_1339_, v_a_1340_);
lean_dec_ref(v_a_1339_);
lean_dec_ref(v_oldTrace_1338_);
lean_dec_ref(v_depTrace_1336_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27(lean_object* v_00_u03b9_1343_, lean_object* v_inst_1344_, lean_object* v_inst_1345_, lean_object* v_info_1346_, lean_object* v_depTrace_1347_, lean_object* v_depHash_1348_, lean_object* v_oldTrace_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1344_, v_inst_1345_, v_info_1346_, v_depTrace_1347_, v_depHash_1348_, v_oldTrace_1349_, v_a_1354_, v_a_1355_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___boxed(lean_object* v_00_u03b9_1358_, lean_object* v_inst_1359_, lean_object* v_inst_1360_, lean_object* v_info_1361_, lean_object* v_depTrace_1362_, lean_object* v_depHash_1363_, lean_object* v_oldTrace_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27(v_00_u03b9_1358_, v_inst_1359_, v_inst_1360_, v_info_1361_, v_depTrace_1362_, v_depHash_1363_, v_oldTrace_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec_ref(v_oldTrace_1364_);
lean_dec_ref(v_depTrace_1362_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg(lean_object* v_inst_1373_, lean_object* v_inst_1374_, lean_object* v_info_1375_, lean_object* v_depTrace_1376_, lean_object* v_depHash_1377_, lean_object* v_oldTrace_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_){
_start:
{
lean_object* v___x_1382_; lean_object* v_a_1383_; lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1401_; 
v___x_1382_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1373_, v_inst_1374_, v_info_1375_, v_depTrace_1376_, v_depHash_1377_, v_oldTrace_1378_, v_a_1379_, v_a_1380_);
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
v_a_1384_ = lean_ctor_get(v___x_1382_, 1);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1386_ = v___x_1382_;
v_isShared_1387_ = v_isSharedCheck_1401_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_inc(v_a_1383_);
lean_dec(v___x_1382_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1401_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
uint8_t v___x_1388_; uint8_t v___x_1389_; uint8_t v___x_1390_; 
v___x_1388_ = 0;
v___x_1389_ = lean_unbox(v_a_1383_);
lean_dec(v_a_1383_);
v___x_1390_ = l_Lake_instDecidableEqOutputStatus(v___x_1389_, v___x_1388_);
if (v___x_1390_ == 0)
{
uint8_t v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1391_ = 1;
v___x_1392_ = lean_box(v___x_1391_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v___x_1392_);
v___x_1394_ = v___x_1386_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_a_1384_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
else
{
uint8_t v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1396_ = 0;
v___x_1397_ = lean_box(v___x_1396_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v___x_1397_);
v___x_1399_ = v___x_1386_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_a_1384_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg___boxed(lean_object* v_inst_1402_, lean_object* v_inst_1403_, lean_object* v_info_1404_, lean_object* v_depTrace_1405_, lean_object* v_depHash_1406_, lean_object* v_oldTrace_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lake_checkHashUpToDate___redArg(v_inst_1402_, v_inst_1403_, v_info_1404_, v_depTrace_1405_, v_depHash_1406_, v_oldTrace_1407_, v_a_1408_, v_a_1409_);
lean_dec_ref(v_a_1408_);
lean_dec_ref(v_oldTrace_1407_);
lean_dec_ref(v_depTrace_1405_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate(lean_object* v_00_u03b9_1412_, lean_object* v_inst_1413_, lean_object* v_inst_1414_, lean_object* v_info_1415_, lean_object* v_depTrace_1416_, lean_object* v_depHash_1417_, lean_object* v_oldTrace_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v___x_1426_; lean_object* v_a_1427_; lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1445_; 
v___x_1426_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1413_, v_inst_1414_, v_info_1415_, v_depTrace_1416_, v_depHash_1417_, v_oldTrace_1418_, v_a_1423_, v_a_1424_);
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
v_a_1428_ = lean_ctor_get(v___x_1426_, 1);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1430_ = v___x_1426_;
v_isShared_1431_ = v_isSharedCheck_1445_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_inc(v_a_1427_);
lean_dec(v___x_1426_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1445_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
uint8_t v___x_1432_; uint8_t v___x_1433_; uint8_t v___x_1434_; 
v___x_1432_ = 0;
v___x_1433_ = lean_unbox(v_a_1427_);
lean_dec(v_a_1427_);
v___x_1434_ = l_Lake_instDecidableEqOutputStatus(v___x_1433_, v___x_1432_);
if (v___x_1434_ == 0)
{
uint8_t v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1435_ = 1;
v___x_1436_ = lean_box(v___x_1435_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1436_);
v___x_1438_ = v___x_1430_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_a_1428_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
else
{
uint8_t v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1440_ = 0;
v___x_1441_ = lean_box(v___x_1440_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1441_);
v___x_1443_ = v___x_1430_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_a_1428_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___boxed(lean_object* v_00_u03b9_1446_, lean_object* v_inst_1447_, lean_object* v_inst_1448_, lean_object* v_info_1449_, lean_object* v_depTrace_1450_, lean_object* v_depHash_1451_, lean_object* v_oldTrace_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Lake_checkHashUpToDate(v_00_u03b9_1446_, v_inst_1447_, v_inst_1448_, v_info_1449_, v_depTrace_1450_, v_depHash_1451_, v_oldTrace_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_);
lean_dec_ref(v_a_1457_);
lean_dec(v_a_1456_);
lean_dec(v_a_1455_);
lean_dec(v_a_1454_);
lean_dec_ref(v_a_1453_);
lean_dec_ref(v_oldTrace_1452_);
lean_dec_ref(v_depTrace_1450_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(lean_object* v_as_1461_, size_t v_i_1462_, size_t v_stop_1463_, lean_object* v_b_1464_, lean_object* v___y_1465_){
_start:
{
uint8_t v___x_1467_; 
v___x_1467_ = lean_usize_dec_eq(v_i_1462_, v_stop_1463_);
if (v___x_1467_ == 0)
{
lean_object* v_log_1468_; uint8_t v_action_1469_; uint8_t v_wantsRebuild_1470_; lean_object* v_trace_1471_; lean_object* v_buildTime_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1485_; 
v_log_1468_ = lean_ctor_get(v___y_1465_, 0);
v_action_1469_ = lean_ctor_get_uint8(v___y_1465_, sizeof(void*)*3);
v_wantsRebuild_1470_ = lean_ctor_get_uint8(v___y_1465_, sizeof(void*)*3 + 1);
v_trace_1471_ = lean_ctor_get(v___y_1465_, 1);
v_buildTime_1472_ = lean_ctor_get(v___y_1465_, 2);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___y_1465_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1474_ = v___y_1465_;
v_isShared_1475_ = v_isSharedCheck_1485_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_buildTime_1472_);
lean_inc(v_trace_1471_);
lean_inc(v_log_1468_);
lean_dec(v___y_1465_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1485_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; 
v___x_1476_ = lean_array_uget_borrowed(v_as_1461_, v_i_1462_);
v___x_1477_ = lean_box(0);
lean_inc(v___x_1476_);
v___x_1478_ = lean_array_push(v_log_1468_, v___x_1476_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 0, v___x_1478_);
v___x_1480_ = v___x_1474_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_trace_1471_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v_buildTime_1472_);
lean_ctor_set_uint8(v_reuseFailAlloc_1484_, sizeof(void*)*3, v_action_1469_);
lean_ctor_set_uint8(v_reuseFailAlloc_1484_, sizeof(void*)*3 + 1, v_wantsRebuild_1470_);
v___x_1480_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
size_t v___x_1481_; size_t v___x_1482_; 
v___x_1481_ = ((size_t)1ULL);
v___x_1482_ = lean_usize_add(v_i_1462_, v___x_1481_);
v_i_1462_ = v___x_1482_;
v_b_1464_ = v___x_1477_;
v___y_1465_ = v___x_1480_;
goto _start;
}
}
}
else
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1486_, 0, v_b_1464_);
lean_ctor_set(v___x_1486_, 1, v___y_1465_);
return v___x_1486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg___boxed(lean_object* v_as_1487_, lean_object* v_i_1488_, lean_object* v_stop_1489_, lean_object* v_b_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
size_t v_i_boxed_1493_; size_t v_stop_boxed_1494_; lean_object* v_res_1495_; 
v_i_boxed_1493_ = lean_unbox_usize(v_i_1488_);
lean_dec(v_i_1488_);
v_stop_boxed_1494_ = lean_unbox_usize(v_stop_1489_);
lean_dec(v_stop_1489_);
v_res_1495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_as_1487_, v_i_boxed_1493_, v_stop_boxed_1494_, v_b_1490_, v___y_1491_);
lean_dec_ref(v_as_1487_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(lean_object* v_log_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; 
v___x_1504_ = lean_unsigned_to_nat(0u);
v___x_1505_ = lean_array_get_size(v_log_1496_);
v___x_1506_ = lean_box(0);
v___x_1507_ = lean_nat_dec_lt(v___x_1504_, v___x_1505_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; 
v___x_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1506_);
lean_ctor_set(v___x_1508_, 1, v_a_1502_);
return v___x_1508_;
}
else
{
uint8_t v___x_1509_; 
v___x_1509_ = lean_nat_dec_le(v___x_1505_, v___x_1505_);
if (v___x_1509_ == 0)
{
if (v___x_1507_ == 0)
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1506_);
lean_ctor_set(v___x_1510_, 1, v_a_1502_);
return v___x_1510_;
}
else
{
size_t v___x_1511_; size_t v___x_1512_; lean_object* v___x_1513_; 
v___x_1511_ = ((size_t)0ULL);
v___x_1512_ = lean_usize_of_nat(v___x_1505_);
v___x_1513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1496_, v___x_1511_, v___x_1512_, v___x_1506_, v_a_1502_);
return v___x_1513_;
}
}
else
{
size_t v___x_1514_; size_t v___x_1515_; lean_object* v___x_1516_; 
v___x_1514_ = ((size_t)0ULL);
v___x_1515_ = lean_usize_of_nat(v___x_1505_);
v___x_1516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1496_, v___x_1514_, v___x_1515_, v___x_1506_, v_a_1502_);
return v___x_1516_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay___boxed(lean_object* v_log_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
lean_dec_ref(v_a_1522_);
lean_dec(v_a_1521_);
lean_dec(v_a_1520_);
lean_dec(v_a_1519_);
lean_dec_ref(v_a_1518_);
lean_dec_ref(v_log_1517_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(lean_object* v_as_1526_, size_t v_i_1527_, size_t v_stop_1528_, lean_object* v_b_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_as_1526_, v_i_1527_, v_stop_1528_, v_b_1529_, v___y_1535_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___boxed(lean_object* v_as_1538_, lean_object* v_i_1539_, lean_object* v_stop_1540_, lean_object* v_b_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
size_t v_i_boxed_1549_; size_t v_stop_boxed_1550_; lean_object* v_res_1551_; 
v_i_boxed_1549_ = lean_unbox_usize(v_i_1539_);
lean_dec(v_i_1539_);
v_stop_boxed_1550_ = lean_unbox_usize(v_stop_1540_);
lean_dec(v_stop_1540_);
v_res_1551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(v_as_1538_, v_i_boxed_1549_, v_stop_boxed_1550_, v_b_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec_ref(v_as_1538_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(lean_object* v_inst_1552_, lean_object* v_inst_1553_, lean_object* v_info_1554_, lean_object* v_depTrace_1555_, lean_object* v_savedTrace_1556_, lean_object* v_oldTrace_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_){
_start:
{
if (lean_obj_tag(v_savedTrace_1556_) == 2)
{
lean_object* v_data_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1615_; 
v_data_1565_ = lean_ctor_get(v_savedTrace_1556_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v_savedTrace_1556_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1567_ = v_savedTrace_1556_;
v_isShared_1568_ = v_isSharedCheck_1615_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_data_1565_);
lean_dec(v_savedTrace_1556_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1615_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
uint64_t v_depHash_1569_; lean_object* v_log_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v_depHash_1569_ = lean_ctor_get_uint64(v_data_1565_, sizeof(void*)*3);
v_log_1570_ = lean_ctor_get(v_data_1565_, 2);
lean_inc_ref(v_log_1570_);
lean_dec_ref(v_data_1565_);
v___x_1571_ = lean_box_uint64(v_depHash_1569_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set_tag(v___x_1567_, 1);
lean_ctor_set(v___x_1567_, 0, v___x_1571_);
v___x_1573_ = v___x_1567_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; lean_object* v_a_1575_; lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1613_; 
v___x_1574_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1552_, v_inst_1553_, v_info_1554_, v_depTrace_1555_, v___x_1573_, v_oldTrace_1557_, v_a_1562_, v_a_1563_);
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
v_a_1576_ = lean_ctor_get(v___x_1574_, 1);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1578_ = v___x_1574_;
v_isShared_1579_ = v_isSharedCheck_1613_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_inc(v_a_1575_);
lean_dec(v___x_1574_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1613_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___y_1581_; uint8_t v___x_1585_; uint8_t v___x_1586_; uint8_t v___x_1587_; 
v___x_1585_ = 0;
v___x_1586_ = lean_unbox(v_a_1575_);
v___x_1587_ = l_Lake_instDecidableEqOutputStatus(v___x_1586_, v___x_1585_);
if (v___x_1587_ == 0)
{
lean_object* v_log_1588_; uint8_t v_action_1589_; uint8_t v_wantsRebuild_1590_; lean_object* v_trace_1591_; lean_object* v_buildTime_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1612_; 
v_log_1588_ = lean_ctor_get(v_a_1576_, 0);
v_action_1589_ = lean_ctor_get_uint8(v_a_1576_, sizeof(void*)*3);
v_wantsRebuild_1590_ = lean_ctor_get_uint8(v_a_1576_, sizeof(void*)*3 + 1);
v_trace_1591_ = lean_ctor_get(v_a_1576_, 1);
v_buildTime_1592_ = lean_ctor_get(v_a_1576_, 2);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_a_1576_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1594_ = v_a_1576_;
v_isShared_1595_ = v_isSharedCheck_1612_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_buildTime_1592_);
lean_inc(v_trace_1591_);
lean_inc(v_log_1588_);
lean_dec(v_a_1576_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1612_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
uint8_t v___x_1596_; uint8_t v___x_1597_; lean_object* v___x_1599_; 
v___x_1596_ = 1;
v___x_1597_ = l_Lake_JobAction_merge(v_action_1589_, v___x_1596_);
if (v_isShared_1595_ == 0)
{
v___x_1599_ = v___x_1594_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_log_1588_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_trace_1591_);
lean_ctor_set(v_reuseFailAlloc_1611_, 2, v_buildTime_1592_);
lean_ctor_set_uint8(v_reuseFailAlloc_1611_, sizeof(void*)*3 + 1, v_wantsRebuild_1590_);
v___x_1599_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1600_; 
lean_ctor_set_uint8(v___x_1599_, sizeof(void*)*3, v___x_1597_);
v___x_1600_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_1570_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v___x_1599_);
lean_dec_ref(v_log_1570_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 1);
lean_inc(v_a_1601_);
lean_dec_ref(v___x_1600_);
v___y_1581_ = v_a_1601_;
goto v___jp_1580_;
}
else
{
lean_object* v_a_1602_; lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_del_object(v___x_1578_);
lean_dec(v_a_1575_);
v_a_1602_ = lean_ctor_get(v___x_1600_, 0);
v_a_1603_ = lean_ctor_get(v___x_1600_, 1);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1600_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_inc(v_a_1602_);
lean_dec(v___x_1600_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1602_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_log_1570_);
v___y_1581_ = v_a_1576_;
goto v___jp_1580_;
}
v___jp_1580_:
{
lean_object* v___x_1583_; 
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 1, v___y_1581_);
v___x_1583_ = v___x_1578_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1575_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v___y_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
}
}
else
{
lean_object* v_toBuildConfig_1616_; uint8_t v_oldMode_1617_; 
lean_dec(v_savedTrace_1556_);
lean_dec_ref(v_inst_1552_);
v_toBuildConfig_1616_ = lean_ctor_get(v_a_1562_, 0);
v_oldMode_1617_ = lean_ctor_get_uint8(v_toBuildConfig_1616_, sizeof(void*)*2);
if (v_oldMode_1617_ == 0)
{
uint8_t v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
lean_dec(v_info_1554_);
lean_dec_ref(v_inst_1553_);
v___x_1618_ = 0;
v___x_1619_ = lean_box(v___x_1618_);
v___x_1620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
lean_ctor_set(v___x_1620_, 1, v_a_1563_);
return v___x_1620_;
}
else
{
uint8_t v___x_1621_; 
v___x_1621_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1553_, v_info_1554_, v_oldTrace_1557_);
if (v___x_1621_ == 0)
{
uint8_t v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1622_ = 0;
v___x_1623_ = lean_box(v___x_1622_);
v___x_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
lean_ctor_set(v___x_1624_, 1, v_a_1563_);
return v___x_1624_;
}
else
{
uint8_t v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1625_ = 1;
v___x_1626_ = lean_box(v___x_1625_);
v___x_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
lean_ctor_set(v___x_1627_, 1, v_a_1563_);
return v___x_1627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg___boxed(lean_object* v_inst_1628_, lean_object* v_inst_1629_, lean_object* v_info_1630_, lean_object* v_depTrace_1631_, lean_object* v_savedTrace_1632_, lean_object* v_oldTrace_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1628_, v_inst_1629_, v_info_1630_, v_depTrace_1631_, v_savedTrace_1632_, v_oldTrace_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_);
lean_dec_ref(v_a_1638_);
lean_dec(v_a_1637_);
lean_dec(v_a_1636_);
lean_dec(v_a_1635_);
lean_dec_ref(v_a_1634_);
lean_dec_ref(v_oldTrace_1633_);
lean_dec_ref(v_depTrace_1631_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27(lean_object* v_00_u03b9_1642_, lean_object* v_inst_1643_, lean_object* v_inst_1644_, lean_object* v_info_1645_, lean_object* v_depTrace_1646_, lean_object* v_savedTrace_1647_, lean_object* v_oldTrace_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1643_, v_inst_1644_, v_info_1645_, v_depTrace_1646_, v_savedTrace_1647_, v_oldTrace_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___boxed(lean_object* v_00_u03b9_1657_, lean_object* v_inst_1658_, lean_object* v_inst_1659_, lean_object* v_info_1660_, lean_object* v_depTrace_1661_, lean_object* v_savedTrace_1662_, lean_object* v_oldTrace_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lake_SavedTrace_replayIfUpToDate_x27(v_00_u03b9_1657_, v_inst_1658_, v_inst_1659_, v_info_1660_, v_depTrace_1661_, v_savedTrace_1662_, v_oldTrace_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
lean_dec_ref(v_a_1668_);
lean_dec(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec(v_a_1665_);
lean_dec_ref(v_a_1664_);
lean_dec_ref(v_oldTrace_1663_);
lean_dec_ref(v_depTrace_1661_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg(lean_object* v_inst_1672_, lean_object* v_inst_1673_, lean_object* v_info_1674_, lean_object* v_depTrace_1675_, lean_object* v_savedTrace_1676_, lean_object* v_oldTrace_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1672_, v_inst_1673_, v_info_1674_, v_depTrace_1675_, v_savedTrace_1676_, v_oldTrace_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1704_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
v_a_1687_ = lean_ctor_get(v___x_1685_, 1);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1689_ = v___x_1685_;
v_isShared_1690_ = v_isSharedCheck_1704_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_inc(v_a_1686_);
lean_dec(v___x_1685_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1704_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
uint8_t v___x_1691_; uint8_t v___x_1692_; uint8_t v___x_1693_; 
v___x_1691_ = 0;
v___x_1692_ = lean_unbox(v_a_1686_);
lean_dec(v_a_1686_);
v___x_1693_ = l_Lake_instDecidableEqOutputStatus(v___x_1692_, v___x_1691_);
if (v___x_1693_ == 0)
{
uint8_t v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1697_; 
v___x_1694_ = 1;
v___x_1695_ = lean_box(v___x_1694_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 0, v___x_1695_);
v___x_1697_ = v___x_1689_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1695_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_a_1687_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
else
{
uint8_t v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1702_; 
v___x_1699_ = 0;
v___x_1700_ = lean_box(v___x_1699_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 0, v___x_1700_);
v___x_1702_ = v___x_1689_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1700_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_a_1687_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
else
{
lean_object* v_a_1705_; lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
v_a_1705_ = lean_ctor_get(v___x_1685_, 0);
v_a_1706_ = lean_ctor_get(v___x_1685_, 1);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1685_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_inc(v_a_1705_);
lean_dec(v___x_1685_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1705_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg___boxed(lean_object* v_inst_1714_, lean_object* v_inst_1715_, lean_object* v_info_1716_, lean_object* v_depTrace_1717_, lean_object* v_savedTrace_1718_, lean_object* v_oldTrace_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lake_SavedTrace_replayIfUpToDate___redArg(v_inst_1714_, v_inst_1715_, v_info_1716_, v_depTrace_1717_, v_savedTrace_1718_, v_oldTrace_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
lean_dec_ref(v_a_1724_);
lean_dec(v_a_1723_);
lean_dec(v_a_1722_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
lean_dec_ref(v_oldTrace_1719_);
lean_dec_ref(v_depTrace_1717_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate(lean_object* v_00_u03b9_1728_, lean_object* v_inst_1729_, lean_object* v_inst_1730_, lean_object* v_info_1731_, lean_object* v_depTrace_1732_, lean_object* v_savedTrace_1733_, lean_object* v_oldTrace_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1729_, v_inst_1730_, v_info_1731_, v_depTrace_1732_, v_savedTrace_1733_, v_oldTrace_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1761_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
v_a_1744_ = lean_ctor_get(v___x_1742_, 1);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1746_ = v___x_1742_;
v_isShared_1747_ = v_isSharedCheck_1761_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_inc(v_a_1743_);
lean_dec(v___x_1742_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1761_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
uint8_t v___x_1748_; uint8_t v___x_1749_; uint8_t v___x_1750_; 
v___x_1748_ = 0;
v___x_1749_ = lean_unbox(v_a_1743_);
lean_dec(v_a_1743_);
v___x_1750_ = l_Lake_instDecidableEqOutputStatus(v___x_1749_, v___x_1748_);
if (v___x_1750_ == 0)
{
uint8_t v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1754_; 
v___x_1751_ = 1;
v___x_1752_ = lean_box(v___x_1751_);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 0, v___x_1752_);
v___x_1754_ = v___x_1746_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1752_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v_a_1744_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
else
{
uint8_t v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1759_; 
v___x_1756_ = 0;
v___x_1757_ = lean_box(v___x_1756_);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 0, v___x_1757_);
v___x_1759_ = v___x_1746_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_a_1744_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
v_a_1762_ = lean_ctor_get(v___x_1742_, 0);
v_a_1763_ = lean_ctor_get(v___x_1742_, 1);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1742_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_inc(v_a_1762_);
lean_dec(v___x_1742_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1762_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___boxed(lean_object* v_00_u03b9_1771_, lean_object* v_inst_1772_, lean_object* v_inst_1773_, lean_object* v_info_1774_, lean_object* v_depTrace_1775_, lean_object* v_savedTrace_1776_, lean_object* v_oldTrace_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Lake_SavedTrace_replayIfUpToDate(v_00_u03b9_1771_, v_inst_1772_, v_inst_1773_, v_info_1774_, v_depTrace_1775_, v_savedTrace_1776_, v_oldTrace_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
lean_dec_ref(v_a_1782_);
lean_dec(v_a_1781_);
lean_dec(v_a_1780_);
lean_dec(v_a_1779_);
lean_dec_ref(v_a_1778_);
lean_dec_ref(v_oldTrace_1777_);
lean_dec_ref(v_depTrace_1775_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(uint64_t v_inputHash_1786_, lean_object* v_self_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v___y_1791_; 
if (lean_obj_tag(v_self_1787_) == 2)
{
lean_object* v_data_1809_; uint64_t v_depHash_1810_; lean_object* v_log_1811_; uint8_t v_synthetic_1812_; uint8_t v___x_1813_; lean_object* v___y_1815_; lean_object* v___y_1819_; 
v_data_1809_ = lean_ctor_get(v_self_1787_, 0);
v_depHash_1810_ = lean_ctor_get_uint64(v_data_1809_, sizeof(void*)*3);
v_log_1811_ = lean_ctor_get(v_data_1809_, 2);
v_synthetic_1812_ = lean_ctor_get_uint8(v_data_1809_, sizeof(void*)*3 + 8);
v___x_1813_ = lean_uint64_dec_eq(v_depHash_1810_, v_inputHash_1786_);
if (v___x_1813_ == 0)
{
v___y_1791_ = v_a_1788_;
goto v___jp_1790_;
}
else
{
if (v_synthetic_1812_ == 0)
{
goto v___jp_1830_;
}
else
{
lean_object* v___x_1856_; lean_object* v___x_1857_; uint8_t v___x_1858_; 
v___x_1856_ = lean_array_get_size(v_log_1811_);
v___x_1857_ = lean_unsigned_to_nat(0u);
v___x_1858_ = lean_nat_dec_eq(v___x_1856_, v___x_1857_);
if (v___x_1858_ == 0)
{
goto v___jp_1830_;
}
else
{
lean_object* v_log_1859_; uint8_t v_action_1860_; uint8_t v_wantsRebuild_1861_; lean_object* v_trace_1862_; lean_object* v_buildTime_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1872_; 
v_log_1859_ = lean_ctor_get(v_a_1788_, 0);
v_action_1860_ = lean_ctor_get_uint8(v_a_1788_, sizeof(void*)*3);
v_wantsRebuild_1861_ = lean_ctor_get_uint8(v_a_1788_, sizeof(void*)*3 + 1);
v_trace_1862_ = lean_ctor_get(v_a_1788_, 1);
v_buildTime_1863_ = lean_ctor_get(v_a_1788_, 2);
v_isSharedCheck_1872_ = !lean_is_exclusive(v_a_1788_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1865_ = v_a_1788_;
v_isShared_1866_ = v_isSharedCheck_1872_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_buildTime_1863_);
lean_inc(v_trace_1862_);
lean_inc(v_log_1859_);
lean_dec(v_a_1788_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1872_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
uint8_t v___x_1867_; uint8_t v___x_1868_; lean_object* v___x_1870_; 
v___x_1867_ = 2;
v___x_1868_ = l_Lake_JobAction_merge(v_action_1860_, v___x_1867_);
if (v_isShared_1866_ == 0)
{
v___x_1870_ = v___x_1865_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_log_1859_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v_trace_1862_);
lean_ctor_set(v_reuseFailAlloc_1871_, 2, v_buildTime_1863_);
lean_ctor_set_uint8(v_reuseFailAlloc_1871_, sizeof(void*)*3 + 1, v_wantsRebuild_1861_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_ctor_set_uint8(v___x_1870_, sizeof(void*)*3, v___x_1868_);
v___y_1815_ = v___x_1870_;
goto v___jp_1814_;
}
}
}
}
}
v___jp_1814_:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1816_ = lean_box(v___x_1813_);
v___x_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
lean_ctor_set(v___x_1817_, 1, v___y_1815_);
return v___x_1817_;
}
v___jp_1818_:
{
if (lean_obj_tag(v___y_1819_) == 0)
{
lean_object* v_a_1820_; 
v_a_1820_ = lean_ctor_get(v___y_1819_, 1);
lean_inc(v_a_1820_);
lean_dec_ref(v___y_1819_);
v___y_1815_ = v_a_1820_;
goto v___jp_1814_;
}
else
{
lean_object* v_a_1821_; lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
v_a_1821_ = lean_ctor_get(v___y_1819_, 0);
v_a_1822_ = lean_ctor_get(v___y_1819_, 1);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___y_1819_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___y_1819_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_inc(v_a_1821_);
lean_dec(v___y_1819_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1821_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
v___jp_1830_:
{
lean_object* v_log_1831_; uint8_t v_action_1832_; uint8_t v_wantsRebuild_1833_; lean_object* v_trace_1834_; lean_object* v_buildTime_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1855_; 
v_log_1831_ = lean_ctor_get(v_a_1788_, 0);
v_action_1832_ = lean_ctor_get_uint8(v_a_1788_, sizeof(void*)*3);
v_wantsRebuild_1833_ = lean_ctor_get_uint8(v_a_1788_, sizeof(void*)*3 + 1);
v_trace_1834_ = lean_ctor_get(v_a_1788_, 1);
v_buildTime_1835_ = lean_ctor_get(v_a_1788_, 2);
v_isSharedCheck_1855_ = !lean_is_exclusive(v_a_1788_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1837_ = v_a_1788_;
v_isShared_1838_ = v_isSharedCheck_1855_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_buildTime_1835_);
lean_inc(v_trace_1834_);
lean_inc(v_log_1831_);
lean_dec(v_a_1788_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1855_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
uint8_t v___x_1839_; uint8_t v___x_1840_; lean_object* v___x_1842_; 
v___x_1839_ = 1;
v___x_1840_ = l_Lake_JobAction_merge(v_action_1832_, v___x_1839_);
if (v_isShared_1838_ == 0)
{
v___x_1842_ = v___x_1837_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_log_1831_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_trace_1834_);
lean_ctor_set(v_reuseFailAlloc_1854_, 2, v_buildTime_1835_);
lean_ctor_set_uint8(v_reuseFailAlloc_1854_, sizeof(void*)*3 + 1, v_wantsRebuild_1833_);
v___x_1842_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; uint8_t v___x_1845_; 
lean_ctor_set_uint8(v___x_1842_, sizeof(void*)*3, v___x_1840_);
v___x_1843_ = lean_unsigned_to_nat(0u);
v___x_1844_ = lean_array_get_size(v_log_1811_);
v___x_1845_ = lean_nat_dec_lt(v___x_1843_, v___x_1844_);
if (v___x_1845_ == 0)
{
v___y_1815_ = v___x_1842_;
goto v___jp_1814_;
}
else
{
lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1846_ = lean_box(0);
v___x_1847_ = lean_nat_dec_le(v___x_1844_, v___x_1844_);
if (v___x_1847_ == 0)
{
if (v___x_1845_ == 0)
{
v___y_1815_ = v___x_1842_;
goto v___jp_1814_;
}
else
{
size_t v___x_1848_; size_t v___x_1849_; lean_object* v___x_1850_; 
v___x_1848_ = ((size_t)0ULL);
v___x_1849_ = lean_usize_of_nat(v___x_1844_);
v___x_1850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1811_, v___x_1848_, v___x_1849_, v___x_1846_, v___x_1842_);
v___y_1819_ = v___x_1850_;
goto v___jp_1818_;
}
}
else
{
size_t v___x_1851_; size_t v___x_1852_; lean_object* v___x_1853_; 
v___x_1851_ = ((size_t)0ULL);
v___x_1852_ = lean_usize_of_nat(v___x_1844_);
v___x_1853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1811_, v___x_1851_, v___x_1852_, v___x_1846_, v___x_1842_);
v___y_1819_ = v___x_1853_;
goto v___jp_1818_;
}
}
}
}
}
}
else
{
v___y_1791_ = v_a_1788_;
goto v___jp_1790_;
}
v___jp_1790_:
{
lean_object* v_log_1792_; uint8_t v_action_1793_; uint8_t v_wantsRebuild_1794_; lean_object* v_trace_1795_; lean_object* v_buildTime_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1808_; 
v_log_1792_ = lean_ctor_get(v___y_1791_, 0);
v_action_1793_ = lean_ctor_get_uint8(v___y_1791_, sizeof(void*)*3);
v_wantsRebuild_1794_ = lean_ctor_get_uint8(v___y_1791_, sizeof(void*)*3 + 1);
v_trace_1795_ = lean_ctor_get(v___y_1791_, 1);
v_buildTime_1796_ = lean_ctor_get(v___y_1791_, 2);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___y_1791_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1798_ = v___y_1791_;
v_isShared_1799_ = v_isSharedCheck_1808_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_buildTime_1796_);
lean_inc(v_trace_1795_);
lean_inc(v_log_1792_);
lean_dec(v___y_1791_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1808_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
uint8_t v___x_1800_; uint8_t v___x_1801_; lean_object* v___x_1803_; 
v___x_1800_ = 2;
v___x_1801_ = l_Lake_JobAction_merge(v_action_1793_, v___x_1800_);
if (v_isShared_1799_ == 0)
{
v___x_1803_ = v___x_1798_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_log_1792_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_trace_1795_);
lean_ctor_set(v_reuseFailAlloc_1807_, 2, v_buildTime_1796_);
lean_ctor_set_uint8(v_reuseFailAlloc_1807_, sizeof(void*)*3 + 1, v_wantsRebuild_1794_);
v___x_1803_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
uint8_t v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
lean_ctor_set_uint8(v___x_1803_, sizeof(void*)*3, v___x_1801_);
v___x_1804_ = 0;
v___x_1805_ = lean_box(v___x_1804_);
v___x_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
lean_ctor_set(v___x_1806_, 1, v___x_1803_);
return v___x_1806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg___boxed(lean_object* v_inputHash_1873_, lean_object* v_self_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
uint64_t v_inputHash_boxed_1877_; lean_object* v_res_1878_; 
v_inputHash_boxed_1877_ = lean_unbox_uint64(v_inputHash_1873_);
lean_dec_ref(v_inputHash_1873_);
v_res_1878_ = l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(v_inputHash_boxed_1877_, v_self_1874_, v_a_1875_);
lean_dec(v_self_1874_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate(uint64_t v_inputHash_1879_, lean_object* v_self_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(v_inputHash_1879_, v_self_1880_, v_a_1886_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___boxed(lean_object* v_inputHash_1889_, lean_object* v_self_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
uint64_t v_inputHash_boxed_1898_; lean_object* v_res_1899_; 
v_inputHash_boxed_1898_ = lean_unbox_uint64(v_inputHash_1889_);
lean_dec_ref(v_inputHash_1889_);
v_res_1899_ = l_Lake_SavedTrace_replayOrFetchIfUpToDate(v_inputHash_boxed_1898_, v_self_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
lean_dec_ref(v_a_1895_);
lean_dec(v_a_1894_);
lean_dec(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_self_1890_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonPUnit___lam__0(lean_object* v_x_1900_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = lean_box(0);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0(lean_object* v_x_1905_){
_start:
{
lean_object* v_descr_1906_; uint64_t v_hash_1907_; lean_object* v_ext_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; 
v_descr_1906_ = lean_ctor_get(v_x_1905_, 0);
v_hash_1907_ = lean_ctor_get_uint64(v_descr_1906_, sizeof(void*)*1);
v_ext_1908_ = lean_ctor_get(v_descr_1906_, 0);
v___x_1909_ = lean_string_utf8_byte_size(v_ext_1908_);
v___x_1910_ = lean_unsigned_to_nat(0u);
v___x_1911_ = lean_nat_dec_eq(v___x_1909_, v___x_1910_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1912_ = l_Lake_Hash_hex(v_hash_1907_);
v___x_1913_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_1914_ = lean_string_append(v___x_1912_, v___x_1913_);
v___x_1915_ = lean_string_append(v___x_1914_, v_ext_1908_);
v___x_1916_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
return v___x_1916_;
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = l_Lake_Hash_hex(v_hash_1907_);
v___x_1918_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1917_);
return v___x_1918_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0___boxed(lean_object* v_x_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Lake_instToOutputJsonArtifact___lam__0(v_x_1919_);
lean_dec_ref(v_x_1919_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0(lean_object* v_val_1923_, lean_object* v_a_x3f_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v___x_1927_; lean_object* v_log_1928_; uint8_t v_action_1929_; uint8_t v_wantsRebuild_1930_; lean_object* v_trace_1931_; lean_object* v_buildTime_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1943_; 
v___x_1927_ = lean_io_mono_ms_now();
v_log_1928_ = lean_ctor_get(v___y_1925_, 0);
v_action_1929_ = lean_ctor_get_uint8(v___y_1925_, sizeof(void*)*3);
v_wantsRebuild_1930_ = lean_ctor_get_uint8(v___y_1925_, sizeof(void*)*3 + 1);
v_trace_1931_ = lean_ctor_get(v___y_1925_, 1);
v_buildTime_1932_ = lean_ctor_get(v___y_1925_, 2);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___y_1925_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1934_ = v___y_1925_;
v_isShared_1935_ = v_isSharedCheck_1943_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_buildTime_1932_);
lean_inc(v_trace_1931_);
lean_inc(v_log_1928_);
lean_dec(v___y_1925_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1943_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1940_; 
v___x_1936_ = lean_nat_sub(v___x_1927_, v_val_1923_);
lean_dec(v___x_1927_);
v___x_1937_ = lean_box(0);
v___x_1938_ = lean_nat_add(v_buildTime_1932_, v___x_1936_);
lean_dec(v___x_1936_);
lean_dec(v_buildTime_1932_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 2, v___x_1938_);
v___x_1940_ = v___x_1934_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_log_1928_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v_trace_1931_);
lean_ctor_set(v_reuseFailAlloc_1942_, 2, v___x_1938_);
lean_ctor_set_uint8(v_reuseFailAlloc_1942_, sizeof(void*)*3, v_action_1929_);
lean_ctor_set_uint8(v_reuseFailAlloc_1942_, sizeof(void*)*3 + 1, v_wantsRebuild_1930_);
v___x_1940_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
lean_object* v___x_1941_; 
v___x_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1937_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
return v___x_1941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0___boxed(lean_object* v_val_1944_, lean_object* v_a_x3f_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lake_buildAction___redArg___lam__0(v_val_1944_, v_a_x3f_1945_, v___y_1946_);
lean_dec(v_a_x3f_1945_);
lean_dec(v_val_1944_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg(lean_object* v_inst_1954_, lean_object* v_depTrace_1955_, lean_object* v_traceFile_1956_, lean_object* v_build_1957_, uint8_t v_action_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_){
_start:
{
lean_object* v_a_1967_; lean_object* v_a_1968_; lean_object* v_log_1971_; uint8_t v_action_1972_; uint8_t v_wantsRebuild_1973_; lean_object* v_trace_1974_; lean_object* v_buildTime_1975_; lean_object* v_toBuildConfig_1981_; lean_object* v_log_1982_; uint8_t v_action_1983_; uint8_t v_wantsRebuild_1984_; lean_object* v_trace_1985_; lean_object* v_buildTime_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2092_; 
v_toBuildConfig_1981_ = lean_ctor_get(v_a_1963_, 0);
v_log_1982_ = lean_ctor_get(v_a_1964_, 0);
v_action_1983_ = lean_ctor_get_uint8(v_a_1964_, sizeof(void*)*3);
v_wantsRebuild_1984_ = lean_ctor_get_uint8(v_a_1964_, sizeof(void*)*3 + 1);
v_trace_1985_ = lean_ctor_get(v_a_1964_, 1);
v_buildTime_1986_ = lean_ctor_get(v_a_1964_, 2);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_a_1964_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_1988_ = v_a_1964_;
v_isShared_1989_ = v_isSharedCheck_2092_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_buildTime_1986_);
lean_inc(v_trace_1985_);
lean_inc(v_log_1982_);
lean_dec(v_a_1964_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2092_;
goto v_resetjp_1987_;
}
v___jp_1966_:
{
lean_object* v___x_1969_; 
v___x_1969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1969_, 0, v_a_1967_);
lean_ctor_set(v___x_1969_, 1, v_a_1968_);
return v___x_1969_;
}
v___jp_1970_:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1976_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_1977_ = lean_array_get_size(v_log_1971_);
v___x_1978_ = lean_array_push(v_log_1971_, v___x_1976_);
v___x_1979_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
lean_ctor_set(v___x_1979_, 1, v_trace_1974_);
lean_ctor_set(v___x_1979_, 2, v_buildTime_1975_);
lean_ctor_set_uint8(v___x_1979_, sizeof(void*)*3, v_action_1972_);
lean_ctor_set_uint8(v___x_1979_, sizeof(void*)*3 + 1, v_wantsRebuild_1973_);
v___x_1980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1977_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
return v___x_1980_;
}
v_resetjp_1987_:
{
uint8_t v_noBuild_1990_; uint8_t v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v_noBuild_1990_ = lean_ctor_get_uint8(v_toBuildConfig_1981_, sizeof(void*)*2 + 2);
v___x_1991_ = l_Lake_JobAction_merge(v_action_1983_, v_action_1958_);
v___x_1992_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_1956_);
v___x_1993_ = l_System_FilePath_addExtension(v_traceFile_1956_, v___x_1992_);
if (v_noBuild_1990_ == 0)
{
lean_object* v___x_1994_; lean_object* v___x_1996_; 
v___x_1994_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_1982_);
if (v_isShared_1989_ == 0)
{
v___x_1996_ = v___x_1988_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_log_1982_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_trace_1985_);
lean_ctor_set(v_reuseFailAlloc_2076_, 2, v_buildTime_1986_);
lean_ctor_set_uint8(v_reuseFailAlloc_2076_, sizeof(void*)*3 + 1, v_wantsRebuild_1984_);
v___x_1996_ = v_reuseFailAlloc_2076_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
lean_object* v___x_1997_; lean_object* v_a_1999_; lean_object* v_a_2000_; 
lean_ctor_set_uint8(v___x_1996_, sizeof(void*)*3, v___x_1991_);
v___x_1997_ = lean_apply_7(v_build_1957_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v___x_1996_, lean_box(0));
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_2004_; lean_object* v_a_2005_; lean_object* v_log_2006_; uint8_t v_action_2007_; uint8_t v_wantsRebuild_2008_; lean_object* v_trace_2009_; lean_object* v_buildTime_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v_a_2004_ = lean_ctor_get(v___x_1997_, 1);
lean_inc(v_a_2004_);
v_a_2005_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_2005_);
lean_dec_ref(v___x_1997_);
v_log_2006_ = lean_ctor_get(v_a_2004_, 0);
v_action_2007_ = lean_ctor_get_uint8(v_a_2004_, sizeof(void*)*3);
v_wantsRebuild_2008_ = lean_ctor_get_uint8(v_a_2004_, sizeof(void*)*3 + 1);
v_trace_2009_ = lean_ctor_get(v_a_2004_, 1);
v_buildTime_2010_ = lean_ctor_get(v_a_2004_, 2);
v___x_2011_ = lean_array_get_size(v_log_1982_);
lean_dec_ref(v_log_1982_);
v___x_2012_ = lean_array_get_size(v_log_2006_);
v___x_2013_ = l_Array_extract___redArg(v_log_2006_, v___x_2011_, v___x_2012_);
lean_inc(v_a_2005_);
v___x_2014_ = lean_apply_1(v_inst_1954_, v_a_2005_);
v___x_2015_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1955_, v___x_2014_, v___x_2013_);
v___x_2016_ = l_Lake_BuildMetadata_writeFile(v_traceFile_1956_, v___x_2015_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2057_; 
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; 
v_unused_2058_ = lean_ctor_get(v___x_2016_, 0);
lean_dec(v_unused_2058_);
v___x_2018_ = v___x_2016_;
v_isShared_2019_ = v_isSharedCheck_2057_;
goto v_resetjp_2017_;
}
else
{
lean_dec(v___x_2016_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2057_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2020_; 
v___x_2020_ = l_Lake_removeFileIfExists(v___x_1993_);
lean_dec_ref(v___x_1993_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2040_; 
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2040_ == 0)
{
lean_object* v_unused_2041_; 
v_unused_2041_ = lean_ctor_get(v___x_2020_, 0);
lean_dec(v_unused_2041_);
v___x_2022_ = v___x_2020_;
v_isShared_2023_ = v_isSharedCheck_2040_;
goto v_resetjp_2021_;
}
else
{
lean_dec(v___x_2020_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2040_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
lean_inc(v_a_2005_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v_a_2005_);
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2005_);
v___x_2025_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
lean_object* v___x_2027_; 
if (v_isShared_2019_ == 0)
{
lean_ctor_set_tag(v___x_2018_, 1);
lean_ctor_set(v___x_2018_, 0, v___x_2025_);
v___x_2027_ = v___x_2018_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2028_; lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
v___x_2028_ = l_Lake_buildAction___redArg___lam__0(v___x_1994_, v___x_2027_, v_a_2004_);
lean_dec_ref(v___x_2027_);
lean_dec(v___x_1994_);
v_a_2029_ = lean_ctor_get(v___x_2028_, 1);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2036_ == 0)
{
lean_object* v_unused_2037_; 
v_unused_2037_ = lean_ctor_get(v___x_2028_, 0);
lean_dec(v_unused_2037_);
v___x_2031_ = v___x_2028_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2028_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 0, v_a_2005_);
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2005_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
}
else
{
lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2053_; 
lean_inc(v_buildTime_2010_);
lean_inc_ref(v_trace_2009_);
lean_inc_ref(v_log_2006_);
lean_del_object(v___x_2018_);
lean_dec(v_a_2005_);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_a_2004_);
if (v_isSharedCheck_2053_ == 0)
{
lean_object* v_unused_2054_; lean_object* v_unused_2055_; lean_object* v_unused_2056_; 
v_unused_2054_ = lean_ctor_get(v_a_2004_, 2);
lean_dec(v_unused_2054_);
v_unused_2055_ = lean_ctor_get(v_a_2004_, 1);
lean_dec(v_unused_2055_);
v_unused_2056_ = lean_ctor_get(v_a_2004_, 0);
lean_dec(v_unused_2056_);
v___x_2043_ = v_a_2004_;
v_isShared_2044_ = v_isSharedCheck_2053_;
goto v_resetjp_2042_;
}
else
{
lean_dec(v_a_2004_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2053_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v_a_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2051_; 
v_a_2045_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2045_);
lean_dec_ref(v___x_2020_);
v___x_2046_ = lean_io_error_to_string(v_a_2045_);
v___x_2047_ = 3;
v___x_2048_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2048_, 0, v___x_2046_);
lean_ctor_set_uint8(v___x_2048_, sizeof(void*)*1, v___x_2047_);
v___x_2049_ = lean_array_push(v_log_2006_, v___x_2048_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v___x_2049_);
v___x_2051_ = v___x_2043_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2049_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_trace_2009_);
lean_ctor_set(v_reuseFailAlloc_2052_, 2, v_buildTime_2010_);
lean_ctor_set_uint8(v_reuseFailAlloc_2052_, sizeof(void*)*3, v_action_2007_);
lean_ctor_set_uint8(v_reuseFailAlloc_2052_, sizeof(void*)*3 + 1, v_wantsRebuild_2008_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
v_a_1999_ = v___x_2012_;
v_a_2000_ = v___x_2051_;
goto v___jp_1998_;
}
}
}
}
}
else
{
lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2070_; 
lean_inc(v_buildTime_2010_);
lean_inc_ref(v_trace_2009_);
lean_inc_ref(v_log_2006_);
lean_dec(v_a_2005_);
lean_dec_ref(v___x_1993_);
v_isSharedCheck_2070_ = !lean_is_exclusive(v_a_2004_);
if (v_isSharedCheck_2070_ == 0)
{
lean_object* v_unused_2071_; lean_object* v_unused_2072_; lean_object* v_unused_2073_; 
v_unused_2071_ = lean_ctor_get(v_a_2004_, 2);
lean_dec(v_unused_2071_);
v_unused_2072_ = lean_ctor_get(v_a_2004_, 1);
lean_dec(v_unused_2072_);
v_unused_2073_ = lean_ctor_get(v_a_2004_, 0);
lean_dec(v_unused_2073_);
v___x_2060_ = v_a_2004_;
v_isShared_2061_ = v_isSharedCheck_2070_;
goto v_resetjp_2059_;
}
else
{
lean_dec(v_a_2004_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2070_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v_a_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2068_; 
v_a_2062_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2062_);
lean_dec_ref(v___x_2016_);
v___x_2063_ = lean_io_error_to_string(v_a_2062_);
v___x_2064_ = 3;
v___x_2065_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2065_, 0, v___x_2063_);
lean_ctor_set_uint8(v___x_2065_, sizeof(void*)*1, v___x_2064_);
v___x_2066_ = lean_array_push(v_log_2006_, v___x_2065_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 0, v___x_2066_);
v___x_2068_ = v___x_2060_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2066_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v_trace_2009_);
lean_ctor_set(v_reuseFailAlloc_2069_, 2, v_buildTime_2010_);
lean_ctor_set_uint8(v_reuseFailAlloc_2069_, sizeof(void*)*3, v_action_2007_);
lean_ctor_set_uint8(v_reuseFailAlloc_2069_, sizeof(void*)*3 + 1, v_wantsRebuild_2008_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
v_a_1999_ = v___x_2012_;
v_a_2000_ = v___x_2068_;
goto v___jp_1998_;
}
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v_a_2075_; 
lean_dec_ref(v___x_1993_);
lean_dec_ref(v_log_1982_);
lean_dec_ref(v_traceFile_1956_);
lean_dec_ref(v_inst_1954_);
v_a_2074_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_2074_);
v_a_2075_ = lean_ctor_get(v___x_1997_, 1);
lean_inc(v_a_2075_);
lean_dec_ref(v___x_1997_);
v_a_1999_ = v_a_2074_;
v_a_2000_ = v_a_2075_;
goto v___jp_1998_;
}
v___jp_1998_:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v_a_2003_; 
v___x_2001_ = lean_box(0);
v___x_2002_ = l_Lake_buildAction___redArg___lam__0(v___x_1994_, v___x_2001_, v_a_2000_);
lean_dec(v___x_1994_);
v_a_2003_ = lean_ctor_get(v___x_2002_, 1);
lean_inc(v_a_2003_);
lean_dec_ref(v___x_2002_);
v_a_1967_ = v_a_1999_;
v_a_1968_ = v_a_2003_;
goto v___jp_1966_;
}
}
}
else
{
uint8_t v___x_2077_; 
lean_dec_ref(v_a_1963_);
lean_dec(v_a_1962_);
lean_dec(v_a_1961_);
lean_dec(v_a_1960_);
lean_dec_ref(v_a_1959_);
lean_dec_ref(v_build_1957_);
lean_dec_ref(v_inst_1954_);
v___x_2077_ = l_System_FilePath_pathExists(v_traceFile_1956_);
lean_dec_ref(v_traceFile_1956_);
if (v___x_2077_ == 0)
{
lean_dec_ref(v___x_1993_);
lean_del_object(v___x_1988_);
v_log_1971_ = v_log_1982_;
v_action_1972_ = v___x_1991_;
v_wantsRebuild_1973_ = v_noBuild_1990_;
v_trace_1974_ = v_trace_1985_;
v_buildTime_1975_ = v_buildTime_1986_;
goto v___jp_1970_;
}
else
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2078_ = lean_box(0);
v___x_2079_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_2080_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1955_, v___x_2078_, v___x_2079_);
v___x_2081_ = l_Lake_BuildMetadata_writeFile(v___x_1993_, v___x_2080_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_dec_ref(v___x_2081_);
lean_del_object(v___x_1988_);
v_log_1971_ = v_log_1982_;
v_action_1972_ = v___x_1991_;
v_wantsRebuild_1973_ = v_noBuild_1990_;
v_trace_1974_ = v_trace_1985_;
v_buildTime_1975_ = v_buildTime_1986_;
goto v___jp_1970_;
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2089_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2082_);
lean_dec_ref(v___x_2081_);
v___x_2083_ = lean_io_error_to_string(v_a_2082_);
v___x_2084_ = 3;
v___x_2085_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2085_, 0, v___x_2083_);
lean_ctor_set_uint8(v___x_2085_, sizeof(void*)*1, v___x_2084_);
v___x_2086_ = lean_array_get_size(v_log_1982_);
v___x_2087_ = lean_array_push(v_log_1982_, v___x_2085_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v___x_2087_);
v___x_2089_ = v___x_1988_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_2087_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_trace_1985_);
lean_ctor_set(v_reuseFailAlloc_2091_, 2, v_buildTime_1986_);
v___x_2089_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
lean_object* v___x_2090_; 
lean_ctor_set_uint8(v___x_2089_, sizeof(void*)*3, v___x_1991_);
lean_ctor_set_uint8(v___x_2089_, sizeof(void*)*3 + 1, v_noBuild_1990_);
v___x_2090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2086_);
lean_ctor_set(v___x_2090_, 1, v___x_2089_);
return v___x_2090_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___boxed(lean_object* v_inst_2093_, lean_object* v_depTrace_2094_, lean_object* v_traceFile_2095_, lean_object* v_build_2096_, lean_object* v_action_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_){
_start:
{
uint8_t v_action_boxed_2105_; lean_object* v_res_2106_; 
v_action_boxed_2105_ = lean_unbox(v_action_2097_);
v_res_2106_ = l_Lake_buildAction___redArg(v_inst_2093_, v_depTrace_2094_, v_traceFile_2095_, v_build_2096_, v_action_boxed_2105_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
lean_dec_ref(v_depTrace_2094_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction(lean_object* v_00_u03b1_2107_, lean_object* v_inst_2108_, lean_object* v_depTrace_2109_, lean_object* v_traceFile_2110_, lean_object* v_build_2111_, uint8_t v_action_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Lake_buildAction___redArg(v_inst_2108_, v_depTrace_2109_, v_traceFile_2110_, v_build_2111_, v_action_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___boxed(lean_object* v_00_u03b1_2121_, lean_object* v_inst_2122_, lean_object* v_depTrace_2123_, lean_object* v_traceFile_2124_, lean_object* v_build_2125_, lean_object* v_action_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_){
_start:
{
uint8_t v_action_boxed_2134_; lean_object* v_res_2135_; 
v_action_boxed_2134_ = lean_unbox(v_action_2126_);
v_res_2135_ = l_Lake_buildAction(v_00_u03b1_2121_, v_inst_2122_, v_depTrace_2123_, v_traceFile_2124_, v_build_2125_, v_action_boxed_2134_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_);
lean_dec_ref(v_depTrace_2123_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg(lean_object* v_inst_2136_, lean_object* v_inst_2137_, lean_object* v_info_2138_, lean_object* v_depTrace_2139_, lean_object* v_traceFile_2140_, lean_object* v_build_2141_, uint8_t v_action_2142_, lean_object* v_oldTrace_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_){
_start:
{
lean_object* v_log_2151_; uint8_t v_action_2152_; uint8_t v_wantsRebuild_2153_; lean_object* v_trace_2154_; lean_object* v_buildTime_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2223_; 
v_log_2151_ = lean_ctor_get(v_a_2149_, 0);
v_action_2152_ = lean_ctor_get_uint8(v_a_2149_, sizeof(void*)*3);
v_wantsRebuild_2153_ = lean_ctor_get_uint8(v_a_2149_, sizeof(void*)*3 + 1);
v_trace_2154_ = lean_ctor_get(v_a_2149_, 1);
v_buildTime_2155_ = lean_ctor_get(v_a_2149_, 2);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_a_2149_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2157_ = v_a_2149_;
v_isShared_2158_ = v_isSharedCheck_2223_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_buildTime_2155_);
lean_inc(v_trace_2154_);
lean_inc(v_log_2151_);
lean_dec(v_a_2149_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2223_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2159_; 
lean_inc_ref(v_traceFile_2140_);
v___x_2159_ = l_Lake_readTraceFile(v_traceFile_2140_, v_log_2151_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v_a_2161_; lean_object* v___x_2163_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2160_);
v_a_2161_ = lean_ctor_get(v___x_2159_, 1);
lean_inc(v_a_2161_);
lean_dec_ref(v___x_2159_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 0, v_a_2161_);
v___x_2163_ = v___x_2157_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2161_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_trace_2154_);
lean_ctor_set(v_reuseFailAlloc_2210_, 2, v_buildTime_2155_);
lean_ctor_set_uint8(v_reuseFailAlloc_2210_, sizeof(void*)*3, v_action_2152_);
lean_ctor_set_uint8(v_reuseFailAlloc_2210_, sizeof(void*)*3 + 1, v_wantsRebuild_2153_);
v___x_2163_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2136_, v_inst_2137_, v_info_2138_, v_depTrace_2139_, v_a_2160_, v_oldTrace_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v___x_2163_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2200_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
v_a_2166_ = lean_ctor_get(v___x_2164_, 1);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2168_ = v___x_2164_;
v_isShared_2169_ = v_isSharedCheck_2200_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_inc(v_a_2165_);
lean_dec(v___x_2164_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2200_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
uint8_t v___x_2170_; uint8_t v___x_2171_; uint8_t v___x_2172_; 
v___x_2170_ = 0;
v___x_2171_ = lean_unbox(v_a_2165_);
lean_dec(v_a_2165_);
v___x_2172_ = l_Lake_instDecidableEqOutputStatus(v___x_2171_, v___x_2170_);
if (v___x_2172_ == 0)
{
uint8_t v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2176_; 
lean_dec_ref(v_a_2148_);
lean_dec(v_a_2147_);
lean_dec(v_a_2146_);
lean_dec(v_a_2145_);
lean_dec_ref(v_a_2144_);
lean_dec_ref(v_build_2141_);
lean_dec_ref(v_traceFile_2140_);
v___x_2173_ = 1;
v___x_2174_ = lean_box(v___x_2173_);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 0, v___x_2174_);
v___x_2176_ = v___x_2168_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2174_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_a_2166_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
else
{
lean_object* v___f_2178_; lean_object* v___x_2179_; 
lean_del_object(v___x_2168_);
v___f_2178_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2179_ = l_Lake_buildAction___redArg(v___f_2178_, v_depTrace_2139_, v_traceFile_2140_, v_build_2141_, v_action_2142_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2166_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2189_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 1);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2189_ == 0)
{
lean_object* v_unused_2190_; 
v_unused_2190_ = lean_ctor_get(v___x_2179_, 0);
lean_dec(v_unused_2190_);
v___x_2182_ = v___x_2179_;
v_isShared_2183_ = v_isSharedCheck_2189_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2179_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2189_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
uint8_t v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2187_; 
v___x_2184_ = 0;
v___x_2185_ = lean_box(v___x_2184_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 0, v___x_2185_);
v___x_2187_ = v___x_2182_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2185_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_a_2180_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
else
{
lean_object* v_a_2191_; lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
v_a_2191_ = lean_ctor_get(v___x_2179_, 0);
v_a_2192_ = lean_ctor_get(v___x_2179_, 1);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2179_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_inc(v_a_2191_);
lean_dec(v___x_2179_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2191_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
}
else
{
lean_object* v_a_2201_; lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_dec_ref(v_a_2148_);
lean_dec(v_a_2147_);
lean_dec(v_a_2146_);
lean_dec(v_a_2145_);
lean_dec_ref(v_a_2144_);
lean_dec_ref(v_build_2141_);
lean_dec_ref(v_traceFile_2140_);
v_a_2201_ = lean_ctor_get(v___x_2164_, 0);
v_a_2202_ = lean_ctor_get(v___x_2164_, 1);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2164_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_inc(v_a_2201_);
lean_dec(v___x_2164_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2201_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
}
else
{
lean_object* v_a_2211_; lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2222_; 
lean_dec_ref(v_a_2148_);
lean_dec(v_a_2147_);
lean_dec(v_a_2146_);
lean_dec(v_a_2145_);
lean_dec_ref(v_a_2144_);
lean_dec_ref(v_build_2141_);
lean_dec_ref(v_traceFile_2140_);
lean_dec(v_info_2138_);
lean_dec_ref(v_inst_2137_);
lean_dec_ref(v_inst_2136_);
v_a_2211_ = lean_ctor_get(v___x_2159_, 0);
v_a_2212_ = lean_ctor_get(v___x_2159_, 1);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2214_ = v___x_2159_;
v_isShared_2215_ = v_isSharedCheck_2222_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_inc(v_a_2211_);
lean_dec(v___x_2159_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2222_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 0, v_a_2212_);
v___x_2217_ = v___x_2157_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2212_);
lean_ctor_set(v_reuseFailAlloc_2221_, 1, v_trace_2154_);
lean_ctor_set(v_reuseFailAlloc_2221_, 2, v_buildTime_2155_);
lean_ctor_set_uint8(v_reuseFailAlloc_2221_, sizeof(void*)*3, v_action_2152_);
lean_ctor_set_uint8(v_reuseFailAlloc_2221_, sizeof(void*)*3 + 1, v_wantsRebuild_2153_);
v___x_2217_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
lean_object* v___x_2219_; 
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 1, v___x_2217_);
v___x_2219_ = v___x_2214_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2211_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v___x_2217_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg___boxed(lean_object* v_inst_2224_, lean_object* v_inst_2225_, lean_object* v_info_2226_, lean_object* v_depTrace_2227_, lean_object* v_traceFile_2228_, lean_object* v_build_2229_, lean_object* v_action_2230_, lean_object* v_oldTrace_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_){
_start:
{
uint8_t v_action_boxed_2239_; lean_object* v_res_2240_; 
v_action_boxed_2239_ = lean_unbox(v_action_2230_);
v_res_2240_ = l_Lake_buildUnlessUpToDate_x3f___redArg(v_inst_2224_, v_inst_2225_, v_info_2226_, v_depTrace_2227_, v_traceFile_2228_, v_build_2229_, v_action_boxed_2239_, v_oldTrace_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
lean_dec_ref(v_oldTrace_2231_);
lean_dec_ref(v_depTrace_2227_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f(lean_object* v_00_u03b9_2241_, lean_object* v_inst_2242_, lean_object* v_inst_2243_, lean_object* v_info_2244_, lean_object* v_depTrace_2245_, lean_object* v_traceFile_2246_, lean_object* v_build_2247_, uint8_t v_action_2248_, lean_object* v_oldTrace_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_){
_start:
{
lean_object* v_log_2257_; uint8_t v_action_2258_; uint8_t v_wantsRebuild_2259_; lean_object* v_trace_2260_; lean_object* v_buildTime_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2329_; 
v_log_2257_ = lean_ctor_get(v_a_2255_, 0);
v_action_2258_ = lean_ctor_get_uint8(v_a_2255_, sizeof(void*)*3);
v_wantsRebuild_2259_ = lean_ctor_get_uint8(v_a_2255_, sizeof(void*)*3 + 1);
v_trace_2260_ = lean_ctor_get(v_a_2255_, 1);
v_buildTime_2261_ = lean_ctor_get(v_a_2255_, 2);
v_isSharedCheck_2329_ = !lean_is_exclusive(v_a_2255_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2263_ = v_a_2255_;
v_isShared_2264_ = v_isSharedCheck_2329_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_buildTime_2261_);
lean_inc(v_trace_2260_);
lean_inc(v_log_2257_);
lean_dec(v_a_2255_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2329_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2265_; 
lean_inc_ref(v_traceFile_2246_);
v___x_2265_ = l_Lake_readTraceFile(v_traceFile_2246_, v_log_2257_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v_a_2267_; lean_object* v___x_2269_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2266_);
v_a_2267_ = lean_ctor_get(v___x_2265_, 1);
lean_inc(v_a_2267_);
lean_dec_ref(v___x_2265_);
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 0, v_a_2267_);
v___x_2269_ = v___x_2263_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2267_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_trace_2260_);
lean_ctor_set(v_reuseFailAlloc_2316_, 2, v_buildTime_2261_);
lean_ctor_set_uint8(v_reuseFailAlloc_2316_, sizeof(void*)*3, v_action_2258_);
lean_ctor_set_uint8(v_reuseFailAlloc_2316_, sizeof(void*)*3 + 1, v_wantsRebuild_2259_);
v___x_2269_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2242_, v_inst_2243_, v_info_2244_, v_depTrace_2245_, v_a_2266_, v_oldTrace_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v___x_2269_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2306_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
v_a_2272_ = lean_ctor_get(v___x_2270_, 1);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2274_ = v___x_2270_;
v_isShared_2275_ = v_isSharedCheck_2306_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_inc(v_a_2271_);
lean_dec(v___x_2270_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2306_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
uint8_t v___x_2276_; uint8_t v___x_2277_; uint8_t v___x_2278_; 
v___x_2276_ = 0;
v___x_2277_ = lean_unbox(v_a_2271_);
lean_dec(v_a_2271_);
v___x_2278_ = l_Lake_instDecidableEqOutputStatus(v___x_2277_, v___x_2276_);
if (v___x_2278_ == 0)
{
uint8_t v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2282_; 
lean_dec_ref(v_a_2254_);
lean_dec(v_a_2253_);
lean_dec(v_a_2252_);
lean_dec(v_a_2251_);
lean_dec_ref(v_a_2250_);
lean_dec_ref(v_build_2247_);
lean_dec_ref(v_traceFile_2246_);
v___x_2279_ = 1;
v___x_2280_ = lean_box(v___x_2279_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 0, v___x_2280_);
v___x_2282_ = v___x_2274_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2280_);
lean_ctor_set(v_reuseFailAlloc_2283_, 1, v_a_2272_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
else
{
lean_object* v___f_2284_; lean_object* v___x_2285_; 
lean_del_object(v___x_2274_);
v___f_2284_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2285_ = l_Lake_buildAction___redArg(v___f_2284_, v_depTrace_2245_, v_traceFile_2246_, v_build_2247_, v_action_2248_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2272_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2295_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 1);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2295_ == 0)
{
lean_object* v_unused_2296_; 
v_unused_2296_ = lean_ctor_get(v___x_2285_, 0);
lean_dec(v_unused_2296_);
v___x_2288_ = v___x_2285_;
v_isShared_2289_ = v_isSharedCheck_2295_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2285_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2295_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
uint8_t v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2293_; 
v___x_2290_ = 0;
v___x_2291_ = lean_box(v___x_2290_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 0, v___x_2291_);
v___x_2293_ = v___x_2288_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2291_);
lean_ctor_set(v_reuseFailAlloc_2294_, 1, v_a_2286_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
else
{
lean_object* v_a_2297_; lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
v_a_2297_ = lean_ctor_get(v___x_2285_, 0);
v_a_2298_ = lean_ctor_get(v___x_2285_, 1);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2285_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_inc(v_a_2297_);
lean_dec(v___x_2285_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2297_);
lean_ctor_set(v_reuseFailAlloc_2304_, 1, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_dec_ref(v_a_2254_);
lean_dec(v_a_2253_);
lean_dec(v_a_2252_);
lean_dec(v_a_2251_);
lean_dec_ref(v_a_2250_);
lean_dec_ref(v_build_2247_);
lean_dec_ref(v_traceFile_2246_);
v_a_2307_ = lean_ctor_get(v___x_2270_, 0);
v_a_2308_ = lean_ctor_get(v___x_2270_, 1);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2270_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_inc(v_a_2307_);
lean_dec(v___x_2270_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2307_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
else
{
lean_object* v_a_2317_; lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2328_; 
lean_dec_ref(v_a_2254_);
lean_dec(v_a_2253_);
lean_dec(v_a_2252_);
lean_dec(v_a_2251_);
lean_dec_ref(v_a_2250_);
lean_dec_ref(v_build_2247_);
lean_dec_ref(v_traceFile_2246_);
lean_dec(v_info_2244_);
lean_dec_ref(v_inst_2243_);
lean_dec_ref(v_inst_2242_);
v_a_2317_ = lean_ctor_get(v___x_2265_, 0);
v_a_2318_ = lean_ctor_get(v___x_2265_, 1);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2320_ = v___x_2265_;
v_isShared_2321_ = v_isSharedCheck_2328_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_inc(v_a_2317_);
lean_dec(v___x_2265_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2328_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 0, v_a_2318_);
v___x_2323_ = v___x_2263_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2318_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_trace_2260_);
lean_ctor_set(v_reuseFailAlloc_2327_, 2, v_buildTime_2261_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, sizeof(void*)*3, v_action_2258_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, sizeof(void*)*3 + 1, v_wantsRebuild_2259_);
v___x_2323_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
lean_object* v___x_2325_; 
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 1, v___x_2323_);
v___x_2325_ = v___x_2320_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2317_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v___x_2323_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___boxed(lean_object* v_00_u03b9_2330_, lean_object* v_inst_2331_, lean_object* v_inst_2332_, lean_object* v_info_2333_, lean_object* v_depTrace_2334_, lean_object* v_traceFile_2335_, lean_object* v_build_2336_, lean_object* v_action_2337_, lean_object* v_oldTrace_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_){
_start:
{
uint8_t v_action_boxed_2346_; lean_object* v_res_2347_; 
v_action_boxed_2346_ = lean_unbox(v_action_2337_);
v_res_2347_ = l_Lake_buildUnlessUpToDate_x3f(v_00_u03b9_2330_, v_inst_2331_, v_inst_2332_, v_info_2333_, v_depTrace_2334_, v_traceFile_2335_, v_build_2336_, v_action_boxed_2346_, v_oldTrace_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_);
lean_dec_ref(v_oldTrace_2338_);
lean_dec_ref(v_depTrace_2334_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg(lean_object* v_inst_2348_, lean_object* v_inst_2349_, lean_object* v_info_2350_, lean_object* v_depTrace_2351_, lean_object* v_traceFile_2352_, lean_object* v_build_2353_, uint8_t v_action_2354_, lean_object* v_oldTrace_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v_a_2364_; lean_object* v_a_2365_; lean_object* v_log_2367_; uint8_t v_action_2368_; uint8_t v_wantsRebuild_2369_; lean_object* v_trace_2370_; lean_object* v_buildTime_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2409_; 
v_log_2367_ = lean_ctor_get(v_a_2361_, 0);
v_action_2368_ = lean_ctor_get_uint8(v_a_2361_, sizeof(void*)*3);
v_wantsRebuild_2369_ = lean_ctor_get_uint8(v_a_2361_, sizeof(void*)*3 + 1);
v_trace_2370_ = lean_ctor_get(v_a_2361_, 1);
v_buildTime_2371_ = lean_ctor_get(v_a_2361_, 2);
v_isSharedCheck_2409_ = !lean_is_exclusive(v_a_2361_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2373_ = v_a_2361_;
v_isShared_2374_ = v_isSharedCheck_2409_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_buildTime_2371_);
lean_inc(v_trace_2370_);
lean_inc(v_log_2367_);
lean_dec(v_a_2361_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2409_;
goto v_resetjp_2372_;
}
v___jp_2363_:
{
lean_object* v___x_2366_; 
v___x_2366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2366_, 0, v_a_2364_);
lean_ctor_set(v___x_2366_, 1, v_a_2365_);
return v___x_2366_;
}
v_resetjp_2372_:
{
lean_object* v___x_2375_; 
lean_inc_ref(v_traceFile_2352_);
v___x_2375_ = l_Lake_readTraceFile(v_traceFile_2352_, v_log_2367_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v_a_2377_; lean_object* v___x_2379_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_a_2376_);
v_a_2377_ = lean_ctor_get(v___x_2375_, 1);
lean_inc(v_a_2377_);
lean_dec_ref(v___x_2375_);
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 0, v_a_2377_);
v___x_2379_ = v___x_2373_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2377_);
lean_ctor_set(v_reuseFailAlloc_2403_, 1, v_trace_2370_);
lean_ctor_set(v_reuseFailAlloc_2403_, 2, v_buildTime_2371_);
lean_ctor_set_uint8(v_reuseFailAlloc_2403_, sizeof(void*)*3, v_action_2368_);
lean_ctor_set_uint8(v_reuseFailAlloc_2403_, sizeof(void*)*3 + 1, v_wantsRebuild_2369_);
v___x_2379_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2348_, v_inst_2349_, v_info_2350_, v_depTrace_2351_, v_a_2376_, v_oldTrace_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v___x_2379_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2400_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
v_a_2382_ = lean_ctor_get(v___x_2380_, 1);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2384_ = v___x_2380_;
v_isShared_2385_ = v_isSharedCheck_2400_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_inc(v_a_2381_);
lean_dec(v___x_2380_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2400_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2386_; lean_object* v_a_2388_; uint8_t v___x_2392_; uint8_t v___x_2393_; uint8_t v___x_2394_; 
v___x_2386_ = lean_box(0);
v___x_2392_ = 0;
v___x_2393_ = lean_unbox(v_a_2381_);
lean_dec(v_a_2381_);
v___x_2394_ = l_Lake_instDecidableEqOutputStatus(v___x_2393_, v___x_2392_);
if (v___x_2394_ == 0)
{
lean_dec_ref(v_a_2360_);
lean_dec(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec(v_a_2357_);
lean_dec_ref(v_a_2356_);
lean_dec_ref(v_build_2353_);
lean_dec_ref(v_traceFile_2352_);
v_a_2388_ = v_a_2382_;
goto v___jp_2387_;
}
else
{
lean_object* v___f_2395_; lean_object* v___x_2396_; 
v___f_2395_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2396_ = l_Lake_buildAction___redArg(v___f_2395_, v_depTrace_2351_, v_traceFile_2352_, v_build_2353_, v_action_2354_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2382_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 1);
lean_inc(v_a_2397_);
lean_dec_ref(v___x_2396_);
v_a_2388_ = v_a_2397_;
goto v___jp_2387_;
}
else
{
lean_object* v_a_2398_; lean_object* v_a_2399_; 
lean_del_object(v___x_2384_);
v_a_2398_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2398_);
v_a_2399_ = lean_ctor_get(v___x_2396_, 1);
lean_inc(v_a_2399_);
lean_dec_ref(v___x_2396_);
v_a_2364_ = v_a_2398_;
v_a_2365_ = v_a_2399_;
goto v___jp_2363_;
}
}
v___jp_2387_:
{
lean_object* v___x_2390_; 
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 1, v_a_2388_);
lean_ctor_set(v___x_2384_, 0, v___x_2386_);
v___x_2390_ = v___x_2384_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2391_, 1, v_a_2388_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
else
{
lean_object* v_a_2401_; lean_object* v_a_2402_; 
lean_dec_ref(v_a_2360_);
lean_dec(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec(v_a_2357_);
lean_dec_ref(v_a_2356_);
lean_dec_ref(v_build_2353_);
lean_dec_ref(v_traceFile_2352_);
v_a_2401_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2401_);
v_a_2402_ = lean_ctor_get(v___x_2380_, 1);
lean_inc(v_a_2402_);
lean_dec_ref(v___x_2380_);
v_a_2364_ = v_a_2401_;
v_a_2365_ = v_a_2402_;
goto v___jp_2363_;
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v_a_2405_; lean_object* v___x_2407_; 
lean_dec_ref(v_a_2360_);
lean_dec(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec(v_a_2357_);
lean_dec_ref(v_a_2356_);
lean_dec_ref(v_build_2353_);
lean_dec_ref(v_traceFile_2352_);
lean_dec(v_info_2350_);
lean_dec_ref(v_inst_2349_);
lean_dec_ref(v_inst_2348_);
v_a_2404_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_a_2404_);
v_a_2405_ = lean_ctor_get(v___x_2375_, 1);
lean_inc(v_a_2405_);
lean_dec_ref(v___x_2375_);
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 0, v_a_2405_);
v___x_2407_ = v___x_2373_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2405_);
lean_ctor_set(v_reuseFailAlloc_2408_, 1, v_trace_2370_);
lean_ctor_set(v_reuseFailAlloc_2408_, 2, v_buildTime_2371_);
lean_ctor_set_uint8(v_reuseFailAlloc_2408_, sizeof(void*)*3, v_action_2368_);
lean_ctor_set_uint8(v_reuseFailAlloc_2408_, sizeof(void*)*3 + 1, v_wantsRebuild_2369_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
v_a_2364_ = v_a_2404_;
v_a_2365_ = v___x_2407_;
goto v___jp_2363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg___boxed(lean_object* v_inst_2410_, lean_object* v_inst_2411_, lean_object* v_info_2412_, lean_object* v_depTrace_2413_, lean_object* v_traceFile_2414_, lean_object* v_build_2415_, lean_object* v_action_2416_, lean_object* v_oldTrace_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
uint8_t v_action_boxed_2425_; lean_object* v_res_2426_; 
v_action_boxed_2425_ = lean_unbox(v_action_2416_);
v_res_2426_ = l_Lake_buildUnlessUpToDate___redArg(v_inst_2410_, v_inst_2411_, v_info_2412_, v_depTrace_2413_, v_traceFile_2414_, v_build_2415_, v_action_boxed_2425_, v_oldTrace_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
lean_dec_ref(v_oldTrace_2417_);
lean_dec_ref(v_depTrace_2413_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate(lean_object* v_00_u03b9_2427_, lean_object* v_inst_2428_, lean_object* v_inst_2429_, lean_object* v_info_2430_, lean_object* v_depTrace_2431_, lean_object* v_traceFile_2432_, lean_object* v_build_2433_, uint8_t v_action_2434_, lean_object* v_oldTrace_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_){
_start:
{
lean_object* v_a_2444_; lean_object* v_a_2445_; lean_object* v_log_2447_; uint8_t v_action_2448_; uint8_t v_wantsRebuild_2449_; lean_object* v_trace_2450_; lean_object* v_buildTime_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2489_; 
v_log_2447_ = lean_ctor_get(v_a_2441_, 0);
v_action_2448_ = lean_ctor_get_uint8(v_a_2441_, sizeof(void*)*3);
v_wantsRebuild_2449_ = lean_ctor_get_uint8(v_a_2441_, sizeof(void*)*3 + 1);
v_trace_2450_ = lean_ctor_get(v_a_2441_, 1);
v_buildTime_2451_ = lean_ctor_get(v_a_2441_, 2);
v_isSharedCheck_2489_ = !lean_is_exclusive(v_a_2441_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2453_ = v_a_2441_;
v_isShared_2454_ = v_isSharedCheck_2489_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_buildTime_2451_);
lean_inc(v_trace_2450_);
lean_inc(v_log_2447_);
lean_dec(v_a_2441_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2489_;
goto v_resetjp_2452_;
}
v___jp_2443_:
{
lean_object* v___x_2446_; 
v___x_2446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2446_, 0, v_a_2444_);
lean_ctor_set(v___x_2446_, 1, v_a_2445_);
return v___x_2446_;
}
v_resetjp_2452_:
{
lean_object* v___x_2455_; 
lean_inc_ref(v_traceFile_2432_);
v___x_2455_ = l_Lake_readTraceFile(v_traceFile_2432_, v_log_2447_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v_a_2457_; lean_object* v___x_2459_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
v_a_2457_ = lean_ctor_get(v___x_2455_, 1);
lean_inc(v_a_2457_);
lean_dec_ref(v___x_2455_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v_a_2457_);
v___x_2459_ = v___x_2453_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2457_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v_trace_2450_);
lean_ctor_set(v_reuseFailAlloc_2483_, 2, v_buildTime_2451_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, sizeof(void*)*3, v_action_2448_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, sizeof(void*)*3 + 1, v_wantsRebuild_2449_);
v___x_2459_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
lean_object* v___x_2460_; 
v___x_2460_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2428_, v_inst_2429_, v_info_2430_, v_depTrace_2431_, v_a_2456_, v_oldTrace_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v___x_2459_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2480_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
v_a_2462_ = lean_ctor_get(v___x_2460_, 1);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2464_ = v___x_2460_;
v_isShared_2465_ = v_isSharedCheck_2480_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_inc(v_a_2461_);
lean_dec(v___x_2460_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2480_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2466_; lean_object* v_a_2468_; uint8_t v___x_2472_; uint8_t v___x_2473_; uint8_t v___x_2474_; 
v___x_2466_ = lean_box(0);
v___x_2472_ = 0;
v___x_2473_ = lean_unbox(v_a_2461_);
lean_dec(v_a_2461_);
v___x_2474_ = l_Lake_instDecidableEqOutputStatus(v___x_2473_, v___x_2472_);
if (v___x_2474_ == 0)
{
lean_dec_ref(v_a_2440_);
lean_dec(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec(v_a_2437_);
lean_dec_ref(v_a_2436_);
lean_dec_ref(v_build_2433_);
lean_dec_ref(v_traceFile_2432_);
v_a_2468_ = v_a_2462_;
goto v___jp_2467_;
}
else
{
lean_object* v___f_2475_; lean_object* v___x_2476_; 
v___f_2475_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2476_ = l_Lake_buildAction___redArg(v___f_2475_, v_depTrace_2431_, v_traceFile_2432_, v_build_2433_, v_action_2434_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2462_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 1);
lean_inc(v_a_2477_);
lean_dec_ref(v___x_2476_);
v_a_2468_ = v_a_2477_;
goto v___jp_2467_;
}
else
{
lean_object* v_a_2478_; lean_object* v_a_2479_; 
lean_del_object(v___x_2464_);
v_a_2478_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2478_);
v_a_2479_ = lean_ctor_get(v___x_2476_, 1);
lean_inc(v_a_2479_);
lean_dec_ref(v___x_2476_);
v_a_2444_ = v_a_2478_;
v_a_2445_ = v_a_2479_;
goto v___jp_2443_;
}
}
v___jp_2467_:
{
lean_object* v___x_2470_; 
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 1, v_a_2468_);
lean_ctor_set(v___x_2464_, 0, v___x_2466_);
v___x_2470_ = v___x_2464_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2466_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v_a_2468_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
else
{
lean_object* v_a_2481_; lean_object* v_a_2482_; 
lean_dec_ref(v_a_2440_);
lean_dec(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec(v_a_2437_);
lean_dec_ref(v_a_2436_);
lean_dec_ref(v_build_2433_);
lean_dec_ref(v_traceFile_2432_);
v_a_2481_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_a_2481_);
v_a_2482_ = lean_ctor_get(v___x_2460_, 1);
lean_inc(v_a_2482_);
lean_dec_ref(v___x_2460_);
v_a_2444_ = v_a_2481_;
v_a_2445_ = v_a_2482_;
goto v___jp_2443_;
}
}
}
else
{
lean_object* v_a_2484_; lean_object* v_a_2485_; lean_object* v___x_2487_; 
lean_dec_ref(v_a_2440_);
lean_dec(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec(v_a_2437_);
lean_dec_ref(v_a_2436_);
lean_dec_ref(v_build_2433_);
lean_dec_ref(v_traceFile_2432_);
lean_dec(v_info_2430_);
lean_dec_ref(v_inst_2429_);
lean_dec_ref(v_inst_2428_);
v_a_2484_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2484_);
v_a_2485_ = lean_ctor_get(v___x_2455_, 1);
lean_inc(v_a_2485_);
lean_dec_ref(v___x_2455_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v_a_2485_);
v___x_2487_ = v___x_2453_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2485_);
lean_ctor_set(v_reuseFailAlloc_2488_, 1, v_trace_2450_);
lean_ctor_set(v_reuseFailAlloc_2488_, 2, v_buildTime_2451_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, sizeof(void*)*3, v_action_2448_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, sizeof(void*)*3 + 1, v_wantsRebuild_2449_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
v_a_2444_ = v_a_2484_;
v_a_2445_ = v___x_2487_;
goto v___jp_2443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___boxed(lean_object* v_00_u03b9_2490_, lean_object* v_inst_2491_, lean_object* v_inst_2492_, lean_object* v_info_2493_, lean_object* v_depTrace_2494_, lean_object* v_traceFile_2495_, lean_object* v_build_2496_, lean_object* v_action_2497_, lean_object* v_oldTrace_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_){
_start:
{
uint8_t v_action_boxed_2506_; lean_object* v_res_2507_; 
v_action_boxed_2506_ = lean_unbox(v_action_2497_);
v_res_2507_ = l_Lake_buildUnlessUpToDate(v_00_u03b9_2490_, v_inst_2491_, v_inst_2492_, v_info_2493_, v_depTrace_2494_, v_traceFile_2495_, v_build_2496_, v_action_boxed_2506_, v_oldTrace_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_);
lean_dec_ref(v_oldTrace_2498_);
lean_dec_ref(v_depTrace_2494_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFileHash(lean_object* v_file_2509_, uint64_t v_hash_2510_){
_start:
{
lean_object* v___x_2512_; lean_object* v_hashFile_2513_; lean_object* v___x_2514_; 
v___x_2512_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
v_hashFile_2513_ = lean_string_append(v_file_2509_, v___x_2512_);
lean_inc_ref(v_hashFile_2513_);
v___x_2514_ = l_Lake_createParentDirs(v_hashFile_2513_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
lean_dec_ref(v___x_2514_);
v___x_2515_ = l_Lake_Hash_hex(v_hash_2510_);
v___x_2516_ = l_IO_FS_writeFile(v_hashFile_2513_, v___x_2515_);
lean_dec_ref(v___x_2515_);
lean_dec_ref(v_hashFile_2513_);
return v___x_2516_;
}
else
{
lean_dec_ref(v_hashFile_2513_);
return v___x_2514_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_writeFileHash___boxed(lean_object* v_file_2517_, lean_object* v_hash_2518_, lean_object* v_a_2519_){
_start:
{
uint64_t v_hash_boxed_2520_; lean_object* v_res_2521_; 
v_hash_boxed_2520_ = lean_unbox_uint64(v_hash_2518_);
lean_dec_ref(v_hash_2518_);
v_res_2521_ = l_Lake_writeFileHash(v_file_2517_, v_hash_boxed_2520_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object* v_file_2522_, uint8_t v_text_2523_){
_start:
{
lean_object* v___y_2526_; 
if (v_text_2523_ == 0)
{
lean_object* v___x_2538_; 
v___x_2538_ = l_Lake_computeBinFileHash(v_file_2522_);
v___y_2526_ = v___x_2538_;
goto v___jp_2525_;
}
else
{
lean_object* v___x_2539_; 
v___x_2539_ = l_Lake_computeTextFileHash(v_file_2522_);
v___y_2526_ = v___x_2539_;
goto v___jp_2525_;
}
v___jp_2525_:
{
if (lean_obj_tag(v___y_2526_) == 0)
{
lean_object* v_a_2527_; uint64_t v___x_2528_; lean_object* v___x_2529_; 
v_a_2527_ = lean_ctor_get(v___y_2526_, 0);
lean_inc(v_a_2527_);
lean_dec_ref(v___y_2526_);
v___x_2528_ = lean_unbox_uint64(v_a_2527_);
lean_dec(v_a_2527_);
v___x_2529_ = l_Lake_writeFileHash(v_file_2522_, v___x_2528_);
return v___x_2529_;
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
lean_dec_ref(v_file_2522_);
v_a_2530_ = lean_ctor_get(v___y_2526_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___y_2526_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2532_ = v___y_2526_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___y_2526_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash___boxed(lean_object* v_file_2540_, lean_object* v_text_2541_, lean_object* v_a_2542_){
_start:
{
uint8_t v_text_boxed_2543_; lean_object* v_res_2544_; 
v_text_boxed_2543_ = lean_unbox(v_text_2541_);
v_res_2544_ = l_Lake_cacheFileHash(v_file_2540_, v_text_boxed_2543_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Lake_clearFileHash(lean_object* v_file_2545_){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2547_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
v___x_2548_ = lean_string_append(v_file_2545_, v___x_2547_);
v___x_2549_ = l_Lake_removeFileIfExists(v___x_2548_);
lean_dec_ref(v___x_2548_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Lake_clearFileHash___boxed(lean_object* v_file_2550_, lean_object* v_a_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lake_clearFileHash(v_file_2550_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg(lean_object* v_file_2553_, uint8_t v_text_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_){
_start:
{
lean_object* v_toBuildConfig_2558_; uint8_t v_trustHash_2559_; lean_object* v___x_2560_; lean_object* v_hashFile_2561_; uint8_t v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2566_; uint8_t v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2601_; 
v_toBuildConfig_2558_ = lean_ctor_get(v_a_2555_, 0);
v_trustHash_2559_ = lean_ctor_get_uint8(v_toBuildConfig_2558_, sizeof(void*)*2 + 1);
v___x_2560_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
lean_inc_ref(v_file_2553_);
v_hashFile_2561_ = lean_string_append(v_file_2553_, v___x_2560_);
if (v_trustHash_2559_ == 0)
{
v___y_2601_ = v_a_2556_;
goto v___jp_2600_;
}
else
{
lean_object* v___x_2614_; 
v___x_2614_ = l_Lake_Hash_load_x3f(v_hashFile_2561_);
if (lean_obj_tag(v___x_2614_) == 1)
{
lean_object* v_val_2615_; lean_object* v___x_2616_; 
lean_dec_ref(v_hashFile_2561_);
lean_dec_ref(v_file_2553_);
v_val_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_val_2615_);
lean_dec_ref(v___x_2614_);
v___x_2616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2616_, 0, v_val_2615_);
lean_ctor_set(v___x_2616_, 1, v_a_2556_);
return v___x_2616_;
}
else
{
lean_dec(v___x_2614_);
v___y_2601_ = v_a_2556_;
goto v___jp_2600_;
}
}
v___jp_2562_:
{
if (lean_obj_tag(v___y_2568_) == 0)
{
lean_object* v_a_2569_; lean_object* v___x_2570_; 
v_a_2569_ = lean_ctor_get(v___y_2568_, 0);
lean_inc(v_a_2569_);
lean_dec_ref(v___y_2568_);
lean_inc_ref(v_hashFile_2561_);
v___x_2570_ = l_Lake_createParentDirs(v_hashFile_2561_);
if (lean_obj_tag(v___x_2570_) == 0)
{
uint64_t v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
lean_dec_ref(v___x_2570_);
v___x_2571_ = lean_unbox_uint64(v_a_2569_);
v___x_2572_ = l_Lake_Hash_hex(v___x_2571_);
v___x_2573_ = l_IO_FS_writeFile(v_hashFile_2561_, v___x_2572_);
lean_dec_ref(v___x_2572_);
lean_dec_ref(v_hashFile_2561_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
lean_dec_ref(v___x_2573_);
v___x_2574_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2574_, 0, v___y_2565_);
lean_ctor_set(v___x_2574_, 1, v___y_2566_);
lean_ctor_set(v___x_2574_, 2, v___y_2564_);
lean_ctor_set_uint8(v___x_2574_, sizeof(void*)*3, v___y_2563_);
lean_ctor_set_uint8(v___x_2574_, sizeof(void*)*3 + 1, v___y_2567_);
v___x_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2575_, 0, v_a_2569_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
return v___x_2575_;
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
lean_dec(v_a_2569_);
v_a_2576_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2576_);
lean_dec_ref(v___x_2573_);
v___x_2577_ = lean_io_error_to_string(v_a_2576_);
v___x_2578_ = 3;
v___x_2579_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2579_, 0, v___x_2577_);
lean_ctor_set_uint8(v___x_2579_, sizeof(void*)*1, v___x_2578_);
v___x_2580_ = lean_array_get_size(v___y_2565_);
v___x_2581_ = lean_array_push(v___y_2565_, v___x_2579_);
v___x_2582_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2582_, 0, v___x_2581_);
lean_ctor_set(v___x_2582_, 1, v___y_2566_);
lean_ctor_set(v___x_2582_, 2, v___y_2564_);
lean_ctor_set_uint8(v___x_2582_, sizeof(void*)*3, v___y_2563_);
lean_ctor_set_uint8(v___x_2582_, sizeof(void*)*3 + 1, v___y_2567_);
v___x_2583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2580_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
return v___x_2583_;
}
}
else
{
lean_object* v_a_2584_; lean_object* v___x_2585_; uint8_t v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
lean_dec(v_a_2569_);
lean_dec_ref(v_hashFile_2561_);
v_a_2584_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_a_2584_);
lean_dec_ref(v___x_2570_);
v___x_2585_ = lean_io_error_to_string(v_a_2584_);
v___x_2586_ = 3;
v___x_2587_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2587_, 0, v___x_2585_);
lean_ctor_set_uint8(v___x_2587_, sizeof(void*)*1, v___x_2586_);
v___x_2588_ = lean_array_get_size(v___y_2565_);
v___x_2589_ = lean_array_push(v___y_2565_, v___x_2587_);
v___x_2590_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
lean_ctor_set(v___x_2590_, 1, v___y_2566_);
lean_ctor_set(v___x_2590_, 2, v___y_2564_);
lean_ctor_set_uint8(v___x_2590_, sizeof(void*)*3, v___y_2563_);
lean_ctor_set_uint8(v___x_2590_, sizeof(void*)*3 + 1, v___y_2567_);
v___x_2591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2588_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
return v___x_2591_;
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2593_; uint8_t v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
lean_dec_ref(v_hashFile_2561_);
v_a_2592_ = lean_ctor_get(v___y_2568_, 0);
lean_inc(v_a_2592_);
lean_dec_ref(v___y_2568_);
v___x_2593_ = lean_io_error_to_string(v_a_2592_);
v___x_2594_ = 3;
v___x_2595_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2595_, 0, v___x_2593_);
lean_ctor_set_uint8(v___x_2595_, sizeof(void*)*1, v___x_2594_);
v___x_2596_ = lean_array_get_size(v___y_2565_);
v___x_2597_ = lean_array_push(v___y_2565_, v___x_2595_);
v___x_2598_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2598_, 0, v___x_2597_);
lean_ctor_set(v___x_2598_, 1, v___y_2566_);
lean_ctor_set(v___x_2598_, 2, v___y_2564_);
lean_ctor_set_uint8(v___x_2598_, sizeof(void*)*3, v___y_2563_);
lean_ctor_set_uint8(v___x_2598_, sizeof(void*)*3 + 1, v___y_2567_);
v___x_2599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2596_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
return v___x_2599_;
}
}
v___jp_2600_:
{
if (v_text_2554_ == 0)
{
lean_object* v_log_2602_; uint8_t v_action_2603_; uint8_t v_wantsRebuild_2604_; lean_object* v_trace_2605_; lean_object* v_buildTime_2606_; lean_object* v___x_2607_; 
v_log_2602_ = lean_ctor_get(v___y_2601_, 0);
lean_inc_ref(v_log_2602_);
v_action_2603_ = lean_ctor_get_uint8(v___y_2601_, sizeof(void*)*3);
v_wantsRebuild_2604_ = lean_ctor_get_uint8(v___y_2601_, sizeof(void*)*3 + 1);
v_trace_2605_ = lean_ctor_get(v___y_2601_, 1);
lean_inc_ref(v_trace_2605_);
v_buildTime_2606_ = lean_ctor_get(v___y_2601_, 2);
lean_inc(v_buildTime_2606_);
lean_dec_ref(v___y_2601_);
v___x_2607_ = l_Lake_computeBinFileHash(v_file_2553_);
lean_dec_ref(v_file_2553_);
v___y_2563_ = v_action_2603_;
v___y_2564_ = v_buildTime_2606_;
v___y_2565_ = v_log_2602_;
v___y_2566_ = v_trace_2605_;
v___y_2567_ = v_wantsRebuild_2604_;
v___y_2568_ = v___x_2607_;
goto v___jp_2562_;
}
else
{
lean_object* v_log_2608_; uint8_t v_action_2609_; uint8_t v_wantsRebuild_2610_; lean_object* v_trace_2611_; lean_object* v_buildTime_2612_; lean_object* v___x_2613_; 
v_log_2608_ = lean_ctor_get(v___y_2601_, 0);
lean_inc_ref(v_log_2608_);
v_action_2609_ = lean_ctor_get_uint8(v___y_2601_, sizeof(void*)*3);
v_wantsRebuild_2610_ = lean_ctor_get_uint8(v___y_2601_, sizeof(void*)*3 + 1);
v_trace_2611_ = lean_ctor_get(v___y_2601_, 1);
lean_inc_ref(v_trace_2611_);
v_buildTime_2612_ = lean_ctor_get(v___y_2601_, 2);
lean_inc(v_buildTime_2612_);
lean_dec_ref(v___y_2601_);
v___x_2613_ = l_Lake_computeTextFileHash(v_file_2553_);
lean_dec_ref(v_file_2553_);
v___y_2563_ = v_action_2609_;
v___y_2564_ = v_buildTime_2612_;
v___y_2565_ = v_log_2608_;
v___y_2566_ = v_trace_2611_;
v___y_2567_ = v_wantsRebuild_2610_;
v___y_2568_ = v___x_2613_;
goto v___jp_2562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg___boxed(lean_object* v_file_2617_, lean_object* v_text_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_){
_start:
{
uint8_t v_text_boxed_2622_; lean_object* v_res_2623_; 
v_text_boxed_2622_ = lean_unbox(v_text_2618_);
v_res_2623_ = l_Lake_fetchFileHash___redArg(v_file_2617_, v_text_boxed_2622_, v_a_2619_, v_a_2620_);
lean_dec_ref(v_a_2619_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash(lean_object* v_file_2624_, uint8_t v_text_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Lake_fetchFileHash___redArg(v_file_2624_, v_text_2625_, v_a_2630_, v_a_2631_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___boxed(lean_object* v_file_2634_, lean_object* v_text_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
uint8_t v_text_boxed_2643_; lean_object* v_res_2644_; 
v_text_boxed_2643_ = lean_unbox(v_text_2635_);
v_res_2644_ = l_Lake_fetchFileHash(v_file_2634_, v_text_boxed_2643_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_);
lean_dec_ref(v_a_2640_);
lean_dec(v_a_2639_);
lean_dec(v_a_2638_);
lean_dec(v_a_2637_);
lean_dec_ref(v_a_2636_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg(lean_object* v_file_2645_, uint8_t v_text_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_){
_start:
{
lean_object* v___x_2650_; 
lean_inc_ref(v_file_2645_);
v___x_2650_ = l_Lake_fetchFileHash___redArg(v_file_2645_, v_text_2646_, v_a_2647_, v_a_2648_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2689_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 1);
v_a_2652_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2654_ = v___x_2650_;
v_isShared_2655_ = v_isSharedCheck_2689_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2651_);
lean_inc(v_a_2652_);
lean_dec(v___x_2650_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2689_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v_log_2656_; uint8_t v_action_2657_; uint8_t v_wantsRebuild_2658_; lean_object* v_trace_2659_; lean_object* v_buildTime_2660_; lean_object* v___x_2661_; 
v_log_2656_ = lean_ctor_get(v_a_2651_, 0);
v_action_2657_ = lean_ctor_get_uint8(v_a_2651_, sizeof(void*)*3);
v_wantsRebuild_2658_ = lean_ctor_get_uint8(v_a_2651_, sizeof(void*)*3 + 1);
v_trace_2659_ = lean_ctor_get(v_a_2651_, 1);
v_buildTime_2660_ = lean_ctor_get(v_a_2651_, 2);
v___x_2661_ = lean_io_metadata(v_file_2645_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; lean_object* v_modified_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; uint64_t v___x_2666_; lean_object* v___x_2668_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2662_);
lean_dec_ref(v___x_2661_);
v_modified_2663_ = lean_ctor_get(v_a_2662_, 1);
lean_inc_ref(v_modified_2663_);
lean_dec(v_a_2662_);
v___x_2664_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_2665_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_2665_, 0, v_file_2645_);
lean_ctor_set(v___x_2665_, 1, v___x_2664_);
lean_ctor_set(v___x_2665_, 2, v_modified_2663_);
v___x_2666_ = lean_unbox_uint64(v_a_2652_);
lean_dec(v_a_2652_);
lean_ctor_set_uint64(v___x_2665_, sizeof(void*)*3, v___x_2666_);
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 0, v___x_2665_);
v___x_2668_ = v___x_2654_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2665_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v_a_2651_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
else
{
lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2685_; 
lean_inc(v_buildTime_2660_);
lean_inc_ref(v_trace_2659_);
lean_inc_ref(v_log_2656_);
lean_dec(v_a_2652_);
lean_dec_ref(v_file_2645_);
v_isSharedCheck_2685_ = !lean_is_exclusive(v_a_2651_);
if (v_isSharedCheck_2685_ == 0)
{
lean_object* v_unused_2686_; lean_object* v_unused_2687_; lean_object* v_unused_2688_; 
v_unused_2686_ = lean_ctor_get(v_a_2651_, 2);
lean_dec(v_unused_2686_);
v_unused_2687_ = lean_ctor_get(v_a_2651_, 1);
lean_dec(v_unused_2687_);
v_unused_2688_ = lean_ctor_get(v_a_2651_, 0);
lean_dec(v_unused_2688_);
v___x_2671_ = v_a_2651_;
v_isShared_2672_ = v_isSharedCheck_2685_;
goto v_resetjp_2670_;
}
else
{
lean_dec(v_a_2651_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2685_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v_a_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2680_; 
v_a_2673_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2673_);
lean_dec_ref(v___x_2661_);
v___x_2674_ = lean_io_error_to_string(v_a_2673_);
v___x_2675_ = 3;
v___x_2676_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2676_, 0, v___x_2674_);
lean_ctor_set_uint8(v___x_2676_, sizeof(void*)*1, v___x_2675_);
v___x_2677_ = lean_array_get_size(v_log_2656_);
v___x_2678_ = lean_array_push(v_log_2656_, v___x_2676_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 0, v___x_2678_);
v___x_2680_ = v___x_2671_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2678_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_trace_2659_);
lean_ctor_set(v_reuseFailAlloc_2684_, 2, v_buildTime_2660_);
lean_ctor_set_uint8(v_reuseFailAlloc_2684_, sizeof(void*)*3, v_action_2657_);
lean_ctor_set_uint8(v_reuseFailAlloc_2684_, sizeof(void*)*3 + 1, v_wantsRebuild_2658_);
v___x_2680_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
lean_object* v___x_2682_; 
if (v_isShared_2655_ == 0)
{
lean_ctor_set_tag(v___x_2654_, 1);
lean_ctor_set(v___x_2654_, 1, v___x_2680_);
lean_ctor_set(v___x_2654_, 0, v___x_2677_);
v___x_2682_ = v___x_2654_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2677_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v___x_2680_);
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
}
else
{
lean_object* v_a_2690_; lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_dec_ref(v_file_2645_);
v_a_2690_ = lean_ctor_get(v___x_2650_, 0);
v_a_2691_ = lean_ctor_get(v___x_2650_, 1);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2650_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_inc(v_a_2690_);
lean_dec(v___x_2650_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2690_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg___boxed(lean_object* v_file_2699_, lean_object* v_text_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_){
_start:
{
uint8_t v_text_boxed_2704_; lean_object* v_res_2705_; 
v_text_boxed_2704_ = lean_unbox(v_text_2700_);
v_res_2705_ = l_Lake_fetchFileTrace___redArg(v_file_2699_, v_text_boxed_2704_, v_a_2701_, v_a_2702_);
lean_dec_ref(v_a_2701_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object* v_file_2706_, uint8_t v_text_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = l_Lake_fetchFileTrace___redArg(v_file_2706_, v_text_2707_, v_a_2712_, v_a_2713_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object* v_file_2716_, lean_object* v_text_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_){
_start:
{
uint8_t v_text_boxed_2725_; lean_object* v_res_2726_; 
v_text_boxed_2725_ = lean_unbox(v_text_2717_);
v_res_2726_ = l_Lake_fetchFileTrace(v_file_2716_, v_text_boxed_2725_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_);
lean_dec_ref(v_a_2722_);
lean_dec(v_a_2721_);
lean_dec(v_a_2720_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(lean_object* v_val_2727_, lean_object* v_a_x3f_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v___x_2731_; lean_object* v_log_2732_; uint8_t v_action_2733_; uint8_t v_wantsRebuild_2734_; lean_object* v_trace_2735_; lean_object* v_buildTime_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2747_; 
v___x_2731_ = lean_io_mono_ms_now();
v_log_2732_ = lean_ctor_get(v___y_2729_, 0);
v_action_2733_ = lean_ctor_get_uint8(v___y_2729_, sizeof(void*)*3);
v_wantsRebuild_2734_ = lean_ctor_get_uint8(v___y_2729_, sizeof(void*)*3 + 1);
v_trace_2735_ = lean_ctor_get(v___y_2729_, 1);
v_buildTime_2736_ = lean_ctor_get(v___y_2729_, 2);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___y_2729_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2738_ = v___y_2729_;
v_isShared_2739_ = v_isSharedCheck_2747_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_buildTime_2736_);
lean_inc(v_trace_2735_);
lean_inc(v_log_2732_);
lean_dec(v___y_2729_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2747_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2744_; 
v___x_2740_ = lean_nat_sub(v___x_2731_, v_val_2727_);
lean_dec(v___x_2731_);
v___x_2741_ = lean_box(0);
v___x_2742_ = lean_nat_add(v_buildTime_2736_, v___x_2740_);
lean_dec(v___x_2740_);
lean_dec(v_buildTime_2736_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 2, v___x_2742_);
v___x_2744_ = v___x_2738_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_log_2732_);
lean_ctor_set(v_reuseFailAlloc_2746_, 1, v_trace_2735_);
lean_ctor_set(v_reuseFailAlloc_2746_, 2, v___x_2742_);
lean_ctor_set_uint8(v_reuseFailAlloc_2746_, sizeof(void*)*3, v_action_2733_);
lean_ctor_set_uint8(v_reuseFailAlloc_2746_, sizeof(void*)*3 + 1, v_wantsRebuild_2734_);
v___x_2744_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
lean_object* v___x_2745_; 
v___x_2745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2741_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
return v___x_2745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0___boxed(lean_object* v_val_2748_, lean_object* v_a_x3f_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v_val_2748_, v_a_x3f_2749_, v___y_2750_);
lean_dec(v_a_x3f_2749_);
lean_dec(v_val_2748_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(lean_object* v_build_2753_, lean_object* v_file_2754_, lean_object* v_a_2755_, lean_object* v_depTrace_2756_, lean_object* v_traceFile_2757_, uint8_t v_action_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_){
_start:
{
lean_object* v_a_2766_; lean_object* v_a_2767_; lean_object* v_log_2770_; uint8_t v_action_2771_; uint8_t v_wantsRebuild_2772_; lean_object* v_trace_2773_; lean_object* v_buildTime_2774_; lean_object* v_toBuildConfig_2780_; lean_object* v_log_2781_; uint8_t v_action_2782_; uint8_t v_wantsRebuild_2783_; lean_object* v_trace_2784_; lean_object* v_buildTime_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2908_; 
v_toBuildConfig_2780_ = lean_ctor_get(v_a_2762_, 0);
v_log_2781_ = lean_ctor_get(v_a_2763_, 0);
v_action_2782_ = lean_ctor_get_uint8(v_a_2763_, sizeof(void*)*3);
v_wantsRebuild_2783_ = lean_ctor_get_uint8(v_a_2763_, sizeof(void*)*3 + 1);
v_trace_2784_ = lean_ctor_get(v_a_2763_, 1);
v_buildTime_2785_ = lean_ctor_get(v_a_2763_, 2);
v_isSharedCheck_2908_ = !lean_is_exclusive(v_a_2763_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2787_ = v_a_2763_;
v_isShared_2788_ = v_isSharedCheck_2908_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_buildTime_2785_);
lean_inc(v_trace_2784_);
lean_inc(v_log_2781_);
lean_dec(v_a_2763_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2908_;
goto v_resetjp_2786_;
}
v___jp_2765_:
{
lean_object* v___x_2768_; 
v___x_2768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2768_, 0, v_a_2766_);
lean_ctor_set(v___x_2768_, 1, v_a_2767_);
return v___x_2768_;
}
v___jp_2769_:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2775_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_2776_ = lean_array_get_size(v_log_2770_);
v___x_2777_ = lean_array_push(v_log_2770_, v___x_2775_);
v___x_2778_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2778_, 0, v___x_2777_);
lean_ctor_set(v___x_2778_, 1, v_trace_2773_);
lean_ctor_set(v___x_2778_, 2, v_buildTime_2774_);
lean_ctor_set_uint8(v___x_2778_, sizeof(void*)*3, v_action_2771_);
lean_ctor_set_uint8(v___x_2778_, sizeof(void*)*3 + 1, v_wantsRebuild_2772_);
v___x_2779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2776_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
return v___x_2779_;
}
v_resetjp_2786_:
{
uint8_t v_noBuild_2789_; uint8_t v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v_noBuild_2789_ = lean_ctor_get_uint8(v_toBuildConfig_2780_, sizeof(void*)*2 + 2);
v___x_2790_ = l_Lake_JobAction_merge(v_action_2782_, v_action_2758_);
v___x_2791_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_2757_);
v___x_2792_ = l_System_FilePath_addExtension(v_traceFile_2757_, v___x_2791_);
if (v_noBuild_2789_ == 0)
{
lean_object* v___x_2793_; lean_object* v___x_2795_; 
v___x_2793_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_2781_);
if (v_isShared_2788_ == 0)
{
v___x_2795_ = v___x_2787_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_log_2781_);
lean_ctor_set(v_reuseFailAlloc_2892_, 1, v_trace_2784_);
lean_ctor_set(v_reuseFailAlloc_2892_, 2, v_buildTime_2785_);
lean_ctor_set_uint8(v_reuseFailAlloc_2892_, sizeof(void*)*3 + 1, v_wantsRebuild_2783_);
v___x_2795_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
lean_object* v___x_2796_; lean_object* v_a_2798_; lean_object* v_a_2799_; 
lean_ctor_set_uint8(v___x_2795_, sizeof(void*)*3, v___x_2790_);
v___x_2796_ = lean_apply_7(v_build_2753_, v_a_2755_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v___x_2795_, lean_box(0));
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2803_; lean_object* v_log_2804_; uint8_t v_action_2805_; uint8_t v_wantsRebuild_2806_; lean_object* v_trace_2807_; lean_object* v_buildTime_2808_; lean_object* v___x_2809_; 
v_a_2803_ = lean_ctor_get(v___x_2796_, 1);
lean_inc(v_a_2803_);
lean_dec_ref(v___x_2796_);
v_log_2804_ = lean_ctor_get(v_a_2803_, 0);
v_action_2805_ = lean_ctor_get_uint8(v_a_2803_, sizeof(void*)*3);
v_wantsRebuild_2806_ = lean_ctor_get_uint8(v_a_2803_, sizeof(void*)*3 + 1);
v_trace_2807_ = lean_ctor_get(v_a_2803_, 1);
v_buildTime_2808_ = lean_ctor_get(v_a_2803_, 2);
v___x_2809_ = l_Lake_clearFileHash(v_file_2754_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v_a_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_a_2810_);
lean_dec_ref(v___x_2809_);
v___x_2811_ = lean_array_get_size(v_log_2781_);
lean_dec_ref(v_log_2781_);
v___x_2812_ = lean_array_get_size(v_log_2804_);
v___x_2813_ = l_Array_extract___redArg(v_log_2804_, v___x_2811_, v___x_2812_);
v___x_2814_ = lean_box(0);
v___x_2815_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_2756_, v___x_2814_, v___x_2813_);
v___x_2816_ = l_Lake_BuildMetadata_writeFile(v_traceFile_2757_, v___x_2815_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2857_; 
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2857_ == 0)
{
lean_object* v_unused_2858_; 
v_unused_2858_ = lean_ctor_get(v___x_2816_, 0);
lean_dec(v_unused_2858_);
v___x_2818_ = v___x_2816_;
v_isShared_2819_ = v_isSharedCheck_2857_;
goto v_resetjp_2817_;
}
else
{
lean_dec(v___x_2816_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2857_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_Lake_removeFileIfExists(v___x_2792_);
lean_dec_ref(v___x_2792_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2840_; 
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2840_ == 0)
{
lean_object* v_unused_2841_; 
v_unused_2841_ = lean_ctor_get(v___x_2820_, 0);
lean_dec(v_unused_2841_);
v___x_2822_ = v___x_2820_;
v_isShared_2823_ = v_isSharedCheck_2840_;
goto v_resetjp_2821_;
}
else
{
lean_dec(v___x_2820_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2840_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
lean_inc(v_a_2810_);
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 0, v_a_2810_);
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2810_);
v___x_2825_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
lean_object* v___x_2827_; 
if (v_isShared_2819_ == 0)
{
lean_ctor_set_tag(v___x_2818_, 1);
lean_ctor_set(v___x_2818_, 0, v___x_2825_);
v___x_2827_ = v___x_2818_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v___x_2825_);
v___x_2827_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
lean_object* v___x_2828_; lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
v___x_2828_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v___x_2793_, v___x_2827_, v_a_2803_);
lean_dec_ref(v___x_2827_);
lean_dec(v___x_2793_);
v_a_2829_ = lean_ctor_get(v___x_2828_, 1);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2836_ == 0)
{
lean_object* v_unused_2837_; 
v_unused_2837_ = lean_ctor_get(v___x_2828_, 0);
lean_dec(v_unused_2837_);
v___x_2831_ = v___x_2828_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2828_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 0, v_a_2810_);
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2810_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_a_2829_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
}
}
else
{
lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2853_; 
lean_inc(v_buildTime_2808_);
lean_inc_ref(v_trace_2807_);
lean_inc_ref(v_log_2804_);
lean_del_object(v___x_2818_);
lean_dec(v_a_2810_);
v_isSharedCheck_2853_ = !lean_is_exclusive(v_a_2803_);
if (v_isSharedCheck_2853_ == 0)
{
lean_object* v_unused_2854_; lean_object* v_unused_2855_; lean_object* v_unused_2856_; 
v_unused_2854_ = lean_ctor_get(v_a_2803_, 2);
lean_dec(v_unused_2854_);
v_unused_2855_ = lean_ctor_get(v_a_2803_, 1);
lean_dec(v_unused_2855_);
v_unused_2856_ = lean_ctor_get(v_a_2803_, 0);
lean_dec(v_unused_2856_);
v___x_2843_ = v_a_2803_;
v_isShared_2844_ = v_isSharedCheck_2853_;
goto v_resetjp_2842_;
}
else
{
lean_dec(v_a_2803_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2853_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v_a_2845_; lean_object* v___x_2846_; uint8_t v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2851_; 
v_a_2845_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2845_);
lean_dec_ref(v___x_2820_);
v___x_2846_ = lean_io_error_to_string(v_a_2845_);
v___x_2847_ = 3;
v___x_2848_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2848_, 0, v___x_2846_);
lean_ctor_set_uint8(v___x_2848_, sizeof(void*)*1, v___x_2847_);
v___x_2849_ = lean_array_push(v_log_2804_, v___x_2848_);
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v___x_2849_);
v___x_2851_ = v___x_2843_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___x_2849_);
lean_ctor_set(v_reuseFailAlloc_2852_, 1, v_trace_2807_);
lean_ctor_set(v_reuseFailAlloc_2852_, 2, v_buildTime_2808_);
lean_ctor_set_uint8(v_reuseFailAlloc_2852_, sizeof(void*)*3, v_action_2805_);
lean_ctor_set_uint8(v_reuseFailAlloc_2852_, sizeof(void*)*3 + 1, v_wantsRebuild_2806_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
v_a_2798_ = v___x_2812_;
v_a_2799_ = v___x_2851_;
goto v___jp_2797_;
}
}
}
}
}
else
{
lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2870_; 
lean_inc(v_buildTime_2808_);
lean_inc_ref(v_trace_2807_);
lean_inc_ref(v_log_2804_);
lean_dec(v_a_2810_);
lean_dec_ref(v___x_2792_);
v_isSharedCheck_2870_ = !lean_is_exclusive(v_a_2803_);
if (v_isSharedCheck_2870_ == 0)
{
lean_object* v_unused_2871_; lean_object* v_unused_2872_; lean_object* v_unused_2873_; 
v_unused_2871_ = lean_ctor_get(v_a_2803_, 2);
lean_dec(v_unused_2871_);
v_unused_2872_ = lean_ctor_get(v_a_2803_, 1);
lean_dec(v_unused_2872_);
v_unused_2873_ = lean_ctor_get(v_a_2803_, 0);
lean_dec(v_unused_2873_);
v___x_2860_ = v_a_2803_;
v_isShared_2861_ = v_isSharedCheck_2870_;
goto v_resetjp_2859_;
}
else
{
lean_dec(v_a_2803_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2870_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v_a_2862_; lean_object* v___x_2863_; uint8_t v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2868_; 
v_a_2862_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2862_);
lean_dec_ref(v___x_2816_);
v___x_2863_ = lean_io_error_to_string(v_a_2862_);
v___x_2864_ = 3;
v___x_2865_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2865_, 0, v___x_2863_);
lean_ctor_set_uint8(v___x_2865_, sizeof(void*)*1, v___x_2864_);
v___x_2866_ = lean_array_push(v_log_2804_, v___x_2865_);
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 0, v___x_2866_);
v___x_2868_ = v___x_2860_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___x_2866_);
lean_ctor_set(v_reuseFailAlloc_2869_, 1, v_trace_2807_);
lean_ctor_set(v_reuseFailAlloc_2869_, 2, v_buildTime_2808_);
lean_ctor_set_uint8(v_reuseFailAlloc_2869_, sizeof(void*)*3, v_action_2805_);
lean_ctor_set_uint8(v_reuseFailAlloc_2869_, sizeof(void*)*3 + 1, v_wantsRebuild_2806_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
v_a_2798_ = v___x_2812_;
v_a_2799_ = v___x_2868_;
goto v___jp_2797_;
}
}
}
}
else
{
lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2886_; 
lean_inc(v_buildTime_2808_);
lean_inc_ref(v_trace_2807_);
lean_inc_ref(v_log_2804_);
lean_dec_ref(v___x_2792_);
lean_dec_ref(v_log_2781_);
lean_dec_ref(v_traceFile_2757_);
v_isSharedCheck_2886_ = !lean_is_exclusive(v_a_2803_);
if (v_isSharedCheck_2886_ == 0)
{
lean_object* v_unused_2887_; lean_object* v_unused_2888_; lean_object* v_unused_2889_; 
v_unused_2887_ = lean_ctor_get(v_a_2803_, 2);
lean_dec(v_unused_2887_);
v_unused_2888_ = lean_ctor_get(v_a_2803_, 1);
lean_dec(v_unused_2888_);
v_unused_2889_ = lean_ctor_get(v_a_2803_, 0);
lean_dec(v_unused_2889_);
v___x_2875_ = v_a_2803_;
v_isShared_2876_ = v_isSharedCheck_2886_;
goto v_resetjp_2874_;
}
else
{
lean_dec(v_a_2803_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2886_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v_a_2877_; lean_object* v___x_2878_; uint8_t v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2884_; 
v_a_2877_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_a_2877_);
lean_dec_ref(v___x_2809_);
v___x_2878_ = lean_io_error_to_string(v_a_2877_);
v___x_2879_ = 3;
v___x_2880_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2880_, 0, v___x_2878_);
lean_ctor_set_uint8(v___x_2880_, sizeof(void*)*1, v___x_2879_);
v___x_2881_ = lean_array_get_size(v_log_2804_);
v___x_2882_ = lean_array_push(v_log_2804_, v___x_2880_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 0, v___x_2882_);
v___x_2884_ = v___x_2875_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2882_);
lean_ctor_set(v_reuseFailAlloc_2885_, 1, v_trace_2807_);
lean_ctor_set(v_reuseFailAlloc_2885_, 2, v_buildTime_2808_);
lean_ctor_set_uint8(v_reuseFailAlloc_2885_, sizeof(void*)*3, v_action_2805_);
lean_ctor_set_uint8(v_reuseFailAlloc_2885_, sizeof(void*)*3 + 1, v_wantsRebuild_2806_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
v_a_2798_ = v___x_2881_;
v_a_2799_ = v___x_2884_;
goto v___jp_2797_;
}
}
}
}
else
{
lean_object* v_a_2890_; lean_object* v_a_2891_; 
lean_dec_ref(v___x_2792_);
lean_dec_ref(v_log_2781_);
lean_dec_ref(v_traceFile_2757_);
lean_dec_ref(v_file_2754_);
v_a_2890_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2890_);
v_a_2891_ = lean_ctor_get(v___x_2796_, 1);
lean_inc(v_a_2891_);
lean_dec_ref(v___x_2796_);
v_a_2798_ = v_a_2890_;
v_a_2799_ = v_a_2891_;
goto v___jp_2797_;
}
v___jp_2797_:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v_a_2802_; 
v___x_2800_ = lean_box(0);
v___x_2801_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v___x_2793_, v___x_2800_, v_a_2799_);
lean_dec(v___x_2793_);
v_a_2802_ = lean_ctor_get(v___x_2801_, 1);
lean_inc(v_a_2802_);
lean_dec_ref(v___x_2801_);
v_a_2766_ = v_a_2798_;
v_a_2767_ = v_a_2802_;
goto v___jp_2765_;
}
}
}
else
{
uint8_t v___x_2893_; 
lean_dec_ref(v_a_2762_);
lean_dec(v_a_2761_);
lean_dec(v_a_2760_);
lean_dec(v_a_2759_);
lean_dec_ref(v_a_2755_);
lean_dec_ref(v_file_2754_);
lean_dec_ref(v_build_2753_);
v___x_2893_ = l_System_FilePath_pathExists(v_traceFile_2757_);
lean_dec_ref(v_traceFile_2757_);
if (v___x_2893_ == 0)
{
lean_dec_ref(v___x_2792_);
lean_del_object(v___x_2787_);
v_log_2770_ = v_log_2781_;
v_action_2771_ = v___x_2790_;
v_wantsRebuild_2772_ = v_noBuild_2789_;
v_trace_2773_ = v_trace_2784_;
v_buildTime_2774_ = v_buildTime_2785_;
goto v___jp_2769_;
}
else
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2894_ = lean_box(0);
v___x_2895_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_2896_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_2756_, v___x_2894_, v___x_2895_);
v___x_2897_ = l_Lake_BuildMetadata_writeFile(v___x_2792_, v___x_2896_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_dec_ref(v___x_2897_);
lean_del_object(v___x_2787_);
v_log_2770_ = v_log_2781_;
v_action_2771_ = v___x_2790_;
v_wantsRebuild_2772_ = v_noBuild_2789_;
v_trace_2773_ = v_trace_2784_;
v_buildTime_2774_ = v_buildTime_2785_;
goto v___jp_2769_;
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2899_; uint8_t v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2905_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_a_2898_);
lean_dec_ref(v___x_2897_);
v___x_2899_ = lean_io_error_to_string(v_a_2898_);
v___x_2900_ = 3;
v___x_2901_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2901_, 0, v___x_2899_);
lean_ctor_set_uint8(v___x_2901_, sizeof(void*)*1, v___x_2900_);
v___x_2902_ = lean_array_get_size(v_log_2781_);
v___x_2903_ = lean_array_push(v_log_2781_, v___x_2901_);
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v___x_2903_);
v___x_2905_ = v___x_2787_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v___x_2903_);
lean_ctor_set(v_reuseFailAlloc_2907_, 1, v_trace_2784_);
lean_ctor_set(v_reuseFailAlloc_2907_, 2, v_buildTime_2785_);
v___x_2905_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
lean_object* v___x_2906_; 
lean_ctor_set_uint8(v___x_2905_, sizeof(void*)*3, v___x_2790_);
lean_ctor_set_uint8(v___x_2905_, sizeof(void*)*3 + 1, v_noBuild_2789_);
v___x_2906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2902_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
return v___x_2906_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___boxed(lean_object* v_build_2909_, lean_object* v_file_2910_, lean_object* v_a_2911_, lean_object* v_depTrace_2912_, lean_object* v_traceFile_2913_, lean_object* v_action_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_){
_start:
{
uint8_t v_action_boxed_2921_; lean_object* v_res_2922_; 
v_action_boxed_2921_ = lean_unbox(v_action_2914_);
v_res_2922_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(v_build_2909_, v_file_2910_, v_a_2911_, v_depTrace_2912_, v_traceFile_2913_, v_action_boxed_2921_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_);
lean_dec_ref(v_depTrace_2912_);
return v_res_2922_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(lean_object* v_info_2923_, lean_object* v_self_2924_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = lean_io_metadata(v_info_2923_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v_modified_2928_; uint8_t v___x_2929_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2927_);
lean_dec_ref(v___x_2926_);
v_modified_2928_ = lean_ctor_get(v_a_2927_, 1);
lean_inc_ref(v_modified_2928_);
lean_dec(v_a_2927_);
v___x_2929_ = l_IO_FS_instOrdSystemTime_ord(v_self_2924_, v_modified_2928_);
lean_dec_ref(v_modified_2928_);
if (v___x_2929_ == 0)
{
uint8_t v___x_2930_; 
v___x_2930_ = 1;
return v___x_2930_;
}
else
{
uint8_t v___x_2931_; 
v___x_2931_ = 0;
return v___x_2931_;
}
}
else
{
uint8_t v___x_2932_; 
lean_dec_ref(v___x_2926_);
v___x_2932_ = 0;
return v___x_2932_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___boxed(lean_object* v_info_2933_, lean_object* v_self_2934_, lean_object* v_a_2935_){
_start:
{
uint8_t v_res_2936_; lean_object* v_r_2937_; 
v_res_2936_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_2933_, v_self_2934_);
lean_dec_ref(v_self_2934_);
lean_dec_ref(v_info_2933_);
v_r_2937_ = lean_box(v_res_2936_);
return v_r_2937_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(lean_object* v_x_2938_, lean_object* v_x_2939_){
_start:
{
if (lean_obj_tag(v_x_2938_) == 0)
{
if (lean_obj_tag(v_x_2939_) == 0)
{
uint8_t v___x_2940_; 
v___x_2940_ = 1;
return v___x_2940_;
}
else
{
uint8_t v___x_2941_; 
v___x_2941_ = 0;
return v___x_2941_;
}
}
else
{
if (lean_obj_tag(v_x_2939_) == 0)
{
uint8_t v___x_2942_; 
v___x_2942_ = 0;
return v___x_2942_;
}
else
{
lean_object* v_val_2943_; lean_object* v_val_2944_; uint64_t v___x_2945_; uint64_t v___x_2946_; uint8_t v___x_2947_; 
v_val_2943_ = lean_ctor_get(v_x_2938_, 0);
v_val_2944_ = lean_ctor_get(v_x_2939_, 0);
v___x_2945_ = lean_unbox_uint64(v_val_2943_);
v___x_2946_ = lean_unbox_uint64(v_val_2944_);
v___x_2947_ = lean_uint64_dec_eq(v___x_2945_, v___x_2946_);
return v___x_2947_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2948_, lean_object* v_x_2949_){
_start:
{
uint8_t v_res_2950_; lean_object* v_r_2951_; 
v_res_2950_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(v_x_2948_, v_x_2949_);
lean_dec(v_x_2949_);
lean_dec(v_x_2948_);
v_r_2951_ = lean_box(v_res_2950_);
return v_r_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(lean_object* v_info_2952_, lean_object* v_depTrace_2953_, lean_object* v_depHash_2954_, lean_object* v_oldTrace_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_){
_start:
{
uint64_t v_hash_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; uint8_t v___x_2962_; 
v_hash_2959_ = lean_ctor_get_uint64(v_depTrace_2953_, sizeof(void*)*3);
v___x_2960_ = lean_box_uint64(v_hash_2959_);
v___x_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2960_);
v___x_2962_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(v___x_2961_, v_depHash_2954_);
lean_dec_ref(v___x_2961_);
if (v___x_2962_ == 0)
{
lean_object* v_toBuildConfig_2963_; uint8_t v_oldMode_2964_; 
v_toBuildConfig_2963_ = lean_ctor_get(v_a_2956_, 0);
v_oldMode_2964_ = lean_ctor_get_uint8(v_toBuildConfig_2963_, sizeof(void*)*2);
if (v_oldMode_2964_ == 0)
{
uint8_t v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2965_ = 0;
v___x_2966_ = lean_box(v___x_2965_);
v___x_2967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2966_);
lean_ctor_set(v___x_2967_, 1, v_a_2957_);
return v___x_2967_;
}
else
{
uint8_t v___x_2968_; 
v___x_2968_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_2952_, v_oldTrace_2955_);
if (v___x_2968_ == 0)
{
uint8_t v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2969_ = 0;
v___x_2970_ = lean_box(v___x_2969_);
v___x_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2970_);
lean_ctor_set(v___x_2971_, 1, v_a_2957_);
return v___x_2971_;
}
else
{
uint8_t v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2972_ = 1;
v___x_2973_ = lean_box(v___x_2972_);
v___x_2974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2973_);
lean_ctor_set(v___x_2974_, 1, v_a_2957_);
return v___x_2974_;
}
}
}
else
{
uint8_t v___x_2975_; 
v___x_2975_ = l_System_FilePath_pathExists(v_info_2952_);
if (v___x_2975_ == 0)
{
uint8_t v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2976_ = 0;
v___x_2977_ = lean_box(v___x_2976_);
v___x_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
lean_ctor_set(v___x_2978_, 1, v_a_2957_);
return v___x_2978_;
}
else
{
uint8_t v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2979_ = 2;
v___x_2980_ = lean_box(v___x_2979_);
v___x_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
lean_ctor_set(v___x_2981_, 1, v_a_2957_);
return v___x_2981_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg___boxed(lean_object* v_info_2982_, lean_object* v_depTrace_2983_, lean_object* v_depHash_2984_, lean_object* v_oldTrace_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_2982_, v_depTrace_2983_, v_depHash_2984_, v_oldTrace_2985_, v_a_2986_, v_a_2987_);
lean_dec_ref(v_a_2986_);
lean_dec_ref(v_oldTrace_2985_);
lean_dec(v_depHash_2984_);
lean_dec_ref(v_depTrace_2983_);
lean_dec_ref(v_info_2982_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(lean_object* v_a_2990_, lean_object* v_info_2991_, lean_object* v_depTrace_2992_, lean_object* v_savedTrace_2993_, lean_object* v_oldTrace_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_){
_start:
{
if (lean_obj_tag(v_savedTrace_2993_) == 2)
{
lean_object* v_data_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3051_; 
v_data_3001_ = lean_ctor_get(v_savedTrace_2993_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v_savedTrace_2993_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3003_ = v_savedTrace_2993_;
v_isShared_3004_ = v_isSharedCheck_3051_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_data_3001_);
lean_dec(v_savedTrace_2993_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3051_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
uint64_t v_depHash_3005_; lean_object* v_log_3006_; lean_object* v___x_3007_; lean_object* v___x_3009_; 
v_depHash_3005_ = lean_ctor_get_uint64(v_data_3001_, sizeof(void*)*3);
v_log_3006_ = lean_ctor_get(v_data_3001_, 2);
lean_inc_ref(v_log_3006_);
lean_dec_ref(v_data_3001_);
v___x_3007_ = lean_box_uint64(v_depHash_3005_);
if (v_isShared_3004_ == 0)
{
lean_ctor_set_tag(v___x_3003_, 1);
lean_ctor_set(v___x_3003_, 0, v___x_3007_);
v___x_3009_ = v___x_3003_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3007_);
v___x_3009_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
lean_object* v___x_3010_; lean_object* v_a_3011_; lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3049_; 
v___x_3010_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_2991_, v_depTrace_2992_, v___x_3009_, v_oldTrace_2994_, v_a_2998_, v_a_2999_);
lean_dec_ref(v___x_3009_);
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
v_a_3012_ = lean_ctor_get(v___x_3010_, 1);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3014_ = v___x_3010_;
v_isShared_3015_ = v_isSharedCheck_3049_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_a_3012_);
lean_inc(v_a_3011_);
lean_dec(v___x_3010_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3049_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___y_3017_; uint8_t v___x_3021_; uint8_t v___x_3022_; uint8_t v___x_3023_; 
v___x_3021_ = 0;
v___x_3022_ = lean_unbox(v_a_3011_);
v___x_3023_ = l_Lake_instDecidableEqOutputStatus(v___x_3022_, v___x_3021_);
if (v___x_3023_ == 0)
{
lean_object* v_log_3024_; uint8_t v_action_3025_; uint8_t v_wantsRebuild_3026_; lean_object* v_trace_3027_; lean_object* v_buildTime_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3048_; 
v_log_3024_ = lean_ctor_get(v_a_3012_, 0);
v_action_3025_ = lean_ctor_get_uint8(v_a_3012_, sizeof(void*)*3);
v_wantsRebuild_3026_ = lean_ctor_get_uint8(v_a_3012_, sizeof(void*)*3 + 1);
v_trace_3027_ = lean_ctor_get(v_a_3012_, 1);
v_buildTime_3028_ = lean_ctor_get(v_a_3012_, 2);
v_isSharedCheck_3048_ = !lean_is_exclusive(v_a_3012_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3030_ = v_a_3012_;
v_isShared_3031_ = v_isSharedCheck_3048_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_buildTime_3028_);
lean_inc(v_trace_3027_);
lean_inc(v_log_3024_);
lean_dec(v_a_3012_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3048_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
uint8_t v___x_3032_; uint8_t v___x_3033_; lean_object* v___x_3035_; 
v___x_3032_ = 1;
v___x_3033_ = l_Lake_JobAction_merge(v_action_3025_, v___x_3032_);
if (v_isShared_3031_ == 0)
{
v___x_3035_ = v___x_3030_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_log_3024_);
lean_ctor_set(v_reuseFailAlloc_3047_, 1, v_trace_3027_);
lean_ctor_set(v_reuseFailAlloc_3047_, 2, v_buildTime_3028_);
lean_ctor_set_uint8(v_reuseFailAlloc_3047_, sizeof(void*)*3 + 1, v_wantsRebuild_3026_);
v___x_3035_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
lean_object* v___x_3036_; 
lean_ctor_set_uint8(v___x_3035_, sizeof(void*)*3, v___x_3033_);
v___x_3036_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_3006_, v_a_2990_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v___x_3035_);
lean_dec_ref(v_log_3006_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v_a_3037_; 
v_a_3037_ = lean_ctor_get(v___x_3036_, 1);
lean_inc(v_a_3037_);
lean_dec_ref(v___x_3036_);
v___y_3017_ = v_a_3037_;
goto v___jp_3016_;
}
else
{
lean_object* v_a_3038_; lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3046_; 
lean_del_object(v___x_3014_);
lean_dec(v_a_3011_);
v_a_3038_ = lean_ctor_get(v___x_3036_, 0);
v_a_3039_ = lean_ctor_get(v___x_3036_, 1);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3041_ = v___x_3036_;
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_inc(v_a_3038_);
lean_dec(v___x_3036_);
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
}
}
else
{
lean_dec_ref(v_log_3006_);
v___y_3017_ = v_a_3012_;
goto v___jp_3016_;
}
v___jp_3016_:
{
lean_object* v___x_3019_; 
if (v_isShared_3015_ == 0)
{
lean_ctor_set(v___x_3014_, 1, v___y_3017_);
v___x_3019_ = v___x_3014_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3011_);
lean_ctor_set(v_reuseFailAlloc_3020_, 1, v___y_3017_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
}
}
else
{
lean_object* v_toBuildConfig_3052_; uint8_t v_oldMode_3053_; 
lean_dec(v_savedTrace_2993_);
v_toBuildConfig_3052_ = lean_ctor_get(v_a_2998_, 0);
v_oldMode_3053_ = lean_ctor_get_uint8(v_toBuildConfig_3052_, sizeof(void*)*2);
if (v_oldMode_3053_ == 0)
{
uint8_t v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3054_ = 0;
v___x_3055_ = lean_box(v___x_3054_);
v___x_3056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
lean_ctor_set(v___x_3056_, 1, v_a_2999_);
return v___x_3056_;
}
else
{
uint8_t v___x_3057_; 
v___x_3057_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_2991_, v_oldTrace_2994_);
if (v___x_3057_ == 0)
{
uint8_t v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3058_ = 0;
v___x_3059_ = lean_box(v___x_3058_);
v___x_3060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3059_);
lean_ctor_set(v___x_3060_, 1, v_a_2999_);
return v___x_3060_;
}
else
{
uint8_t v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3061_ = 1;
v___x_3062_ = lean_box(v___x_3061_);
v___x_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3062_);
lean_ctor_set(v___x_3063_, 1, v_a_2999_);
return v___x_3063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0___boxed(lean_object* v_a_3064_, lean_object* v_info_3065_, lean_object* v_depTrace_3066_, lean_object* v_savedTrace_3067_, lean_object* v_oldTrace_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_3064_, v_info_3065_, v_depTrace_3066_, v_savedTrace_3067_, v_oldTrace_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_);
lean_dec_ref(v_a_3072_);
lean_dec(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec(v_a_3069_);
lean_dec_ref(v_oldTrace_3068_);
lean_dec_ref(v_depTrace_3066_);
lean_dec_ref(v_info_3065_);
lean_dec_ref(v_a_3064_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27(lean_object* v_file_3077_, lean_object* v_build_3078_, uint8_t v_text_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_){
_start:
{
lean_object* v_a_3088_; lean_object* v_a_3089_; lean_object* v_a_3092_; lean_object* v_log_3125_; uint8_t v_action_3126_; uint8_t v_wantsRebuild_3127_; lean_object* v_trace_3128_; lean_object* v_buildTime_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3160_; 
v_log_3125_ = lean_ctor_get(v_a_3085_, 0);
v_action_3126_ = lean_ctor_get_uint8(v_a_3085_, sizeof(void*)*3);
v_wantsRebuild_3127_ = lean_ctor_get_uint8(v_a_3085_, sizeof(void*)*3 + 1);
v_trace_3128_ = lean_ctor_get(v_a_3085_, 1);
v_buildTime_3129_ = lean_ctor_get(v_a_3085_, 2);
v_isSharedCheck_3160_ = !lean_is_exclusive(v_a_3085_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3131_ = v_a_3085_;
v_isShared_3132_ = v_isSharedCheck_3160_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_buildTime_3129_);
lean_inc(v_trace_3128_);
lean_inc(v_log_3125_);
lean_dec(v_a_3085_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3160_;
goto v_resetjp_3130_;
}
v___jp_3087_:
{
lean_object* v___x_3090_; 
v___x_3090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3090_, 0, v_a_3088_);
lean_ctor_set(v___x_3090_, 1, v_a_3089_);
return v___x_3090_;
}
v___jp_3091_:
{
lean_object* v___x_3093_; 
v___x_3093_ = l_Lake_fetchFileTrace___redArg(v_file_3077_, v_text_3079_, v_a_3084_, v_a_3092_);
lean_dec_ref(v_a_3084_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3115_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 1);
v_a_3095_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3097_ = v___x_3093_;
v_isShared_3098_ = v_isSharedCheck_3115_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3094_);
lean_inc(v_a_3095_);
lean_dec(v___x_3093_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3115_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v_log_3099_; uint8_t v_action_3100_; uint8_t v_wantsRebuild_3101_; lean_object* v_buildTime_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3113_; 
v_log_3099_ = lean_ctor_get(v_a_3094_, 0);
v_action_3100_ = lean_ctor_get_uint8(v_a_3094_, sizeof(void*)*3);
v_wantsRebuild_3101_ = lean_ctor_get_uint8(v_a_3094_, sizeof(void*)*3 + 1);
v_buildTime_3102_ = lean_ctor_get(v_a_3094_, 2);
v_isSharedCheck_3113_ = !lean_is_exclusive(v_a_3094_);
if (v_isSharedCheck_3113_ == 0)
{
lean_object* v_unused_3114_; 
v_unused_3114_ = lean_ctor_get(v_a_3094_, 1);
lean_dec(v_unused_3114_);
v___x_3104_ = v_a_3094_;
v_isShared_3105_ = v_isSharedCheck_3113_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_buildTime_3102_);
lean_inc(v_log_3099_);
lean_dec(v_a_3094_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3113_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3106_; lean_object* v___x_3108_; 
v___x_3106_ = lean_box(0);
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 1, v_a_3095_);
v___x_3108_ = v___x_3104_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_log_3099_);
lean_ctor_set(v_reuseFailAlloc_3112_, 1, v_a_3095_);
lean_ctor_set(v_reuseFailAlloc_3112_, 2, v_buildTime_3102_);
lean_ctor_set_uint8(v_reuseFailAlloc_3112_, sizeof(void*)*3, v_action_3100_);
lean_ctor_set_uint8(v_reuseFailAlloc_3112_, sizeof(void*)*3 + 1, v_wantsRebuild_3101_);
v___x_3108_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
lean_object* v___x_3110_; 
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 1, v___x_3108_);
lean_ctor_set(v___x_3097_, 0, v___x_3106_);
v___x_3110_ = v___x_3097_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3106_);
lean_ctor_set(v_reuseFailAlloc_3111_, 1, v___x_3108_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
}
else
{
lean_object* v_a_3116_; lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
v_a_3116_ = lean_ctor_get(v___x_3093_, 0);
v_a_3117_ = lean_ctor_get(v___x_3093_, 1);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3093_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_inc(v_a_3116_);
lean_dec(v___x_3093_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3116_);
lean_ctor_set(v_reuseFailAlloc_3123_, 1, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
v_resetjp_3130_:
{
lean_object* v___x_3133_; lean_object* v_traceFile_3134_; lean_object* v___x_3135_; 
v___x_3133_ = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(v_file_3077_);
v_traceFile_3134_ = lean_string_append(v_file_3077_, v___x_3133_);
lean_inc_ref(v_traceFile_3134_);
v___x_3135_ = l_Lake_readTraceFile(v_traceFile_3134_, v_log_3125_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v_a_3137_; lean_object* v_mtime_3138_; lean_object* v___x_3140_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_a_3136_);
v_a_3137_ = lean_ctor_get(v___x_3135_, 1);
lean_inc(v_a_3137_);
lean_dec_ref(v___x_3135_);
v_mtime_3138_ = lean_ctor_get(v_trace_3128_, 2);
lean_inc_ref(v_trace_3128_);
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 0, v_a_3137_);
v___x_3140_ = v___x_3131_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3137_);
lean_ctor_set(v_reuseFailAlloc_3154_, 1, v_trace_3128_);
lean_ctor_set(v_reuseFailAlloc_3154_, 2, v_buildTime_3129_);
lean_ctor_set_uint8(v_reuseFailAlloc_3154_, sizeof(void*)*3, v_action_3126_);
lean_ctor_set_uint8(v_reuseFailAlloc_3154_, sizeof(void*)*3 + 1, v_wantsRebuild_3127_);
v___x_3140_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
lean_object* v___x_3141_; 
v___x_3141_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_3080_, v_file_3077_, v_trace_3128_, v_a_3136_, v_mtime_3138_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v___x_3140_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; lean_object* v_a_3143_; uint8_t v___x_3144_; uint8_t v___x_3145_; uint8_t v___x_3146_; 
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_a_3142_);
v_a_3143_ = lean_ctor_get(v___x_3141_, 1);
lean_inc(v_a_3143_);
lean_dec_ref(v___x_3141_);
v___x_3144_ = 0;
v___x_3145_ = lean_unbox(v_a_3142_);
lean_dec(v_a_3142_);
v___x_3146_ = l_Lake_instDecidableEqOutputStatus(v___x_3145_, v___x_3144_);
if (v___x_3146_ == 0)
{
lean_dec_ref(v_traceFile_3134_);
lean_dec_ref(v_trace_3128_);
lean_dec(v_a_3083_);
lean_dec(v_a_3082_);
lean_dec(v_a_3081_);
lean_dec_ref(v_a_3080_);
lean_dec_ref(v_build_3078_);
v_a_3092_ = v_a_3143_;
goto v___jp_3091_;
}
else
{
uint8_t v___x_3147_; lean_object* v___x_3148_; 
v___x_3147_ = 3;
lean_inc_ref(v_a_3084_);
lean_inc_ref(v_file_3077_);
v___x_3148_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(v_build_3078_, v_file_3077_, v_a_3080_, v_trace_3128_, v_traceFile_3134_, v___x_3147_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3143_);
lean_dec_ref(v_trace_3128_);
if (lean_obj_tag(v___x_3148_) == 0)
{
lean_object* v_a_3149_; 
v_a_3149_ = lean_ctor_get(v___x_3148_, 1);
lean_inc(v_a_3149_);
lean_dec_ref(v___x_3148_);
v_a_3092_ = v_a_3149_;
goto v___jp_3091_;
}
else
{
lean_object* v_a_3150_; lean_object* v_a_3151_; 
lean_dec_ref(v_a_3084_);
lean_dec_ref(v_file_3077_);
v_a_3150_ = lean_ctor_get(v___x_3148_, 0);
lean_inc(v_a_3150_);
v_a_3151_ = lean_ctor_get(v___x_3148_, 1);
lean_inc(v_a_3151_);
lean_dec_ref(v___x_3148_);
v_a_3088_ = v_a_3150_;
v_a_3089_ = v_a_3151_;
goto v___jp_3087_;
}
}
}
else
{
lean_object* v_a_3152_; lean_object* v_a_3153_; 
lean_dec_ref(v_traceFile_3134_);
lean_dec_ref(v_trace_3128_);
lean_dec_ref(v_a_3084_);
lean_dec(v_a_3083_);
lean_dec(v_a_3082_);
lean_dec(v_a_3081_);
lean_dec_ref(v_a_3080_);
lean_dec_ref(v_build_3078_);
lean_dec_ref(v_file_3077_);
v_a_3152_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_a_3152_);
v_a_3153_ = lean_ctor_get(v___x_3141_, 1);
lean_inc(v_a_3153_);
lean_dec_ref(v___x_3141_);
v_a_3088_ = v_a_3152_;
v_a_3089_ = v_a_3153_;
goto v___jp_3087_;
}
}
}
else
{
lean_object* v_a_3155_; lean_object* v_a_3156_; lean_object* v___x_3158_; 
lean_dec_ref(v_traceFile_3134_);
lean_dec_ref(v_a_3084_);
lean_dec(v_a_3083_);
lean_dec(v_a_3082_);
lean_dec(v_a_3081_);
lean_dec_ref(v_a_3080_);
lean_dec_ref(v_build_3078_);
lean_dec_ref(v_file_3077_);
v_a_3155_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_a_3155_);
v_a_3156_ = lean_ctor_get(v___x_3135_, 1);
lean_inc(v_a_3156_);
lean_dec_ref(v___x_3135_);
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 0, v_a_3156_);
v___x_3158_ = v___x_3131_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3156_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v_trace_3128_);
lean_ctor_set(v_reuseFailAlloc_3159_, 2, v_buildTime_3129_);
lean_ctor_set_uint8(v_reuseFailAlloc_3159_, sizeof(void*)*3, v_action_3126_);
lean_ctor_set_uint8(v_reuseFailAlloc_3159_, sizeof(void*)*3 + 1, v_wantsRebuild_3127_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
v_a_3088_ = v_a_3155_;
v_a_3089_ = v___x_3158_;
goto v___jp_3087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27___boxed(lean_object* v_file_3161_, lean_object* v_build_3162_, lean_object* v_text_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_){
_start:
{
uint8_t v_text_boxed_3171_; lean_object* v_res_3172_; 
v_text_boxed_3171_ = lean_unbox(v_text_3163_);
v_res_3172_ = l_Lake_buildFileUnlessUpToDate_x27(v_file_3161_, v_build_3162_, v_text_boxed_3171_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(lean_object* v_a_3173_, lean_object* v_info_3174_, lean_object* v_depTrace_3175_, lean_object* v_depHash_3176_, lean_object* v_oldTrace_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_){
_start:
{
lean_object* v___x_3184_; 
v___x_3184_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_3174_, v_depTrace_3175_, v_depHash_3176_, v_oldTrace_3177_, v_a_3181_, v_a_3182_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___boxed(lean_object* v_a_3185_, lean_object* v_info_3186_, lean_object* v_depTrace_3187_, lean_object* v_depHash_3188_, lean_object* v_oldTrace_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(v_a_3185_, v_info_3186_, v_depTrace_3187_, v_depHash_3188_, v_oldTrace_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_);
lean_dec_ref(v_a_3193_);
lean_dec(v_a_3192_);
lean_dec(v_a_3191_);
lean_dec(v_a_3190_);
lean_dec_ref(v_oldTrace_3189_);
lean_dec(v_depHash_3188_);
lean_dec_ref(v_depTrace_3187_);
lean_dec_ref(v_info_3186_);
lean_dec_ref(v_a_3185_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0(lean_object* v_file_3197_, uint64_t v___x_3198_, lean_object* v___x_3199_, uint8_t v_useLocalFile_3200_, lean_object* v___x_3201_, lean_object* v_____r_3202_){
_start:
{
lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3211_; lean_object* v___x_3212_; 
lean_inc_ref(v_file_3197_);
v___x_3212_ = l_Lake_writeFileHash(v_file_3197_, v___x_3198_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v___x_3213_; 
lean_dec_ref(v___x_3212_);
v___x_3213_ = lean_io_metadata(v___x_3201_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_a_3214_; lean_object* v_modified_3215_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_a_3214_);
lean_dec_ref(v___x_3213_);
v_modified_3215_ = lean_ctor_get(v_a_3214_, 1);
lean_inc_ref(v_modified_3215_);
lean_dec(v_a_3214_);
v___y_3211_ = v_modified_3215_;
goto v___jp_3210_;
}
else
{
lean_object* v___x_3216_; 
lean_dec_ref(v___x_3213_);
v___x_3216_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___y_3211_ = v___x_3216_;
goto v___jp_3210_;
}
}
else
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
lean_dec_ref(v___x_3201_);
lean_dec_ref(v___x_3199_);
lean_dec_ref(v_file_3197_);
v_a_3217_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_3212_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3212_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3222_; 
if (v_isShared_3220_ == 0)
{
v___x_3222_ = v___x_3219_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_a_3217_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
v___jp_3204_:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3207_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3199_);
lean_ctor_set(v___x_3207_, 1, v___y_3206_);
lean_ctor_set(v___x_3207_, 2, v_file_3197_);
lean_ctor_set(v___x_3207_, 3, v___y_3205_);
v___x_3208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3207_);
v___x_3209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3208_);
return v___x_3209_;
}
v___jp_3210_:
{
if (v_useLocalFile_3200_ == 0)
{
v___y_3205_ = v___y_3211_;
v___y_3206_ = v___x_3201_;
goto v___jp_3204_;
}
else
{
lean_dec_ref(v___x_3201_);
lean_inc_ref(v_file_3197_);
v___y_3205_ = v___y_3211_;
v___y_3206_ = v_file_3197_;
goto v___jp_3204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0___boxed(lean_object* v_file_3225_, lean_object* v___x_3226_, lean_object* v___x_3227_, lean_object* v_useLocalFile_3228_, lean_object* v___x_3229_, lean_object* v_____r_3230_, lean_object* v___y_3231_){
_start:
{
uint64_t v___x_3808__boxed_3232_; uint8_t v_useLocalFile_boxed_3233_; lean_object* v_res_3234_; 
v___x_3808__boxed_3232_ = lean_unbox_uint64(v___x_3226_);
lean_dec_ref(v___x_3226_);
v_useLocalFile_boxed_3233_ = lean_unbox(v_useLocalFile_3228_);
v_res_3234_ = l_Lake_Cache_saveArtifact___lam__0(v_file_3225_, v___x_3808__boxed_3232_, v___x_3227_, v_useLocalFile_boxed_3233_, v___x_3229_, v_____r_3230_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__1(lean_object* v_file_3235_, uint64_t v___x_3236_, lean_object* v___x_3237_, uint8_t v_useLocalFile_3238_, lean_object* v___x_3239_, lean_object* v_____r_3240_){
_start:
{
lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3249_; lean_object* v___x_3250_; 
lean_inc_ref(v_file_3235_);
v___x_3250_ = l_Lake_writeFileHash(v_file_3235_, v___x_3236_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v___x_3251_; 
lean_dec_ref(v___x_3250_);
v___x_3251_ = lean_io_metadata(v___x_3239_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v_a_3252_; lean_object* v_modified_3253_; 
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc(v_a_3252_);
lean_dec_ref(v___x_3251_);
v_modified_3253_ = lean_ctor_get(v_a_3252_, 1);
lean_inc_ref(v_modified_3253_);
lean_dec(v_a_3252_);
v___y_3249_ = v_modified_3253_;
goto v___jp_3248_;
}
else
{
lean_object* v___x_3254_; 
lean_dec_ref(v___x_3251_);
v___x_3254_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___y_3249_ = v___x_3254_;
goto v___jp_3248_;
}
}
else
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_dec_ref(v___x_3239_);
lean_dec_ref(v___x_3237_);
lean_dec_ref(v_file_3235_);
v_a_3255_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3257_ = v___x_3250_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3250_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
v___jp_3242_:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3245_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3237_);
lean_ctor_set(v___x_3245_, 1, v___y_3244_);
lean_ctor_set(v___x_3245_, 2, v_file_3235_);
lean_ctor_set(v___x_3245_, 3, v___y_3243_);
v___x_3246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3245_);
v___x_3247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3246_);
return v___x_3247_;
}
v___jp_3248_:
{
if (v_useLocalFile_3238_ == 0)
{
v___y_3243_ = v___y_3249_;
v___y_3244_ = v___x_3239_;
goto v___jp_3242_;
}
else
{
lean_dec_ref(v___x_3239_);
lean_inc_ref(v_file_3235_);
v___y_3243_ = v___y_3249_;
v___y_3244_ = v_file_3235_;
goto v___jp_3242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__1___boxed(lean_object* v_file_3263_, lean_object* v___x_3264_, lean_object* v___x_3265_, lean_object* v_useLocalFile_3266_, lean_object* v___x_3267_, lean_object* v_____r_3268_, lean_object* v___y_3269_){
_start:
{
uint64_t v___x_3873__boxed_3270_; uint8_t v_useLocalFile_boxed_3271_; lean_object* v_res_3272_; 
v___x_3873__boxed_3270_ = lean_unbox_uint64(v___x_3264_);
lean_dec_ref(v___x_3264_);
v_useLocalFile_boxed_3271_ = lean_unbox(v_useLocalFile_3266_);
v_res_3272_ = l_Lake_Cache_saveArtifact___lam__1(v_file_3263_, v___x_3873__boxed_3270_, v___x_3265_, v_useLocalFile_boxed_3271_, v___x_3267_, v_____r_3268_);
return v_res_3272_;
}
}
static lean_object* _init_l_Lake_Cache_saveArtifact___closed__3(void){
_start:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3278_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__2));
v___x_3279_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
lean_ctor_set(v___x_3279_, 1, v___x_3278_);
lean_ctor_set(v___x_3279_, 2, v___x_3278_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact(lean_object* v_cache_3280_, lean_object* v_file_3281_, lean_object* v_ext_3282_, uint8_t v_text_3283_, uint8_t v_exe_3284_, uint8_t v_useLocalFile_3285_){
_start:
{
lean_object* v_a_3288_; lean_object* v___y_3295_; uint8_t v___x_3306_; 
v___x_3306_ = 1;
if (v_text_3283_ == 0)
{
lean_object* v___x_3307_; 
v___x_3307_ = l_IO_FS_readBinFile(v_file_3281_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3308_; uint64_t v___x_3309_; uint64_t v___x_3310_; uint64_t v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___y_3316_; lean_object* v___x_3336_; lean_object* v___x_3337_; uint8_t v___x_3338_; 
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_a_3308_);
lean_dec_ref(v___x_3307_);
v___x_3309_ = l_Lake_Hash_nil;
v___x_3310_ = lean_byte_array_hash(v_a_3308_);
v___x_3311_ = lean_uint64_mix_hash(v___x_3309_, v___x_3310_);
lean_inc_ref(v_ext_3282_);
v___x_3312_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3312_, 0, v_ext_3282_);
lean_ctor_set_uint64(v___x_3312_, sizeof(void*)*1, v___x_3311_);
v___x_3313_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
v___x_3314_ = l_System_FilePath_join(v_cache_3280_, v___x_3313_);
v___x_3336_ = lean_string_utf8_byte_size(v_ext_3282_);
v___x_3337_ = lean_unsigned_to_nat(0u);
v___x_3338_ = lean_nat_dec_eq(v___x_3336_, v___x_3337_);
if (v___x_3338_ == 0)
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3339_ = l_Lake_Hash_hex(v___x_3311_);
v___x_3340_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_3341_ = lean_string_append(v___x_3339_, v___x_3340_);
v___x_3342_ = lean_string_append(v___x_3341_, v_ext_3282_);
lean_dec_ref(v_ext_3282_);
v___y_3316_ = v___x_3342_;
goto v___jp_3315_;
}
else
{
lean_object* v___x_3343_; 
lean_dec_ref(v_ext_3282_);
v___x_3343_ = l_Lake_Hash_hex(v___x_3311_);
v___y_3316_ = v___x_3343_;
goto v___jp_3315_;
}
v___jp_3315_:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3317_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_3317_, 0, v___x_3306_);
lean_ctor_set_uint8(v___x_3317_, 1, v_text_3283_);
lean_ctor_set_uint8(v___x_3317_, 2, v_exe_3284_);
lean_inc_ref_n(v___x_3317_, 2);
v___x_3318_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3317_);
lean_ctor_set(v___x_3318_, 1, v___x_3317_);
lean_ctor_set(v___x_3318_, 2, v___x_3317_);
v___x_3319_ = l_IO_setAccessRights(v_file_3281_, v___x_3318_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v___x_3320_; uint8_t v___x_3321_; 
lean_dec_ref(v___x_3319_);
v___x_3320_ = l_Lake_joinRelative(v___x_3314_, v___y_3316_);
v___x_3321_ = l_System_FilePath_pathExists(v___x_3320_);
if (v___x_3321_ == 0)
{
lean_object* v___x_3322_; 
lean_inc_ref(v___x_3320_);
v___x_3322_ = l_Lake_createParentDirs(v___x_3320_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v___x_3323_; 
lean_dec_ref(v___x_3322_);
v___x_3323_ = lean_io_hard_link(v_file_3281_, v___x_3320_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
lean_dec_ref(v___x_3323_);
lean_dec_ref(v___x_3318_);
lean_dec(v_a_3308_);
v___x_3324_ = lean_box(0);
v___x_3325_ = l_Lake_Cache_saveArtifact___lam__0(v_file_3281_, v___x_3311_, v___x_3312_, v_useLocalFile_3285_, v___x_3320_, v___x_3324_);
v___y_3295_ = v___x_3325_;
goto v___jp_3294_;
}
else
{
lean_object* v___x_3326_; 
lean_dec_ref(v___x_3323_);
v___x_3326_ = l_IO_FS_writeBinFile(v___x_3320_, v_a_3308_);
lean_dec(v_a_3308_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v___x_3327_; 
lean_dec_ref(v___x_3326_);
v___x_3327_ = l_IO_setAccessRights(v___x_3320_, v___x_3318_);
lean_dec_ref(v___x_3318_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; lean_object* v___x_3329_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_a_3328_);
lean_dec_ref(v___x_3327_);
v___x_3329_ = l_Lake_Cache_saveArtifact___lam__0(v_file_3281_, v___x_3311_, v___x_3312_, v_useLocalFile_3285_, v___x_3320_, v_a_3328_);
v___y_3295_ = v___x_3329_;
goto v___jp_3294_;
}
else
{
lean_object* v_a_3330_; 
lean_dec_ref(v___x_3320_);
lean_dec_ref(v___x_3312_);
lean_dec_ref(v_file_3281_);
v_a_3330_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_a_3330_);
lean_dec_ref(v___x_3327_);
v_a_3288_ = v_a_3330_;
goto v___jp_3287_;
}
}
else
{
lean_object* v_a_3331_; 
lean_dec_ref(v___x_3320_);
lean_dec_ref(v___x_3318_);
lean_dec_ref(v___x_3312_);
lean_dec_ref(v_file_3281_);
v_a_3331_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3331_);
lean_dec_ref(v___x_3326_);
v_a_3288_ = v_a_3331_;
goto v___jp_3287_;
}
}
}
else
{
lean_object* v_a_3332_; 
lean_dec_ref(v___x_3320_);
lean_dec_ref(v___x_3318_);
lean_dec_ref(v___x_3312_);
lean_dec(v_a_3308_);
lean_dec_ref(v_file_3281_);
v_a_3332_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3332_);
lean_dec_ref(v___x_3322_);
v_a_3288_ = v_a_3332_;
goto v___jp_3287_;
}
}
else
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
lean_dec_ref(v___x_3318_);
lean_dec(v_a_3308_);
v___x_3333_ = lean_box(0);
v___x_3334_ = l_Lake_Cache_saveArtifact___lam__0(v_file_3281_, v___x_3311_, v___x_3312_, v_useLocalFile_3285_, v___x_3320_, v___x_3333_);
v___y_3295_ = v___x_3334_;
goto v___jp_3294_;
}
}
else
{
lean_object* v_a_3335_; 
lean_dec_ref(v___x_3318_);
lean_dec_ref(v___y_3316_);
lean_dec_ref(v___x_3314_);
lean_dec_ref(v___x_3312_);
lean_dec(v_a_3308_);
lean_dec_ref(v_file_3281_);
v_a_3335_ = lean_ctor_get(v___x_3319_, 0);
lean_inc(v_a_3335_);
lean_dec_ref(v___x_3319_);
v_a_3288_ = v_a_3335_;
goto v___jp_3287_;
}
}
}
else
{
lean_object* v_a_3344_; 
lean_dec_ref(v_ext_3282_);
lean_dec_ref(v_file_3281_);
lean_dec_ref(v_cache_3280_);
v_a_3344_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_a_3344_);
lean_dec_ref(v___x_3307_);
v_a_3288_ = v_a_3344_;
goto v___jp_3287_;
}
}
else
{
lean_object* v___x_3345_; 
v___x_3345_ = l_IO_FS_readFile(v_file_3281_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; lean_object* v___x_3347_; uint64_t v___x_3348_; uint64_t v___x_3349_; uint64_t v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___y_3355_; lean_object* v___x_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_a_3346_);
lean_dec_ref(v___x_3345_);
v___x_3347_ = l_String_crlfToLf(v_a_3346_);
lean_dec(v_a_3346_);
v___x_3348_ = l_Lake_Hash_nil;
v___x_3349_ = lean_string_hash(v___x_3347_);
v___x_3350_ = lean_uint64_mix_hash(v___x_3348_, v___x_3349_);
lean_inc_ref(v_ext_3282_);
v___x_3351_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3351_, 0, v_ext_3282_);
lean_ctor_set_uint64(v___x_3351_, sizeof(void*)*1, v___x_3350_);
v___x_3352_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
v___x_3353_ = l_System_FilePath_join(v_cache_3280_, v___x_3352_);
v___x_3371_ = lean_string_utf8_byte_size(v_ext_3282_);
v___x_3372_ = lean_unsigned_to_nat(0u);
v___x_3373_ = lean_nat_dec_eq(v___x_3371_, v___x_3372_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3374_ = l_Lake_Hash_hex(v___x_3350_);
v___x_3375_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_3376_ = lean_string_append(v___x_3374_, v___x_3375_);
v___x_3377_ = lean_string_append(v___x_3376_, v_ext_3282_);
lean_dec_ref(v_ext_3282_);
v___y_3355_ = v___x_3377_;
goto v___jp_3354_;
}
else
{
lean_object* v___x_3378_; 
lean_dec_ref(v_ext_3282_);
v___x_3378_ = l_Lake_Hash_hex(v___x_3350_);
v___y_3355_ = v___x_3378_;
goto v___jp_3354_;
}
v___jp_3354_:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3356_ = lean_obj_once(&l_Lake_Cache_saveArtifact___closed__3, &l_Lake_Cache_saveArtifact___closed__3_once, _init_l_Lake_Cache_saveArtifact___closed__3);
v___x_3357_ = l_IO_setAccessRights(v_file_3281_, v___x_3356_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v___x_3358_; uint8_t v___x_3359_; 
lean_dec_ref(v___x_3357_);
v___x_3358_ = l_Lake_joinRelative(v___x_3353_, v___y_3355_);
v___x_3359_ = l_System_FilePath_pathExists(v___x_3358_);
if (v___x_3359_ == 0)
{
lean_object* v___x_3360_; 
lean_inc_ref(v___x_3358_);
v___x_3360_ = l_Lake_createParentDirs(v___x_3358_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v___x_3361_; 
lean_dec_ref(v___x_3360_);
v___x_3361_ = l_IO_FS_writeFile(v___x_3358_, v___x_3347_);
lean_dec_ref(v___x_3347_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v___x_3362_; 
lean_dec_ref(v___x_3361_);
v___x_3362_ = l_IO_setAccessRights(v___x_3358_, v___x_3356_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3364_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref(v___x_3362_);
v___x_3364_ = l_Lake_Cache_saveArtifact___lam__1(v_file_3281_, v___x_3350_, v___x_3351_, v_useLocalFile_3285_, v___x_3358_, v_a_3363_);
v___y_3295_ = v___x_3364_;
goto v___jp_3294_;
}
else
{
lean_object* v_a_3365_; 
lean_dec_ref(v___x_3358_);
lean_dec_ref(v___x_3351_);
lean_dec_ref(v_file_3281_);
v_a_3365_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3365_);
lean_dec_ref(v___x_3362_);
v_a_3288_ = v_a_3365_;
goto v___jp_3287_;
}
}
else
{
lean_object* v_a_3366_; 
lean_dec_ref(v___x_3358_);
lean_dec_ref(v___x_3351_);
lean_dec_ref(v_file_3281_);
v_a_3366_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3366_);
lean_dec_ref(v___x_3361_);
v_a_3288_ = v_a_3366_;
goto v___jp_3287_;
}
}
else
{
lean_object* v_a_3367_; 
lean_dec_ref(v___x_3358_);
lean_dec_ref(v___x_3351_);
lean_dec_ref(v___x_3347_);
lean_dec_ref(v_file_3281_);
v_a_3367_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3367_);
lean_dec_ref(v___x_3360_);
v_a_3288_ = v_a_3367_;
goto v___jp_3287_;
}
}
else
{
lean_object* v___x_3368_; lean_object* v___x_3369_; 
lean_dec_ref(v___x_3347_);
v___x_3368_ = lean_box(0);
v___x_3369_ = l_Lake_Cache_saveArtifact___lam__1(v_file_3281_, v___x_3350_, v___x_3351_, v_useLocalFile_3285_, v___x_3358_, v___x_3368_);
v___y_3295_ = v___x_3369_;
goto v___jp_3294_;
}
}
else
{
lean_object* v_a_3370_; 
lean_dec_ref(v___y_3355_);
lean_dec_ref(v___x_3353_);
lean_dec_ref(v___x_3351_);
lean_dec_ref(v___x_3347_);
lean_dec_ref(v_file_3281_);
v_a_3370_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_a_3370_);
lean_dec_ref(v___x_3357_);
v_a_3288_ = v_a_3370_;
goto v___jp_3287_;
}
}
}
else
{
lean_object* v_a_3379_; 
lean_dec_ref(v_ext_3282_);
lean_dec_ref(v_file_3281_);
lean_dec_ref(v_cache_3280_);
v_a_3379_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_a_3379_);
lean_dec_ref(v___x_3345_);
v_a_3288_ = v_a_3379_;
goto v___jp_3287_;
}
}
v___jp_3287_:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3289_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__0));
v___x_3290_ = lean_io_error_to_string(v_a_3288_);
v___x_3291_ = lean_string_append(v___x_3289_, v___x_3290_);
lean_dec_ref(v___x_3290_);
v___x_3292_ = lean_mk_io_user_error(v___x_3291_);
v___x_3293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3292_);
return v___x_3293_;
}
v___jp_3294_:
{
if (lean_obj_tag(v___y_3295_) == 0)
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3304_; 
v_a_3296_ = lean_ctor_get(v___y_3295_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___y_3295_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3298_ = v___y_3295_;
v_isShared_3299_ = v_isSharedCheck_3304_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___y_3295_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3304_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v_a_3300_; lean_object* v___x_3302_; 
v_a_3300_ = lean_ctor_get(v_a_3296_, 0);
lean_inc(v_a_3300_);
lean_dec(v_a_3296_);
if (v_isShared_3299_ == 0)
{
lean_ctor_set(v___x_3298_, 0, v_a_3300_);
v___x_3302_ = v___x_3298_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3300_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
else
{
lean_object* v_a_3305_; 
v_a_3305_ = lean_ctor_get(v___y_3295_, 0);
lean_inc(v_a_3305_);
lean_dec_ref(v___y_3295_);
v_a_3288_ = v_a_3305_;
goto v___jp_3287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___boxed(lean_object* v_cache_3380_, lean_object* v_file_3381_, lean_object* v_ext_3382_, lean_object* v_text_3383_, lean_object* v_exe_3384_, lean_object* v_useLocalFile_3385_, lean_object* v_a_3386_){
_start:
{
uint8_t v_text_boxed_3387_; uint8_t v_exe_boxed_3388_; uint8_t v_useLocalFile_boxed_3389_; lean_object* v_res_3390_; 
v_text_boxed_3387_ = lean_unbox(v_text_3383_);
v_exe_boxed_3388_ = lean_unbox(v_exe_3384_);
v_useLocalFile_boxed_3389_ = lean_unbox(v_useLocalFile_3385_);
v_res_3390_ = l_Lake_Cache_saveArtifact(v_cache_3380_, v_file_3381_, v_ext_3382_, v_text_boxed_3387_, v_exe_boxed_3388_, v_useLocalFile_boxed_3389_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0(lean_object* v_x_3391_){
_start:
{
lean_object* v_lakeCache_3392_; 
v_lakeCache_3392_ = lean_ctor_get(v_x_3391_, 3);
lean_inc_ref(v_lakeCache_3392_);
return v_lakeCache_3392_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0___boxed(lean_object* v_x_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l_Lake_cacheArtifact___redArg___lam__0(v_x_3393_);
lean_dec_ref(v_x_3393_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1(lean_object* v_file_3395_, lean_object* v_ext_3396_, uint8_t v_text_3397_, uint8_t v_exe_3398_, uint8_t v_useLocalFile_3399_, lean_object* v_inst_3400_, lean_object* v_____do__lift_3401_){
_start:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3402_ = lean_box(v_text_3397_);
v___x_3403_ = lean_box(v_exe_3398_);
v___x_3404_ = lean_box(v_useLocalFile_3399_);
v___x_3405_ = lean_alloc_closure((void*)(l_Lake_Cache_saveArtifact___boxed), 7, 6);
lean_closure_set(v___x_3405_, 0, v_____do__lift_3401_);
lean_closure_set(v___x_3405_, 1, v_file_3395_);
lean_closure_set(v___x_3405_, 2, v_ext_3396_);
lean_closure_set(v___x_3405_, 3, v___x_3402_);
lean_closure_set(v___x_3405_, 4, v___x_3403_);
lean_closure_set(v___x_3405_, 5, v___x_3404_);
v___x_3406_ = lean_apply_2(v_inst_3400_, lean_box(0), v___x_3405_);
return v___x_3406_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1___boxed(lean_object* v_file_3407_, lean_object* v_ext_3408_, lean_object* v_text_3409_, lean_object* v_exe_3410_, lean_object* v_useLocalFile_3411_, lean_object* v_inst_3412_, lean_object* v_____do__lift_3413_){
_start:
{
uint8_t v_text_boxed_3414_; uint8_t v_exe_boxed_3415_; uint8_t v_useLocalFile_boxed_3416_; lean_object* v_res_3417_; 
v_text_boxed_3414_ = lean_unbox(v_text_3409_);
v_exe_boxed_3415_ = lean_unbox(v_exe_3410_);
v_useLocalFile_boxed_3416_ = lean_unbox(v_useLocalFile_3411_);
v_res_3417_ = l_Lake_cacheArtifact___redArg___lam__1(v_file_3407_, v_ext_3408_, v_text_boxed_3414_, v_exe_boxed_3415_, v_useLocalFile_boxed_3416_, v_inst_3412_, v_____do__lift_3413_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg(lean_object* v_inst_3419_, lean_object* v_inst_3420_, lean_object* v_inst_3421_, lean_object* v_file_3422_, lean_object* v_ext_3423_, uint8_t v_text_3424_, uint8_t v_exe_3425_, uint8_t v_useLocalFile_3426_){
_start:
{
lean_object* v_toApplicative_3427_; lean_object* v_toFunctor_3428_; lean_object* v_toBind_3429_; lean_object* v_map_3430_; lean_object* v___f_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___f_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v_toApplicative_3427_ = lean_ctor_get(v_inst_3421_, 0);
v_toFunctor_3428_ = lean_ctor_get(v_toApplicative_3427_, 0);
lean_inc_ref(v_toFunctor_3428_);
v_toBind_3429_ = lean_ctor_get(v_inst_3421_, 1);
lean_inc(v_toBind_3429_);
lean_dec_ref(v_inst_3421_);
v_map_3430_ = lean_ctor_get(v_toFunctor_3428_, 0);
lean_inc(v_map_3430_);
lean_dec_ref(v_toFunctor_3428_);
v___f_3431_ = ((lean_object*)(l_Lake_cacheArtifact___redArg___closed__0));
v___x_3432_ = lean_box(v_text_3424_);
v___x_3433_ = lean_box(v_exe_3425_);
v___x_3434_ = lean_box(v_useLocalFile_3426_);
v___f_3435_ = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_3435_, 0, v_file_3422_);
lean_closure_set(v___f_3435_, 1, v_ext_3423_);
lean_closure_set(v___f_3435_, 2, v___x_3432_);
lean_closure_set(v___f_3435_, 3, v___x_3433_);
lean_closure_set(v___f_3435_, 4, v___x_3434_);
lean_closure_set(v___f_3435_, 5, v_inst_3420_);
v___x_3436_ = lean_apply_4(v_map_3430_, lean_box(0), lean_box(0), v___f_3431_, v_inst_3419_);
v___x_3437_ = lean_apply_4(v_toBind_3429_, lean_box(0), lean_box(0), v___x_3436_, v___f_3435_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___boxed(lean_object* v_inst_3438_, lean_object* v_inst_3439_, lean_object* v_inst_3440_, lean_object* v_file_3441_, lean_object* v_ext_3442_, lean_object* v_text_3443_, lean_object* v_exe_3444_, lean_object* v_useLocalFile_3445_){
_start:
{
uint8_t v_text_boxed_3446_; uint8_t v_exe_boxed_3447_; uint8_t v_useLocalFile_boxed_3448_; lean_object* v_res_3449_; 
v_text_boxed_3446_ = lean_unbox(v_text_3443_);
v_exe_boxed_3447_ = lean_unbox(v_exe_3444_);
v_useLocalFile_boxed_3448_ = lean_unbox(v_useLocalFile_3445_);
v_res_3449_ = l_Lake_cacheArtifact___redArg(v_inst_3438_, v_inst_3439_, v_inst_3440_, v_file_3441_, v_ext_3442_, v_text_boxed_3446_, v_exe_boxed_3447_, v_useLocalFile_boxed_3448_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact(lean_object* v_m_3450_, lean_object* v_inst_3451_, lean_object* v_inst_3452_, lean_object* v_inst_3453_, lean_object* v_file_3454_, lean_object* v_ext_3455_, uint8_t v_text_3456_, uint8_t v_exe_3457_, uint8_t v_useLocalFile_3458_){
_start:
{
lean_object* v_toApplicative_3459_; lean_object* v_toFunctor_3460_; lean_object* v_toBind_3461_; lean_object* v_map_3462_; lean_object* v___f_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___f_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v_toApplicative_3459_ = lean_ctor_get(v_inst_3453_, 0);
v_toFunctor_3460_ = lean_ctor_get(v_toApplicative_3459_, 0);
lean_inc_ref(v_toFunctor_3460_);
v_toBind_3461_ = lean_ctor_get(v_inst_3453_, 1);
lean_inc(v_toBind_3461_);
lean_dec_ref(v_inst_3453_);
v_map_3462_ = lean_ctor_get(v_toFunctor_3460_, 0);
lean_inc(v_map_3462_);
lean_dec_ref(v_toFunctor_3460_);
v___f_3463_ = ((lean_object*)(l_Lake_cacheArtifact___redArg___closed__0));
v___x_3464_ = lean_box(v_text_3456_);
v___x_3465_ = lean_box(v_exe_3457_);
v___x_3466_ = lean_box(v_useLocalFile_3458_);
v___f_3467_ = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_3467_, 0, v_file_3454_);
lean_closure_set(v___f_3467_, 1, v_ext_3455_);
lean_closure_set(v___f_3467_, 2, v___x_3464_);
lean_closure_set(v___f_3467_, 3, v___x_3465_);
lean_closure_set(v___f_3467_, 4, v___x_3466_);
lean_closure_set(v___f_3467_, 5, v_inst_3452_);
v___x_3468_ = lean_apply_4(v_map_3462_, lean_box(0), lean_box(0), v___f_3463_, v_inst_3451_);
v___x_3469_ = lean_apply_4(v_toBind_3461_, lean_box(0), lean_box(0), v___x_3468_, v___f_3467_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___boxed(lean_object* v_m_3470_, lean_object* v_inst_3471_, lean_object* v_inst_3472_, lean_object* v_inst_3473_, lean_object* v_file_3474_, lean_object* v_ext_3475_, lean_object* v_text_3476_, lean_object* v_exe_3477_, lean_object* v_useLocalFile_3478_){
_start:
{
uint8_t v_text_boxed_3479_; uint8_t v_exe_boxed_3480_; uint8_t v_useLocalFile_boxed_3481_; lean_object* v_res_3482_; 
v_text_boxed_3479_ = lean_unbox(v_text_3476_);
v_exe_boxed_3480_ = lean_unbox(v_exe_3477_);
v_useLocalFile_boxed_3481_ = lean_unbox(v_useLocalFile_3478_);
v_res_3482_ = l_Lake_cacheArtifact(v_m_3470_, v_inst_3471_, v_inst_3472_, v_inst_3473_, v_file_3474_, v_ext_3475_, v_text_boxed_3479_, v_exe_boxed_3480_, v_useLocalFile_boxed_3481_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0(lean_object* v_x1_3484_, lean_object* v_x2_3485_){
_start:
{
lean_object* v_message_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v_message_3486_ = lean_ctor_get(v_x2_3485_, 0);
v___x_3487_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0));
v___x_3488_ = lean_string_append(v_x1_3484_, v___x_3487_);
v___x_3489_ = lean_string_append(v___x_3488_, v_message_3486_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___boxed(lean_object* v_x1_3490_, lean_object* v_x2_3491_){
_start:
{
lean_object* v_res_3492_; 
v_res_3492_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0(v_x1_3490_, v_x2_3491_);
lean_dec_ref(v_x2_3491_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(lean_object* v_inst_3496_, uint64_t v_inputHash_3497_, lean_object* v_pkg_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_){
_start:
{
lean_object* v_toContext_3506_; lean_object* v_log_3507_; uint8_t v_action_3508_; uint8_t v_wantsRebuild_3509_; lean_object* v_trace_3510_; lean_object* v_buildTime_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3606_; 
v_toContext_3506_ = lean_ctor_get(v_a_3503_, 1);
v_log_3507_ = lean_ctor_get(v_a_3504_, 0);
v_action_3508_ = lean_ctor_get_uint8(v_a_3504_, sizeof(void*)*3);
v_wantsRebuild_3509_ = lean_ctor_get_uint8(v_a_3504_, sizeof(void*)*3 + 1);
v_trace_3510_ = lean_ctor_get(v_a_3504_, 1);
v_buildTime_3511_ = lean_ctor_get(v_a_3504_, 2);
v_isSharedCheck_3606_ = !lean_is_exclusive(v_a_3504_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3513_ = v_a_3504_;
v_isShared_3514_ = v_isSharedCheck_3606_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_buildTime_3511_);
lean_inc(v_trace_3510_);
lean_inc(v_log_3507_);
lean_dec(v_a_3504_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3606_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v_lakeCache_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v_lakeCache_3515_ = lean_ctor_get(v_toContext_3506_, 3);
v___x_3516_ = l_Lake_Package_cacheScope(v_pkg_3498_);
lean_inc_ref(v_lakeCache_3515_);
v___x_3517_ = l_Lake_Cache_readOutputs_x3f(v_lakeCache_3515_, v___x_3516_, v_inputHash_3497_, v_log_3507_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_a_3518_; lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3593_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
v_a_3519_ = lean_ctor_get(v___x_3517_, 1);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3521_ = v___x_3517_;
v_isShared_3522_ = v_isSharedCheck_3593_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_inc(v_a_3518_);
lean_dec(v___x_3517_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3593_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3524_; 
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 0, v_a_3519_);
v___x_3524_ = v___x_3513_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_a_3519_);
lean_ctor_set(v_reuseFailAlloc_3592_, 1, v_trace_3510_);
lean_ctor_set(v_reuseFailAlloc_3592_, 2, v_buildTime_3511_);
lean_ctor_set_uint8(v_reuseFailAlloc_3592_, sizeof(void*)*3, v_action_3508_);
lean_ctor_set_uint8(v_reuseFailAlloc_3592_, sizeof(void*)*3 + 1, v_wantsRebuild_3509_);
v___x_3524_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
if (lean_obj_tag(v_a_3518_) == 1)
{
lean_object* v_val_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3587_; 
v_val_3525_ = lean_ctor_get(v_a_3518_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v_a_3518_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3527_ = v_a_3518_;
v_isShared_3528_ = v_isSharedCheck_3587_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_val_3525_);
lean_dec(v_a_3518_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3587_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3529_; lean_object* v_r_3531_; lean_object* v___y_3532_; 
v___x_3529_ = lean_apply_8(v_inst_3496_, v_val_3525_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v___x_3524_, lean_box(0));
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v_a_3536_; lean_object* v_a_3537_; lean_object* v___x_3539_; 
v_a_3536_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_a_3536_);
v_a_3537_ = lean_ctor_get(v___x_3529_, 1);
lean_inc(v_a_3537_);
lean_dec_ref(v___x_3529_);
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 0, v_a_3536_);
v___x_3539_ = v___x_3527_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3536_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
v_r_3531_ = v___x_3539_;
v___y_3532_ = v_a_3537_;
goto v___jp_3530_;
}
}
else
{
lean_object* v_a_3541_; lean_object* v_a_3542_; lean_object* v_log_3543_; uint8_t v_action_3544_; uint8_t v_wantsRebuild_3545_; lean_object* v_trace_3546_; lean_object* v_buildTime_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3586_; 
lean_del_object(v___x_3527_);
v_a_3541_ = lean_ctor_get(v___x_3529_, 1);
lean_inc(v_a_3541_);
v_a_3542_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_a_3542_);
lean_dec_ref(v___x_3529_);
v_log_3543_ = lean_ctor_get(v_a_3541_, 0);
v_action_3544_ = lean_ctor_get_uint8(v_a_3541_, sizeof(void*)*3);
v_wantsRebuild_3545_ = lean_ctor_get_uint8(v_a_3541_, sizeof(void*)*3 + 1);
v_trace_3546_ = lean_ctor_get(v_a_3541_, 1);
v_buildTime_3547_ = lean_ctor_get(v_a_3541_, 2);
v_isSharedCheck_3586_ = !lean_is_exclusive(v_a_3541_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3549_ = v_a_3541_;
v_isShared_3550_ = v_isSharedCheck_3586_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_buildTime_3547_);
lean_inc(v_trace_3546_);
lean_inc(v_log_3543_);
lean_dec(v_a_3541_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3586_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___y_3555_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; uint8_t v___x_3577_; 
v___x_3551_ = lean_array_get_size(v_log_3543_);
lean_inc(v_a_3542_);
v___x_3552_ = l_Array_extract___redArg(v_log_3543_, v_a_3542_, v___x_3551_);
v___x_3553_ = l_Array_shrink___redArg(v_log_3543_, v_a_3542_);
lean_dec(v_a_3542_);
v___x_3563_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0));
v___x_3564_ = l_Lake_Hash_hex(v_inputHash_3497_);
v___x_3565_ = lean_unsigned_to_nat(7u);
v___x_3566_ = lean_unsigned_to_nat(0u);
v___x_3567_ = lean_string_utf8_byte_size(v___x_3564_);
lean_inc_ref(v___x_3564_);
v___x_3568_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3564_);
lean_ctor_set(v___x_3568_, 1, v___x_3566_);
lean_ctor_set(v___x_3568_, 2, v___x_3567_);
v___x_3569_ = l_String_Slice_Pos_nextn(v___x_3568_, v___x_3566_, v___x_3565_);
lean_dec_ref(v___x_3568_);
v___x_3570_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3564_);
lean_ctor_set(v___x_3570_, 1, v___x_3566_);
lean_ctor_set(v___x_3570_, 2, v___x_3569_);
v___x_3571_ = l_String_Slice_toString(v___x_3570_);
lean_dec_ref(v___x_3570_);
v___x_3572_ = lean_string_append(v___x_3563_, v___x_3571_);
lean_dec_ref(v___x_3571_);
v___x_3573_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1));
v___x_3574_ = lean_string_append(v___x_3572_, v___x_3573_);
v___x_3575_ = lean_array_get_size(v___x_3552_);
v___x_3576_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__10));
v___x_3577_ = lean_nat_dec_lt(v___x_3566_, v___x_3575_);
if (v___x_3577_ == 0)
{
lean_dec_ref(v___x_3552_);
v___y_3555_ = v___x_3574_;
goto v___jp_3554_;
}
else
{
lean_object* v___f_3578_; uint8_t v___x_3579_; 
v___f_3578_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__2));
v___x_3579_ = lean_nat_dec_le(v___x_3575_, v___x_3575_);
if (v___x_3579_ == 0)
{
if (v___x_3577_ == 0)
{
lean_dec_ref(v___x_3552_);
v___y_3555_ = v___x_3574_;
goto v___jp_3554_;
}
else
{
size_t v___x_3580_; size_t v___x_3581_; lean_object* v___x_3582_; 
v___x_3580_ = ((size_t)0ULL);
v___x_3581_ = lean_usize_of_nat(v___x_3575_);
v___x_3582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3576_, v___f_3578_, v___x_3552_, v___x_3580_, v___x_3581_, v___x_3574_);
v___y_3555_ = v___x_3582_;
goto v___jp_3554_;
}
}
else
{
size_t v___x_3583_; size_t v___x_3584_; lean_object* v___x_3585_; 
v___x_3583_ = ((size_t)0ULL);
v___x_3584_ = lean_usize_of_nat(v___x_3575_);
v___x_3585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3576_, v___f_3578_, v___x_3552_, v___x_3583_, v___x_3584_, v___x_3574_);
v___y_3555_ = v___x_3585_;
goto v___jp_3554_;
}
}
v___jp_3554_:
{
uint8_t v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3560_; 
v___x_3556_ = 2;
v___x_3557_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3557_, 0, v___y_3555_);
lean_ctor_set_uint8(v___x_3557_, sizeof(void*)*1, v___x_3556_);
v___x_3558_ = lean_array_push(v___x_3553_, v___x_3557_);
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 0, v___x_3558_);
v___x_3560_ = v___x_3549_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v___x_3558_);
lean_ctor_set(v_reuseFailAlloc_3562_, 1, v_trace_3546_);
lean_ctor_set(v_reuseFailAlloc_3562_, 2, v_buildTime_3547_);
lean_ctor_set_uint8(v_reuseFailAlloc_3562_, sizeof(void*)*3, v_action_3544_);
lean_ctor_set_uint8(v_reuseFailAlloc_3562_, sizeof(void*)*3 + 1, v_wantsRebuild_3545_);
v___x_3560_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
lean_object* v___x_3561_; 
v___x_3561_ = lean_box(0);
v_r_3531_ = v___x_3561_;
v___y_3532_ = v___x_3560_;
goto v___jp_3530_;
}
}
}
}
v___jp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 1, v___y_3532_);
lean_ctor_set(v___x_3521_, 0, v_r_3531_);
v___x_3534_ = v___x_3521_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_r_3531_);
lean_ctor_set(v_reuseFailAlloc_3535_, 1, v___y_3532_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
}
else
{
lean_object* v___x_3588_; lean_object* v___x_3590_; 
lean_dec(v_a_3518_);
lean_dec_ref(v_a_3503_);
lean_dec(v_a_3502_);
lean_dec(v_a_3501_);
lean_dec(v_a_3500_);
lean_dec_ref(v_a_3499_);
lean_dec_ref(v_inst_3496_);
v___x_3588_ = lean_box(0);
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 1, v___x_3524_);
lean_ctor_set(v___x_3521_, 0, v___x_3588_);
v___x_3590_ = v___x_3521_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3588_);
lean_ctor_set(v_reuseFailAlloc_3591_, 1, v___x_3524_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
}
else
{
lean_object* v_a_3594_; lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3605_; 
lean_dec_ref(v_a_3503_);
lean_dec(v_a_3502_);
lean_dec(v_a_3501_);
lean_dec(v_a_3500_);
lean_dec_ref(v_a_3499_);
lean_dec_ref(v_inst_3496_);
v_a_3594_ = lean_ctor_get(v___x_3517_, 0);
v_a_3595_ = lean_ctor_get(v___x_3517_, 1);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3597_ = v___x_3517_;
v_isShared_3598_ = v_isSharedCheck_3605_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_inc(v_a_3594_);
lean_dec(v___x_3517_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3605_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 0, v_a_3595_);
v___x_3600_ = v___x_3513_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_a_3595_);
lean_ctor_set(v_reuseFailAlloc_3604_, 1, v_trace_3510_);
lean_ctor_set(v_reuseFailAlloc_3604_, 2, v_buildTime_3511_);
lean_ctor_set_uint8(v_reuseFailAlloc_3604_, sizeof(void*)*3, v_action_3508_);
lean_ctor_set_uint8(v_reuseFailAlloc_3604_, sizeof(void*)*3 + 1, v_wantsRebuild_3509_);
v___x_3600_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
lean_object* v___x_3602_; 
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 1, v___x_3600_);
v___x_3602_ = v___x_3597_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_a_3594_);
lean_ctor_set(v_reuseFailAlloc_3603_, 1, v___x_3600_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___boxed(lean_object* v_inst_3607_, lean_object* v_inputHash_3608_, lean_object* v_pkg_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_){
_start:
{
uint64_t v_inputHash_boxed_3617_; lean_object* v_res_3618_; 
v_inputHash_boxed_3617_ = lean_unbox_uint64(v_inputHash_3608_);
lean_dec_ref(v_inputHash_3608_);
v_res_3618_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3607_, v_inputHash_boxed_3617_, v_pkg_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f(lean_object* v_00_u03b1_3619_, lean_object* v_inst_3620_, uint64_t v_inputHash_3621_, lean_object* v_pkg_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_){
_start:
{
lean_object* v___x_3630_; 
v___x_3630_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3620_, v_inputHash_3621_, v_pkg_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___boxed(lean_object* v_00_u03b1_3631_, lean_object* v_inst_3632_, lean_object* v_inputHash_3633_, lean_object* v_pkg_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_){
_start:
{
uint64_t v_inputHash_boxed_3642_; lean_object* v_res_3643_; 
v_inputHash_boxed_3642_ = lean_unbox_uint64(v_inputHash_3633_);
lean_dec_ref(v_inputHash_3633_);
v_res_3643_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f(v_00_u03b1_3631_, v_inst_3632_, v_inputHash_boxed_3642_, v_pkg_3634_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(lean_object* v_a_3644_, lean_object* v_____r_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3653_, 0, v_a_3644_);
v___x_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3653_);
v___x_3655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3654_);
lean_ctor_set(v___x_3655_, 1, v___y_3651_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0___boxed(lean_object* v_a_3656_, lean_object* v_____r_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3656_, v_____r_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_);
lean_dec_ref(v___y_3662_);
lean_dec(v___y_3661_);
lean_dec(v___y_3660_);
lean_dec(v___y_3659_);
lean_dec_ref(v___y_3658_);
return v_res_3665_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg(lean_object* v_inst_3667_, uint64_t v_inputHash_3668_, lean_object* v_savedTrace_3669_, lean_object* v_pkg_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_){
_start:
{
lean_object* v___y_3679_; lean_object* v_a_3683_; lean_object* v_a_3684_; lean_object* v___y_3699_; 
if (lean_obj_tag(v_savedTrace_3669_) == 2)
{
lean_object* v_data_3714_; uint64_t v_depHash_3715_; lean_object* v_outputs_x3f_3716_; uint8_t v___x_3717_; 
v_data_3714_ = lean_ctor_get(v_savedTrace_3669_, 0);
lean_inc_ref(v_data_3714_);
lean_dec_ref(v_savedTrace_3669_);
v_depHash_3715_ = lean_ctor_get_uint64(v_data_3714_, sizeof(void*)*3);
v_outputs_x3f_3716_ = lean_ctor_get(v_data_3714_, 1);
lean_inc(v_outputs_x3f_3716_);
lean_dec_ref(v_data_3714_);
v___x_3717_ = lean_uint64_dec_eq(v_depHash_3715_, v_inputHash_3668_);
if (v___x_3717_ == 0)
{
lean_dec(v_outputs_x3f_3716_);
lean_dec_ref(v_a_3675_);
lean_dec(v_a_3674_);
lean_dec(v_a_3673_);
lean_dec(v_a_3672_);
lean_dec_ref(v_a_3671_);
lean_dec_ref(v_pkg_3670_);
lean_dec_ref(v_inst_3667_);
v___y_3679_ = v_a_3676_;
goto v___jp_3678_;
}
else
{
if (lean_obj_tag(v_outputs_x3f_3716_) == 1)
{
lean_object* v_val_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v_val_3718_ = lean_ctor_get(v_outputs_x3f_3716_, 0);
lean_inc(v_val_3718_);
lean_dec_ref(v_outputs_x3f_3716_);
v___x_3719_ = lean_box(0);
lean_inc(v_val_3718_);
v___x_3720_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3720_, 0, v_val_3718_);
lean_ctor_set(v___x_3720_, 1, v___x_3719_);
lean_ctor_set(v___x_3720_, 2, v___x_3719_);
lean_inc_ref(v_a_3675_);
lean_inc(v_a_3674_);
lean_inc(v_a_3673_);
lean_inc(v_a_3672_);
lean_inc_ref(v_a_3671_);
v___x_3721_ = lean_apply_8(v_inst_3667_, v___x_3720_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, lean_box(0));
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v_config_3722_; lean_object* v_a_3723_; lean_object* v_a_3724_; lean_object* v_enableArtifactCache_x3f_3725_; lean_object* v_a_3727_; uint8_t v_a_3731_; lean_object* v_a_3732_; 
v_config_3722_ = lean_ctor_get(v_pkg_3670_, 6);
v_a_3723_ = lean_ctor_get(v___x_3721_, 0);
lean_inc(v_a_3723_);
v_a_3724_ = lean_ctor_get(v___x_3721_, 1);
lean_inc(v_a_3724_);
lean_dec_ref(v___x_3721_);
v_enableArtifactCache_x3f_3725_ = lean_ctor_get(v_config_3722_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_3725_) == 0)
{
lean_object* v_toContext_3763_; lean_object* v_lakeEnv_3764_; lean_object* v_enableArtifactCache_x3f_3765_; 
v_toContext_3763_ = lean_ctor_get(v_a_3675_, 1);
v_lakeEnv_3764_ = lean_ctor_get(v_toContext_3763_, 1);
v_enableArtifactCache_x3f_3765_ = lean_ctor_get(v_lakeEnv_3764_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_3765_) == 0)
{
lean_object* v_root_3766_; lean_object* v_config_3767_; lean_object* v_enableArtifactCache_x3f_3768_; 
v_root_3766_ = lean_ctor_get(v_toContext_3763_, 0);
v_config_3767_ = lean_ctor_get(v_root_3766_, 6);
v_enableArtifactCache_x3f_3768_ = lean_ctor_get(v_config_3767_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_3768_) == 0)
{
lean_dec(v_val_3718_);
lean_dec_ref(v_pkg_3670_);
v_a_3727_ = v_a_3724_;
goto v___jp_3726_;
}
else
{
lean_object* v_val_3769_; uint8_t v___x_3770_; 
v_val_3769_ = lean_ctor_get(v_enableArtifactCache_x3f_3768_, 0);
v___x_3770_ = lean_unbox(v_val_3769_);
v_a_3731_ = v___x_3770_;
v_a_3732_ = v_a_3724_;
goto v___jp_3730_;
}
}
else
{
lean_object* v_val_3771_; uint8_t v___x_3772_; 
v_val_3771_ = lean_ctor_get(v_enableArtifactCache_x3f_3765_, 0);
v___x_3772_ = lean_unbox(v_val_3771_);
v_a_3731_ = v___x_3772_;
v_a_3732_ = v_a_3724_;
goto v___jp_3730_;
}
}
else
{
lean_object* v_val_3773_; uint8_t v___x_3774_; 
v_val_3773_ = lean_ctor_get(v_enableArtifactCache_x3f_3725_, 0);
v___x_3774_ = lean_unbox(v_val_3773_);
v_a_3731_ = v___x_3774_;
v_a_3732_ = v_a_3724_;
goto v___jp_3730_;
}
v___jp_3726_:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3728_ = lean_box(0);
v___x_3729_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3723_, v___x_3728_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3727_);
lean_dec_ref(v_a_3675_);
lean_dec(v_a_3674_);
lean_dec(v_a_3673_);
lean_dec(v_a_3672_);
lean_dec_ref(v_a_3671_);
v___y_3699_ = v___x_3729_;
goto v___jp_3698_;
}
v___jp_3730_:
{
if (v_a_3731_ == 0)
{
lean_dec(v_val_3718_);
lean_dec_ref(v_pkg_3670_);
v_a_3727_ = v_a_3732_;
goto v___jp_3726_;
}
else
{
lean_object* v_toContext_3733_; lean_object* v_log_3734_; uint8_t v_action_3735_; uint8_t v_wantsRebuild_3736_; lean_object* v_trace_3737_; lean_object* v_buildTime_3738_; lean_object* v_lakeCache_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
v_toContext_3733_ = lean_ctor_get(v_a_3675_, 1);
v_log_3734_ = lean_ctor_get(v_a_3732_, 0);
v_action_3735_ = lean_ctor_get_uint8(v_a_3732_, sizeof(void*)*3);
v_wantsRebuild_3736_ = lean_ctor_get_uint8(v_a_3732_, sizeof(void*)*3 + 1);
v_trace_3737_ = lean_ctor_get(v_a_3732_, 1);
v_buildTime_3738_ = lean_ctor_get(v_a_3732_, 2);
v_lakeCache_3739_ = lean_ctor_get(v_toContext_3733_, 3);
v___x_3740_ = l_Lake_Package_cacheScope(v_pkg_3670_);
lean_inc_ref(v_lakeCache_3739_);
v___x_3741_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_3739_, v___x_3740_, v_inputHash_3668_, v_val_3718_, v___x_3719_, v___x_3719_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v___x_3742_; lean_object* v___x_3743_; 
lean_dec_ref(v___x_3741_);
v___x_3742_ = lean_box(0);
v___x_3743_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3723_, v___x_3742_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3732_);
lean_dec_ref(v_a_3675_);
lean_dec(v_a_3674_);
lean_dec(v_a_3673_);
lean_dec(v_a_3672_);
lean_dec_ref(v_a_3671_);
v___y_3699_ = v___x_3743_;
goto v___jp_3698_;
}
else
{
lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3759_; 
lean_inc(v_buildTime_3738_);
lean_inc_ref(v_trace_3737_);
lean_inc_ref(v_log_3734_);
v_isSharedCheck_3759_ = !lean_is_exclusive(v_a_3732_);
if (v_isSharedCheck_3759_ == 0)
{
lean_object* v_unused_3760_; lean_object* v_unused_3761_; lean_object* v_unused_3762_; 
v_unused_3760_ = lean_ctor_get(v_a_3732_, 2);
lean_dec(v_unused_3760_);
v_unused_3761_ = lean_ctor_get(v_a_3732_, 1);
lean_dec(v_unused_3761_);
v_unused_3762_ = lean_ctor_get(v_a_3732_, 0);
lean_dec(v_unused_3762_);
v___x_3745_ = v_a_3732_;
v_isShared_3746_ = v_isSharedCheck_3759_;
goto v_resetjp_3744_;
}
else
{
lean_dec(v_a_3732_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3759_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v_a_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; uint8_t v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3756_; 
v_a_3747_ = lean_ctor_get(v___x_3741_, 0);
lean_inc(v_a_3747_);
lean_dec_ref(v___x_3741_);
v___x_3748_ = ((lean_object*)(l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0));
v___x_3749_ = lean_io_error_to_string(v_a_3747_);
v___x_3750_ = lean_string_append(v___x_3748_, v___x_3749_);
lean_dec_ref(v___x_3749_);
v___x_3751_ = 2;
v___x_3752_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3752_, 0, v___x_3750_);
lean_ctor_set_uint8(v___x_3752_, sizeof(void*)*1, v___x_3751_);
v___x_3753_ = lean_box(0);
v___x_3754_ = lean_array_push(v_log_3734_, v___x_3752_);
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 0, v___x_3754_);
v___x_3756_ = v___x_3745_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v___x_3754_);
lean_ctor_set(v_reuseFailAlloc_3758_, 1, v_trace_3737_);
lean_ctor_set(v_reuseFailAlloc_3758_, 2, v_buildTime_3738_);
lean_ctor_set_uint8(v_reuseFailAlloc_3758_, sizeof(void*)*3, v_action_3735_);
lean_ctor_set_uint8(v_reuseFailAlloc_3758_, sizeof(void*)*3 + 1, v_wantsRebuild_3736_);
v___x_3756_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
lean_object* v___x_3757_; 
v___x_3757_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3723_, v___x_3753_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v___x_3756_);
lean_dec_ref(v_a_3675_);
lean_dec(v_a_3674_);
lean_dec(v_a_3673_);
lean_dec(v_a_3672_);
lean_dec_ref(v_a_3671_);
v___y_3699_ = v___x_3757_;
goto v___jp_3698_;
}
}
}
}
}
}
else
{
lean_object* v_a_3775_; lean_object* v_a_3776_; 
lean_dec(v_val_3718_);
lean_dec_ref(v_a_3675_);
lean_dec(v_a_3674_);
lean_dec(v_a_3673_);
lean_dec(v_a_3672_);
lean_dec_ref(v_a_3671_);
lean_dec_ref(v_pkg_3670_);
v_a_3775_ = lean_ctor_get(v___x_3721_, 0);
lean_inc(v_a_3775_);
v_a_3776_ = lean_ctor_get(v___x_3721_, 1);
lean_inc(v_a_3776_);
lean_dec_ref(v___x_3721_);
v_a_3683_ = v_a_3775_;
v_a_3684_ = v_a_3776_;
goto v___jp_3682_;
}
}
else
{
lean_dec(v_outputs_x3f_3716_);
lean_dec_ref(v_a_3675_);
lean_dec(v_a_3674_);
lean_dec(v_a_3673_);
lean_dec(v_a_3672_);
lean_dec_ref(v_a_3671_);
lean_dec_ref(v_pkg_3670_);
lean_dec_ref(v_inst_3667_);
v___y_3679_ = v_a_3676_;
goto v___jp_3678_;
}
}
}
else
{
lean_dec_ref(v_a_3675_);
lean_dec(v_a_3674_);
lean_dec(v_a_3673_);
lean_dec(v_a_3672_);
lean_dec_ref(v_a_3671_);
lean_dec_ref(v_pkg_3670_);
lean_dec(v_savedTrace_3669_);
lean_dec_ref(v_inst_3667_);
v___y_3679_ = v_a_3676_;
goto v___jp_3678_;
}
v___jp_3678_:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3680_ = lean_box(0);
v___x_3681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3680_);
lean_ctor_set(v___x_3681_, 1, v___y_3679_);
return v___x_3681_;
}
v___jp_3682_:
{
lean_object* v_log_3685_; uint8_t v_action_3686_; uint8_t v_wantsRebuild_3687_; lean_object* v_trace_3688_; lean_object* v_buildTime_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3697_; 
v_log_3685_ = lean_ctor_get(v_a_3684_, 0);
v_action_3686_ = lean_ctor_get_uint8(v_a_3684_, sizeof(void*)*3);
v_wantsRebuild_3687_ = lean_ctor_get_uint8(v_a_3684_, sizeof(void*)*3 + 1);
v_trace_3688_ = lean_ctor_get(v_a_3684_, 1);
v_buildTime_3689_ = lean_ctor_get(v_a_3684_, 2);
v_isSharedCheck_3697_ = !lean_is_exclusive(v_a_3684_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3691_ = v_a_3684_;
v_isShared_3692_ = v_isSharedCheck_3697_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_buildTime_3689_);
lean_inc(v_trace_3688_);
lean_inc(v_log_3685_);
lean_dec(v_a_3684_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3697_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3693_; lean_object* v___x_3695_; 
v___x_3693_ = l_Array_shrink___redArg(v_log_3685_, v_a_3683_);
lean_dec(v_a_3683_);
if (v_isShared_3692_ == 0)
{
lean_ctor_set(v___x_3691_, 0, v___x_3693_);
v___x_3695_ = v___x_3691_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3693_);
lean_ctor_set(v_reuseFailAlloc_3696_, 1, v_trace_3688_);
lean_ctor_set(v_reuseFailAlloc_3696_, 2, v_buildTime_3689_);
lean_ctor_set_uint8(v_reuseFailAlloc_3696_, sizeof(void*)*3, v_action_3686_);
lean_ctor_set_uint8(v_reuseFailAlloc_3696_, sizeof(void*)*3 + 1, v_wantsRebuild_3687_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
v___y_3679_ = v___x_3695_;
goto v___jp_3678_;
}
}
}
v___jp_3698_:
{
if (lean_obj_tag(v___y_3699_) == 0)
{
lean_object* v_a_3700_; 
v_a_3700_ = lean_ctor_get(v___y_3699_, 0);
if (lean_obj_tag(v_a_3700_) == 0)
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3709_; 
lean_inc_ref(v_a_3700_);
v_a_3701_ = lean_ctor_get(v___y_3699_, 1);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___y_3699_);
if (v_isSharedCheck_3709_ == 0)
{
lean_object* v_unused_3710_; 
v_unused_3710_ = lean_ctor_get(v___y_3699_, 0);
lean_dec(v_unused_3710_);
v___x_3703_ = v___y_3699_;
v_isShared_3704_ = v_isSharedCheck_3709_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___y_3699_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3709_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v_a_3705_; lean_object* v___x_3707_; 
v_a_3705_ = lean_ctor_get(v_a_3700_, 0);
lean_inc(v_a_3705_);
lean_dec_ref(v_a_3700_);
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 0, v_a_3705_);
v___x_3707_ = v___x_3703_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_a_3705_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v_a_3701_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
else
{
lean_object* v_a_3711_; 
v_a_3711_ = lean_ctor_get(v___y_3699_, 1);
lean_inc(v_a_3711_);
lean_dec_ref(v___y_3699_);
v___y_3679_ = v_a_3711_;
goto v___jp_3678_;
}
}
else
{
lean_object* v_a_3712_; lean_object* v_a_3713_; 
v_a_3712_ = lean_ctor_get(v___y_3699_, 0);
lean_inc(v_a_3712_);
v_a_3713_ = lean_ctor_get(v___y_3699_, 1);
lean_inc(v_a_3713_);
lean_dec_ref(v___y_3699_);
v_a_3683_ = v_a_3712_;
v_a_3684_ = v_a_3713_;
goto v___jp_3682_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___boxed(lean_object* v_inst_3777_, lean_object* v_inputHash_3778_, lean_object* v_savedTrace_3779_, lean_object* v_pkg_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_){
_start:
{
uint64_t v_inputHash_boxed_3788_; lean_object* v_res_3789_; 
v_inputHash_boxed_3788_ = lean_unbox_uint64(v_inputHash_3778_);
lean_dec_ref(v_inputHash_3778_);
v_res_3789_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3777_, v_inputHash_boxed_3788_, v_savedTrace_3779_, v_pkg_3780_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_, v_a_3785_, v_a_3786_);
return v_res_3789_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f(lean_object* v_00_u03b1_3790_, lean_object* v_inst_3791_, uint64_t v_inputHash_3792_, lean_object* v_savedTrace_3793_, lean_object* v_pkg_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_){
_start:
{
lean_object* v___x_3802_; 
v___x_3802_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3791_, v_inputHash_3792_, v_savedTrace_3793_, v_pkg_3794_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___boxed(lean_object* v_00_u03b1_3803_, lean_object* v_inst_3804_, lean_object* v_inputHash_3805_, lean_object* v_savedTrace_3806_, lean_object* v_pkg_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_){
_start:
{
uint64_t v_inputHash_boxed_3815_; lean_object* v_res_3816_; 
v_inputHash_boxed_3815_ = lean_unbox_uint64(v_inputHash_3805_);
lean_dec_ref(v_inputHash_3805_);
v_res_3816_ = l_Lake_getArtifactsUsingTrace_x3f(v_00_u03b1_3803_, v_inst_3804_, v_inputHash_boxed_3815_, v_savedTrace_3806_, v_pkg_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg(lean_object* v_inst_3817_, uint64_t v_inputHash_3818_, lean_object* v_savedTrace_3819_, lean_object* v_pkg_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_){
_start:
{
lean_object* v___x_3828_; 
lean_inc_ref(v_a_3825_);
lean_inc(v_a_3824_);
lean_inc(v_a_3823_);
lean_inc(v_a_3822_);
lean_inc_ref(v_a_3821_);
lean_inc_ref(v_pkg_3820_);
lean_inc_ref(v_inst_3817_);
v___x_3828_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3817_, v_inputHash_3818_, v_pkg_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_a_3829_);
if (lean_obj_tag(v_a_3829_) == 1)
{
lean_dec_ref(v_a_3829_);
lean_dec_ref(v_a_3825_);
lean_dec(v_a_3824_);
lean_dec(v_a_3823_);
lean_dec(v_a_3822_);
lean_dec_ref(v_a_3821_);
lean_dec_ref(v_pkg_3820_);
lean_dec(v_savedTrace_3819_);
lean_dec_ref(v_inst_3817_);
return v___x_3828_;
}
else
{
lean_object* v_a_3830_; lean_object* v___x_3831_; lean_object* v_a_3832_; 
lean_dec(v_a_3829_);
v_a_3830_ = lean_ctor_get(v___x_3828_, 1);
lean_inc(v_a_3830_);
lean_dec_ref(v___x_3828_);
v___x_3831_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3817_, v_inputHash_3818_, v_savedTrace_3819_, v_pkg_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3830_);
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
lean_inc(v_a_3832_);
if (lean_obj_tag(v_a_3832_) == 1)
{
lean_dec_ref(v_a_3832_);
return v___x_3831_;
}
else
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3841_; 
lean_dec(v_a_3832_);
v_a_3833_ = lean_ctor_get(v___x_3831_, 1);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3841_ == 0)
{
lean_object* v_unused_3842_; 
v_unused_3842_ = lean_ctor_get(v___x_3831_, 0);
lean_dec(v_unused_3842_);
v___x_3835_ = v___x_3831_;
v_isShared_3836_ = v_isSharedCheck_3841_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___x_3831_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3841_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3837_; lean_object* v___x_3839_; 
v___x_3837_ = lean_box(0);
if (v_isShared_3836_ == 0)
{
lean_ctor_set(v___x_3835_, 0, v___x_3837_);
v___x_3839_ = v___x_3835_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v___x_3837_);
lean_ctor_set(v_reuseFailAlloc_3840_, 1, v_a_3833_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_3825_);
lean_dec(v_a_3824_);
lean_dec(v_a_3823_);
lean_dec(v_a_3822_);
lean_dec_ref(v_a_3821_);
lean_dec_ref(v_pkg_3820_);
lean_dec(v_savedTrace_3819_);
lean_dec_ref(v_inst_3817_);
return v___x_3828_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___boxed(lean_object* v_inst_3843_, lean_object* v_inputHash_3844_, lean_object* v_savedTrace_3845_, lean_object* v_pkg_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_){
_start:
{
uint64_t v_inputHash_boxed_3854_; lean_object* v_res_3855_; 
v_inputHash_boxed_3854_ = lean_unbox_uint64(v_inputHash_3844_);
lean_dec_ref(v_inputHash_3844_);
v_res_3855_ = l_Lake_getArtifacts_x3f___redArg(v_inst_3843_, v_inputHash_boxed_3854_, v_savedTrace_3845_, v_pkg_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f(lean_object* v_00_u03b1_3856_, lean_object* v_inst_3857_, uint64_t v_inputHash_3858_, lean_object* v_savedTrace_3859_, lean_object* v_pkg_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_){
_start:
{
lean_object* v___x_3868_; 
lean_inc_ref(v_a_3865_);
lean_inc(v_a_3864_);
lean_inc(v_a_3863_);
lean_inc(v_a_3862_);
lean_inc_ref(v_a_3861_);
lean_inc_ref(v_pkg_3860_);
lean_inc_ref(v_inst_3857_);
v___x_3868_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3857_, v_inputHash_3858_, v_pkg_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_);
if (lean_obj_tag(v___x_3868_) == 0)
{
lean_object* v_a_3869_; 
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
lean_inc(v_a_3869_);
if (lean_obj_tag(v_a_3869_) == 1)
{
lean_dec_ref(v_a_3869_);
lean_dec_ref(v_a_3865_);
lean_dec(v_a_3864_);
lean_dec(v_a_3863_);
lean_dec(v_a_3862_);
lean_dec_ref(v_a_3861_);
lean_dec_ref(v_pkg_3860_);
lean_dec(v_savedTrace_3859_);
lean_dec_ref(v_inst_3857_);
return v___x_3868_;
}
else
{
lean_object* v_a_3870_; lean_object* v___x_3871_; lean_object* v_a_3872_; 
lean_dec(v_a_3869_);
v_a_3870_ = lean_ctor_get(v___x_3868_, 1);
lean_inc(v_a_3870_);
lean_dec_ref(v___x_3868_);
v___x_3871_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3857_, v_inputHash_3858_, v_savedTrace_3859_, v_pkg_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3870_);
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_a_3872_);
if (lean_obj_tag(v_a_3872_) == 1)
{
lean_dec_ref(v_a_3872_);
return v___x_3871_;
}
else
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3881_; 
lean_dec(v_a_3872_);
v_a_3873_ = lean_ctor_get(v___x_3871_, 1);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3881_ == 0)
{
lean_object* v_unused_3882_; 
v_unused_3882_ = lean_ctor_get(v___x_3871_, 0);
lean_dec(v_unused_3882_);
v___x_3875_ = v___x_3871_;
v_isShared_3876_ = v_isSharedCheck_3881_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3871_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3881_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3877_; lean_object* v___x_3879_; 
v___x_3877_ = lean_box(0);
if (v_isShared_3876_ == 0)
{
lean_ctor_set(v___x_3875_, 0, v___x_3877_);
v___x_3879_ = v___x_3875_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3877_);
lean_ctor_set(v_reuseFailAlloc_3880_, 1, v_a_3873_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_3865_);
lean_dec(v_a_3864_);
lean_dec(v_a_3863_);
lean_dec(v_a_3862_);
lean_dec_ref(v_a_3861_);
lean_dec_ref(v_pkg_3860_);
lean_dec(v_savedTrace_3859_);
lean_dec_ref(v_inst_3857_);
return v___x_3868_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___boxed(lean_object* v_00_u03b1_3883_, lean_object* v_inst_3884_, lean_object* v_inputHash_3885_, lean_object* v_savedTrace_3886_, lean_object* v_pkg_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_){
_start:
{
uint64_t v_inputHash_boxed_3895_; lean_object* v_res_3896_; 
v_inputHash_boxed_3895_ = lean_unbox_uint64(v_inputHash_3885_);
lean_dec_ref(v_inputHash_3885_);
v_res_3896_ = l_Lake_getArtifacts_x3f(v_00_u03b1_3883_, v_inst_3884_, v_inputHash_boxed_3895_, v_savedTrace_3886_, v_pkg_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___redArg(lean_object* v_descr_3909_, lean_object* v_service_x3f_3910_, lean_object* v_scope_x3f_3911_, uint8_t v_exe_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_){
_start:
{
lean_object* v___y_3917_; lean_object* v_mtime_3918_; lean_object* v___y_3919_; lean_object* v___y_3923_; lean_object* v_log_3924_; uint8_t v_action_3925_; uint8_t v_wantsRebuild_3926_; lean_object* v_trace_3927_; lean_object* v_buildTime_3928_; lean_object* v_toContext_3943_; lean_object* v_log_3944_; uint8_t v_action_3945_; uint8_t v_wantsRebuild_3946_; lean_object* v_trace_3947_; lean_object* v_buildTime_3948_; lean_object* v_lakeConfig_3949_; lean_object* v_lakeCache_3950_; uint64_t v_hash_3951_; lean_object* v_ext_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___y_3956_; lean_object* v___x_4055_; lean_object* v___x_4056_; uint8_t v___x_4057_; 
v_toContext_3943_ = lean_ctor_get(v_a_3913_, 1);
lean_inc(v_toContext_3943_);
lean_dec_ref(v_a_3913_);
v_log_3944_ = lean_ctor_get(v_a_3914_, 0);
v_action_3945_ = lean_ctor_get_uint8(v_a_3914_, sizeof(void*)*3);
v_wantsRebuild_3946_ = lean_ctor_get_uint8(v_a_3914_, sizeof(void*)*3 + 1);
v_trace_3947_ = lean_ctor_get(v_a_3914_, 1);
v_buildTime_3948_ = lean_ctor_get(v_a_3914_, 2);
v_lakeConfig_3949_ = lean_ctor_get(v_toContext_3943_, 2);
lean_inc_ref(v_lakeConfig_3949_);
v_lakeCache_3950_ = lean_ctor_get(v_toContext_3943_, 3);
lean_inc_ref(v_lakeCache_3950_);
lean_dec(v_toContext_3943_);
v_hash_3951_ = lean_ctor_get_uint64(v_descr_3909_, sizeof(void*)*1);
v_ext_3952_ = lean_ctor_get(v_descr_3909_, 0);
v___x_3953_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
v___x_3954_ = l_System_FilePath_join(v_lakeCache_3950_, v___x_3953_);
v___x_4055_ = lean_string_utf8_byte_size(v_ext_3952_);
v___x_4056_ = lean_unsigned_to_nat(0u);
v___x_4057_ = lean_nat_dec_eq(v___x_4055_, v___x_4056_);
if (v___x_4057_ == 0)
{
lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4058_ = l_Lake_Hash_hex(v_hash_3951_);
v___x_4059_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_4060_ = lean_string_append(v___x_4058_, v___x_4059_);
v___x_4061_ = lean_string_append(v___x_4060_, v_ext_3952_);
v___y_3956_ = v___x_4061_;
goto v___jp_3955_;
}
else
{
lean_object* v___x_4062_; 
v___x_4062_ = l_Lake_Hash_hex(v_hash_3951_);
v___y_3956_ = v___x_4062_;
goto v___jp_3955_;
}
v___jp_3916_:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; 
lean_inc_ref(v___y_3917_);
v___x_3920_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3920_, 0, v_descr_3909_);
lean_ctor_set(v___x_3920_, 1, v___y_3917_);
lean_ctor_set(v___x_3920_, 2, v___y_3917_);
lean_ctor_set(v___x_3920_, 3, v_mtime_3918_);
v___x_3921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3920_);
lean_ctor_set(v___x_3921_, 1, v___y_3919_);
return v___x_3921_;
}
v___jp_3922_:
{
lean_object* v___x_3929_; 
v___x_3929_ = lean_io_metadata(v___y_3923_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v_a_3930_; lean_object* v_modified_3931_; lean_object* v___x_3932_; 
v_a_3930_ = lean_ctor_get(v___x_3929_, 0);
lean_inc(v_a_3930_);
lean_dec_ref(v___x_3929_);
v_modified_3931_ = lean_ctor_get(v_a_3930_, 1);
lean_inc_ref(v_modified_3931_);
lean_dec(v_a_3930_);
v___x_3932_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3932_, 0, v_log_3924_);
lean_ctor_set(v___x_3932_, 1, v_trace_3927_);
lean_ctor_set(v___x_3932_, 2, v_buildTime_3928_);
lean_ctor_set_uint8(v___x_3932_, sizeof(void*)*3, v_action_3925_);
lean_ctor_set_uint8(v___x_3932_, sizeof(void*)*3 + 1, v_wantsRebuild_3926_);
v___y_3917_ = v___y_3923_;
v_mtime_3918_ = v_modified_3931_;
v___y_3919_ = v___x_3932_;
goto v___jp_3916_;
}
else
{
lean_object* v_a_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; uint8_t v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
lean_dec_ref(v___y_3923_);
lean_dec_ref(v_descr_3909_);
v_a_3933_ = lean_ctor_get(v___x_3929_, 0);
lean_inc(v_a_3933_);
lean_dec_ref(v___x_3929_);
v___x_3934_ = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__0));
v___x_3935_ = lean_io_error_to_string(v_a_3933_);
v___x_3936_ = lean_string_append(v___x_3934_, v___x_3935_);
lean_dec_ref(v___x_3935_);
v___x_3937_ = 3;
v___x_3938_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3938_, 0, v___x_3936_);
lean_ctor_set_uint8(v___x_3938_, sizeof(void*)*1, v___x_3937_);
v___x_3939_ = lean_array_get_size(v_log_3924_);
v___x_3940_ = lean_array_push(v_log_3924_, v___x_3938_);
v___x_3941_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3941_, 0, v___x_3940_);
lean_ctor_set(v___x_3941_, 1, v_trace_3927_);
lean_ctor_set(v___x_3941_, 2, v_buildTime_3928_);
lean_ctor_set_uint8(v___x_3941_, sizeof(void*)*3, v_action_3925_);
lean_ctor_set_uint8(v___x_3941_, sizeof(void*)*3 + 1, v_wantsRebuild_3926_);
v___x_3942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3939_);
lean_ctor_set(v___x_3942_, 1, v___x_3941_);
return v___x_3942_;
}
}
v___jp_3955_:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; 
v___x_3957_ = l_Lake_joinRelative(v___x_3954_, v___y_3956_);
v___x_3958_ = lean_io_metadata(v___x_3957_);
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_object* v_a_3959_; lean_object* v_modified_3960_; 
lean_dec_ref(v_lakeConfig_3949_);
lean_dec(v_scope_x3f_3911_);
lean_dec(v_service_x3f_3910_);
v_a_3959_ = lean_ctor_get(v___x_3958_, 0);
lean_inc(v_a_3959_);
lean_dec_ref(v___x_3958_);
v_modified_3960_ = lean_ctor_get(v_a_3959_, 1);
lean_inc_ref(v_modified_3960_);
lean_dec(v_a_3959_);
v___y_3917_ = v___x_3957_;
v_mtime_3918_ = v_modified_3960_;
v___y_3919_ = v_a_3914_;
goto v___jp_3916_;
}
else
{
lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_4051_; 
lean_inc(v_buildTime_3948_);
lean_inc_ref(v_trace_3947_);
lean_inc_ref(v_log_3944_);
v_isSharedCheck_4051_ = !lean_is_exclusive(v_a_3914_);
if (v_isSharedCheck_4051_ == 0)
{
lean_object* v_unused_4052_; lean_object* v_unused_4053_; lean_object* v_unused_4054_; 
v_unused_4052_ = lean_ctor_get(v_a_3914_, 2);
lean_dec(v_unused_4052_);
v_unused_4053_ = lean_ctor_get(v_a_3914_, 1);
lean_dec(v_unused_4053_);
v_unused_4054_ = lean_ctor_get(v_a_3914_, 0);
lean_dec(v_unused_4054_);
v___x_3962_ = v_a_3914_;
v_isShared_3963_ = v_isSharedCheck_4051_;
goto v_resetjp_3961_;
}
else
{
lean_dec(v_a_3914_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_4051_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v_a_3964_; 
v_a_3964_ = lean_ctor_get(v___x_3958_, 0);
lean_inc(v_a_3964_);
lean_dec_ref(v___x_3958_);
if (lean_obj_tag(v_a_3964_) == 11)
{
lean_dec_ref(v_a_3964_);
if (lean_obj_tag(v_service_x3f_3910_) == 1)
{
lean_object* v_val_3965_; lean_object* v_cacheServices_3966_; uint8_t v___x_3967_; uint8_t v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v_val_3965_ = lean_ctor_get(v_service_x3f_3910_, 0);
lean_inc(v_val_3965_);
lean_dec_ref(v_service_x3f_3910_);
v_cacheServices_3966_ = lean_ctor_get(v_lakeConfig_3949_, 3);
lean_inc(v_cacheServices_3966_);
lean_dec_ref(v_lakeConfig_3949_);
v___x_3967_ = 2;
v___x_3968_ = l_Lake_JobAction_merge(v_action_3945_, v___x_3967_);
v___x_3969_ = lean_box(0);
lean_inc(v_val_3965_);
v___x_3970_ = l_Lean_Name_str___override(v___x_3969_, v_val_3965_);
v___x_3971_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_cacheServices_3966_, v___x_3970_);
lean_dec(v___x_3970_);
lean_dec(v_cacheServices_3966_);
if (lean_obj_tag(v___x_3971_) == 1)
{
lean_dec(v_val_3965_);
if (lean_obj_tag(v_scope_x3f_3911_) == 1)
{
lean_object* v_val_3972_; lean_object* v_val_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; uint8_t v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v_val_3972_ = lean_ctor_get(v___x_3971_, 0);
lean_inc(v_val_3972_);
lean_dec_ref(v___x_3971_);
v_val_3973_ = lean_ctor_get(v_scope_x3f_3911_, 0);
lean_inc(v_val_3973_);
lean_dec_ref(v_scope_x3f_3911_);
v___x_3974_ = l_Lake_CacheService_artifactUrl(v_hash_3951_, v_val_3972_, v_val_3973_);
v___x_3975_ = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__1));
v___x_3976_ = l_Lake_Hash_hex(v_hash_3951_);
v___x_3977_ = lean_string_append(v___x_3975_, v___x_3976_);
lean_dec_ref(v___x_3976_);
v___x_3978_ = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__2));
v___x_3979_ = lean_string_append(v___x_3977_, v___x_3978_);
v___x_3980_ = lean_string_append(v___x_3979_, v___x_3957_);
v___x_3981_ = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__3));
v___x_3982_ = lean_string_append(v___x_3980_, v___x_3981_);
v___x_3983_ = lean_string_append(v___x_3982_, v___x_3974_);
v___x_3984_ = 0;
v___x_3985_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3985_, 0, v___x_3983_);
lean_ctor_set_uint8(v___x_3985_, sizeof(void*)*1, v___x_3984_);
v___x_3986_ = lean_array_push(v_log_3944_, v___x_3985_);
lean_inc_ref(v___x_3957_);
v___x_3987_ = l_Lake_downloadArtifactCore(v_hash_3951_, v___x_3974_, v___x_3957_, v___x_3986_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v_a_3988_; uint8_t v___x_3989_; uint8_t v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
lean_del_object(v___x_3962_);
v_a_3988_ = lean_ctor_get(v___x_3987_, 1);
lean_inc(v_a_3988_);
lean_dec_ref(v___x_3987_);
v___x_3989_ = 1;
v___x_3990_ = 0;
v___x_3991_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_3991_, 0, v___x_3989_);
lean_ctor_set_uint8(v___x_3991_, 1, v___x_3990_);
lean_ctor_set_uint8(v___x_3991_, 2, v_exe_3912_);
lean_inc_ref_n(v___x_3991_, 2);
v___x_3992_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3991_);
lean_ctor_set(v___x_3992_, 1, v___x_3991_);
lean_ctor_set(v___x_3992_, 2, v___x_3991_);
v___x_3993_ = l_IO_setAccessRights(v___x_3957_, v___x_3992_);
lean_dec_ref(v___x_3992_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_dec_ref(v___x_3993_);
v___y_3923_ = v___x_3957_;
v_log_3924_ = v_a_3988_;
v_action_3925_ = v___x_3968_;
v_wantsRebuild_3926_ = v_wantsRebuild_3946_;
v_trace_3927_ = v_trace_3947_;
v_buildTime_3928_ = v_buildTime_3948_;
goto v___jp_3922_;
}
else
{
lean_object* v_a_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; uint8_t v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
lean_inc(v_a_3994_);
lean_dec_ref(v___x_3993_);
v___x_3995_ = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__4));
v___x_3996_ = lean_io_error_to_string(v_a_3994_);
v___x_3997_ = lean_string_append(v___x_3995_, v___x_3996_);
lean_dec_ref(v___x_3996_);
v___x_3998_ = 2;
v___x_3999_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3999_, 0, v___x_3997_);
lean_ctor_set_uint8(v___x_3999_, sizeof(void*)*1, v___x_3998_);
v___x_4000_ = lean_array_push(v_a_3988_, v___x_3999_);
v___y_3923_ = v___x_3957_;
v_log_3924_ = v___x_4000_;
v_action_3925_ = v___x_3968_;
v_wantsRebuild_3926_ = v_wantsRebuild_3946_;
v_trace_3927_ = v_trace_3947_;
v_buildTime_3928_ = v_buildTime_3948_;
goto v___jp_3922_;
}
}
else
{
lean_object* v_a_4001_; lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4012_; 
lean_dec_ref(v___x_3957_);
lean_dec_ref(v_descr_3909_);
v_a_4001_ = lean_ctor_get(v___x_3987_, 0);
v_a_4002_ = lean_ctor_get(v___x_3987_, 1);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4004_ = v___x_3987_;
v_isShared_4005_ = v_isSharedCheck_4012_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_inc(v_a_4001_);
lean_dec(v___x_3987_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4012_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_3963_ == 0)
{
lean_ctor_set(v___x_3962_, 0, v_a_4002_);
v___x_4007_ = v___x_3962_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4002_);
lean_ctor_set(v_reuseFailAlloc_4011_, 1, v_trace_3947_);
lean_ctor_set(v_reuseFailAlloc_4011_, 2, v_buildTime_3948_);
lean_ctor_set_uint8(v_reuseFailAlloc_4011_, sizeof(void*)*3 + 1, v_wantsRebuild_3946_);
v___x_4007_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
lean_object* v___x_4009_; 
lean_ctor_set_uint8(v___x_4007_, sizeof(void*)*3, v___x_3968_);
if (v_isShared_4005_ == 0)
{
lean_ctor_set(v___x_4004_, 1, v___x_4007_);
v___x_4009_ = v___x_4004_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_a_4001_);
lean_ctor_set(v_reuseFailAlloc_4010_, 1, v___x_4007_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
}
}
else
{
lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4017_; 
lean_dec_ref(v___x_3971_);
lean_dec_ref(v___x_3957_);
lean_dec(v_scope_x3f_3911_);
lean_dec_ref(v_descr_3909_);
v___x_4013_ = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__6));
v___x_4014_ = lean_array_get_size(v_log_3944_);
v___x_4015_ = lean_array_push(v_log_3944_, v___x_4013_);
if (v_isShared_3963_ == 0)
{
lean_ctor_set(v___x_3962_, 0, v___x_4015_);
v___x_4017_ = v___x_3962_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v___x_4015_);
lean_ctor_set(v_reuseFailAlloc_4019_, 1, v_trace_3947_);
lean_ctor_set(v_reuseFailAlloc_4019_, 2, v_buildTime_3948_);
lean_ctor_set_uint8(v_reuseFailAlloc_4019_, sizeof(void*)*3 + 1, v_wantsRebuild_3946_);
v___x_4017_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
lean_object* v___x_4018_; 
lean_ctor_set_uint8(v___x_4017_, sizeof(void*)*3, v___x_3968_);
v___x_4018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4014_);
lean_ctor_set(v___x_4018_, 1, v___x_4017_);
return v___x_4018_;
}
}
}
else
{
lean_object* v___x_4020_; lean_object* v___x_4021_; uint8_t v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4027_; 
lean_dec(v___x_3971_);
lean_dec_ref(v___x_3957_);
lean_dec(v_scope_x3f_3911_);
lean_dec_ref(v_descr_3909_);
v___x_4020_ = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__7));
v___x_4021_ = lean_string_append(v___x_4020_, v_val_3965_);
lean_dec(v_val_3965_);
v___x_4022_ = 3;
v___x_4023_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4023_, 0, v___x_4021_);
lean_ctor_set_uint8(v___x_4023_, sizeof(void*)*1, v___x_4022_);
v___x_4024_ = lean_array_get_size(v_log_3944_);
v___x_4025_ = lean_array_push(v_log_3944_, v___x_4023_);
if (v_isShared_3963_ == 0)
{
lean_ctor_set(v___x_3962_, 0, v___x_4025_);
v___x_4027_ = v___x_3962_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v___x_4025_);
lean_ctor_set(v_reuseFailAlloc_4029_, 1, v_trace_3947_);
lean_ctor_set(v_reuseFailAlloc_4029_, 2, v_buildTime_3948_);
lean_ctor_set_uint8(v_reuseFailAlloc_4029_, sizeof(void*)*3 + 1, v_wantsRebuild_3946_);
v___x_4027_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
lean_object* v___x_4028_; 
lean_ctor_set_uint8(v___x_4027_, sizeof(void*)*3, v___x_3968_);
v___x_4028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4024_);
lean_ctor_set(v___x_4028_, 1, v___x_4027_);
return v___x_4028_;
}
}
}
else
{
lean_object* v___x_4030_; lean_object* v___x_4031_; uint8_t v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4037_; 
lean_dec_ref(v_lakeConfig_3949_);
lean_dec(v_scope_x3f_3911_);
lean_dec(v_service_x3f_3910_);
lean_dec_ref(v_descr_3909_);
v___x_4030_ = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__8));
v___x_4031_ = lean_string_append(v___x_4030_, v___x_3957_);
lean_dec_ref(v___x_3957_);
v___x_4032_ = 3;
v___x_4033_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4033_, 0, v___x_4031_);
lean_ctor_set_uint8(v___x_4033_, sizeof(void*)*1, v___x_4032_);
v___x_4034_ = lean_array_get_size(v_log_3944_);
v___x_4035_ = lean_array_push(v_log_3944_, v___x_4033_);
if (v_isShared_3963_ == 0)
{
lean_ctor_set(v___x_3962_, 0, v___x_4035_);
v___x_4037_ = v___x_3962_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v___x_4035_);
lean_ctor_set(v_reuseFailAlloc_4039_, 1, v_trace_3947_);
lean_ctor_set(v_reuseFailAlloc_4039_, 2, v_buildTime_3948_);
lean_ctor_set_uint8(v_reuseFailAlloc_4039_, sizeof(void*)*3, v_action_3945_);
lean_ctor_set_uint8(v_reuseFailAlloc_4039_, sizeof(void*)*3 + 1, v_wantsRebuild_3946_);
v___x_4037_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
lean_object* v___x_4038_; 
v___x_4038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4034_);
lean_ctor_set(v___x_4038_, 1, v___x_4037_);
return v___x_4038_;
}
}
}
else
{
lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; uint8_t v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4048_; 
lean_dec_ref(v___x_3957_);
lean_dec_ref(v_lakeConfig_3949_);
lean_dec(v_scope_x3f_3911_);
lean_dec(v_service_x3f_3910_);
lean_dec_ref(v_descr_3909_);
v___x_4040_ = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__9));
v___x_4041_ = lean_io_error_to_string(v_a_3964_);
v___x_4042_ = lean_string_append(v___x_4040_, v___x_4041_);
lean_dec_ref(v___x_4041_);
v___x_4043_ = 3;
v___x_4044_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4044_, 0, v___x_4042_);
lean_ctor_set_uint8(v___x_4044_, sizeof(void*)*1, v___x_4043_);
v___x_4045_ = lean_array_get_size(v_log_3944_);
v___x_4046_ = lean_array_push(v_log_3944_, v___x_4044_);
if (v_isShared_3963_ == 0)
{
lean_ctor_set(v___x_3962_, 0, v___x_4046_);
v___x_4048_ = v___x_3962_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v___x_4046_);
lean_ctor_set(v_reuseFailAlloc_4050_, 1, v_trace_3947_);
lean_ctor_set(v_reuseFailAlloc_4050_, 2, v_buildTime_3948_);
lean_ctor_set_uint8(v_reuseFailAlloc_4050_, sizeof(void*)*3, v_action_3945_);
lean_ctor_set_uint8(v_reuseFailAlloc_4050_, sizeof(void*)*3 + 1, v_wantsRebuild_3946_);
v___x_4048_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
lean_object* v___x_4049_; 
v___x_4049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4045_);
lean_ctor_set(v___x_4049_, 1, v___x_4048_);
return v___x_4049_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___redArg___boxed(lean_object* v_descr_4063_, lean_object* v_service_x3f_4064_, lean_object* v_scope_x3f_4065_, lean_object* v_exe_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_){
_start:
{
uint8_t v_exe_boxed_4070_; lean_object* v_res_4071_; 
v_exe_boxed_4070_ = lean_unbox(v_exe_4066_);
v_res_4071_ = l_Lake_resolveArtifact___redArg(v_descr_4063_, v_service_x3f_4064_, v_scope_x3f_4065_, v_exe_boxed_4070_, v_a_4067_, v_a_4068_);
return v_res_4071_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact(lean_object* v_descr_4072_, lean_object* v_service_x3f_4073_, lean_object* v_scope_x3f_4074_, uint8_t v_exe_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_){
_start:
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Lake_resolveArtifact___redArg(v_descr_4072_, v_service_x3f_4073_, v_scope_x3f_4074_, v_exe_4075_, v_a_4080_, v_a_4081_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___boxed(lean_object* v_descr_4084_, lean_object* v_service_x3f_4085_, lean_object* v_scope_x3f_4086_, lean_object* v_exe_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_){
_start:
{
uint8_t v_exe_boxed_4095_; lean_object* v_res_4096_; 
v_exe_boxed_4095_ = lean_unbox(v_exe_4087_);
v_res_4096_ = l_Lake_resolveArtifact(v_descr_4084_, v_service_x3f_4085_, v_scope_x3f_4086_, v_exe_boxed_4095_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_, v_a_4093_);
lean_dec(v_a_4091_);
lean_dec(v_a_4090_);
lean_dec(v_a_4089_);
lean_dec_ref(v_a_4088_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput___redArg(lean_object* v_out_4099_, uint8_t v_exe_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_){
_start:
{
lean_object* v_data_4104_; lean_object* v_service_x3f_4105_; lean_object* v_scope_x3f_4106_; lean_object* v___x_4107_; 
v_data_4104_ = lean_ctor_get(v_out_4099_, 0);
lean_inc(v_data_4104_);
v_service_x3f_4105_ = lean_ctor_get(v_out_4099_, 1);
lean_inc(v_service_x3f_4105_);
v_scope_x3f_4106_ = lean_ctor_get(v_out_4099_, 2);
lean_inc(v_scope_x3f_4106_);
lean_dec_ref(v_out_4099_);
lean_inc(v_data_4104_);
v___x_4107_ = l_Lake_ArtifactDescr_fromJson_x3f(v_data_4104_);
if (lean_obj_tag(v___x_4107_) == 0)
{
lean_object* v_a_4108_; lean_object* v_log_4109_; uint8_t v_action_4110_; uint8_t v_wantsRebuild_4111_; lean_object* v_trace_4112_; lean_object* v_buildTime_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4135_; 
lean_dec(v_scope_x3f_4106_);
lean_dec(v_service_x3f_4105_);
lean_dec_ref(v_a_4101_);
v_a_4108_ = lean_ctor_get(v___x_4107_, 0);
lean_inc(v_a_4108_);
lean_dec_ref(v___x_4107_);
v_log_4109_ = lean_ctor_get(v_a_4102_, 0);
v_action_4110_ = lean_ctor_get_uint8(v_a_4102_, sizeof(void*)*3);
v_wantsRebuild_4111_ = lean_ctor_get_uint8(v_a_4102_, sizeof(void*)*3 + 1);
v_trace_4112_ = lean_ctor_get(v_a_4102_, 1);
v_buildTime_4113_ = lean_ctor_get(v_a_4102_, 2);
v_isSharedCheck_4135_ = !lean_is_exclusive(v_a_4102_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4115_ = v_a_4102_;
v_isShared_4116_ = v_isSharedCheck_4135_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_buildTime_4113_);
lean_inc(v_trace_4112_);
lean_inc(v_log_4109_);
lean_dec(v_a_4102_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4135_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; uint8_t v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4132_; 
v___x_4117_ = ((lean_object*)(l_Lake_resolveArtifactOutput___redArg___closed__0));
v___x_4118_ = l_Lean_Json_render(v_data_4104_);
v___x_4119_ = lean_unsigned_to_nat(80u);
v___x_4120_ = lean_unsigned_to_nat(2u);
v___x_4121_ = lean_unsigned_to_nat(0u);
v___x_4122_ = l_Std_Format_pretty(v___x_4118_, v___x_4119_, v___x_4120_, v___x_4121_);
v___x_4123_ = lean_string_append(v___x_4117_, v___x_4122_);
lean_dec_ref(v___x_4122_);
v___x_4124_ = ((lean_object*)(l_Lake_resolveArtifactOutput___redArg___closed__1));
v___x_4125_ = lean_string_append(v___x_4123_, v___x_4124_);
v___x_4126_ = lean_string_append(v___x_4125_, v_a_4108_);
lean_dec(v_a_4108_);
v___x_4127_ = 3;
v___x_4128_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4128_, 0, v___x_4126_);
lean_ctor_set_uint8(v___x_4128_, sizeof(void*)*1, v___x_4127_);
v___x_4129_ = lean_array_get_size(v_log_4109_);
v___x_4130_ = lean_array_push(v_log_4109_, v___x_4128_);
if (v_isShared_4116_ == 0)
{
lean_ctor_set(v___x_4115_, 0, v___x_4130_);
v___x_4132_ = v___x_4115_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v___x_4130_);
lean_ctor_set(v_reuseFailAlloc_4134_, 1, v_trace_4112_);
lean_ctor_set(v_reuseFailAlloc_4134_, 2, v_buildTime_4113_);
lean_ctor_set_uint8(v_reuseFailAlloc_4134_, sizeof(void*)*3, v_action_4110_);
lean_ctor_set_uint8(v_reuseFailAlloc_4134_, sizeof(void*)*3 + 1, v_wantsRebuild_4111_);
v___x_4132_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
lean_object* v___x_4133_; 
v___x_4133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4133_, 0, v___x_4129_);
lean_ctor_set(v___x_4133_, 1, v___x_4132_);
return v___x_4133_;
}
}
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4137_; 
lean_dec(v_data_4104_);
v_a_4136_ = lean_ctor_get(v___x_4107_, 0);
lean_inc(v_a_4136_);
lean_dec_ref(v___x_4107_);
v___x_4137_ = l_Lake_resolveArtifact___redArg(v_a_4136_, v_service_x3f_4105_, v_scope_x3f_4106_, v_exe_4100_, v_a_4101_, v_a_4102_);
return v___x_4137_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput___redArg___boxed(lean_object* v_out_4138_, lean_object* v_exe_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_){
_start:
{
uint8_t v_exe_boxed_4143_; lean_object* v_res_4144_; 
v_exe_boxed_4143_ = lean_unbox(v_exe_4139_);
v_res_4144_ = l_Lake_resolveArtifactOutput___redArg(v_out_4138_, v_exe_boxed_4143_, v_a_4140_, v_a_4141_);
return v_res_4144_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput(lean_object* v_out_4145_, uint8_t v_exe_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_){
_start:
{
lean_object* v___x_4154_; 
v___x_4154_ = l_Lake_resolveArtifactOutput___redArg(v_out_4145_, v_exe_4146_, v_a_4151_, v_a_4152_);
return v___x_4154_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput___boxed(lean_object* v_out_4155_, lean_object* v_exe_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_){
_start:
{
uint8_t v_exe_boxed_4164_; lean_object* v_res_4165_; 
v_exe_boxed_4164_ = lean_unbox(v_exe_4156_);
v_res_4165_ = l_Lake_resolveArtifactOutput(v_out_4155_, v_exe_boxed_4164_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_);
lean_dec(v_a_4160_);
lean_dec(v_a_4159_);
lean_dec(v_a_4158_);
lean_dec_ref(v_a_4157_);
return v_res_4165_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(uint8_t v_exe_4166_, lean_object* v_out_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_){
_start:
{
lean_object* v___x_4175_; 
v___x_4175_ = l_Lake_resolveArtifactOutput___redArg(v_out_4167_, v_exe_4166_, v___y_4172_, v___y_4173_);
return v___x_4175_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed(lean_object* v_exe_4176_, lean_object* v_out_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_){
_start:
{
uint8_t v_exe_boxed_4185_; lean_object* v_res_4186_; 
v_exe_boxed_4185_ = lean_unbox(v_exe_4176_);
v_res_4186_ = l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(v_exe_boxed_4185_, v_out_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
lean_dec(v___y_4181_);
lean_dec(v___y_4180_);
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(uint8_t v_exe_4187_){
_start:
{
lean_object* v___x_4188_; lean_object* v___f_4189_; 
v___x_4188_ = lean_box(v_exe_4187_);
v___f_4189_ = lean_alloc_closure((void*)(l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4189_, 0, v___x_4188_);
return v___f_4189_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___boxed(lean_object* v_exe_4190_){
_start:
{
uint8_t v_exe_boxed_4191_; lean_object* v_res_4192_; 
v_exe_boxed_4191_ = lean_unbox(v_exe_4190_);
v_res_4192_ = l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(v_exe_boxed_4191_);
return v_res_4192_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg(lean_object* v_path_4193_, lean_object* v_ext_4194_, uint8_t v_text_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_){
_start:
{
lean_object* v___x_4199_; 
lean_inc_ref(v_path_4193_);
v___x_4199_ = l_Lake_fetchFileHash___redArg(v_path_4193_, v_text_4195_, v_a_4196_, v_a_4197_);
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_object* v_a_4200_; lean_object* v_a_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4218_; 
v_a_4200_ = lean_ctor_get(v___x_4199_, 0);
v_a_4201_ = lean_ctor_get(v___x_4199_, 1);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4203_ = v___x_4199_;
v_isShared_4204_ = v_isSharedCheck_4218_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_a_4201_);
lean_inc(v_a_4200_);
lean_dec(v___x_4199_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4218_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v___x_4214_; 
v___x_4214_ = lean_io_metadata(v_path_4193_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_object* v_a_4215_; lean_object* v_modified_4216_; 
v_a_4215_ = lean_ctor_get(v___x_4214_, 0);
lean_inc(v_a_4215_);
lean_dec_ref(v___x_4214_);
v_modified_4216_ = lean_ctor_get(v_a_4215_, 1);
lean_inc_ref(v_modified_4216_);
lean_dec(v_a_4215_);
v___y_4206_ = v_a_4201_;
v___y_4207_ = v_modified_4216_;
goto v___jp_4205_;
}
else
{
lean_object* v___x_4217_; 
lean_dec_ref(v___x_4214_);
v___x_4217_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___y_4206_ = v_a_4201_;
v___y_4207_ = v___x_4217_;
goto v___jp_4205_;
}
v___jp_4205_:
{
lean_object* v___x_4208_; uint64_t v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4212_; 
v___x_4208_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4208_, 0, v_ext_4194_);
v___x_4209_ = lean_unbox_uint64(v_a_4200_);
lean_dec(v_a_4200_);
lean_ctor_set_uint64(v___x_4208_, sizeof(void*)*1, v___x_4209_);
lean_inc_ref(v_path_4193_);
v___x_4210_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4208_);
lean_ctor_set(v___x_4210_, 1, v_path_4193_);
lean_ctor_set(v___x_4210_, 2, v_path_4193_);
lean_ctor_set(v___x_4210_, 3, v___y_4207_);
if (v_isShared_4204_ == 0)
{
lean_ctor_set(v___x_4203_, 1, v___y_4206_);
lean_ctor_set(v___x_4203_, 0, v___x_4210_);
v___x_4212_ = v___x_4203_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v___x_4210_);
lean_ctor_set(v_reuseFailAlloc_4213_, 1, v___y_4206_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
}
}
else
{
lean_object* v_a_4219_; lean_object* v_a_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4227_; 
lean_dec_ref(v_ext_4194_);
lean_dec_ref(v_path_4193_);
v_a_4219_ = lean_ctor_get(v___x_4199_, 0);
v_a_4220_ = lean_ctor_get(v___x_4199_, 1);
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4222_ = v___x_4199_;
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_a_4220_);
lean_inc(v_a_4219_);
lean_dec(v___x_4199_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v___x_4225_; 
if (v_isShared_4223_ == 0)
{
v___x_4225_ = v___x_4222_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_a_4219_);
lean_ctor_set(v_reuseFailAlloc_4226_, 1, v_a_4220_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
return v___x_4225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg___boxed(lean_object* v_path_4228_, lean_object* v_ext_4229_, lean_object* v_text_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_){
_start:
{
uint8_t v_text_boxed_4234_; lean_object* v_res_4235_; 
v_text_boxed_4234_ = lean_unbox(v_text_4230_);
v_res_4235_ = l_Lake_computeArtifact___redArg(v_path_4228_, v_ext_4229_, v_text_boxed_4234_, v_a_4231_, v_a_4232_);
lean_dec_ref(v_a_4231_);
return v_res_4235_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact(lean_object* v_path_4236_, lean_object* v_ext_4237_, uint8_t v_text_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_){
_start:
{
lean_object* v___x_4246_; 
v___x_4246_ = l_Lake_computeArtifact___redArg(v_path_4236_, v_ext_4237_, v_text_4238_, v_a_4243_, v_a_4244_);
return v___x_4246_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___boxed(lean_object* v_path_4247_, lean_object* v_ext_4248_, lean_object* v_text_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_){
_start:
{
uint8_t v_text_boxed_4257_; lean_object* v_res_4258_; 
v_text_boxed_4257_ = lean_unbox(v_text_4249_);
v_res_4258_ = l_Lake_computeArtifact(v_path_4247_, v_ext_4248_, v_text_boxed_4257_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_);
lean_dec_ref(v_a_4254_);
lean_dec(v_a_4253_);
lean_dec(v_a_4252_);
lean_dec(v_a_4251_);
lean_dec_ref(v_a_4250_);
return v_res_4258_;
}
}
LEAN_EXPORT lean_object* l_Lake_restoreArtifact(lean_object* v_file_4262_, lean_object* v_art_4263_, uint8_t v_exe_4264_, lean_object* v_a_4265_){
_start:
{
lean_object* v___y_4268_; uint8_t v___x_4281_; 
v___x_4281_ = l_System_FilePath_pathExists(v_file_4262_);
if (v___x_4281_ == 0)
{
lean_object* v_descr_4282_; lean_object* v_path_4283_; lean_object* v___y_4285_; lean_object* v___x_4300_; lean_object* v___x_4301_; uint8_t v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; 
v_descr_4282_ = lean_ctor_get(v_art_4263_, 0);
v_path_4283_ = lean_ctor_get(v_art_4263_, 1);
v___x_4300_ = ((lean_object*)(l_Lake_restoreArtifact___closed__1));
v___x_4301_ = lean_string_append(v___x_4300_, v_path_4283_);
v___x_4302_ = 0;
v___x_4303_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4303_, 0, v___x_4301_);
lean_ctor_set_uint8(v___x_4303_, sizeof(void*)*1, v___x_4302_);
v___x_4304_ = lean_array_push(v_a_4265_, v___x_4303_);
lean_inc_ref(v_file_4262_);
v___x_4305_ = l_Lake_createParentDirs(v_file_4262_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v___x_4306_; 
lean_dec_ref(v___x_4305_);
v___x_4306_ = lean_io_hard_link(v_path_4283_, v_file_4262_);
if (lean_obj_tag(v___x_4306_) == 0)
{
lean_dec_ref(v___x_4306_);
v___y_4285_ = v___x_4304_;
goto v___jp_4284_;
}
else
{
lean_object* v_a_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; 
v_a_4307_ = lean_ctor_get(v___x_4306_, 0);
lean_inc(v_a_4307_);
lean_dec_ref(v___x_4306_);
v___x_4308_ = ((lean_object*)(l_Lake_restoreArtifact___closed__2));
v___x_4309_ = lean_io_error_to_string(v_a_4307_);
v___x_4310_ = lean_string_append(v___x_4308_, v___x_4309_);
lean_dec_ref(v___x_4309_);
v___x_4311_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4311_, 0, v___x_4310_);
lean_ctor_set_uint8(v___x_4311_, sizeof(void*)*1, v___x_4302_);
v___x_4312_ = lean_array_push(v___x_4304_, v___x_4311_);
v___x_4313_ = l_Lake_copyFile(v_path_4283_, v_file_4262_);
if (lean_obj_tag(v___x_4313_) == 0)
{
uint8_t v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
lean_dec_ref(v___x_4313_);
v___x_4314_ = 1;
v___x_4315_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4315_, 0, v___x_4314_);
lean_ctor_set_uint8(v___x_4315_, 1, v___x_4281_);
lean_ctor_set_uint8(v___x_4315_, 2, v_exe_4264_);
lean_inc_ref_n(v___x_4315_, 2);
v___x_4316_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4316_, 0, v___x_4315_);
lean_ctor_set(v___x_4316_, 1, v___x_4315_);
lean_ctor_set(v___x_4316_, 2, v___x_4315_);
v___x_4317_ = l_IO_setAccessRights(v_file_4262_, v___x_4316_);
lean_dec_ref(v___x_4316_);
if (lean_obj_tag(v___x_4317_) == 0)
{
lean_dec_ref(v___x_4317_);
v___y_4285_ = v___x_4312_;
goto v___jp_4284_;
}
else
{
lean_object* v_a_4318_; lean_object* v___x_4319_; uint8_t v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; 
lean_dec_ref(v_art_4263_);
lean_dec_ref(v_file_4262_);
v_a_4318_ = lean_ctor_get(v___x_4317_, 0);
lean_inc(v_a_4318_);
lean_dec_ref(v___x_4317_);
v___x_4319_ = lean_io_error_to_string(v_a_4318_);
v___x_4320_ = 3;
v___x_4321_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4321_, 0, v___x_4319_);
lean_ctor_set_uint8(v___x_4321_, sizeof(void*)*1, v___x_4320_);
v___x_4322_ = lean_array_get_size(v___x_4312_);
v___x_4323_ = lean_array_push(v___x_4312_, v___x_4321_);
v___x_4324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4324_, 0, v___x_4322_);
lean_ctor_set(v___x_4324_, 1, v___x_4323_);
return v___x_4324_;
}
}
else
{
lean_object* v_a_4325_; lean_object* v___x_4326_; uint8_t v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
lean_dec_ref(v_art_4263_);
lean_dec_ref(v_file_4262_);
v_a_4325_ = lean_ctor_get(v___x_4313_, 0);
lean_inc(v_a_4325_);
lean_dec_ref(v___x_4313_);
v___x_4326_ = lean_io_error_to_string(v_a_4325_);
v___x_4327_ = 3;
v___x_4328_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4328_, 0, v___x_4326_);
lean_ctor_set_uint8(v___x_4328_, sizeof(void*)*1, v___x_4327_);
v___x_4329_ = lean_array_get_size(v___x_4312_);
v___x_4330_ = lean_array_push(v___x_4312_, v___x_4328_);
v___x_4331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4331_, 0, v___x_4329_);
lean_ctor_set(v___x_4331_, 1, v___x_4330_);
return v___x_4331_;
}
}
}
else
{
lean_object* v_a_4332_; lean_object* v___x_4333_; uint8_t v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; 
lean_dec_ref(v_art_4263_);
lean_dec_ref(v_file_4262_);
v_a_4332_ = lean_ctor_get(v___x_4305_, 0);
lean_inc(v_a_4332_);
lean_dec_ref(v___x_4305_);
v___x_4333_ = lean_io_error_to_string(v_a_4332_);
v___x_4334_ = 3;
v___x_4335_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4335_, 0, v___x_4333_);
lean_ctor_set_uint8(v___x_4335_, sizeof(void*)*1, v___x_4334_);
v___x_4336_ = lean_array_get_size(v___x_4304_);
v___x_4337_ = lean_array_push(v___x_4304_, v___x_4335_);
v___x_4338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4336_);
lean_ctor_set(v___x_4338_, 1, v___x_4337_);
return v___x_4338_;
}
v___jp_4284_:
{
uint64_t v_hash_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; uint8_t v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; 
v_hash_4286_ = lean_ctor_get_uint64(v_descr_4282_, sizeof(void*)*1);
v___x_4287_ = ((lean_object*)(l_Lake_restoreArtifact___closed__0));
v___x_4288_ = lean_string_append(v___x_4287_, v_file_4262_);
v___x_4289_ = 0;
v___x_4290_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4290_, 0, v___x_4288_);
lean_ctor_set_uint8(v___x_4290_, sizeof(void*)*1, v___x_4289_);
v___x_4291_ = lean_array_push(v___y_4285_, v___x_4290_);
lean_inc_ref(v_file_4262_);
v___x_4292_ = l_Lake_writeFileHash(v_file_4262_, v_hash_4286_);
if (lean_obj_tag(v___x_4292_) == 0)
{
lean_dec_ref(v___x_4292_);
v___y_4268_ = v___x_4291_;
goto v___jp_4267_;
}
else
{
lean_object* v_a_4293_; lean_object* v___x_4294_; uint8_t v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; 
lean_dec_ref(v_art_4263_);
lean_dec_ref(v_file_4262_);
v_a_4293_ = lean_ctor_get(v___x_4292_, 0);
lean_inc(v_a_4293_);
lean_dec_ref(v___x_4292_);
v___x_4294_ = lean_io_error_to_string(v_a_4293_);
v___x_4295_ = 3;
v___x_4296_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4296_, 0, v___x_4294_);
lean_ctor_set_uint8(v___x_4296_, sizeof(void*)*1, v___x_4295_);
v___x_4297_ = lean_array_get_size(v___x_4291_);
v___x_4298_ = lean_array_push(v___x_4291_, v___x_4296_);
v___x_4299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4299_, 0, v___x_4297_);
lean_ctor_set(v___x_4299_, 1, v___x_4298_);
return v___x_4299_;
}
}
}
else
{
v___y_4268_ = v_a_4265_;
goto v___jp_4267_;
}
v___jp_4267_:
{
lean_object* v_descr_4269_; lean_object* v_mtime_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4278_; 
v_descr_4269_ = lean_ctor_get(v_art_4263_, 0);
v_mtime_4270_ = lean_ctor_get(v_art_4263_, 3);
v_isSharedCheck_4278_ = !lean_is_exclusive(v_art_4263_);
if (v_isSharedCheck_4278_ == 0)
{
lean_object* v_unused_4279_; lean_object* v_unused_4280_; 
v_unused_4279_ = lean_ctor_get(v_art_4263_, 2);
lean_dec(v_unused_4279_);
v_unused_4280_ = lean_ctor_get(v_art_4263_, 1);
lean_dec(v_unused_4280_);
v___x_4272_ = v_art_4263_;
v_isShared_4273_ = v_isSharedCheck_4278_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_mtime_4270_);
lean_inc(v_descr_4269_);
lean_dec(v_art_4263_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4278_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4275_; 
lean_inc_ref(v_file_4262_);
if (v_isShared_4273_ == 0)
{
lean_ctor_set(v___x_4272_, 2, v_file_4262_);
lean_ctor_set(v___x_4272_, 1, v_file_4262_);
v___x_4275_ = v___x_4272_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_descr_4269_);
lean_ctor_set(v_reuseFailAlloc_4277_, 1, v_file_4262_);
lean_ctor_set(v_reuseFailAlloc_4277_, 2, v_file_4262_);
lean_ctor_set(v_reuseFailAlloc_4277_, 3, v_mtime_4270_);
v___x_4275_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
lean_object* v___x_4276_; 
v___x_4276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4276_, 0, v___x_4275_);
lean_ctor_set(v___x_4276_, 1, v___y_4268_);
return v___x_4276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_restoreArtifact___boxed(lean_object* v_file_4339_, lean_object* v_art_4340_, lean_object* v_exe_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_){
_start:
{
uint8_t v_exe_boxed_4344_; lean_object* v_res_4345_; 
v_exe_boxed_4344_ = lean_unbox(v_exe_4341_);
v_res_4345_ = l_Lake_restoreArtifact(v_file_4339_, v_art_4340_, v_exe_boxed_4344_, v_a_4342_);
return v_res_4345_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(lean_object* v_val_4346_, lean_object* v_a_x3f_4347_, lean_object* v___y_4348_){
_start:
{
lean_object* v___x_4350_; lean_object* v_log_4351_; uint8_t v_action_4352_; uint8_t v_wantsRebuild_4353_; lean_object* v_trace_4354_; lean_object* v_buildTime_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4366_; 
v___x_4350_ = lean_io_mono_ms_now();
v_log_4351_ = lean_ctor_get(v___y_4348_, 0);
v_action_4352_ = lean_ctor_get_uint8(v___y_4348_, sizeof(void*)*3);
v_wantsRebuild_4353_ = lean_ctor_get_uint8(v___y_4348_, sizeof(void*)*3 + 1);
v_trace_4354_ = lean_ctor_get(v___y_4348_, 1);
v_buildTime_4355_ = lean_ctor_get(v___y_4348_, 2);
v_isSharedCheck_4366_ = !lean_is_exclusive(v___y_4348_);
if (v_isSharedCheck_4366_ == 0)
{
v___x_4357_ = v___y_4348_;
v_isShared_4358_ = v_isSharedCheck_4366_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_buildTime_4355_);
lean_inc(v_trace_4354_);
lean_inc(v_log_4351_);
lean_dec(v___y_4348_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4366_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4363_; 
v___x_4359_ = lean_nat_sub(v___x_4350_, v_val_4346_);
lean_dec(v___x_4350_);
v___x_4360_ = lean_box(0);
v___x_4361_ = lean_nat_add(v_buildTime_4355_, v___x_4359_);
lean_dec(v___x_4359_);
lean_dec(v_buildTime_4355_);
if (v_isShared_4358_ == 0)
{
lean_ctor_set(v___x_4357_, 2, v___x_4361_);
v___x_4363_ = v___x_4357_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_log_4351_);
lean_ctor_set(v_reuseFailAlloc_4365_, 1, v_trace_4354_);
lean_ctor_set(v_reuseFailAlloc_4365_, 2, v___x_4361_);
lean_ctor_set_uint8(v_reuseFailAlloc_4365_, sizeof(void*)*3, v_action_4352_);
lean_ctor_set_uint8(v_reuseFailAlloc_4365_, sizeof(void*)*3 + 1, v_wantsRebuild_4353_);
v___x_4363_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
lean_object* v___x_4364_; 
v___x_4364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4364_, 0, v___x_4360_);
lean_ctor_set(v___x_4364_, 1, v___x_4363_);
return v___x_4364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0___boxed(lean_object* v_val_4367_, lean_object* v_a_x3f_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
lean_object* v_res_4371_; 
v_res_4371_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v_val_4367_, v_a_x3f_4368_, v___y_4369_);
lean_dec(v_a_x3f_4368_);
lean_dec(v_val_4367_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(lean_object* v_file_4372_, lean_object* v_build_4373_, lean_object* v_traceFile_4374_, lean_object* v_ext_4375_, uint8_t v_text_4376_, lean_object* v_a_4377_, lean_object* v_depTrace_4378_, lean_object* v_traceFile_4379_, uint8_t v_action_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_){
_start:
{
lean_object* v_a_4388_; lean_object* v_a_4389_; lean_object* v_log_4392_; uint8_t v_action_4393_; uint8_t v_wantsRebuild_4394_; lean_object* v_trace_4395_; lean_object* v_buildTime_4396_; lean_object* v_toBuildConfig_4402_; lean_object* v_log_4403_; uint8_t v_action_4404_; uint8_t v_wantsRebuild_4405_; lean_object* v_trace_4406_; lean_object* v_buildTime_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4586_; 
v_toBuildConfig_4402_ = lean_ctor_get(v_a_4384_, 0);
v_log_4403_ = lean_ctor_get(v_a_4385_, 0);
v_action_4404_ = lean_ctor_get_uint8(v_a_4385_, sizeof(void*)*3);
v_wantsRebuild_4405_ = lean_ctor_get_uint8(v_a_4385_, sizeof(void*)*3 + 1);
v_trace_4406_ = lean_ctor_get(v_a_4385_, 1);
v_buildTime_4407_ = lean_ctor_get(v_a_4385_, 2);
v_isSharedCheck_4586_ = !lean_is_exclusive(v_a_4385_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4409_ = v_a_4385_;
v_isShared_4410_ = v_isSharedCheck_4586_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_buildTime_4407_);
lean_inc(v_trace_4406_);
lean_inc(v_log_4403_);
lean_dec(v_a_4385_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4586_;
goto v_resetjp_4408_;
}
v___jp_4387_:
{
lean_object* v___x_4390_; 
v___x_4390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4390_, 0, v_a_4388_);
lean_ctor_set(v___x_4390_, 1, v_a_4389_);
return v___x_4390_;
}
v___jp_4391_:
{
lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; 
v___x_4397_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_4398_ = lean_array_get_size(v_log_4392_);
v___x_4399_ = lean_array_push(v_log_4392_, v___x_4397_);
v___x_4400_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4400_, 0, v___x_4399_);
lean_ctor_set(v___x_4400_, 1, v_trace_4395_);
lean_ctor_set(v___x_4400_, 2, v_buildTime_4396_);
lean_ctor_set_uint8(v___x_4400_, sizeof(void*)*3, v_action_4393_);
lean_ctor_set_uint8(v___x_4400_, sizeof(void*)*3 + 1, v_wantsRebuild_4394_);
v___x_4401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4401_, 0, v___x_4398_);
lean_ctor_set(v___x_4401_, 1, v___x_4400_);
return v___x_4401_;
}
v_resetjp_4408_:
{
uint8_t v_noBuild_4411_; uint8_t v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v_noBuild_4411_ = lean_ctor_get_uint8(v_toBuildConfig_4402_, sizeof(void*)*2 + 2);
v___x_4412_ = l_Lake_JobAction_merge(v_action_4404_, v_action_4380_);
v___x_4413_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_4379_);
v___x_4414_ = l_System_FilePath_addExtension(v_traceFile_4379_, v___x_4413_);
if (v_noBuild_4411_ == 0)
{
lean_object* v___x_4415_; lean_object* v_a_4417_; lean_object* v_a_4418_; lean_object* v___x_4422_; 
v___x_4415_ = lean_io_mono_ms_now();
v___x_4422_ = l_Lake_removeFileIfExists(v_file_4372_);
if (lean_obj_tag(v___x_4422_) == 0)
{
lean_object* v___x_4424_; 
lean_dec_ref(v___x_4422_);
lean_inc_ref(v_log_4403_);
if (v_isShared_4410_ == 0)
{
v___x_4424_ = v___x_4409_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_log_4403_);
lean_ctor_set(v_reuseFailAlloc_4561_, 1, v_trace_4406_);
lean_ctor_set(v_reuseFailAlloc_4561_, 2, v_buildTime_4407_);
lean_ctor_set_uint8(v_reuseFailAlloc_4561_, sizeof(void*)*3 + 1, v_wantsRebuild_4405_);
v___x_4424_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
lean_object* v___x_4425_; 
lean_ctor_set_uint8(v___x_4424_, sizeof(void*)*3, v___x_4412_);
lean_inc_ref(v_a_4384_);
v___x_4425_ = lean_apply_7(v_build_4373_, v_a_4377_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v___x_4424_, lean_box(0));
if (lean_obj_tag(v___x_4425_) == 0)
{
lean_object* v_a_4426_; lean_object* v_log_4427_; uint8_t v_action_4428_; uint8_t v_wantsRebuild_4429_; lean_object* v_trace_4430_; lean_object* v_buildTime_4431_; lean_object* v___x_4432_; 
v_a_4426_ = lean_ctor_get(v___x_4425_, 1);
lean_inc(v_a_4426_);
lean_dec_ref(v___x_4425_);
v_log_4427_ = lean_ctor_get(v_a_4426_, 0);
v_action_4428_ = lean_ctor_get_uint8(v_a_4426_, sizeof(void*)*3);
v_wantsRebuild_4429_ = lean_ctor_get_uint8(v_a_4426_, sizeof(void*)*3 + 1);
v_trace_4430_ = lean_ctor_get(v_a_4426_, 1);
v_buildTime_4431_ = lean_ctor_get(v_a_4426_, 2);
lean_inc_ref(v_file_4372_);
v___x_4432_ = l_Lake_clearFileHash(v_file_4372_);
if (lean_obj_tag(v___x_4432_) == 0)
{
lean_object* v___x_4433_; 
lean_dec_ref(v___x_4432_);
v___x_4433_ = l_Lake_removeFileIfExists(v_traceFile_4374_);
if (lean_obj_tag(v___x_4433_) == 0)
{
lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4525_; 
v_isSharedCheck_4525_ = !lean_is_exclusive(v___x_4433_);
if (v_isSharedCheck_4525_ == 0)
{
lean_object* v_unused_4526_; 
v_unused_4526_ = lean_ctor_get(v___x_4433_, 0);
lean_dec(v_unused_4526_);
v___x_4435_ = v___x_4433_;
v_isShared_4436_ = v_isSharedCheck_4525_;
goto v_resetjp_4434_;
}
else
{
lean_dec(v___x_4433_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4525_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4437_; 
v___x_4437_ = l_Lake_computeArtifact___redArg(v_file_4372_, v_ext_4375_, v_text_4376_, v_a_4384_, v_a_4426_);
lean_dec_ref(v_a_4384_);
if (lean_obj_tag(v___x_4437_) == 0)
{
lean_object* v_a_4438_; lean_object* v_a_4439_; lean_object* v_descr_4440_; lean_object* v_log_4441_; uint8_t v_action_4442_; uint8_t v_wantsRebuild_4443_; lean_object* v_trace_4444_; lean_object* v_buildTime_4445_; uint64_t v_hash_4446_; lean_object* v_ext_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___y_4452_; lean_object* v___x_4515_; lean_object* v___x_4516_; uint8_t v___x_4517_; 
v_a_4438_ = lean_ctor_get(v___x_4437_, 1);
lean_inc(v_a_4438_);
v_a_4439_ = lean_ctor_get(v___x_4437_, 0);
lean_inc(v_a_4439_);
lean_dec_ref(v___x_4437_);
v_descr_4440_ = lean_ctor_get(v_a_4439_, 0);
v_log_4441_ = lean_ctor_get(v_a_4438_, 0);
v_action_4442_ = lean_ctor_get_uint8(v_a_4438_, sizeof(void*)*3);
v_wantsRebuild_4443_ = lean_ctor_get_uint8(v_a_4438_, sizeof(void*)*3 + 1);
v_trace_4444_ = lean_ctor_get(v_a_4438_, 1);
v_buildTime_4445_ = lean_ctor_get(v_a_4438_, 2);
v_hash_4446_ = lean_ctor_get_uint64(v_descr_4440_, sizeof(void*)*1);
v_ext_4447_ = lean_ctor_get(v_descr_4440_, 0);
v___x_4448_ = lean_array_get_size(v_log_4403_);
lean_dec_ref(v_log_4403_);
v___x_4449_ = lean_array_get_size(v_log_4441_);
v___x_4450_ = l_Array_extract___redArg(v_log_4441_, v___x_4448_, v___x_4449_);
v___x_4515_ = lean_string_utf8_byte_size(v_ext_4447_);
v___x_4516_ = lean_unsigned_to_nat(0u);
v___x_4517_ = lean_nat_dec_eq(v___x_4515_, v___x_4516_);
if (v___x_4517_ == 0)
{
lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; 
v___x_4518_ = l_Lake_Hash_hex(v_hash_4446_);
v___x_4519_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_4520_ = lean_string_append(v___x_4518_, v___x_4519_);
v___x_4521_ = lean_string_append(v___x_4520_, v_ext_4447_);
v___y_4452_ = v___x_4521_;
goto v___jp_4451_;
}
else
{
lean_object* v___x_4522_; 
v___x_4522_ = l_Lake_Hash_hex(v_hash_4446_);
v___y_4452_ = v___x_4522_;
goto v___jp_4451_;
}
v___jp_4451_:
{
lean_object* v___x_4454_; 
if (v_isShared_4436_ == 0)
{
lean_ctor_set_tag(v___x_4435_, 3);
lean_ctor_set(v___x_4435_, 0, v___y_4452_);
v___x_4454_ = v___x_4435_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v___y_4452_);
v___x_4454_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
lean_object* v___x_4455_; lean_object* v___x_4456_; 
v___x_4455_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_4378_, v___x_4454_, v___x_4450_);
v___x_4456_ = l_Lake_BuildMetadata_writeFile(v_traceFile_4379_, v___x_4455_);
if (lean_obj_tag(v___x_4456_) == 0)
{
lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4497_; 
v_isSharedCheck_4497_ = !lean_is_exclusive(v___x_4456_);
if (v_isSharedCheck_4497_ == 0)
{
lean_object* v_unused_4498_; 
v_unused_4498_ = lean_ctor_get(v___x_4456_, 0);
lean_dec(v_unused_4498_);
v___x_4458_ = v___x_4456_;
v_isShared_4459_ = v_isSharedCheck_4497_;
goto v_resetjp_4457_;
}
else
{
lean_dec(v___x_4456_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4497_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v___x_4460_; 
v___x_4460_ = l_Lake_removeFileIfExists(v___x_4414_);
lean_dec_ref(v___x_4414_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4480_; 
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4480_ == 0)
{
lean_object* v_unused_4481_; 
v_unused_4481_ = lean_ctor_get(v___x_4460_, 0);
lean_dec(v_unused_4481_);
v___x_4462_ = v___x_4460_;
v_isShared_4463_ = v_isSharedCheck_4480_;
goto v_resetjp_4461_;
}
else
{
lean_dec(v___x_4460_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4480_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4465_; 
lean_inc(v_a_4439_);
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 0, v_a_4439_);
v___x_4465_ = v___x_4462_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_a_4439_);
v___x_4465_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
lean_object* v___x_4467_; 
if (v_isShared_4459_ == 0)
{
lean_ctor_set_tag(v___x_4458_, 1);
lean_ctor_set(v___x_4458_, 0, v___x_4465_);
v___x_4467_ = v___x_4458_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v___x_4465_);
v___x_4467_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
lean_object* v___x_4468_; lean_object* v_a_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4476_; 
v___x_4468_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v___x_4415_, v___x_4467_, v_a_4438_);
lean_dec_ref(v___x_4467_);
lean_dec(v___x_4415_);
v_a_4469_ = lean_ctor_get(v___x_4468_, 1);
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4468_);
if (v_isSharedCheck_4476_ == 0)
{
lean_object* v_unused_4477_; 
v_unused_4477_ = lean_ctor_get(v___x_4468_, 0);
lean_dec(v_unused_4477_);
v___x_4471_ = v___x_4468_;
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_a_4469_);
lean_dec(v___x_4468_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4474_; 
if (v_isShared_4472_ == 0)
{
lean_ctor_set(v___x_4471_, 0, v_a_4439_);
v___x_4474_ = v___x_4471_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_a_4439_);
lean_ctor_set(v_reuseFailAlloc_4475_, 1, v_a_4469_);
v___x_4474_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
return v___x_4474_;
}
}
}
}
}
}
else
{
lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4493_; 
lean_inc(v_buildTime_4445_);
lean_inc_ref(v_trace_4444_);
lean_inc_ref(v_log_4441_);
lean_del_object(v___x_4458_);
lean_dec(v_a_4439_);
v_isSharedCheck_4493_ = !lean_is_exclusive(v_a_4438_);
if (v_isSharedCheck_4493_ == 0)
{
lean_object* v_unused_4494_; lean_object* v_unused_4495_; lean_object* v_unused_4496_; 
v_unused_4494_ = lean_ctor_get(v_a_4438_, 2);
lean_dec(v_unused_4494_);
v_unused_4495_ = lean_ctor_get(v_a_4438_, 1);
lean_dec(v_unused_4495_);
v_unused_4496_ = lean_ctor_get(v_a_4438_, 0);
lean_dec(v_unused_4496_);
v___x_4483_ = v_a_4438_;
v_isShared_4484_ = v_isSharedCheck_4493_;
goto v_resetjp_4482_;
}
else
{
lean_dec(v_a_4438_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4493_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v_a_4485_; lean_object* v___x_4486_; uint8_t v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4491_; 
v_a_4485_ = lean_ctor_get(v___x_4460_, 0);
lean_inc(v_a_4485_);
lean_dec_ref(v___x_4460_);
v___x_4486_ = lean_io_error_to_string(v_a_4485_);
v___x_4487_ = 3;
v___x_4488_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4488_, 0, v___x_4486_);
lean_ctor_set_uint8(v___x_4488_, sizeof(void*)*1, v___x_4487_);
v___x_4489_ = lean_array_push(v_log_4441_, v___x_4488_);
if (v_isShared_4484_ == 0)
{
lean_ctor_set(v___x_4483_, 0, v___x_4489_);
v___x_4491_ = v___x_4483_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v___x_4489_);
lean_ctor_set(v_reuseFailAlloc_4492_, 1, v_trace_4444_);
lean_ctor_set(v_reuseFailAlloc_4492_, 2, v_buildTime_4445_);
lean_ctor_set_uint8(v_reuseFailAlloc_4492_, sizeof(void*)*3, v_action_4442_);
lean_ctor_set_uint8(v_reuseFailAlloc_4492_, sizeof(void*)*3 + 1, v_wantsRebuild_4443_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
v_a_4417_ = v___x_4449_;
v_a_4418_ = v___x_4491_;
goto v___jp_4416_;
}
}
}
}
}
else
{
lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4510_; 
lean_inc(v_buildTime_4445_);
lean_inc_ref(v_trace_4444_);
lean_inc_ref(v_log_4441_);
lean_dec(v_a_4439_);
lean_dec_ref(v___x_4414_);
v_isSharedCheck_4510_ = !lean_is_exclusive(v_a_4438_);
if (v_isSharedCheck_4510_ == 0)
{
lean_object* v_unused_4511_; lean_object* v_unused_4512_; lean_object* v_unused_4513_; 
v_unused_4511_ = lean_ctor_get(v_a_4438_, 2);
lean_dec(v_unused_4511_);
v_unused_4512_ = lean_ctor_get(v_a_4438_, 1);
lean_dec(v_unused_4512_);
v_unused_4513_ = lean_ctor_get(v_a_4438_, 0);
lean_dec(v_unused_4513_);
v___x_4500_ = v_a_4438_;
v_isShared_4501_ = v_isSharedCheck_4510_;
goto v_resetjp_4499_;
}
else
{
lean_dec(v_a_4438_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4510_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v_a_4502_; lean_object* v___x_4503_; uint8_t v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4508_; 
v_a_4502_ = lean_ctor_get(v___x_4456_, 0);
lean_inc(v_a_4502_);
lean_dec_ref(v___x_4456_);
v___x_4503_ = lean_io_error_to_string(v_a_4502_);
v___x_4504_ = 3;
v___x_4505_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4505_, 0, v___x_4503_);
lean_ctor_set_uint8(v___x_4505_, sizeof(void*)*1, v___x_4504_);
v___x_4506_ = lean_array_push(v_log_4441_, v___x_4505_);
if (v_isShared_4501_ == 0)
{
lean_ctor_set(v___x_4500_, 0, v___x_4506_);
v___x_4508_ = v___x_4500_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v___x_4506_);
lean_ctor_set(v_reuseFailAlloc_4509_, 1, v_trace_4444_);
lean_ctor_set(v_reuseFailAlloc_4509_, 2, v_buildTime_4445_);
lean_ctor_set_uint8(v_reuseFailAlloc_4509_, sizeof(void*)*3, v_action_4442_);
lean_ctor_set_uint8(v_reuseFailAlloc_4509_, sizeof(void*)*3 + 1, v_wantsRebuild_4443_);
v___x_4508_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
v_a_4417_ = v___x_4449_;
v_a_4418_ = v___x_4508_;
goto v___jp_4416_;
}
}
}
}
}
}
else
{
lean_object* v_a_4523_; lean_object* v_a_4524_; 
lean_del_object(v___x_4435_);
lean_dec_ref(v___x_4414_);
lean_dec_ref(v_log_4403_);
lean_dec_ref(v_traceFile_4379_);
v_a_4523_ = lean_ctor_get(v___x_4437_, 0);
lean_inc(v_a_4523_);
v_a_4524_ = lean_ctor_get(v___x_4437_, 1);
lean_inc(v_a_4524_);
lean_dec_ref(v___x_4437_);
v_a_4417_ = v_a_4523_;
v_a_4418_ = v_a_4524_;
goto v___jp_4416_;
}
}
}
else
{
lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4539_; 
lean_inc(v_buildTime_4431_);
lean_inc_ref(v_trace_4430_);
lean_inc_ref(v_log_4427_);
lean_dec_ref(v___x_4414_);
lean_dec_ref(v_log_4403_);
lean_dec_ref(v_a_4384_);
lean_dec_ref(v_traceFile_4379_);
lean_dec_ref(v_ext_4375_);
lean_dec_ref(v_file_4372_);
v_isSharedCheck_4539_ = !lean_is_exclusive(v_a_4426_);
if (v_isSharedCheck_4539_ == 0)
{
lean_object* v_unused_4540_; lean_object* v_unused_4541_; lean_object* v_unused_4542_; 
v_unused_4540_ = lean_ctor_get(v_a_4426_, 2);
lean_dec(v_unused_4540_);
v_unused_4541_ = lean_ctor_get(v_a_4426_, 1);
lean_dec(v_unused_4541_);
v_unused_4542_ = lean_ctor_get(v_a_4426_, 0);
lean_dec(v_unused_4542_);
v___x_4528_ = v_a_4426_;
v_isShared_4529_ = v_isSharedCheck_4539_;
goto v_resetjp_4527_;
}
else
{
lean_dec(v_a_4426_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4539_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v_a_4530_; lean_object* v___x_4531_; uint8_t v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4537_; 
v_a_4530_ = lean_ctor_get(v___x_4433_, 0);
lean_inc(v_a_4530_);
lean_dec_ref(v___x_4433_);
v___x_4531_ = lean_io_error_to_string(v_a_4530_);
v___x_4532_ = 3;
v___x_4533_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4533_, 0, v___x_4531_);
lean_ctor_set_uint8(v___x_4533_, sizeof(void*)*1, v___x_4532_);
v___x_4534_ = lean_array_get_size(v_log_4427_);
v___x_4535_ = lean_array_push(v_log_4427_, v___x_4533_);
if (v_isShared_4529_ == 0)
{
lean_ctor_set(v___x_4528_, 0, v___x_4535_);
v___x_4537_ = v___x_4528_;
goto v_reusejp_4536_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v___x_4535_);
lean_ctor_set(v_reuseFailAlloc_4538_, 1, v_trace_4430_);
lean_ctor_set(v_reuseFailAlloc_4538_, 2, v_buildTime_4431_);
lean_ctor_set_uint8(v_reuseFailAlloc_4538_, sizeof(void*)*3, v_action_4428_);
lean_ctor_set_uint8(v_reuseFailAlloc_4538_, sizeof(void*)*3 + 1, v_wantsRebuild_4429_);
v___x_4537_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4536_;
}
v_reusejp_4536_:
{
v_a_4417_ = v___x_4534_;
v_a_4418_ = v___x_4537_;
goto v___jp_4416_;
}
}
}
}
else
{
lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4555_; 
lean_inc(v_buildTime_4431_);
lean_inc_ref(v_trace_4430_);
lean_inc_ref(v_log_4427_);
lean_dec_ref(v___x_4414_);
lean_dec_ref(v_log_4403_);
lean_dec_ref(v_a_4384_);
lean_dec_ref(v_traceFile_4379_);
lean_dec_ref(v_ext_4375_);
lean_dec_ref(v_file_4372_);
v_isSharedCheck_4555_ = !lean_is_exclusive(v_a_4426_);
if (v_isSharedCheck_4555_ == 0)
{
lean_object* v_unused_4556_; lean_object* v_unused_4557_; lean_object* v_unused_4558_; 
v_unused_4556_ = lean_ctor_get(v_a_4426_, 2);
lean_dec(v_unused_4556_);
v_unused_4557_ = lean_ctor_get(v_a_4426_, 1);
lean_dec(v_unused_4557_);
v_unused_4558_ = lean_ctor_get(v_a_4426_, 0);
lean_dec(v_unused_4558_);
v___x_4544_ = v_a_4426_;
v_isShared_4545_ = v_isSharedCheck_4555_;
goto v_resetjp_4543_;
}
else
{
lean_dec(v_a_4426_);
v___x_4544_ = lean_box(0);
v_isShared_4545_ = v_isSharedCheck_4555_;
goto v_resetjp_4543_;
}
v_resetjp_4543_:
{
lean_object* v_a_4546_; lean_object* v___x_4547_; uint8_t v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4553_; 
v_a_4546_ = lean_ctor_get(v___x_4432_, 0);
lean_inc(v_a_4546_);
lean_dec_ref(v___x_4432_);
v___x_4547_ = lean_io_error_to_string(v_a_4546_);
v___x_4548_ = 3;
v___x_4549_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4549_, 0, v___x_4547_);
lean_ctor_set_uint8(v___x_4549_, sizeof(void*)*1, v___x_4548_);
v___x_4550_ = lean_array_get_size(v_log_4427_);
v___x_4551_ = lean_array_push(v_log_4427_, v___x_4549_);
if (v_isShared_4545_ == 0)
{
lean_ctor_set(v___x_4544_, 0, v___x_4551_);
v___x_4553_ = v___x_4544_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4554_; 
v_reuseFailAlloc_4554_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4554_, 0, v___x_4551_);
lean_ctor_set(v_reuseFailAlloc_4554_, 1, v_trace_4430_);
lean_ctor_set(v_reuseFailAlloc_4554_, 2, v_buildTime_4431_);
lean_ctor_set_uint8(v_reuseFailAlloc_4554_, sizeof(void*)*3, v_action_4428_);
lean_ctor_set_uint8(v_reuseFailAlloc_4554_, sizeof(void*)*3 + 1, v_wantsRebuild_4429_);
v___x_4553_ = v_reuseFailAlloc_4554_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
v_a_4417_ = v___x_4550_;
v_a_4418_ = v___x_4553_;
goto v___jp_4416_;
}
}
}
}
else
{
lean_object* v_a_4559_; lean_object* v_a_4560_; 
lean_dec_ref(v___x_4414_);
lean_dec_ref(v_log_4403_);
lean_dec_ref(v_a_4384_);
lean_dec_ref(v_traceFile_4379_);
lean_dec_ref(v_ext_4375_);
lean_dec_ref(v_file_4372_);
v_a_4559_ = lean_ctor_get(v___x_4425_, 0);
lean_inc(v_a_4559_);
v_a_4560_ = lean_ctor_get(v___x_4425_, 1);
lean_inc(v_a_4560_);
lean_dec_ref(v___x_4425_);
v_a_4417_ = v_a_4559_;
v_a_4418_ = v_a_4560_;
goto v___jp_4416_;
}
}
}
else
{
lean_object* v_a_4562_; lean_object* v___x_4563_; uint8_t v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4569_; 
lean_dec_ref(v___x_4414_);
lean_dec_ref(v_a_4384_);
lean_dec(v_a_4383_);
lean_dec(v_a_4382_);
lean_dec(v_a_4381_);
lean_dec_ref(v_traceFile_4379_);
lean_dec_ref(v_a_4377_);
lean_dec_ref(v_ext_4375_);
lean_dec_ref(v_build_4373_);
lean_dec_ref(v_file_4372_);
v_a_4562_ = lean_ctor_get(v___x_4422_, 0);
lean_inc(v_a_4562_);
lean_dec_ref(v___x_4422_);
v___x_4563_ = lean_io_error_to_string(v_a_4562_);
v___x_4564_ = 3;
v___x_4565_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4565_, 0, v___x_4563_);
lean_ctor_set_uint8(v___x_4565_, sizeof(void*)*1, v___x_4564_);
v___x_4566_ = lean_array_get_size(v_log_4403_);
v___x_4567_ = lean_array_push(v_log_4403_, v___x_4565_);
if (v_isShared_4410_ == 0)
{
lean_ctor_set(v___x_4409_, 0, v___x_4567_);
v___x_4569_ = v___x_4409_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v___x_4567_);
lean_ctor_set(v_reuseFailAlloc_4570_, 1, v_trace_4406_);
lean_ctor_set(v_reuseFailAlloc_4570_, 2, v_buildTime_4407_);
lean_ctor_set_uint8(v_reuseFailAlloc_4570_, sizeof(void*)*3 + 1, v_wantsRebuild_4405_);
v___x_4569_ = v_reuseFailAlloc_4570_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
lean_ctor_set_uint8(v___x_4569_, sizeof(void*)*3, v___x_4412_);
v_a_4417_ = v___x_4566_;
v_a_4418_ = v___x_4569_;
goto v___jp_4416_;
}
}
v___jp_4416_:
{
lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v_a_4421_; 
v___x_4419_ = lean_box(0);
v___x_4420_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v___x_4415_, v___x_4419_, v_a_4418_);
lean_dec(v___x_4415_);
v_a_4421_ = lean_ctor_get(v___x_4420_, 1);
lean_inc(v_a_4421_);
lean_dec_ref(v___x_4420_);
v_a_4388_ = v_a_4417_;
v_a_4389_ = v_a_4421_;
goto v___jp_4387_;
}
}
else
{
uint8_t v___x_4571_; 
lean_dec_ref(v_a_4384_);
lean_dec(v_a_4383_);
lean_dec(v_a_4382_);
lean_dec(v_a_4381_);
lean_dec_ref(v_a_4377_);
lean_dec_ref(v_ext_4375_);
lean_dec_ref(v_build_4373_);
lean_dec_ref(v_file_4372_);
v___x_4571_ = l_System_FilePath_pathExists(v_traceFile_4379_);
lean_dec_ref(v_traceFile_4379_);
if (v___x_4571_ == 0)
{
lean_dec_ref(v___x_4414_);
lean_del_object(v___x_4409_);
v_log_4392_ = v_log_4403_;
v_action_4393_ = v___x_4412_;
v_wantsRebuild_4394_ = v_noBuild_4411_;
v_trace_4395_ = v_trace_4406_;
v_buildTime_4396_ = v_buildTime_4407_;
goto v___jp_4391_;
}
else
{
lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; 
v___x_4572_ = lean_box(0);
v___x_4573_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_4574_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_4378_, v___x_4572_, v___x_4573_);
v___x_4575_ = l_Lake_BuildMetadata_writeFile(v___x_4414_, v___x_4574_);
if (lean_obj_tag(v___x_4575_) == 0)
{
lean_dec_ref(v___x_4575_);
lean_del_object(v___x_4409_);
v_log_4392_ = v_log_4403_;
v_action_4393_ = v___x_4412_;
v_wantsRebuild_4394_ = v_noBuild_4411_;
v_trace_4395_ = v_trace_4406_;
v_buildTime_4396_ = v_buildTime_4407_;
goto v___jp_4391_;
}
else
{
lean_object* v_a_4576_; lean_object* v___x_4577_; uint8_t v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4583_; 
v_a_4576_ = lean_ctor_get(v___x_4575_, 0);
lean_inc(v_a_4576_);
lean_dec_ref(v___x_4575_);
v___x_4577_ = lean_io_error_to_string(v_a_4576_);
v___x_4578_ = 3;
v___x_4579_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4579_, 0, v___x_4577_);
lean_ctor_set_uint8(v___x_4579_, sizeof(void*)*1, v___x_4578_);
v___x_4580_ = lean_array_get_size(v_log_4403_);
v___x_4581_ = lean_array_push(v_log_4403_, v___x_4579_);
if (v_isShared_4410_ == 0)
{
lean_ctor_set(v___x_4409_, 0, v___x_4581_);
v___x_4583_ = v___x_4409_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v___x_4581_);
lean_ctor_set(v_reuseFailAlloc_4585_, 1, v_trace_4406_);
lean_ctor_set(v_reuseFailAlloc_4585_, 2, v_buildTime_4407_);
v___x_4583_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
lean_object* v___x_4584_; 
lean_ctor_set_uint8(v___x_4583_, sizeof(void*)*3, v___x_4412_);
lean_ctor_set_uint8(v___x_4583_, sizeof(void*)*3 + 1, v_noBuild_4411_);
v___x_4584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4584_, 0, v___x_4580_);
lean_ctor_set(v___x_4584_, 1, v___x_4583_);
return v___x_4584_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___boxed(lean_object* v_file_4587_, lean_object* v_build_4588_, lean_object* v_traceFile_4589_, lean_object* v_ext_4590_, lean_object* v_text_4591_, lean_object* v_a_4592_, lean_object* v_depTrace_4593_, lean_object* v_traceFile_4594_, lean_object* v_action_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_){
_start:
{
uint8_t v_text_boxed_4602_; uint8_t v_action_boxed_4603_; lean_object* v_res_4604_; 
v_text_boxed_4602_ = lean_unbox(v_text_4591_);
v_action_boxed_4603_ = lean_unbox(v_action_4595_);
v_res_4604_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(v_file_4587_, v_build_4588_, v_traceFile_4589_, v_ext_4590_, v_text_boxed_4602_, v_a_4592_, v_depTrace_4593_, v_traceFile_4594_, v_action_boxed_4603_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_);
lean_dec_ref(v_depTrace_4593_);
lean_dec_ref(v_traceFile_4589_);
return v_res_4604_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(lean_object* v_file_4605_, lean_object* v_build_4606_, uint8_t v_text_4607_, lean_object* v_ext_4608_, lean_object* v_depTrace_4609_, lean_object* v_traceFile_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_){
_start:
{
uint8_t v___x_4618_; lean_object* v___x_4619_; 
v___x_4618_ = 3;
lean_inc_ref(v_traceFile_4610_);
v___x_4619_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(v_file_4605_, v_build_4606_, v_traceFile_4610_, v_ext_4608_, v_text_4607_, v_a_4611_, v_depTrace_4609_, v_traceFile_4610_, v___x_4618_, v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
lean_dec_ref(v_traceFile_4610_);
return v___x_4619_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild___boxed(lean_object* v_file_4620_, lean_object* v_build_4621_, lean_object* v_text_4622_, lean_object* v_ext_4623_, lean_object* v_depTrace_4624_, lean_object* v_traceFile_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_){
_start:
{
uint8_t v_text_boxed_4633_; lean_object* v_res_4634_; 
v_text_boxed_4633_ = lean_unbox(v_text_4622_);
v_res_4634_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_4620_, v_build_4621_, v_text_boxed_4633_, v_ext_4623_, v_depTrace_4624_, v_traceFile_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_);
lean_dec_ref(v_depTrace_4624_);
return v_res_4634_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(lean_object* v_art_4636_, lean_object* v_traceFile_4637_, lean_object* v_a_4638_){
_start:
{
lean_object* v_log_4640_; uint8_t v_action_4641_; uint8_t v_wantsRebuild_4642_; lean_object* v_trace_4643_; lean_object* v_buildTime_4644_; lean_object* v___x_4645_; 
v_log_4640_ = lean_ctor_get(v_a_4638_, 0);
v_action_4641_ = lean_ctor_get_uint8(v_a_4638_, sizeof(void*)*3);
v_wantsRebuild_4642_ = lean_ctor_get_uint8(v_a_4638_, sizeof(void*)*3 + 1);
v_trace_4643_ = lean_ctor_get(v_a_4638_, 1);
v_buildTime_4644_ = lean_ctor_get(v_a_4638_, 2);
v___x_4645_ = lean_io_metadata(v_traceFile_4637_);
if (lean_obj_tag(v___x_4645_) == 0)
{
lean_object* v_a_4646_; lean_object* v_modified_4647_; lean_object* v_descr_4648_; lean_object* v_path_4649_; lean_object* v_name_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4658_; 
v_a_4646_ = lean_ctor_get(v___x_4645_, 0);
lean_inc(v_a_4646_);
lean_dec_ref(v___x_4645_);
v_modified_4647_ = lean_ctor_get(v_a_4646_, 1);
lean_inc_ref(v_modified_4647_);
lean_dec(v_a_4646_);
v_descr_4648_ = lean_ctor_get(v_art_4636_, 0);
v_path_4649_ = lean_ctor_get(v_art_4636_, 1);
v_name_4650_ = lean_ctor_get(v_art_4636_, 2);
v_isSharedCheck_4658_ = !lean_is_exclusive(v_art_4636_);
if (v_isSharedCheck_4658_ == 0)
{
lean_object* v_unused_4659_; 
v_unused_4659_ = lean_ctor_get(v_art_4636_, 3);
lean_dec(v_unused_4659_);
v___x_4652_ = v_art_4636_;
v_isShared_4653_ = v_isSharedCheck_4658_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_name_4650_);
lean_inc(v_path_4649_);
lean_inc(v_descr_4648_);
lean_dec(v_art_4636_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4658_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v___x_4655_; 
if (v_isShared_4653_ == 0)
{
lean_ctor_set(v___x_4652_, 3, v_modified_4647_);
v___x_4655_ = v___x_4652_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_descr_4648_);
lean_ctor_set(v_reuseFailAlloc_4657_, 1, v_path_4649_);
lean_ctor_set(v_reuseFailAlloc_4657_, 2, v_name_4650_);
lean_ctor_set(v_reuseFailAlloc_4657_, 3, v_modified_4647_);
v___x_4655_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
lean_object* v___x_4656_; 
v___x_4656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4656_, 0, v___x_4655_);
lean_ctor_set(v___x_4656_, 1, v_a_4638_);
return v___x_4656_;
}
}
}
else
{
lean_object* v_a_4660_; 
v_a_4660_ = lean_ctor_get(v___x_4645_, 0);
lean_inc(v_a_4660_);
lean_dec_ref(v___x_4645_);
if (lean_obj_tag(v_a_4660_) == 11)
{
lean_object* v___x_4661_; 
lean_dec_ref(v_a_4660_);
v___x_4661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4661_, 0, v_art_4636_);
lean_ctor_set(v___x_4661_, 1, v_a_4638_);
return v___x_4661_;
}
else
{
lean_object* v___x_4663_; uint8_t v_isShared_4664_; uint8_t v_isSharedCheck_4676_; 
lean_inc(v_buildTime_4644_);
lean_inc_ref(v_trace_4643_);
lean_inc_ref(v_log_4640_);
lean_dec_ref(v_art_4636_);
v_isSharedCheck_4676_ = !lean_is_exclusive(v_a_4638_);
if (v_isSharedCheck_4676_ == 0)
{
lean_object* v_unused_4677_; lean_object* v_unused_4678_; lean_object* v_unused_4679_; 
v_unused_4677_ = lean_ctor_get(v_a_4638_, 2);
lean_dec(v_unused_4677_);
v_unused_4678_ = lean_ctor_get(v_a_4638_, 1);
lean_dec(v_unused_4678_);
v_unused_4679_ = lean_ctor_get(v_a_4638_, 0);
lean_dec(v_unused_4679_);
v___x_4663_ = v_a_4638_;
v_isShared_4664_ = v_isSharedCheck_4676_;
goto v_resetjp_4662_;
}
else
{
lean_dec(v_a_4638_);
v___x_4663_ = lean_box(0);
v_isShared_4664_ = v_isSharedCheck_4676_;
goto v_resetjp_4662_;
}
v_resetjp_4662_:
{
lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; uint8_t v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4673_; 
v___x_4665_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___closed__0));
v___x_4666_ = lean_io_error_to_string(v_a_4660_);
v___x_4667_ = lean_string_append(v___x_4665_, v___x_4666_);
lean_dec_ref(v___x_4666_);
v___x_4668_ = 3;
v___x_4669_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4669_, 0, v___x_4667_);
lean_ctor_set_uint8(v___x_4669_, sizeof(void*)*1, v___x_4668_);
v___x_4670_ = lean_array_get_size(v_log_4640_);
v___x_4671_ = lean_array_push(v_log_4640_, v___x_4669_);
if (v_isShared_4664_ == 0)
{
lean_ctor_set(v___x_4663_, 0, v___x_4671_);
v___x_4673_ = v___x_4663_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v___x_4671_);
lean_ctor_set(v_reuseFailAlloc_4675_, 1, v_trace_4643_);
lean_ctor_set(v_reuseFailAlloc_4675_, 2, v_buildTime_4644_);
lean_ctor_set_uint8(v_reuseFailAlloc_4675_, sizeof(void*)*3, v_action_4641_);
lean_ctor_set_uint8(v_reuseFailAlloc_4675_, sizeof(void*)*3 + 1, v_wantsRebuild_4642_);
v___x_4673_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
lean_object* v___x_4674_; 
v___x_4674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4674_, 0, v___x_4670_);
lean_ctor_set(v___x_4674_, 1, v___x_4673_);
return v___x_4674_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___boxed(lean_object* v_art_4680_, lean_object* v_traceFile_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_){
_start:
{
lean_object* v_res_4684_; 
v_res_4684_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_4680_, v_traceFile_4681_, v_a_4682_);
lean_dec_ref(v_traceFile_4681_);
return v_res_4684_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(lean_object* v_art_4685_, lean_object* v_traceFile_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_){
_start:
{
lean_object* v___x_4694_; 
v___x_4694_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_4685_, v_traceFile_4686_, v_a_4692_);
return v___x_4694_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___boxed(lean_object* v_art_4695_, lean_object* v_traceFile_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_){
_start:
{
lean_object* v_res_4704_; 
v_res_4704_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(v_art_4695_, v_traceFile_4696_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_);
lean_dec_ref(v_a_4701_);
lean_dec(v_a_4700_);
lean_dec(v_a_4699_);
lean_dec(v_a_4698_);
lean_dec_ref(v_a_4697_);
lean_dec_ref(v_traceFile_4696_);
return v_res_4704_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0(lean_object* v_a_4705_, lean_object* v_____r_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_){
_start:
{
lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; 
v___x_4714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4714_, 0, v_a_4705_);
v___x_4715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4715_, 0, v___x_4714_);
v___x_4716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4716_, 0, v___x_4715_);
lean_ctor_set(v___x_4716_, 1, v___y_4712_);
return v___x_4716_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0___boxed(lean_object* v_a_4717_, lean_object* v_____r_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_){
_start:
{
lean_object* v_res_4726_; 
v_res_4726_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0(v_a_4717_, v_____r_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_);
lean_dec_ref(v___y_4723_);
lean_dec(v___y_4722_);
lean_dec(v___y_4721_);
lean_dec(v___y_4720_);
lean_dec_ref(v___y_4719_);
return v_res_4726_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(uint8_t v_exe_4727_, lean_object* v___y_4728_, uint64_t v_inputHash_4729_, lean_object* v_savedTrace_4730_, lean_object* v_pkg_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_){
_start:
{
lean_object* v___y_4739_; lean_object* v_a_4743_; lean_object* v_a_4744_; lean_object* v___y_4759_; 
if (lean_obj_tag(v_savedTrace_4730_) == 2)
{
lean_object* v_data_4774_; uint64_t v_depHash_4775_; lean_object* v_outputs_x3f_4776_; uint8_t v___x_4777_; 
v_data_4774_ = lean_ctor_get(v_savedTrace_4730_, 0);
lean_inc_ref(v_data_4774_);
lean_dec_ref(v_savedTrace_4730_);
v_depHash_4775_ = lean_ctor_get_uint64(v_data_4774_, sizeof(void*)*3);
v_outputs_x3f_4776_ = lean_ctor_get(v_data_4774_, 1);
lean_inc(v_outputs_x3f_4776_);
lean_dec_ref(v_data_4774_);
v___x_4777_ = lean_uint64_dec_eq(v_depHash_4775_, v_inputHash_4729_);
if (v___x_4777_ == 0)
{
lean_dec(v_outputs_x3f_4776_);
lean_dec_ref(v_a_4735_);
lean_dec_ref(v_pkg_4731_);
v___y_4739_ = v_a_4736_;
goto v___jp_4738_;
}
else
{
if (lean_obj_tag(v_outputs_x3f_4776_) == 1)
{
lean_object* v_val_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; 
v_val_4778_ = lean_ctor_get(v_outputs_x3f_4776_, 0);
lean_inc(v_val_4778_);
lean_dec_ref(v_outputs_x3f_4776_);
v___x_4779_ = lean_box(0);
lean_inc(v_val_4778_);
v___x_4780_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4780_, 0, v_val_4778_);
lean_ctor_set(v___x_4780_, 1, v___x_4779_);
lean_ctor_set(v___x_4780_, 2, v___x_4779_);
lean_inc_ref(v_a_4735_);
v___x_4781_ = l_Lake_resolveArtifactOutput___redArg(v___x_4780_, v_exe_4727_, v_a_4735_, v_a_4736_);
if (lean_obj_tag(v___x_4781_) == 0)
{
lean_object* v_config_4782_; lean_object* v_a_4783_; lean_object* v_a_4784_; lean_object* v_enableArtifactCache_x3f_4785_; lean_object* v_a_4787_; uint8_t v_a_4791_; lean_object* v_a_4792_; 
v_config_4782_ = lean_ctor_get(v_pkg_4731_, 6);
v_a_4783_ = lean_ctor_get(v___x_4781_, 0);
lean_inc(v_a_4783_);
v_a_4784_ = lean_ctor_get(v___x_4781_, 1);
lean_inc(v_a_4784_);
lean_dec_ref(v___x_4781_);
v_enableArtifactCache_x3f_4785_ = lean_ctor_get(v_config_4782_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_4785_) == 0)
{
lean_object* v_toContext_4823_; lean_object* v_lakeEnv_4824_; lean_object* v_enableArtifactCache_x3f_4825_; 
v_toContext_4823_ = lean_ctor_get(v_a_4735_, 1);
v_lakeEnv_4824_ = lean_ctor_get(v_toContext_4823_, 1);
v_enableArtifactCache_x3f_4825_ = lean_ctor_get(v_lakeEnv_4824_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_4825_) == 0)
{
lean_object* v_root_4826_; lean_object* v_config_4827_; lean_object* v_enableArtifactCache_x3f_4828_; 
v_root_4826_ = lean_ctor_get(v_toContext_4823_, 0);
v_config_4827_ = lean_ctor_get(v_root_4826_, 6);
v_enableArtifactCache_x3f_4828_ = lean_ctor_get(v_config_4827_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_4828_) == 0)
{
lean_dec(v_val_4778_);
lean_dec_ref(v_pkg_4731_);
v_a_4787_ = v_a_4784_;
goto v___jp_4786_;
}
else
{
lean_object* v_val_4829_; uint8_t v___x_4830_; 
v_val_4829_ = lean_ctor_get(v_enableArtifactCache_x3f_4828_, 0);
v___x_4830_ = lean_unbox(v_val_4829_);
v_a_4791_ = v___x_4830_;
v_a_4792_ = v_a_4784_;
goto v___jp_4790_;
}
}
else
{
lean_object* v_val_4831_; uint8_t v___x_4832_; 
v_val_4831_ = lean_ctor_get(v_enableArtifactCache_x3f_4825_, 0);
v___x_4832_ = lean_unbox(v_val_4831_);
v_a_4791_ = v___x_4832_;
v_a_4792_ = v_a_4784_;
goto v___jp_4790_;
}
}
else
{
lean_object* v_val_4833_; uint8_t v___x_4834_; 
v_val_4833_ = lean_ctor_get(v_enableArtifactCache_x3f_4785_, 0);
v___x_4834_ = lean_unbox(v_val_4833_);
v_a_4791_ = v___x_4834_;
v_a_4792_ = v_a_4784_;
goto v___jp_4790_;
}
v___jp_4786_:
{
lean_object* v___x_4788_; lean_object* v___x_4789_; 
v___x_4788_ = lean_box(0);
v___x_4789_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0(v_a_4783_, v___x_4788_, v___y_4728_, v_a_4732_, v_a_4733_, v_a_4734_, v_a_4735_, v_a_4787_);
lean_dec_ref(v_a_4735_);
v___y_4759_ = v___x_4789_;
goto v___jp_4758_;
}
v___jp_4790_:
{
if (v_a_4791_ == 0)
{
lean_dec(v_val_4778_);
lean_dec_ref(v_pkg_4731_);
v_a_4787_ = v_a_4792_;
goto v___jp_4786_;
}
else
{
lean_object* v_toContext_4793_; lean_object* v_log_4794_; uint8_t v_action_4795_; uint8_t v_wantsRebuild_4796_; lean_object* v_trace_4797_; lean_object* v_buildTime_4798_; lean_object* v_lakeCache_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; 
v_toContext_4793_ = lean_ctor_get(v_a_4735_, 1);
v_log_4794_ = lean_ctor_get(v_a_4792_, 0);
v_action_4795_ = lean_ctor_get_uint8(v_a_4792_, sizeof(void*)*3);
v_wantsRebuild_4796_ = lean_ctor_get_uint8(v_a_4792_, sizeof(void*)*3 + 1);
v_trace_4797_ = lean_ctor_get(v_a_4792_, 1);
v_buildTime_4798_ = lean_ctor_get(v_a_4792_, 2);
v_lakeCache_4799_ = lean_ctor_get(v_toContext_4793_, 3);
v___x_4800_ = l_Lake_Package_cacheScope(v_pkg_4731_);
lean_inc_ref(v_lakeCache_4799_);
v___x_4801_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_4799_, v___x_4800_, v_inputHash_4729_, v_val_4778_, v___x_4779_, v___x_4779_);
if (lean_obj_tag(v___x_4801_) == 0)
{
lean_object* v___x_4802_; lean_object* v___x_4803_; 
lean_dec_ref(v___x_4801_);
v___x_4802_ = lean_box(0);
v___x_4803_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0(v_a_4783_, v___x_4802_, v___y_4728_, v_a_4732_, v_a_4733_, v_a_4734_, v_a_4735_, v_a_4792_);
lean_dec_ref(v_a_4735_);
v___y_4759_ = v___x_4803_;
goto v___jp_4758_;
}
else
{
lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4819_; 
lean_inc(v_buildTime_4798_);
lean_inc_ref(v_trace_4797_);
lean_inc_ref(v_log_4794_);
v_isSharedCheck_4819_ = !lean_is_exclusive(v_a_4792_);
if (v_isSharedCheck_4819_ == 0)
{
lean_object* v_unused_4820_; lean_object* v_unused_4821_; lean_object* v_unused_4822_; 
v_unused_4820_ = lean_ctor_get(v_a_4792_, 2);
lean_dec(v_unused_4820_);
v_unused_4821_ = lean_ctor_get(v_a_4792_, 1);
lean_dec(v_unused_4821_);
v_unused_4822_ = lean_ctor_get(v_a_4792_, 0);
lean_dec(v_unused_4822_);
v___x_4805_ = v_a_4792_;
v_isShared_4806_ = v_isSharedCheck_4819_;
goto v_resetjp_4804_;
}
else
{
lean_dec(v_a_4792_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4819_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v_a_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; uint8_t v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4816_; 
v_a_4807_ = lean_ctor_get(v___x_4801_, 0);
lean_inc(v_a_4807_);
lean_dec_ref(v___x_4801_);
v___x_4808_ = ((lean_object*)(l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0));
v___x_4809_ = lean_io_error_to_string(v_a_4807_);
v___x_4810_ = lean_string_append(v___x_4808_, v___x_4809_);
lean_dec_ref(v___x_4809_);
v___x_4811_ = 2;
v___x_4812_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4812_, 0, v___x_4810_);
lean_ctor_set_uint8(v___x_4812_, sizeof(void*)*1, v___x_4811_);
v___x_4813_ = lean_box(0);
v___x_4814_ = lean_array_push(v_log_4794_, v___x_4812_);
if (v_isShared_4806_ == 0)
{
lean_ctor_set(v___x_4805_, 0, v___x_4814_);
v___x_4816_ = v___x_4805_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v___x_4814_);
lean_ctor_set(v_reuseFailAlloc_4818_, 1, v_trace_4797_);
lean_ctor_set(v_reuseFailAlloc_4818_, 2, v_buildTime_4798_);
lean_ctor_set_uint8(v_reuseFailAlloc_4818_, sizeof(void*)*3, v_action_4795_);
lean_ctor_set_uint8(v_reuseFailAlloc_4818_, sizeof(void*)*3 + 1, v_wantsRebuild_4796_);
v___x_4816_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
lean_object* v___x_4817_; 
v___x_4817_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0(v_a_4783_, v___x_4813_, v___y_4728_, v_a_4732_, v_a_4733_, v_a_4734_, v_a_4735_, v___x_4816_);
lean_dec_ref(v_a_4735_);
v___y_4759_ = v___x_4817_;
goto v___jp_4758_;
}
}
}
}
}
}
else
{
lean_object* v_a_4835_; lean_object* v_a_4836_; 
lean_dec(v_val_4778_);
lean_dec_ref(v_a_4735_);
lean_dec_ref(v_pkg_4731_);
v_a_4835_ = lean_ctor_get(v___x_4781_, 0);
lean_inc(v_a_4835_);
v_a_4836_ = lean_ctor_get(v___x_4781_, 1);
lean_inc(v_a_4836_);
lean_dec_ref(v___x_4781_);
v_a_4743_ = v_a_4835_;
v_a_4744_ = v_a_4836_;
goto v___jp_4742_;
}
}
else
{
lean_dec(v_outputs_x3f_4776_);
lean_dec_ref(v_a_4735_);
lean_dec_ref(v_pkg_4731_);
v___y_4739_ = v_a_4736_;
goto v___jp_4738_;
}
}
}
else
{
lean_dec_ref(v_a_4735_);
lean_dec_ref(v_pkg_4731_);
lean_dec(v_savedTrace_4730_);
v___y_4739_ = v_a_4736_;
goto v___jp_4738_;
}
v___jp_4738_:
{
lean_object* v___x_4740_; lean_object* v___x_4741_; 
v___x_4740_ = lean_box(0);
v___x_4741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4741_, 0, v___x_4740_);
lean_ctor_set(v___x_4741_, 1, v___y_4739_);
return v___x_4741_;
}
v___jp_4742_:
{
lean_object* v_log_4745_; uint8_t v_action_4746_; uint8_t v_wantsRebuild_4747_; lean_object* v_trace_4748_; lean_object* v_buildTime_4749_; lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4757_; 
v_log_4745_ = lean_ctor_get(v_a_4744_, 0);
v_action_4746_ = lean_ctor_get_uint8(v_a_4744_, sizeof(void*)*3);
v_wantsRebuild_4747_ = lean_ctor_get_uint8(v_a_4744_, sizeof(void*)*3 + 1);
v_trace_4748_ = lean_ctor_get(v_a_4744_, 1);
v_buildTime_4749_ = lean_ctor_get(v_a_4744_, 2);
v_isSharedCheck_4757_ = !lean_is_exclusive(v_a_4744_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4751_ = v_a_4744_;
v_isShared_4752_ = v_isSharedCheck_4757_;
goto v_resetjp_4750_;
}
else
{
lean_inc(v_buildTime_4749_);
lean_inc(v_trace_4748_);
lean_inc(v_log_4745_);
lean_dec(v_a_4744_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4757_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
lean_object* v___x_4753_; lean_object* v___x_4755_; 
v___x_4753_ = l_Array_shrink___redArg(v_log_4745_, v_a_4743_);
lean_dec(v_a_4743_);
if (v_isShared_4752_ == 0)
{
lean_ctor_set(v___x_4751_, 0, v___x_4753_);
v___x_4755_ = v___x_4751_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v___x_4753_);
lean_ctor_set(v_reuseFailAlloc_4756_, 1, v_trace_4748_);
lean_ctor_set(v_reuseFailAlloc_4756_, 2, v_buildTime_4749_);
lean_ctor_set_uint8(v_reuseFailAlloc_4756_, sizeof(void*)*3, v_action_4746_);
lean_ctor_set_uint8(v_reuseFailAlloc_4756_, sizeof(void*)*3 + 1, v_wantsRebuild_4747_);
v___x_4755_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
v___y_4739_ = v___x_4755_;
goto v___jp_4738_;
}
}
}
v___jp_4758_:
{
if (lean_obj_tag(v___y_4759_) == 0)
{
lean_object* v_a_4760_; 
v_a_4760_ = lean_ctor_get(v___y_4759_, 0);
if (lean_obj_tag(v_a_4760_) == 0)
{
lean_object* v_a_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4769_; 
lean_inc_ref(v_a_4760_);
v_a_4761_ = lean_ctor_get(v___y_4759_, 1);
v_isSharedCheck_4769_ = !lean_is_exclusive(v___y_4759_);
if (v_isSharedCheck_4769_ == 0)
{
lean_object* v_unused_4770_; 
v_unused_4770_ = lean_ctor_get(v___y_4759_, 0);
lean_dec(v_unused_4770_);
v___x_4763_ = v___y_4759_;
v_isShared_4764_ = v_isSharedCheck_4769_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_a_4761_);
lean_dec(v___y_4759_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4769_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v_a_4765_; lean_object* v___x_4767_; 
v_a_4765_ = lean_ctor_get(v_a_4760_, 0);
lean_inc(v_a_4765_);
lean_dec_ref(v_a_4760_);
if (v_isShared_4764_ == 0)
{
lean_ctor_set(v___x_4763_, 0, v_a_4765_);
v___x_4767_ = v___x_4763_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v_a_4765_);
lean_ctor_set(v_reuseFailAlloc_4768_, 1, v_a_4761_);
v___x_4767_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
return v___x_4767_;
}
}
}
else
{
lean_object* v_a_4771_; 
v_a_4771_ = lean_ctor_get(v___y_4759_, 1);
lean_inc(v_a_4771_);
lean_dec_ref(v___y_4759_);
v___y_4739_ = v_a_4771_;
goto v___jp_4738_;
}
}
else
{
lean_object* v_a_4772_; lean_object* v_a_4773_; 
v_a_4772_ = lean_ctor_get(v___y_4759_, 0);
lean_inc(v_a_4772_);
v_a_4773_ = lean_ctor_get(v___y_4759_, 1);
lean_inc(v_a_4773_);
lean_dec_ref(v___y_4759_);
v_a_4743_ = v_a_4772_;
v_a_4744_ = v_a_4773_;
goto v___jp_4742_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___boxed(lean_object* v_exe_4837_, lean_object* v___y_4838_, lean_object* v_inputHash_4839_, lean_object* v_savedTrace_4840_, lean_object* v_pkg_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_){
_start:
{
uint8_t v_exe_boxed_4848_; uint64_t v_inputHash_boxed_4849_; lean_object* v_res_4850_; 
v_exe_boxed_4848_ = lean_unbox(v_exe_4837_);
v_inputHash_boxed_4849_ = lean_unbox_uint64(v_inputHash_4839_);
lean_dec_ref(v_inputHash_4839_);
v_res_4850_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(v_exe_boxed_4848_, v___y_4838_, v_inputHash_boxed_4849_, v_savedTrace_4840_, v_pkg_4841_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_);
lean_dec(v_a_4844_);
lean_dec(v_a_4843_);
lean_dec(v_a_4842_);
lean_dec_ref(v___y_4838_);
return v_res_4850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(lean_object* v_as_4851_, size_t v_i_4852_, size_t v_stop_4853_, lean_object* v_b_4854_){
_start:
{
uint8_t v___x_4855_; 
v___x_4855_ = lean_usize_dec_eq(v_i_4852_, v_stop_4853_);
if (v___x_4855_ == 0)
{
lean_object* v___x_4856_; lean_object* v_message_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; size_t v___x_4861_; size_t v___x_4862_; 
v___x_4856_ = lean_array_uget_borrowed(v_as_4851_, v_i_4852_);
v_message_4857_ = lean_ctor_get(v___x_4856_, 0);
v___x_4858_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0));
v___x_4859_ = lean_string_append(v_b_4854_, v___x_4858_);
v___x_4860_ = lean_string_append(v___x_4859_, v_message_4857_);
v___x_4861_ = ((size_t)1ULL);
v___x_4862_ = lean_usize_add(v_i_4852_, v___x_4861_);
v_i_4852_ = v___x_4862_;
v_b_4854_ = v___x_4860_;
goto _start;
}
else
{
return v_b_4854_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0___boxed(lean_object* v_as_4864_, lean_object* v_i_4865_, lean_object* v_stop_4866_, lean_object* v_b_4867_){
_start:
{
size_t v_i_boxed_4868_; size_t v_stop_boxed_4869_; lean_object* v_res_4870_; 
v_i_boxed_4868_ = lean_unbox_usize(v_i_4865_);
lean_dec(v_i_4865_);
v_stop_boxed_4869_ = lean_unbox_usize(v_stop_4866_);
lean_dec(v_stop_4866_);
v_res_4870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(v_as_4864_, v_i_boxed_4868_, v_stop_boxed_4869_, v_b_4867_);
lean_dec_ref(v_as_4864_);
return v_res_4870_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___redArg(uint8_t v_exe_4871_, uint64_t v_inputHash_4872_, lean_object* v_pkg_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_){
_start:
{
lean_object* v_toContext_4877_; lean_object* v_log_4878_; uint8_t v_action_4879_; uint8_t v_wantsRebuild_4880_; lean_object* v_trace_4881_; lean_object* v_buildTime_4882_; lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4975_; 
v_toContext_4877_ = lean_ctor_get(v_a_4874_, 1);
v_log_4878_ = lean_ctor_get(v_a_4875_, 0);
v_action_4879_ = lean_ctor_get_uint8(v_a_4875_, sizeof(void*)*3);
v_wantsRebuild_4880_ = lean_ctor_get_uint8(v_a_4875_, sizeof(void*)*3 + 1);
v_trace_4881_ = lean_ctor_get(v_a_4875_, 1);
v_buildTime_4882_ = lean_ctor_get(v_a_4875_, 2);
v_isSharedCheck_4975_ = !lean_is_exclusive(v_a_4875_);
if (v_isSharedCheck_4975_ == 0)
{
v___x_4884_ = v_a_4875_;
v_isShared_4885_ = v_isSharedCheck_4975_;
goto v_resetjp_4883_;
}
else
{
lean_inc(v_buildTime_4882_);
lean_inc(v_trace_4881_);
lean_inc(v_log_4878_);
lean_dec(v_a_4875_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4975_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
lean_object* v_lakeCache_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; 
v_lakeCache_4886_ = lean_ctor_get(v_toContext_4877_, 3);
v___x_4887_ = l_Lake_Package_cacheScope(v_pkg_4873_);
lean_inc_ref(v_lakeCache_4886_);
v___x_4888_ = l_Lake_Cache_readOutputs_x3f(v_lakeCache_4886_, v___x_4887_, v_inputHash_4872_, v_log_4878_);
if (lean_obj_tag(v___x_4888_) == 0)
{
lean_object* v_a_4889_; lean_object* v_a_4890_; lean_object* v___x_4892_; uint8_t v_isShared_4893_; uint8_t v_isSharedCheck_4962_; 
v_a_4889_ = lean_ctor_get(v___x_4888_, 0);
v_a_4890_ = lean_ctor_get(v___x_4888_, 1);
v_isSharedCheck_4962_ = !lean_is_exclusive(v___x_4888_);
if (v_isSharedCheck_4962_ == 0)
{
v___x_4892_ = v___x_4888_;
v_isShared_4893_ = v_isSharedCheck_4962_;
goto v_resetjp_4891_;
}
else
{
lean_inc(v_a_4890_);
lean_inc(v_a_4889_);
lean_dec(v___x_4888_);
v___x_4892_ = lean_box(0);
v_isShared_4893_ = v_isSharedCheck_4962_;
goto v_resetjp_4891_;
}
v_resetjp_4891_:
{
lean_object* v___x_4895_; 
if (v_isShared_4885_ == 0)
{
lean_ctor_set(v___x_4884_, 0, v_a_4890_);
v___x_4895_ = v___x_4884_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4961_; 
v_reuseFailAlloc_4961_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4961_, 0, v_a_4890_);
lean_ctor_set(v_reuseFailAlloc_4961_, 1, v_trace_4881_);
lean_ctor_set(v_reuseFailAlloc_4961_, 2, v_buildTime_4882_);
lean_ctor_set_uint8(v_reuseFailAlloc_4961_, sizeof(void*)*3, v_action_4879_);
lean_ctor_set_uint8(v_reuseFailAlloc_4961_, sizeof(void*)*3 + 1, v_wantsRebuild_4880_);
v___x_4895_ = v_reuseFailAlloc_4961_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
if (lean_obj_tag(v_a_4889_) == 1)
{
lean_object* v_val_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4956_; 
v_val_4896_ = lean_ctor_get(v_a_4889_, 0);
v_isSharedCheck_4956_ = !lean_is_exclusive(v_a_4889_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4898_ = v_a_4889_;
v_isShared_4899_ = v_isSharedCheck_4956_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_val_4896_);
lean_dec(v_a_4889_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4956_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
lean_object* v___x_4900_; lean_object* v_r_4902_; lean_object* v___y_4903_; 
v___x_4900_ = l_Lake_resolveArtifactOutput___redArg(v_val_4896_, v_exe_4871_, v_a_4874_, v___x_4895_);
if (lean_obj_tag(v___x_4900_) == 0)
{
lean_object* v_a_4907_; lean_object* v_a_4908_; lean_object* v___x_4910_; 
v_a_4907_ = lean_ctor_get(v___x_4900_, 0);
lean_inc(v_a_4907_);
v_a_4908_ = lean_ctor_get(v___x_4900_, 1);
lean_inc(v_a_4908_);
lean_dec_ref(v___x_4900_);
if (v_isShared_4899_ == 0)
{
lean_ctor_set(v___x_4898_, 0, v_a_4907_);
v___x_4910_ = v___x_4898_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_a_4907_);
v___x_4910_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
v_r_4902_ = v___x_4910_;
v___y_4903_ = v_a_4908_;
goto v___jp_4901_;
}
}
else
{
lean_object* v_a_4912_; lean_object* v_a_4913_; lean_object* v_log_4914_; uint8_t v_action_4915_; uint8_t v_wantsRebuild_4916_; lean_object* v_trace_4917_; lean_object* v_buildTime_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4955_; 
lean_del_object(v___x_4898_);
v_a_4912_ = lean_ctor_get(v___x_4900_, 1);
lean_inc(v_a_4912_);
v_a_4913_ = lean_ctor_get(v___x_4900_, 0);
lean_inc(v_a_4913_);
lean_dec_ref(v___x_4900_);
v_log_4914_ = lean_ctor_get(v_a_4912_, 0);
v_action_4915_ = lean_ctor_get_uint8(v_a_4912_, sizeof(void*)*3);
v_wantsRebuild_4916_ = lean_ctor_get_uint8(v_a_4912_, sizeof(void*)*3 + 1);
v_trace_4917_ = lean_ctor_get(v_a_4912_, 1);
v_buildTime_4918_ = lean_ctor_get(v_a_4912_, 2);
v_isSharedCheck_4955_ = !lean_is_exclusive(v_a_4912_);
if (v_isSharedCheck_4955_ == 0)
{
v___x_4920_ = v_a_4912_;
v_isShared_4921_ = v_isSharedCheck_4955_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_buildTime_4918_);
lean_inc(v_trace_4917_);
lean_inc(v_log_4914_);
lean_dec(v_a_4912_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4955_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___y_4926_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; uint8_t v___x_4947_; 
v___x_4922_ = lean_array_get_size(v_log_4914_);
lean_inc(v_a_4913_);
v___x_4923_ = l_Array_extract___redArg(v_log_4914_, v_a_4913_, v___x_4922_);
v___x_4924_ = l_Array_shrink___redArg(v_log_4914_, v_a_4913_);
lean_dec(v_a_4913_);
v___x_4934_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0));
v___x_4935_ = l_Lake_Hash_hex(v_inputHash_4872_);
v___x_4936_ = lean_unsigned_to_nat(7u);
v___x_4937_ = lean_unsigned_to_nat(0u);
v___x_4938_ = lean_string_utf8_byte_size(v___x_4935_);
lean_inc_ref(v___x_4935_);
v___x_4939_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4939_, 0, v___x_4935_);
lean_ctor_set(v___x_4939_, 1, v___x_4937_);
lean_ctor_set(v___x_4939_, 2, v___x_4938_);
v___x_4940_ = l_String_Slice_Pos_nextn(v___x_4939_, v___x_4937_, v___x_4936_);
lean_dec_ref(v___x_4939_);
v___x_4941_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4941_, 0, v___x_4935_);
lean_ctor_set(v___x_4941_, 1, v___x_4937_);
lean_ctor_set(v___x_4941_, 2, v___x_4940_);
v___x_4942_ = l_String_Slice_toString(v___x_4941_);
lean_dec_ref(v___x_4941_);
v___x_4943_ = lean_string_append(v___x_4934_, v___x_4942_);
lean_dec_ref(v___x_4942_);
v___x_4944_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1));
v___x_4945_ = lean_string_append(v___x_4943_, v___x_4944_);
v___x_4946_ = lean_array_get_size(v___x_4923_);
v___x_4947_ = lean_nat_dec_lt(v___x_4937_, v___x_4946_);
if (v___x_4947_ == 0)
{
lean_dec_ref(v___x_4923_);
v___y_4926_ = v___x_4945_;
goto v___jp_4925_;
}
else
{
uint8_t v___x_4948_; 
v___x_4948_ = lean_nat_dec_le(v___x_4946_, v___x_4946_);
if (v___x_4948_ == 0)
{
if (v___x_4947_ == 0)
{
lean_dec_ref(v___x_4923_);
v___y_4926_ = v___x_4945_;
goto v___jp_4925_;
}
else
{
size_t v___x_4949_; size_t v___x_4950_; lean_object* v___x_4951_; 
v___x_4949_ = ((size_t)0ULL);
v___x_4950_ = lean_usize_of_nat(v___x_4946_);
v___x_4951_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(v___x_4923_, v___x_4949_, v___x_4950_, v___x_4945_);
lean_dec_ref(v___x_4923_);
v___y_4926_ = v___x_4951_;
goto v___jp_4925_;
}
}
else
{
size_t v___x_4952_; size_t v___x_4953_; lean_object* v___x_4954_; 
v___x_4952_ = ((size_t)0ULL);
v___x_4953_ = lean_usize_of_nat(v___x_4946_);
v___x_4954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(v___x_4923_, v___x_4952_, v___x_4953_, v___x_4945_);
lean_dec_ref(v___x_4923_);
v___y_4926_ = v___x_4954_;
goto v___jp_4925_;
}
}
v___jp_4925_:
{
uint8_t v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4931_; 
v___x_4927_ = 2;
v___x_4928_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4928_, 0, v___y_4926_);
lean_ctor_set_uint8(v___x_4928_, sizeof(void*)*1, v___x_4927_);
v___x_4929_ = lean_array_push(v___x_4924_, v___x_4928_);
if (v_isShared_4921_ == 0)
{
lean_ctor_set(v___x_4920_, 0, v___x_4929_);
v___x_4931_ = v___x_4920_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4933_; 
v_reuseFailAlloc_4933_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4933_, 0, v___x_4929_);
lean_ctor_set(v_reuseFailAlloc_4933_, 1, v_trace_4917_);
lean_ctor_set(v_reuseFailAlloc_4933_, 2, v_buildTime_4918_);
lean_ctor_set_uint8(v_reuseFailAlloc_4933_, sizeof(void*)*3, v_action_4915_);
lean_ctor_set_uint8(v_reuseFailAlloc_4933_, sizeof(void*)*3 + 1, v_wantsRebuild_4916_);
v___x_4931_ = v_reuseFailAlloc_4933_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
lean_object* v___x_4932_; 
v___x_4932_ = lean_box(0);
v_r_4902_ = v___x_4932_;
v___y_4903_ = v___x_4931_;
goto v___jp_4901_;
}
}
}
}
v___jp_4901_:
{
lean_object* v___x_4905_; 
if (v_isShared_4893_ == 0)
{
lean_ctor_set(v___x_4892_, 1, v___y_4903_);
lean_ctor_set(v___x_4892_, 0, v_r_4902_);
v___x_4905_ = v___x_4892_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_r_4902_);
lean_ctor_set(v_reuseFailAlloc_4906_, 1, v___y_4903_);
v___x_4905_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
return v___x_4905_;
}
}
}
}
else
{
lean_object* v___x_4957_; lean_object* v___x_4959_; 
lean_dec(v_a_4889_);
lean_dec_ref(v_a_4874_);
v___x_4957_ = lean_box(0);
if (v_isShared_4893_ == 0)
{
lean_ctor_set(v___x_4892_, 1, v___x_4895_);
lean_ctor_set(v___x_4892_, 0, v___x_4957_);
v___x_4959_ = v___x_4892_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4960_; 
v_reuseFailAlloc_4960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4960_, 0, v___x_4957_);
lean_ctor_set(v_reuseFailAlloc_4960_, 1, v___x_4895_);
v___x_4959_ = v_reuseFailAlloc_4960_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
return v___x_4959_;
}
}
}
}
}
else
{
lean_object* v_a_4963_; lean_object* v_a_4964_; lean_object* v___x_4966_; uint8_t v_isShared_4967_; uint8_t v_isSharedCheck_4974_; 
lean_dec_ref(v_a_4874_);
v_a_4963_ = lean_ctor_get(v___x_4888_, 0);
v_a_4964_ = lean_ctor_get(v___x_4888_, 1);
v_isSharedCheck_4974_ = !lean_is_exclusive(v___x_4888_);
if (v_isSharedCheck_4974_ == 0)
{
v___x_4966_ = v___x_4888_;
v_isShared_4967_ = v_isSharedCheck_4974_;
goto v_resetjp_4965_;
}
else
{
lean_inc(v_a_4964_);
lean_inc(v_a_4963_);
lean_dec(v___x_4888_);
v___x_4966_ = lean_box(0);
v_isShared_4967_ = v_isSharedCheck_4974_;
goto v_resetjp_4965_;
}
v_resetjp_4965_:
{
lean_object* v___x_4969_; 
if (v_isShared_4885_ == 0)
{
lean_ctor_set(v___x_4884_, 0, v_a_4964_);
v___x_4969_ = v___x_4884_;
goto v_reusejp_4968_;
}
else
{
lean_object* v_reuseFailAlloc_4973_; 
v_reuseFailAlloc_4973_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4973_, 0, v_a_4964_);
lean_ctor_set(v_reuseFailAlloc_4973_, 1, v_trace_4881_);
lean_ctor_set(v_reuseFailAlloc_4973_, 2, v_buildTime_4882_);
lean_ctor_set_uint8(v_reuseFailAlloc_4973_, sizeof(void*)*3, v_action_4879_);
lean_ctor_set_uint8(v_reuseFailAlloc_4973_, sizeof(void*)*3 + 1, v_wantsRebuild_4880_);
v___x_4969_ = v_reuseFailAlloc_4973_;
goto v_reusejp_4968_;
}
v_reusejp_4968_:
{
lean_object* v___x_4971_; 
if (v_isShared_4967_ == 0)
{
lean_ctor_set(v___x_4966_, 1, v___x_4969_);
v___x_4971_ = v___x_4966_;
goto v_reusejp_4970_;
}
else
{
lean_object* v_reuseFailAlloc_4972_; 
v_reuseFailAlloc_4972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4972_, 0, v_a_4963_);
lean_ctor_set(v_reuseFailAlloc_4972_, 1, v___x_4969_);
v___x_4971_ = v_reuseFailAlloc_4972_;
goto v_reusejp_4970_;
}
v_reusejp_4970_:
{
return v___x_4971_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___redArg___boxed(lean_object* v_exe_4976_, lean_object* v_inputHash_4977_, lean_object* v_pkg_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_){
_start:
{
uint8_t v_exe_boxed_4982_; uint64_t v_inputHash_boxed_4983_; lean_object* v_res_4984_; 
v_exe_boxed_4982_ = lean_unbox(v_exe_4976_);
v_inputHash_boxed_4983_ = lean_unbox_uint64(v_inputHash_4977_);
lean_dec_ref(v_inputHash_4977_);
v_res_4984_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___redArg(v_exe_boxed_4982_, v_inputHash_boxed_4983_, v_pkg_4978_, v_a_4979_, v_a_4980_);
return v_res_4984_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(uint8_t v_exe_4985_, uint64_t v_hash_4986_, lean_object* v_val_4987_, lean_object* v_file_4988_, lean_object* v___x_4989_, lean_object* v_a_4990_, uint8_t v_restore_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_){
_start:
{
lean_object* v_a_5000_; lean_object* v___y_5004_; lean_object* v___y_5005_; lean_object* v___y_5006_; lean_object* v___y_5044_; lean_object* v___y_5045_; lean_object* v___y_5046_; lean_object* v___y_5047_; lean_object* v___y_5048_; uint8_t v___y_5049_; uint8_t v___y_5050_; lean_object* v___y_5051_; lean_object* v___y_5065_; lean_object* v___x_5122_; 
lean_inc_ref(v___y_4996_);
lean_inc_ref(v_val_4987_);
v___x_5122_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___redArg(v_exe_4985_, v_hash_4986_, v_val_4987_, v___y_4996_, v___y_4997_);
if (lean_obj_tag(v___x_5122_) == 0)
{
lean_object* v_a_5123_; 
v_a_5123_ = lean_ctor_get(v___x_5122_, 0);
lean_inc(v_a_5123_);
if (lean_obj_tag(v_a_5123_) == 1)
{
lean_dec_ref(v_a_5123_);
lean_dec_ref(v___y_4996_);
lean_dec_ref(v_val_4987_);
v___y_5065_ = v___x_5122_;
goto v___jp_5064_;
}
else
{
lean_object* v_a_5124_; lean_object* v___x_5125_; lean_object* v_a_5126_; 
lean_dec(v_a_5123_);
v_a_5124_ = lean_ctor_get(v___x_5122_, 1);
lean_inc(v_a_5124_);
lean_dec_ref(v___x_5122_);
lean_inc(v_a_4990_);
v___x_5125_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(v_exe_4985_, v___y_4992_, v_hash_4986_, v_a_4990_, v_val_4987_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_, v_a_5124_);
v_a_5126_ = lean_ctor_get(v___x_5125_, 0);
lean_inc(v_a_5126_);
if (lean_obj_tag(v_a_5126_) == 1)
{
lean_dec_ref(v_a_5126_);
v___y_5065_ = v___x_5125_;
goto v___jp_5064_;
}
else
{
lean_object* v_a_5127_; 
lean_dec(v_a_5126_);
lean_dec(v_a_4990_);
lean_dec_ref(v___x_4989_);
lean_dec_ref(v_file_4988_);
v_a_5127_ = lean_ctor_get(v___x_5125_, 1);
lean_inc(v_a_5127_);
lean_dec_ref(v___x_5125_);
v_a_5000_ = v_a_5127_;
goto v___jp_4999_;
}
}
}
else
{
lean_dec_ref(v___y_4996_);
lean_dec_ref(v_val_4987_);
v___y_5065_ = v___x_5122_;
goto v___jp_5064_;
}
v___jp_4999_:
{
lean_object* v___x_5001_; lean_object* v___x_5002_; 
v___x_5001_ = lean_box(0);
v___x_5002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5002_, 0, v___x_5001_);
lean_ctor_set(v___x_5002_, 1, v_a_5000_);
return v___x_5002_;
}
v___jp_5003_:
{
if (v_restore_4991_ == 0)
{
lean_object* v___x_5007_; 
lean_dec_ref(v___y_5004_);
lean_dec_ref(v_file_4988_);
v___x_5007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5007_, 0, v___y_5005_);
lean_ctor_set(v___x_5007_, 1, v___y_5006_);
return v___x_5007_;
}
else
{
lean_object* v_log_5008_; uint8_t v_action_5009_; uint8_t v_wantsRebuild_5010_; lean_object* v_trace_5011_; lean_object* v_buildTime_5012_; lean_object* v___x_5014_; uint8_t v_isShared_5015_; uint8_t v_isSharedCheck_5042_; 
lean_dec(v___y_5005_);
v_log_5008_ = lean_ctor_get(v___y_5006_, 0);
v_action_5009_ = lean_ctor_get_uint8(v___y_5006_, sizeof(void*)*3);
v_wantsRebuild_5010_ = lean_ctor_get_uint8(v___y_5006_, sizeof(void*)*3 + 1);
v_trace_5011_ = lean_ctor_get(v___y_5006_, 1);
v_buildTime_5012_ = lean_ctor_get(v___y_5006_, 2);
v_isSharedCheck_5042_ = !lean_is_exclusive(v___y_5006_);
if (v_isSharedCheck_5042_ == 0)
{
v___x_5014_ = v___y_5006_;
v_isShared_5015_ = v_isSharedCheck_5042_;
goto v_resetjp_5013_;
}
else
{
lean_inc(v_buildTime_5012_);
lean_inc(v_trace_5011_);
lean_inc(v_log_5008_);
lean_dec(v___y_5006_);
v___x_5014_ = lean_box(0);
v_isShared_5015_ = v_isSharedCheck_5042_;
goto v_resetjp_5013_;
}
v_resetjp_5013_:
{
lean_object* v___x_5016_; 
v___x_5016_ = l_Lake_restoreArtifact(v_file_4988_, v___y_5004_, v_exe_4985_, v_log_5008_);
if (lean_obj_tag(v___x_5016_) == 0)
{
lean_object* v_a_5017_; lean_object* v_a_5018_; lean_object* v___x_5020_; uint8_t v_isShared_5021_; uint8_t v_isSharedCheck_5029_; 
v_a_5017_ = lean_ctor_get(v___x_5016_, 0);
v_a_5018_ = lean_ctor_get(v___x_5016_, 1);
v_isSharedCheck_5029_ = !lean_is_exclusive(v___x_5016_);
if (v_isSharedCheck_5029_ == 0)
{
v___x_5020_ = v___x_5016_;
v_isShared_5021_ = v_isSharedCheck_5029_;
goto v_resetjp_5019_;
}
else
{
lean_inc(v_a_5018_);
lean_inc(v_a_5017_);
lean_dec(v___x_5016_);
v___x_5020_ = lean_box(0);
v_isShared_5021_ = v_isSharedCheck_5029_;
goto v_resetjp_5019_;
}
v_resetjp_5019_:
{
lean_object* v___x_5023_; 
if (v_isShared_5015_ == 0)
{
lean_ctor_set(v___x_5014_, 0, v_a_5018_);
v___x_5023_ = v___x_5014_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v_a_5018_);
lean_ctor_set(v_reuseFailAlloc_5028_, 1, v_trace_5011_);
lean_ctor_set(v_reuseFailAlloc_5028_, 2, v_buildTime_5012_);
lean_ctor_set_uint8(v_reuseFailAlloc_5028_, sizeof(void*)*3, v_action_5009_);
lean_ctor_set_uint8(v_reuseFailAlloc_5028_, sizeof(void*)*3 + 1, v_wantsRebuild_5010_);
v___x_5023_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5022_;
}
v_reusejp_5022_:
{
lean_object* v___x_5024_; lean_object* v___x_5026_; 
v___x_5024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5024_, 0, v_a_5017_);
if (v_isShared_5021_ == 0)
{
lean_ctor_set(v___x_5020_, 1, v___x_5023_);
lean_ctor_set(v___x_5020_, 0, v___x_5024_);
v___x_5026_ = v___x_5020_;
goto v_reusejp_5025_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v___x_5024_);
lean_ctor_set(v_reuseFailAlloc_5027_, 1, v___x_5023_);
v___x_5026_ = v_reuseFailAlloc_5027_;
goto v_reusejp_5025_;
}
v_reusejp_5025_:
{
return v___x_5026_;
}
}
}
}
else
{
lean_object* v_a_5030_; lean_object* v_a_5031_; lean_object* v___x_5033_; uint8_t v_isShared_5034_; uint8_t v_isSharedCheck_5041_; 
v_a_5030_ = lean_ctor_get(v___x_5016_, 0);
v_a_5031_ = lean_ctor_get(v___x_5016_, 1);
v_isSharedCheck_5041_ = !lean_is_exclusive(v___x_5016_);
if (v_isSharedCheck_5041_ == 0)
{
v___x_5033_ = v___x_5016_;
v_isShared_5034_ = v_isSharedCheck_5041_;
goto v_resetjp_5032_;
}
else
{
lean_inc(v_a_5031_);
lean_inc(v_a_5030_);
lean_dec(v___x_5016_);
v___x_5033_ = lean_box(0);
v_isShared_5034_ = v_isSharedCheck_5041_;
goto v_resetjp_5032_;
}
v_resetjp_5032_:
{
lean_object* v___x_5036_; 
if (v_isShared_5015_ == 0)
{
lean_ctor_set(v___x_5014_, 0, v_a_5031_);
v___x_5036_ = v___x_5014_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5040_; 
v_reuseFailAlloc_5040_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5040_, 0, v_a_5031_);
lean_ctor_set(v_reuseFailAlloc_5040_, 1, v_trace_5011_);
lean_ctor_set(v_reuseFailAlloc_5040_, 2, v_buildTime_5012_);
lean_ctor_set_uint8(v_reuseFailAlloc_5040_, sizeof(void*)*3, v_action_5009_);
lean_ctor_set_uint8(v_reuseFailAlloc_5040_, sizeof(void*)*3 + 1, v_wantsRebuild_5010_);
v___x_5036_ = v_reuseFailAlloc_5040_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
lean_object* v___x_5038_; 
if (v_isShared_5034_ == 0)
{
lean_ctor_set(v___x_5033_, 1, v___x_5036_);
v___x_5038_ = v___x_5033_;
goto v_reusejp_5037_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v_a_5030_);
lean_ctor_set(v_reuseFailAlloc_5039_, 1, v___x_5036_);
v___x_5038_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5037_;
}
v_reusejp_5037_:
{
return v___x_5038_;
}
}
}
}
}
}
}
v___jp_5043_:
{
lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; 
v___x_5052_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5052_, 0, v___y_5051_);
v___x_5053_ = l_Lake_BuildMetadata_ofFetch(v_hash_4986_, v___x_5052_);
v___x_5054_ = l_Lake_BuildMetadata_writeFile(v___x_4989_, v___x_5053_);
if (lean_obj_tag(v___x_5054_) == 0)
{
lean_object* v___x_5055_; 
lean_dec_ref(v___x_5054_);
v___x_5055_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5055_, 0, v___y_5048_);
lean_ctor_set(v___x_5055_, 1, v___y_5047_);
lean_ctor_set(v___x_5055_, 2, v___y_5045_);
lean_ctor_set_uint8(v___x_5055_, sizeof(void*)*3, v___y_5049_);
lean_ctor_set_uint8(v___x_5055_, sizeof(void*)*3 + 1, v___y_5050_);
v___y_5004_ = v___y_5044_;
v___y_5005_ = v___y_5046_;
v___y_5006_ = v___x_5055_;
goto v___jp_5003_;
}
else
{
lean_object* v_a_5056_; lean_object* v___x_5057_; uint8_t v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; 
lean_dec(v___y_5046_);
lean_dec_ref(v___y_5044_);
lean_dec_ref(v_file_4988_);
v_a_5056_ = lean_ctor_get(v___x_5054_, 0);
lean_inc(v_a_5056_);
lean_dec_ref(v___x_5054_);
v___x_5057_ = lean_io_error_to_string(v_a_5056_);
v___x_5058_ = 3;
v___x_5059_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5059_, 0, v___x_5057_);
lean_ctor_set_uint8(v___x_5059_, sizeof(void*)*1, v___x_5058_);
v___x_5060_ = lean_array_get_size(v___y_5048_);
v___x_5061_ = lean_array_push(v___y_5048_, v___x_5059_);
v___x_5062_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5062_, 0, v___x_5061_);
lean_ctor_set(v___x_5062_, 1, v___y_5047_);
lean_ctor_set(v___x_5062_, 2, v___y_5045_);
lean_ctor_set_uint8(v___x_5062_, sizeof(void*)*3, v___y_5049_);
lean_ctor_set_uint8(v___x_5062_, sizeof(void*)*3 + 1, v___y_5050_);
v___x_5063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5063_, 0, v___x_5060_);
lean_ctor_set(v___x_5063_, 1, v___x_5062_);
return v___x_5063_;
}
}
v___jp_5064_:
{
if (lean_obj_tag(v___y_5065_) == 0)
{
lean_object* v_a_5066_; 
v_a_5066_ = lean_ctor_get(v___y_5065_, 0);
if (lean_obj_tag(v_a_5066_) == 1)
{
lean_object* v_a_5067_; lean_object* v_val_5068_; lean_object* v___x_5069_; 
lean_inc_ref(v_a_5066_);
v_a_5067_ = lean_ctor_get(v___y_5065_, 1);
lean_inc(v_a_5067_);
lean_dec_ref(v___y_5065_);
v_val_5068_ = lean_ctor_get(v_a_5066_, 0);
lean_inc(v_val_5068_);
v___x_5069_ = l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(v_hash_4986_, v_a_4990_, v_a_5067_);
lean_dec(v_a_4990_);
if (lean_obj_tag(v___x_5069_) == 0)
{
lean_object* v_a_5070_; uint8_t v___x_5071_; 
v_a_5070_ = lean_ctor_get(v___x_5069_, 0);
lean_inc(v_a_5070_);
v___x_5071_ = lean_unbox(v_a_5070_);
lean_dec(v_a_5070_);
if (v___x_5071_ == 0)
{
lean_object* v_a_5072_; lean_object* v___x_5074_; uint8_t v_isShared_5075_; uint8_t v_isSharedCheck_5109_; 
v_a_5072_ = lean_ctor_get(v___x_5069_, 1);
v_isSharedCheck_5109_ = !lean_is_exclusive(v___x_5069_);
if (v_isSharedCheck_5109_ == 0)
{
lean_object* v_unused_5110_; 
v_unused_5110_ = lean_ctor_get(v___x_5069_, 0);
lean_dec(v_unused_5110_);
v___x_5074_ = v___x_5069_;
v_isShared_5075_ = v_isSharedCheck_5109_;
goto v_resetjp_5073_;
}
else
{
lean_inc(v_a_5072_);
lean_dec(v___x_5069_);
v___x_5074_ = lean_box(0);
v_isShared_5075_ = v_isSharedCheck_5109_;
goto v_resetjp_5073_;
}
v_resetjp_5073_:
{
lean_object* v_log_5076_; uint8_t v_action_5077_; uint8_t v_wantsRebuild_5078_; lean_object* v_trace_5079_; lean_object* v_buildTime_5080_; lean_object* v___x_5082_; uint8_t v_isShared_5083_; uint8_t v_isSharedCheck_5108_; 
v_log_5076_ = lean_ctor_get(v_a_5072_, 0);
v_action_5077_ = lean_ctor_get_uint8(v_a_5072_, sizeof(void*)*3);
v_wantsRebuild_5078_ = lean_ctor_get_uint8(v_a_5072_, sizeof(void*)*3 + 1);
v_trace_5079_ = lean_ctor_get(v_a_5072_, 1);
v_buildTime_5080_ = lean_ctor_get(v_a_5072_, 2);
v_isSharedCheck_5108_ = !lean_is_exclusive(v_a_5072_);
if (v_isSharedCheck_5108_ == 0)
{
v___x_5082_ = v_a_5072_;
v_isShared_5083_ = v_isSharedCheck_5108_;
goto v_resetjp_5081_;
}
else
{
lean_inc(v_buildTime_5080_);
lean_inc(v_trace_5079_);
lean_inc(v_log_5076_);
lean_dec(v_a_5072_);
v___x_5082_ = lean_box(0);
v_isShared_5083_ = v_isSharedCheck_5108_;
goto v_resetjp_5081_;
}
v_resetjp_5081_:
{
lean_object* v___x_5084_; 
v___x_5084_ = l_Lake_removeFileIfExists(v_file_4988_);
if (lean_obj_tag(v___x_5084_) == 0)
{
lean_object* v_descr_5085_; uint64_t v_hash_5086_; lean_object* v_ext_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; uint8_t v___x_5090_; 
lean_dec_ref(v___x_5084_);
lean_del_object(v___x_5082_);
lean_del_object(v___x_5074_);
v_descr_5085_ = lean_ctor_get(v_val_5068_, 0);
v_hash_5086_ = lean_ctor_get_uint64(v_descr_5085_, sizeof(void*)*1);
v_ext_5087_ = lean_ctor_get(v_descr_5085_, 0);
v___x_5088_ = lean_string_utf8_byte_size(v_ext_5087_);
v___x_5089_ = lean_unsigned_to_nat(0u);
v___x_5090_ = lean_nat_dec_eq(v___x_5088_, v___x_5089_);
if (v___x_5090_ == 0)
{
lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; 
v___x_5091_ = l_Lake_Hash_hex(v_hash_5086_);
v___x_5092_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5093_ = lean_string_append(v___x_5091_, v___x_5092_);
v___x_5094_ = lean_string_append(v___x_5093_, v_ext_5087_);
v___y_5044_ = v_val_5068_;
v___y_5045_ = v_buildTime_5080_;
v___y_5046_ = v_a_5066_;
v___y_5047_ = v_trace_5079_;
v___y_5048_ = v_log_5076_;
v___y_5049_ = v_action_5077_;
v___y_5050_ = v_wantsRebuild_5078_;
v___y_5051_ = v___x_5094_;
goto v___jp_5043_;
}
else
{
lean_object* v___x_5095_; 
v___x_5095_ = l_Lake_Hash_hex(v_hash_5086_);
v___y_5044_ = v_val_5068_;
v___y_5045_ = v_buildTime_5080_;
v___y_5046_ = v_a_5066_;
v___y_5047_ = v_trace_5079_;
v___y_5048_ = v_log_5076_;
v___y_5049_ = v_action_5077_;
v___y_5050_ = v_wantsRebuild_5078_;
v___y_5051_ = v___x_5095_;
goto v___jp_5043_;
}
}
else
{
lean_object* v_a_5096_; lean_object* v___x_5097_; uint8_t v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5103_; 
lean_dec(v_val_5068_);
lean_dec_ref(v_a_5066_);
lean_dec_ref(v___x_4989_);
lean_dec_ref(v_file_4988_);
v_a_5096_ = lean_ctor_get(v___x_5084_, 0);
lean_inc(v_a_5096_);
lean_dec_ref(v___x_5084_);
v___x_5097_ = lean_io_error_to_string(v_a_5096_);
v___x_5098_ = 3;
v___x_5099_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5099_, 0, v___x_5097_);
lean_ctor_set_uint8(v___x_5099_, sizeof(void*)*1, v___x_5098_);
v___x_5100_ = lean_array_get_size(v_log_5076_);
v___x_5101_ = lean_array_push(v_log_5076_, v___x_5099_);
if (v_isShared_5083_ == 0)
{
lean_ctor_set(v___x_5082_, 0, v___x_5101_);
v___x_5103_ = v___x_5082_;
goto v_reusejp_5102_;
}
else
{
lean_object* v_reuseFailAlloc_5107_; 
v_reuseFailAlloc_5107_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5107_, 0, v___x_5101_);
lean_ctor_set(v_reuseFailAlloc_5107_, 1, v_trace_5079_);
lean_ctor_set(v_reuseFailAlloc_5107_, 2, v_buildTime_5080_);
lean_ctor_set_uint8(v_reuseFailAlloc_5107_, sizeof(void*)*3, v_action_5077_);
lean_ctor_set_uint8(v_reuseFailAlloc_5107_, sizeof(void*)*3 + 1, v_wantsRebuild_5078_);
v___x_5103_ = v_reuseFailAlloc_5107_;
goto v_reusejp_5102_;
}
v_reusejp_5102_:
{
lean_object* v___x_5105_; 
if (v_isShared_5075_ == 0)
{
lean_ctor_set_tag(v___x_5074_, 1);
lean_ctor_set(v___x_5074_, 1, v___x_5103_);
lean_ctor_set(v___x_5074_, 0, v___x_5100_);
v___x_5105_ = v___x_5074_;
goto v_reusejp_5104_;
}
else
{
lean_object* v_reuseFailAlloc_5106_; 
v_reuseFailAlloc_5106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5106_, 0, v___x_5100_);
lean_ctor_set(v_reuseFailAlloc_5106_, 1, v___x_5103_);
v___x_5105_ = v_reuseFailAlloc_5106_;
goto v_reusejp_5104_;
}
v_reusejp_5104_:
{
return v___x_5105_;
}
}
}
}
}
}
else
{
lean_object* v_a_5111_; 
lean_dec_ref(v___x_4989_);
v_a_5111_ = lean_ctor_get(v___x_5069_, 1);
lean_inc(v_a_5111_);
lean_dec_ref(v___x_5069_);
v___y_5004_ = v_val_5068_;
v___y_5005_ = v_a_5066_;
v___y_5006_ = v_a_5111_;
goto v___jp_5003_;
}
}
else
{
lean_object* v_a_5112_; lean_object* v_a_5113_; lean_object* v___x_5115_; uint8_t v_isShared_5116_; uint8_t v_isSharedCheck_5120_; 
lean_dec(v_val_5068_);
lean_dec_ref(v_a_5066_);
lean_dec_ref(v___x_4989_);
lean_dec_ref(v_file_4988_);
v_a_5112_ = lean_ctor_get(v___x_5069_, 0);
v_a_5113_ = lean_ctor_get(v___x_5069_, 1);
v_isSharedCheck_5120_ = !lean_is_exclusive(v___x_5069_);
if (v_isSharedCheck_5120_ == 0)
{
v___x_5115_ = v___x_5069_;
v_isShared_5116_ = v_isSharedCheck_5120_;
goto v_resetjp_5114_;
}
else
{
lean_inc(v_a_5113_);
lean_inc(v_a_5112_);
lean_dec(v___x_5069_);
v___x_5115_ = lean_box(0);
v_isShared_5116_ = v_isSharedCheck_5120_;
goto v_resetjp_5114_;
}
v_resetjp_5114_:
{
lean_object* v___x_5118_; 
if (v_isShared_5116_ == 0)
{
v___x_5118_ = v___x_5115_;
goto v_reusejp_5117_;
}
else
{
lean_object* v_reuseFailAlloc_5119_; 
v_reuseFailAlloc_5119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5119_, 0, v_a_5112_);
lean_ctor_set(v_reuseFailAlloc_5119_, 1, v_a_5113_);
v___x_5118_ = v_reuseFailAlloc_5119_;
goto v_reusejp_5117_;
}
v_reusejp_5117_:
{
return v___x_5118_;
}
}
}
}
else
{
lean_object* v_a_5121_; 
lean_dec(v_a_4990_);
lean_dec_ref(v___x_4989_);
lean_dec_ref(v_file_4988_);
v_a_5121_ = lean_ctor_get(v___y_5065_, 1);
lean_inc(v_a_5121_);
lean_dec_ref(v___y_5065_);
v_a_5000_ = v_a_5121_;
goto v___jp_4999_;
}
}
else
{
lean_dec(v_a_4990_);
lean_dec_ref(v___x_4989_);
lean_dec_ref(v_file_4988_);
return v___y_5065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object* v_exe_5128_, lean_object* v_hash_5129_, lean_object* v_val_5130_, lean_object* v_file_5131_, lean_object* v___x_5132_, lean_object* v_a_5133_, lean_object* v_restore_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_){
_start:
{
uint8_t v_exe_boxed_5142_; uint64_t v_hash_boxed_5143_; uint8_t v_restore_boxed_5144_; lean_object* v_res_5145_; 
v_exe_boxed_5142_ = lean_unbox(v_exe_5128_);
v_hash_boxed_5143_ = lean_unbox_uint64(v_hash_5129_);
lean_dec_ref(v_hash_5129_);
v_restore_boxed_5144_ = lean_unbox(v_restore_5134_);
v_res_5145_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_boxed_5142_, v_hash_boxed_5143_, v_val_5130_, v_file_5131_, v___x_5132_, v_a_5133_, v_restore_boxed_5144_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
lean_dec(v___y_5138_);
lean_dec(v___y_5137_);
lean_dec(v___y_5136_);
lean_dec_ref(v___y_5135_);
return v_res_5145_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1(uint8_t v_a_5146_, lean_object* v_file_5147_, lean_object* v_ext_5148_, uint8_t v_text_5149_, uint8_t v_exe_5150_, uint8_t v___y_5151_, lean_object* v_val_5152_, uint64_t v_hash_5153_, lean_object* v_____r_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_){
_start:
{
uint8_t v___x_5162_; uint8_t v___x_5163_; 
v___x_5162_ = 1;
v___x_5163_ = l_Lake_instDecidableEqOutputStatus(v_a_5146_, v___x_5162_);
if (v___x_5163_ == 0)
{
lean_object* v_toContext_5164_; lean_object* v_log_5165_; uint8_t v_action_5166_; uint8_t v_wantsRebuild_5167_; lean_object* v_trace_5168_; lean_object* v_buildTime_5169_; lean_object* v_lakeCache_5170_; lean_object* v___x_5171_; 
v_toContext_5164_ = lean_ctor_get(v___y_5159_, 1);
lean_inc(v_toContext_5164_);
lean_dec_ref(v___y_5159_);
v_log_5165_ = lean_ctor_get(v___y_5160_, 0);
v_action_5166_ = lean_ctor_get_uint8(v___y_5160_, sizeof(void*)*3);
v_wantsRebuild_5167_ = lean_ctor_get_uint8(v___y_5160_, sizeof(void*)*3 + 1);
v_trace_5168_ = lean_ctor_get(v___y_5160_, 1);
v_buildTime_5169_ = lean_ctor_get(v___y_5160_, 2);
v_lakeCache_5170_ = lean_ctor_get(v_toContext_5164_, 3);
lean_inc_ref(v_lakeCache_5170_);
lean_dec(v_toContext_5164_);
lean_inc_ref(v_lakeCache_5170_);
v___x_5171_ = l_Lake_Cache_saveArtifact(v_lakeCache_5170_, v_file_5147_, v_ext_5148_, v_text_5149_, v_exe_5150_, v___y_5151_);
if (lean_obj_tag(v___x_5171_) == 0)
{
lean_object* v_a_5172_; lean_object* v___x_5174_; uint8_t v_isShared_5175_; uint8_t v_isSharedCheck_5213_; 
v_a_5172_ = lean_ctor_get(v___x_5171_, 0);
v_isSharedCheck_5213_ = !lean_is_exclusive(v___x_5171_);
if (v_isSharedCheck_5213_ == 0)
{
v___x_5174_ = v___x_5171_;
v_isShared_5175_ = v_isSharedCheck_5213_;
goto v_resetjp_5173_;
}
else
{
lean_inc(v_a_5172_);
lean_dec(v___x_5171_);
v___x_5174_ = lean_box(0);
v_isShared_5175_ = v_isSharedCheck_5213_;
goto v_resetjp_5173_;
}
v_resetjp_5173_:
{
lean_object* v_descr_5176_; uint64_t v_hash_5177_; lean_object* v_ext_5178_; lean_object* v___x_5179_; lean_object* v___y_5181_; lean_object* v___x_5205_; lean_object* v___x_5206_; uint8_t v___x_5207_; 
v_descr_5176_ = lean_ctor_get(v_a_5172_, 0);
v_hash_5177_ = lean_ctor_get_uint64(v_descr_5176_, sizeof(void*)*1);
v_ext_5178_ = lean_ctor_get(v_descr_5176_, 0);
v___x_5179_ = l_Lake_Package_cacheScope(v_val_5152_);
v___x_5205_ = lean_string_utf8_byte_size(v_ext_5178_);
v___x_5206_ = lean_unsigned_to_nat(0u);
v___x_5207_ = lean_nat_dec_eq(v___x_5205_, v___x_5206_);
if (v___x_5207_ == 0)
{
lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; 
v___x_5208_ = l_Lake_Hash_hex(v_hash_5177_);
v___x_5209_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5210_ = lean_string_append(v___x_5208_, v___x_5209_);
v___x_5211_ = lean_string_append(v___x_5210_, v_ext_5178_);
v___y_5181_ = v___x_5211_;
goto v___jp_5180_;
}
else
{
lean_object* v___x_5212_; 
v___x_5212_ = l_Lake_Hash_hex(v_hash_5177_);
v___y_5181_ = v___x_5212_;
goto v___jp_5180_;
}
v___jp_5180_:
{
lean_object* v___x_5183_; 
if (v_isShared_5175_ == 0)
{
lean_ctor_set_tag(v___x_5174_, 3);
lean_ctor_set(v___x_5174_, 0, v___y_5181_);
v___x_5183_ = v___x_5174_;
goto v_reusejp_5182_;
}
else
{
lean_object* v_reuseFailAlloc_5204_; 
v_reuseFailAlloc_5204_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5204_, 0, v___y_5181_);
v___x_5183_ = v_reuseFailAlloc_5204_;
goto v_reusejp_5182_;
}
v_reusejp_5182_:
{
lean_object* v___x_5184_; lean_object* v___x_5185_; 
v___x_5184_ = lean_box(0);
v___x_5185_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_5170_, v___x_5179_, v_hash_5153_, v___x_5183_, v___x_5184_, v___x_5184_);
if (lean_obj_tag(v___x_5185_) == 0)
{
lean_object* v___x_5186_; 
lean_dec_ref(v___x_5185_);
v___x_5186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5186_, 0, v_a_5172_);
lean_ctor_set(v___x_5186_, 1, v___y_5160_);
return v___x_5186_;
}
else
{
lean_object* v___x_5188_; uint8_t v_isShared_5189_; uint8_t v_isSharedCheck_5200_; 
lean_inc(v_buildTime_5169_);
lean_inc_ref(v_trace_5168_);
lean_inc_ref(v_log_5165_);
lean_dec(v_a_5172_);
v_isSharedCheck_5200_ = !lean_is_exclusive(v___y_5160_);
if (v_isSharedCheck_5200_ == 0)
{
lean_object* v_unused_5201_; lean_object* v_unused_5202_; lean_object* v_unused_5203_; 
v_unused_5201_ = lean_ctor_get(v___y_5160_, 2);
lean_dec(v_unused_5201_);
v_unused_5202_ = lean_ctor_get(v___y_5160_, 1);
lean_dec(v_unused_5202_);
v_unused_5203_ = lean_ctor_get(v___y_5160_, 0);
lean_dec(v_unused_5203_);
v___x_5188_ = v___y_5160_;
v_isShared_5189_ = v_isSharedCheck_5200_;
goto v_resetjp_5187_;
}
else
{
lean_dec(v___y_5160_);
v___x_5188_ = lean_box(0);
v_isShared_5189_ = v_isSharedCheck_5200_;
goto v_resetjp_5187_;
}
v_resetjp_5187_:
{
lean_object* v_a_5190_; lean_object* v___x_5191_; uint8_t v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5197_; 
v_a_5190_ = lean_ctor_get(v___x_5185_, 0);
lean_inc(v_a_5190_);
lean_dec_ref(v___x_5185_);
v___x_5191_ = lean_io_error_to_string(v_a_5190_);
v___x_5192_ = 3;
v___x_5193_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5193_, 0, v___x_5191_);
lean_ctor_set_uint8(v___x_5193_, sizeof(void*)*1, v___x_5192_);
v___x_5194_ = lean_array_get_size(v_log_5165_);
v___x_5195_ = lean_array_push(v_log_5165_, v___x_5193_);
if (v_isShared_5189_ == 0)
{
lean_ctor_set(v___x_5188_, 0, v___x_5195_);
v___x_5197_ = v___x_5188_;
goto v_reusejp_5196_;
}
else
{
lean_object* v_reuseFailAlloc_5199_; 
v_reuseFailAlloc_5199_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5199_, 0, v___x_5195_);
lean_ctor_set(v_reuseFailAlloc_5199_, 1, v_trace_5168_);
lean_ctor_set(v_reuseFailAlloc_5199_, 2, v_buildTime_5169_);
lean_ctor_set_uint8(v_reuseFailAlloc_5199_, sizeof(void*)*3, v_action_5166_);
lean_ctor_set_uint8(v_reuseFailAlloc_5199_, sizeof(void*)*3 + 1, v_wantsRebuild_5167_);
v___x_5197_ = v_reuseFailAlloc_5199_;
goto v_reusejp_5196_;
}
v_reusejp_5196_:
{
lean_object* v___x_5198_; 
v___x_5198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5198_, 0, v___x_5194_);
lean_ctor_set(v___x_5198_, 1, v___x_5197_);
return v___x_5198_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5215_; uint8_t v_isShared_5216_; uint8_t v_isSharedCheck_5227_; 
lean_inc(v_buildTime_5169_);
lean_inc_ref(v_trace_5168_);
lean_inc_ref(v_log_5165_);
lean_dec_ref(v_lakeCache_5170_);
lean_dec_ref(v_val_5152_);
v_isSharedCheck_5227_ = !lean_is_exclusive(v___y_5160_);
if (v_isSharedCheck_5227_ == 0)
{
lean_object* v_unused_5228_; lean_object* v_unused_5229_; lean_object* v_unused_5230_; 
v_unused_5228_ = lean_ctor_get(v___y_5160_, 2);
lean_dec(v_unused_5228_);
v_unused_5229_ = lean_ctor_get(v___y_5160_, 1);
lean_dec(v_unused_5229_);
v_unused_5230_ = lean_ctor_get(v___y_5160_, 0);
lean_dec(v_unused_5230_);
v___x_5215_ = v___y_5160_;
v_isShared_5216_ = v_isSharedCheck_5227_;
goto v_resetjp_5214_;
}
else
{
lean_dec(v___y_5160_);
v___x_5215_ = lean_box(0);
v_isShared_5216_ = v_isSharedCheck_5227_;
goto v_resetjp_5214_;
}
v_resetjp_5214_:
{
lean_object* v_a_5217_; lean_object* v___x_5218_; uint8_t v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5224_; 
v_a_5217_ = lean_ctor_get(v___x_5171_, 0);
lean_inc(v_a_5217_);
lean_dec_ref(v___x_5171_);
v___x_5218_ = lean_io_error_to_string(v_a_5217_);
v___x_5219_ = 3;
v___x_5220_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5220_, 0, v___x_5218_);
lean_ctor_set_uint8(v___x_5220_, sizeof(void*)*1, v___x_5219_);
v___x_5221_ = lean_array_get_size(v_log_5165_);
v___x_5222_ = lean_array_push(v_log_5165_, v___x_5220_);
if (v_isShared_5216_ == 0)
{
lean_ctor_set(v___x_5215_, 0, v___x_5222_);
v___x_5224_ = v___x_5215_;
goto v_reusejp_5223_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v___x_5222_);
lean_ctor_set(v_reuseFailAlloc_5226_, 1, v_trace_5168_);
lean_ctor_set(v_reuseFailAlloc_5226_, 2, v_buildTime_5169_);
lean_ctor_set_uint8(v_reuseFailAlloc_5226_, sizeof(void*)*3, v_action_5166_);
lean_ctor_set_uint8(v_reuseFailAlloc_5226_, sizeof(void*)*3 + 1, v_wantsRebuild_5167_);
v___x_5224_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5223_;
}
v_reusejp_5223_:
{
lean_object* v___x_5225_; 
v___x_5225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5225_, 0, v___x_5221_);
lean_ctor_set(v___x_5225_, 1, v___x_5224_);
return v___x_5225_;
}
}
}
}
else
{
lean_object* v___x_5231_; 
lean_dec_ref(v_val_5152_);
v___x_5231_ = l_Lake_computeArtifact___redArg(v_file_5147_, v_ext_5148_, v_text_5149_, v___y_5159_, v___y_5160_);
lean_dec_ref(v___y_5159_);
return v___x_5231_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___boxed(lean_object* v_a_5232_, lean_object* v_file_5233_, lean_object* v_ext_5234_, lean_object* v_text_5235_, lean_object* v_exe_5236_, lean_object* v___y_5237_, lean_object* v_val_5238_, lean_object* v_hash_5239_, lean_object* v_____r_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_){
_start:
{
uint8_t v_a_320498__boxed_5248_; uint8_t v_text_boxed_5249_; uint8_t v_exe_boxed_5250_; uint8_t v___y_320499__boxed_5251_; uint64_t v_hash_boxed_5252_; lean_object* v_res_5253_; 
v_a_320498__boxed_5248_ = lean_unbox(v_a_5232_);
v_text_boxed_5249_ = lean_unbox(v_text_5235_);
v_exe_boxed_5250_ = lean_unbox(v_exe_5236_);
v___y_320499__boxed_5251_ = lean_unbox(v___y_5237_);
v_hash_boxed_5252_ = lean_unbox_uint64(v_hash_5239_);
lean_dec_ref(v_hash_5239_);
v_res_5253_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v_a_320498__boxed_5248_, v_file_5233_, v_ext_5234_, v_text_boxed_5249_, v_exe_boxed_5250_, v___y_320499__boxed_5251_, v_val_5238_, v_hash_boxed_5252_, v_____r_5240_, v___y_5241_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_);
lean_dec(v___y_5244_);
lean_dec(v___y_5243_);
lean_dec(v___y_5242_);
lean_dec_ref(v___y_5241_);
return v_res_5253_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object* v_file_5254_, lean_object* v_build_5255_, uint8_t v_text_5256_, lean_object* v_ext_5257_, uint8_t v_restore_5258_, uint8_t v_exe_5259_, uint8_t v_platformIndependent_5260_, lean_object* v_a_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_){
_start:
{
lean_object* v_log_5268_; uint8_t v_action_5269_; uint8_t v_wantsRebuild_5270_; lean_object* v_trace_5271_; lean_object* v_buildTime_5272_; lean_object* v___x_5274_; uint8_t v_isShared_5275_; uint8_t v_isSharedCheck_5521_; 
v_log_5268_ = lean_ctor_get(v_a_5266_, 0);
v_action_5269_ = lean_ctor_get_uint8(v_a_5266_, sizeof(void*)*3);
v_wantsRebuild_5270_ = lean_ctor_get_uint8(v_a_5266_, sizeof(void*)*3 + 1);
v_trace_5271_ = lean_ctor_get(v_a_5266_, 1);
v_buildTime_5272_ = lean_ctor_get(v_a_5266_, 2);
v_isSharedCheck_5521_ = !lean_is_exclusive(v_a_5266_);
if (v_isSharedCheck_5521_ == 0)
{
v___x_5274_ = v_a_5266_;
v_isShared_5275_ = v_isSharedCheck_5521_;
goto v_resetjp_5273_;
}
else
{
lean_inc(v_buildTime_5272_);
lean_inc(v_trace_5271_);
lean_inc(v_log_5268_);
lean_dec(v_a_5266_);
v___x_5274_ = lean_box(0);
v_isShared_5275_ = v_isSharedCheck_5521_;
goto v_resetjp_5273_;
}
v_resetjp_5273_:
{
lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v_art_5279_; lean_object* v___y_5280_; lean_object* v___y_5296_; lean_object* v_log_5297_; uint8_t v_action_5298_; uint8_t v_wantsRebuild_5299_; lean_object* v_buildTime_5300_; lean_object* v___x_5306_; 
v___x_5276_ = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(v_file_5254_);
v___x_5277_ = lean_string_append(v_file_5254_, v___x_5276_);
lean_inc_ref(v___x_5277_);
v___x_5306_ = l_Lake_readTraceFile(v___x_5277_, v_log_5268_);
if (lean_obj_tag(v___x_5306_) == 0)
{
if (lean_obj_tag(v_a_5262_) == 1)
{
lean_object* v_a_5307_; lean_object* v_a_5308_; lean_object* v_val_5309_; uint64_t v_hash_5310_; lean_object* v_mtime_5311_; uint8_t v___y_5313_; lean_object* v___y_5314_; lean_object* v___y_5315_; lean_object* v___y_5316_; uint8_t v___y_5317_; lean_object* v___y_5318_; lean_object* v___y_5319_; lean_object* v___y_5320_; lean_object* v___y_5321_; lean_object* v_wsIdx_5325_; lean_object* v_config_5326_; lean_object* v_a_5328_; lean_object* v_a_5329_; lean_object* v___y_5359_; lean_object* v_enableArtifactCache_x3f_5362_; lean_object* v_restoreAllArtifacts_x3f_5363_; uint8_t v___y_5365_; lean_object* v_a_5366_; uint8_t v___y_5383_; uint8_t v_a_5384_; lean_object* v_a_5385_; lean_object* v_a_5388_; lean_object* v___y_5418_; uint8_t v___y_5419_; uint8_t v___y_5458_; uint8_t v_a_5459_; lean_object* v_a_5460_; uint8_t v_a_5462_; lean_object* v_a_5463_; lean_object* v___x_5473_; 
v_a_5307_ = lean_ctor_get(v___x_5306_, 0);
lean_inc(v_a_5307_);
v_a_5308_ = lean_ctor_get(v___x_5306_, 1);
lean_inc(v_a_5308_);
lean_dec_ref(v___x_5306_);
v_val_5309_ = lean_ctor_get(v_a_5262_, 0);
v_hash_5310_ = lean_ctor_get_uint64(v_trace_5271_, sizeof(void*)*3);
v_mtime_5311_ = lean_ctor_get(v_trace_5271_, 2);
v_wsIdx_5325_ = lean_ctor_get(v_val_5309_, 0);
lean_inc(v_wsIdx_5325_);
v_config_5326_ = lean_ctor_get(v_val_5309_, 6);
v_enableArtifactCache_x3f_5362_ = lean_ctor_get(v_config_5326_, 24);
v_restoreAllArtifacts_x3f_5363_ = lean_ctor_get(v_config_5326_, 25);
lean_inc_ref(v_trace_5271_);
v___x_5473_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5473_, 0, v_a_5308_);
lean_ctor_set(v___x_5473_, 1, v_trace_5271_);
lean_ctor_set(v___x_5473_, 2, v_buildTime_5272_);
lean_ctor_set_uint8(v___x_5473_, sizeof(void*)*3, v_action_5269_);
lean_ctor_set_uint8(v___x_5473_, sizeof(void*)*3 + 1, v_wantsRebuild_5270_);
if (lean_obj_tag(v_enableArtifactCache_x3f_5362_) == 0)
{
lean_object* v_toContext_5474_; lean_object* v_lakeEnv_5475_; lean_object* v_enableArtifactCache_x3f_5476_; 
v_toContext_5474_ = lean_ctor_get(v_a_5265_, 1);
v_lakeEnv_5475_ = lean_ctor_get(v_toContext_5474_, 1);
v_enableArtifactCache_x3f_5476_ = lean_ctor_get(v_lakeEnv_5475_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_5476_) == 0)
{
lean_object* v_root_5477_; lean_object* v_config_5478_; lean_object* v_enableArtifactCache_x3f_5479_; 
v_root_5477_ = lean_ctor_get(v_toContext_5474_, 0);
v_config_5478_ = lean_ctor_get(v_root_5477_, 6);
v_enableArtifactCache_x3f_5479_ = lean_ctor_get(v_config_5478_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_5479_) == 0)
{
v_a_5388_ = v___x_5473_;
goto v___jp_5387_;
}
else
{
lean_object* v_val_5480_; uint8_t v___x_5481_; 
v_val_5480_ = lean_ctor_get(v_enableArtifactCache_x3f_5479_, 0);
v___x_5481_ = lean_unbox(v_val_5480_);
v_a_5462_ = v___x_5481_;
v_a_5463_ = v___x_5473_;
goto v___jp_5461_;
}
}
else
{
lean_object* v_val_5482_; uint8_t v___x_5483_; 
v_val_5482_ = lean_ctor_get(v_enableArtifactCache_x3f_5476_, 0);
v___x_5483_ = lean_unbox(v_val_5482_);
v_a_5462_ = v___x_5483_;
v_a_5463_ = v___x_5473_;
goto v___jp_5461_;
}
}
else
{
lean_object* v_val_5484_; uint8_t v___x_5485_; 
v_val_5484_ = lean_ctor_get(v_enableArtifactCache_x3f_5362_, 0);
v___x_5485_ = lean_unbox(v_val_5484_);
v_a_5462_ = v___x_5485_;
v_a_5463_ = v___x_5473_;
goto v___jp_5461_;
}
v___jp_5312_:
{
lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; 
lean_dec_ref(v___y_5319_);
v___x_5322_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5322_, 0, v___y_5321_);
v___x_5323_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_hash_5310_, v___x_5322_, v___y_5315_, v_platformIndependent_5260_);
v___x_5324_ = lean_st_ref_set(v___y_5318_, v___x_5323_);
lean_dec(v___y_5318_);
v___y_5296_ = v___y_5316_;
v_log_5297_ = v___y_5320_;
v_action_5298_ = v___y_5313_;
v_wantsRebuild_5299_ = v___y_5317_;
v_buildTime_5300_ = v___y_5314_;
goto v___jp_5295_;
}
v___jp_5327_:
{
lean_object* v___x_5330_; uint8_t v___x_5331_; 
v___x_5330_ = lean_unsigned_to_nat(0u);
v___x_5331_ = lean_nat_dec_eq(v_wsIdx_5325_, v___x_5330_);
lean_dec(v_wsIdx_5325_);
if (v___x_5331_ == 0)
{
lean_object* v_log_5332_; uint8_t v_action_5333_; uint8_t v_wantsRebuild_5334_; lean_object* v_buildTime_5335_; 
lean_dec_ref(v_a_5265_);
v_log_5332_ = lean_ctor_get(v_a_5329_, 0);
lean_inc_ref(v_log_5332_);
v_action_5333_ = lean_ctor_get_uint8(v_a_5329_, sizeof(void*)*3);
v_wantsRebuild_5334_ = lean_ctor_get_uint8(v_a_5329_, sizeof(void*)*3 + 1);
v_buildTime_5335_ = lean_ctor_get(v_a_5329_, 2);
lean_inc(v_buildTime_5335_);
lean_dec_ref(v_a_5329_);
v___y_5296_ = v_a_5328_;
v_log_5297_ = v_log_5332_;
v_action_5298_ = v_action_5333_;
v_wantsRebuild_5299_ = v_wantsRebuild_5334_;
v_buildTime_5300_ = v_buildTime_5335_;
goto v___jp_5295_;
}
else
{
lean_object* v_outputsRef_x3f_5336_; 
v_outputsRef_x3f_5336_ = lean_ctor_get(v_a_5265_, 4);
lean_inc(v_outputsRef_x3f_5336_);
lean_dec_ref(v_a_5265_);
if (lean_obj_tag(v_outputsRef_x3f_5336_) == 1)
{
lean_object* v_log_5337_; uint8_t v_action_5338_; uint8_t v_wantsRebuild_5339_; lean_object* v_trace_5340_; lean_object* v_buildTime_5341_; lean_object* v_val_5342_; lean_object* v___x_5343_; lean_object* v_descr_5344_; uint64_t v_hash_5345_; lean_object* v_ext_5346_; lean_object* v___x_5347_; uint8_t v___x_5348_; 
v_log_5337_ = lean_ctor_get(v_a_5329_, 0);
lean_inc_ref(v_log_5337_);
v_action_5338_ = lean_ctor_get_uint8(v_a_5329_, sizeof(void*)*3);
v_wantsRebuild_5339_ = lean_ctor_get_uint8(v_a_5329_, sizeof(void*)*3 + 1);
v_trace_5340_ = lean_ctor_get(v_a_5329_, 1);
lean_inc_ref(v_trace_5340_);
v_buildTime_5341_ = lean_ctor_get(v_a_5329_, 2);
lean_inc(v_buildTime_5341_);
lean_dec_ref(v_a_5329_);
v_val_5342_ = lean_ctor_get(v_outputsRef_x3f_5336_, 0);
lean_inc(v_val_5342_);
lean_dec_ref(v_outputsRef_x3f_5336_);
v___x_5343_ = lean_st_ref_take(v_val_5342_);
v_descr_5344_ = lean_ctor_get(v_a_5328_, 0);
v_hash_5345_ = lean_ctor_get_uint64(v_descr_5344_, sizeof(void*)*1);
v_ext_5346_ = lean_ctor_get(v_descr_5344_, 0);
v___x_5347_ = lean_string_utf8_byte_size(v_ext_5346_);
v___x_5348_ = lean_nat_dec_eq(v___x_5347_, v___x_5330_);
if (v___x_5348_ == 0)
{
lean_object* v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; 
v___x_5349_ = l_Lake_Hash_hex(v_hash_5345_);
v___x_5350_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5351_ = lean_string_append(v___x_5349_, v___x_5350_);
v___x_5352_ = lean_string_append(v___x_5351_, v_ext_5346_);
v___y_5313_ = v_action_5338_;
v___y_5314_ = v_buildTime_5341_;
v___y_5315_ = v___x_5343_;
v___y_5316_ = v_a_5328_;
v___y_5317_ = v_wantsRebuild_5339_;
v___y_5318_ = v_val_5342_;
v___y_5319_ = v_trace_5340_;
v___y_5320_ = v_log_5337_;
v___y_5321_ = v___x_5352_;
goto v___jp_5312_;
}
else
{
lean_object* v___x_5353_; 
v___x_5353_ = l_Lake_Hash_hex(v_hash_5345_);
v___y_5313_ = v_action_5338_;
v___y_5314_ = v_buildTime_5341_;
v___y_5315_ = v___x_5343_;
v___y_5316_ = v_a_5328_;
v___y_5317_ = v_wantsRebuild_5339_;
v___y_5318_ = v_val_5342_;
v___y_5319_ = v_trace_5340_;
v___y_5320_ = v_log_5337_;
v___y_5321_ = v___x_5353_;
goto v___jp_5312_;
}
}
else
{
lean_object* v_log_5354_; uint8_t v_action_5355_; uint8_t v_wantsRebuild_5356_; lean_object* v_buildTime_5357_; 
lean_dec(v_outputsRef_x3f_5336_);
v_log_5354_ = lean_ctor_get(v_a_5329_, 0);
lean_inc_ref(v_log_5354_);
v_action_5355_ = lean_ctor_get_uint8(v_a_5329_, sizeof(void*)*3);
v_wantsRebuild_5356_ = lean_ctor_get_uint8(v_a_5329_, sizeof(void*)*3 + 1);
v_buildTime_5357_ = lean_ctor_get(v_a_5329_, 2);
lean_inc(v_buildTime_5357_);
lean_dec_ref(v_a_5329_);
v___y_5296_ = v_a_5328_;
v_log_5297_ = v_log_5354_;
v_action_5298_ = v_action_5355_;
v_wantsRebuild_5299_ = v_wantsRebuild_5356_;
v_buildTime_5300_ = v_buildTime_5357_;
goto v___jp_5295_;
}
}
}
v___jp_5358_:
{
if (lean_obj_tag(v___y_5359_) == 0)
{
lean_object* v_a_5360_; lean_object* v_a_5361_; 
v_a_5360_ = lean_ctor_get(v___y_5359_, 0);
lean_inc(v_a_5360_);
v_a_5361_ = lean_ctor_get(v___y_5359_, 1);
lean_inc(v_a_5361_);
lean_dec_ref(v___y_5359_);
v_a_5328_ = v_a_5360_;
v_a_5329_ = v_a_5361_;
goto v___jp_5327_;
}
else
{
lean_dec(v_wsIdx_5325_);
lean_dec_ref(v___x_5277_);
lean_del_object(v___x_5274_);
lean_dec_ref(v_a_5265_);
return v___y_5359_;
}
}
v___jp_5364_:
{
lean_object* v___x_5367_; 
lean_inc_ref(v_a_5265_);
lean_inc_ref(v___x_5277_);
lean_inc_ref(v_file_5254_);
lean_inc(v_val_5309_);
v___x_5367_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_5259_, v_hash_5310_, v_val_5309_, v_file_5254_, v___x_5277_, v_a_5307_, v___y_5365_, v_a_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5366_);
if (lean_obj_tag(v___x_5367_) == 0)
{
lean_object* v_a_5368_; 
v_a_5368_ = lean_ctor_get(v___x_5367_, 0);
lean_inc(v_a_5368_);
if (lean_obj_tag(v_a_5368_) == 1)
{
lean_object* v_a_5369_; lean_object* v_val_5370_; 
lean_dec_ref(v_a_5262_);
lean_dec_ref(v_trace_5271_);
lean_dec(v_a_5264_);
lean_dec(v_a_5263_);
lean_dec_ref(v_a_5261_);
lean_dec_ref(v_ext_5257_);
lean_dec_ref(v_build_5255_);
lean_dec_ref(v_file_5254_);
v_a_5369_ = lean_ctor_get(v___x_5367_, 1);
lean_inc(v_a_5369_);
lean_dec_ref(v___x_5367_);
v_val_5370_ = lean_ctor_get(v_a_5368_, 0);
lean_inc(v_val_5370_);
lean_dec_ref(v_a_5368_);
v_a_5328_ = v_val_5370_;
v_a_5329_ = v_a_5369_;
goto v___jp_5327_;
}
else
{
lean_object* v_a_5371_; lean_object* v___x_5372_; 
lean_dec(v_a_5368_);
v_a_5371_ = lean_ctor_get(v___x_5367_, 1);
lean_inc(v_a_5371_);
lean_dec_ref(v___x_5367_);
lean_inc_ref(v_a_5265_);
lean_inc_ref(v___x_5277_);
v___x_5372_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5254_, v_build_5255_, v_text_5256_, v_ext_5257_, v_trace_5271_, v___x_5277_, v_a_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5371_);
lean_dec_ref(v_trace_5271_);
v___y_5359_ = v___x_5372_;
goto v___jp_5358_;
}
}
else
{
lean_object* v_a_5373_; lean_object* v_a_5374_; lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5381_; 
lean_dec(v_wsIdx_5325_);
lean_dec_ref(v_a_5262_);
lean_dec_ref(v___x_5277_);
lean_del_object(v___x_5274_);
lean_dec_ref(v_trace_5271_);
lean_dec_ref(v_a_5265_);
lean_dec(v_a_5264_);
lean_dec(v_a_5263_);
lean_dec_ref(v_a_5261_);
lean_dec_ref(v_ext_5257_);
lean_dec_ref(v_build_5255_);
lean_dec_ref(v_file_5254_);
v_a_5373_ = lean_ctor_get(v___x_5367_, 0);
v_a_5374_ = lean_ctor_get(v___x_5367_, 1);
v_isSharedCheck_5381_ = !lean_is_exclusive(v___x_5367_);
if (v_isSharedCheck_5381_ == 0)
{
v___x_5376_ = v___x_5367_;
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
else
{
lean_inc(v_a_5374_);
lean_inc(v_a_5373_);
lean_dec(v___x_5367_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
lean_object* v___x_5379_; 
if (v_isShared_5377_ == 0)
{
v___x_5379_ = v___x_5376_;
goto v_reusejp_5378_;
}
else
{
lean_object* v_reuseFailAlloc_5380_; 
v_reuseFailAlloc_5380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5380_, 0, v_a_5373_);
lean_ctor_set(v_reuseFailAlloc_5380_, 1, v_a_5374_);
v___x_5379_ = v_reuseFailAlloc_5380_;
goto v_reusejp_5378_;
}
v_reusejp_5378_:
{
return v___x_5379_;
}
}
}
}
v___jp_5382_:
{
if (v_a_5384_ == 0)
{
lean_object* v___x_5386_; 
lean_dec(v_a_5307_);
lean_inc_ref(v_a_5265_);
lean_inc_ref(v___x_5277_);
v___x_5386_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5254_, v_build_5255_, v_text_5256_, v_ext_5257_, v_trace_5271_, v___x_5277_, v_a_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5385_);
lean_dec_ref(v_trace_5271_);
v___y_5359_ = v___x_5386_;
goto v___jp_5358_;
}
else
{
v___y_5365_ = v___y_5383_;
v_a_5366_ = v_a_5385_;
goto v___jp_5364_;
}
}
v___jp_5387_:
{
lean_object* v___x_5389_; 
lean_inc(v_a_5307_);
v___x_5389_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5261_, v_file_5254_, v_trace_5271_, v_a_5307_, v_mtime_5311_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5388_);
if (lean_obj_tag(v___x_5389_) == 0)
{
lean_object* v_a_5390_; lean_object* v_a_5391_; uint8_t v___x_5392_; uint8_t v___x_5393_; uint8_t v___x_5394_; 
v_a_5390_ = lean_ctor_get(v___x_5389_, 0);
lean_inc(v_a_5390_);
v_a_5391_ = lean_ctor_get(v___x_5389_, 1);
lean_inc(v_a_5391_);
lean_dec_ref(v___x_5389_);
v___x_5392_ = 0;
v___x_5393_ = lean_unbox(v_a_5390_);
lean_dec(v_a_5390_);
v___x_5394_ = l_Lake_instDecidableEqOutputStatus(v___x_5393_, v___x_5392_);
if (v___x_5394_ == 0)
{
lean_object* v___x_5395_; 
lean_dec(v_a_5307_);
lean_dec_ref(v_a_5262_);
lean_dec_ref(v_trace_5271_);
lean_dec(v_a_5264_);
lean_dec(v_a_5263_);
lean_dec_ref(v_a_5261_);
lean_dec_ref(v_build_5255_);
v___x_5395_ = l_Lake_computeArtifact___redArg(v_file_5254_, v_ext_5257_, v_text_5256_, v_a_5265_, v_a_5391_);
v___y_5359_ = v___x_5395_;
goto v___jp_5358_;
}
else
{
if (lean_obj_tag(v_enableArtifactCache_x3f_5362_) == 0)
{
lean_object* v_toContext_5396_; lean_object* v_lakeEnv_5397_; lean_object* v_enableArtifactCache_x3f_5398_; 
v_toContext_5396_ = lean_ctor_get(v_a_5265_, 1);
v_lakeEnv_5397_ = lean_ctor_get(v_toContext_5396_, 1);
v_enableArtifactCache_x3f_5398_ = lean_ctor_get(v_lakeEnv_5397_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_5398_) == 0)
{
lean_object* v_root_5399_; lean_object* v_config_5400_; lean_object* v_enableArtifactCache_x3f_5401_; 
v_root_5399_ = lean_ctor_get(v_toContext_5396_, 0);
v_config_5400_ = lean_ctor_get(v_root_5399_, 6);
v_enableArtifactCache_x3f_5401_ = lean_ctor_get(v_config_5400_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_5401_) == 0)
{
v___y_5365_ = v___x_5394_;
v_a_5366_ = v_a_5391_;
goto v___jp_5364_;
}
else
{
lean_object* v_val_5402_; uint8_t v___x_5403_; 
v_val_5402_ = lean_ctor_get(v_enableArtifactCache_x3f_5401_, 0);
v___x_5403_ = lean_unbox(v_val_5402_);
v___y_5383_ = v___x_5394_;
v_a_5384_ = v___x_5403_;
v_a_5385_ = v_a_5391_;
goto v___jp_5382_;
}
}
else
{
lean_object* v_val_5404_; uint8_t v___x_5405_; 
v_val_5404_ = lean_ctor_get(v_enableArtifactCache_x3f_5398_, 0);
v___x_5405_ = lean_unbox(v_val_5404_);
v___y_5383_ = v___x_5394_;
v_a_5384_ = v___x_5405_;
v_a_5385_ = v_a_5391_;
goto v___jp_5382_;
}
}
else
{
lean_object* v_val_5406_; uint8_t v___x_5407_; 
v_val_5406_ = lean_ctor_get(v_enableArtifactCache_x3f_5362_, 0);
v___x_5407_ = lean_unbox(v_val_5406_);
v___y_5383_ = v___x_5394_;
v_a_5384_ = v___x_5407_;
v_a_5385_ = v_a_5391_;
goto v___jp_5382_;
}
}
}
else
{
lean_object* v_a_5408_; lean_object* v_a_5409_; lean_object* v___x_5411_; uint8_t v_isShared_5412_; uint8_t v_isSharedCheck_5416_; 
lean_dec(v_wsIdx_5325_);
lean_dec_ref(v_a_5262_);
lean_dec(v_a_5307_);
lean_dec_ref(v___x_5277_);
lean_del_object(v___x_5274_);
lean_dec_ref(v_trace_5271_);
lean_dec_ref(v_a_5265_);
lean_dec(v_a_5264_);
lean_dec(v_a_5263_);
lean_dec_ref(v_a_5261_);
lean_dec_ref(v_ext_5257_);
lean_dec_ref(v_build_5255_);
lean_dec_ref(v_file_5254_);
v_a_5408_ = lean_ctor_get(v___x_5389_, 0);
v_a_5409_ = lean_ctor_get(v___x_5389_, 1);
v_isSharedCheck_5416_ = !lean_is_exclusive(v___x_5389_);
if (v_isSharedCheck_5416_ == 0)
{
v___x_5411_ = v___x_5389_;
v_isShared_5412_ = v_isSharedCheck_5416_;
goto v_resetjp_5410_;
}
else
{
lean_inc(v_a_5409_);
lean_inc(v_a_5408_);
lean_dec(v___x_5389_);
v___x_5411_ = lean_box(0);
v_isShared_5412_ = v_isSharedCheck_5416_;
goto v_resetjp_5410_;
}
v_resetjp_5410_:
{
lean_object* v___x_5414_; 
if (v_isShared_5412_ == 0)
{
v___x_5414_ = v___x_5411_;
goto v_reusejp_5413_;
}
else
{
lean_object* v_reuseFailAlloc_5415_; 
v_reuseFailAlloc_5415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5415_, 0, v_a_5408_);
lean_ctor_set(v_reuseFailAlloc_5415_, 1, v_a_5409_);
v___x_5414_ = v_reuseFailAlloc_5415_;
goto v_reusejp_5413_;
}
v_reusejp_5413_:
{
return v___x_5414_;
}
}
}
}
v___jp_5417_:
{
lean_object* v___x_5420_; 
lean_inc_ref(v_a_5265_);
lean_inc(v_a_5307_);
lean_inc_ref(v___x_5277_);
lean_inc_ref(v_file_5254_);
lean_inc(v_val_5309_);
v___x_5420_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_5259_, v_hash_5310_, v_val_5309_, v_file_5254_, v___x_5277_, v_a_5307_, v___y_5419_, v_a_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v___y_5418_);
if (lean_obj_tag(v___x_5420_) == 0)
{
lean_object* v_a_5421_; 
v_a_5421_ = lean_ctor_get(v___x_5420_, 0);
lean_inc(v_a_5421_);
if (lean_obj_tag(v_a_5421_) == 1)
{
lean_object* v_a_5422_; lean_object* v_val_5423_; 
lean_dec(v_val_5309_);
lean_dec_ref(v_a_5262_);
lean_dec(v_a_5307_);
lean_dec_ref(v_trace_5271_);
lean_dec(v_a_5264_);
lean_dec(v_a_5263_);
lean_dec_ref(v_a_5261_);
lean_dec_ref(v_ext_5257_);
lean_dec_ref(v_build_5255_);
lean_dec_ref(v_file_5254_);
v_a_5422_ = lean_ctor_get(v___x_5420_, 1);
lean_inc(v_a_5422_);
lean_dec_ref(v___x_5420_);
v_val_5423_ = lean_ctor_get(v_a_5421_, 0);
lean_inc(v_val_5423_);
lean_dec_ref(v_a_5421_);
v_a_5328_ = v_val_5423_;
v_a_5329_ = v_a_5422_;
goto v___jp_5327_;
}
else
{
lean_object* v_a_5424_; lean_object* v___x_5425_; 
lean_dec(v_a_5421_);
v_a_5424_ = lean_ctor_get(v___x_5420_, 1);
lean_inc(v_a_5424_);
lean_dec_ref(v___x_5420_);
v___x_5425_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5261_, v_file_5254_, v_trace_5271_, v_a_5307_, v_mtime_5311_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5424_);
if (lean_obj_tag(v___x_5425_) == 0)
{
lean_object* v_a_5426_; lean_object* v_a_5427_; uint8_t v___x_5428_; uint8_t v___x_5429_; uint8_t v___x_5430_; 
v_a_5426_ = lean_ctor_get(v___x_5425_, 0);
lean_inc(v_a_5426_);
v_a_5427_ = lean_ctor_get(v___x_5425_, 1);
lean_inc(v_a_5427_);
lean_dec_ref(v___x_5425_);
v___x_5428_ = 0;
v___x_5429_ = lean_unbox(v_a_5426_);
v___x_5430_ = l_Lake_instDecidableEqOutputStatus(v___x_5429_, v___x_5428_);
if (v___x_5430_ == 0)
{
lean_object* v___x_5431_; uint8_t v___x_5432_; lean_object* v___x_5433_; 
lean_dec_ref(v_trace_5271_);
lean_dec_ref(v_build_5255_);
v___x_5431_ = lean_box(0);
v___x_5432_ = lean_unbox(v_a_5426_);
lean_dec(v_a_5426_);
lean_inc_ref(v_a_5265_);
v___x_5433_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v___x_5432_, v_file_5254_, v_ext_5257_, v_text_5256_, v_exe_5259_, v___y_5419_, v_val_5309_, v_hash_5310_, v___x_5431_, v_a_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5427_);
lean_dec(v_a_5264_);
lean_dec(v_a_5263_);
lean_dec_ref(v_a_5262_);
lean_dec_ref(v_a_5261_);
v___y_5359_ = v___x_5433_;
goto v___jp_5358_;
}
else
{
lean_object* v___x_5434_; 
lean_inc_ref(v_a_5265_);
lean_inc(v_a_5264_);
lean_inc(v_a_5263_);
lean_inc_ref(v_a_5262_);
lean_inc_ref(v_a_5261_);
lean_inc_ref(v___x_5277_);
lean_inc_ref(v_ext_5257_);
lean_inc_ref(v_file_5254_);
v___x_5434_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5254_, v_build_5255_, v_text_5256_, v_ext_5257_, v_trace_5271_, v___x_5277_, v_a_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5427_);
lean_dec_ref(v_trace_5271_);
if (lean_obj_tag(v___x_5434_) == 0)
{
lean_object* v_a_5435_; lean_object* v___x_5436_; uint8_t v___x_5437_; lean_object* v___x_5438_; 
v_a_5435_ = lean_ctor_get(v___x_5434_, 1);
lean_inc(v_a_5435_);
lean_dec_ref(v___x_5434_);
v___x_5436_ = lean_box(0);
v___x_5437_ = lean_unbox(v_a_5426_);
lean_dec(v_a_5426_);
lean_inc_ref(v_a_5265_);
v___x_5438_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v___x_5437_, v_file_5254_, v_ext_5257_, v_text_5256_, v_exe_5259_, v___y_5419_, v_val_5309_, v_hash_5310_, v___x_5436_, v_a_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5435_);
lean_dec(v_a_5264_);
lean_dec(v_a_5263_);
lean_dec_ref(v_a_5262_);
lean_dec_ref(v_a_5261_);
v___y_5359_ = v___x_5438_;
goto v___jp_5358_;
}
else
{
lean_dec(v_a_5426_);
lean_dec(v_wsIdx_5325_);
lean_dec(v_val_5309_);
lean_dec_ref(v_a_5262_);
lean_dec_ref(v___x_5277_);
lean_del_object(v___x_5274_);
lean_dec_ref(v_a_5265_);
lean_dec(v_a_5264_);
lean_dec(v_a_5263_);
lean_dec_ref(v_a_5261_);
lean_dec_ref(v_ext_5257_);
lean_dec_ref(v_file_5254_);
return v___x_5434_;
}
}
}
else
{
lean_object* v_a_5439_; lean_object* v_a_5440_; lean_object* v___x_5442_; uint8_t v_isShared_5443_; uint8_t v_isSharedCheck_5447_; 
lean_dec(v_wsIdx_5325_);
lean_dec(v_val_5309_);
lean_dec_ref(v_a_5262_);
lean_dec_ref(v___x_5277_);
lean_del_object(v___x_5274_);
lean_dec_ref(v_trace_5271_);
lean_dec_ref(v_a_5265_);
lean_dec(v_a_5264_);
lean_dec(v_a_5263_);
lean_dec_ref(v_a_5261_);
lean_dec_ref(v_ext_5257_);
lean_dec_ref(v_build_5255_);
lean_dec_ref(v_file_5254_);
v_a_5439_ = lean_ctor_get(v___x_5425_, 0);
v_a_5440_ = lean_ctor_get(v___x_5425_, 1);
v_isSharedCheck_5447_ = !lean_is_exclusive(v___x_5425_);
if (v_isSharedCheck_5447_ == 0)
{
v___x_5442_ = v___x_5425_;
v_isShared_5443_ = v_isSharedCheck_5447_;
goto v_resetjp_5441_;
}
else
{
lean_inc(v_a_5440_);
lean_inc(v_a_5439_);
lean_dec(v___x_5425_);
v___x_5442_ = lean_box(0);
v_isShared_5443_ = v_isSharedCheck_5447_;
goto v_resetjp_5441_;
}
v_resetjp_5441_:
{
lean_object* v___x_5445_; 
if (v_isShared_5443_ == 0)
{
v___x_5445_ = v___x_5442_;
goto v_reusejp_5444_;
}
else
{
lean_object* v_reuseFailAlloc_5446_; 
v_reuseFailAlloc_5446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5446_, 0, v_a_5439_);
lean_ctor_set(v_reuseFailAlloc_5446_, 1, v_a_5440_);
v___x_5445_ = v_reuseFailAlloc_5446_;
goto v_reusejp_5444_;
}
v_reusejp_5444_:
{
return v___x_5445_;
}
}
}
}
}
else
{
lean_object* v_a_5448_; lean_object* v_a_5449_; lean_object* v___x_5451_; uint8_t v_isShared_5452_; uint8_t v_isSharedCheck_5456_; 
lean_dec(v_wsIdx_5325_);
lean_dec(v_val_5309_);
lean_dec_ref(v_a_5262_);
lean_dec(v_a_5307_);
lean_dec_ref(v___x_5277_);
lean_del_object(v___x_5274_);
lean_dec_ref(v_trace_5271_);
lean_dec_ref(v_a_5265_);
lean_dec(v_a_5264_);
lean_dec(v_a_5263_);
lean_dec_ref(v_a_5261_);
lean_dec_ref(v_ext_5257_);
lean_dec_ref(v_build_5255_);
lean_dec_ref(v_file_5254_);
v_a_5448_ = lean_ctor_get(v___x_5420_, 0);
v_a_5449_ = lean_ctor_get(v___x_5420_, 1);
v_isSharedCheck_5456_ = !lean_is_exclusive(v___x_5420_);
if (v_isSharedCheck_5456_ == 0)
{
v___x_5451_ = v___x_5420_;
v_isShared_5452_ = v_isSharedCheck_5456_;
goto v_resetjp_5450_;
}
else
{
lean_inc(v_a_5449_);
lean_inc(v_a_5448_);
lean_dec(v___x_5420_);
v___x_5451_ = lean_box(0);
v_isShared_5452_ = v_isSharedCheck_5456_;
goto v_resetjp_5450_;
}
v_resetjp_5450_:
{
lean_object* v___x_5454_; 
if (v_isShared_5452_ == 0)
{
v___x_5454_ = v___x_5451_;
goto v_reusejp_5453_;
}
else
{
lean_object* v_reuseFailAlloc_5455_; 
v_reuseFailAlloc_5455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5455_, 0, v_a_5448_);
lean_ctor_set(v_reuseFailAlloc_5455_, 1, v_a_5449_);
v___x_5454_ = v_reuseFailAlloc_5455_;
goto v_reusejp_5453_;
}
v_reusejp_5453_:
{
return v___x_5454_;
}
}
}
}
v___jp_5457_:
{
if (v_restore_5258_ == 0)
{
v___y_5418_ = v_a_5460_;
v___y_5419_ = v_a_5459_;
goto v___jp_5417_;
}
else
{
v___y_5418_ = v_a_5460_;
v___y_5419_ = v___y_5458_;
goto v___jp_5417_;
}
}
v___jp_5461_:
{
if (v_a_5462_ == 0)
{
v_a_5388_ = v_a_5463_;
goto v___jp_5387_;
}
else
{
lean_inc(v_val_5309_);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5363_) == 0)
{
lean_object* v_toContext_5464_; lean_object* v_root_5465_; lean_object* v_config_5466_; lean_object* v_restoreAllArtifacts_x3f_5467_; 
v_toContext_5464_ = lean_ctor_get(v_a_5265_, 1);
v_root_5465_ = lean_ctor_get(v_toContext_5464_, 0);
v_config_5466_ = lean_ctor_get(v_root_5465_, 6);
v_restoreAllArtifacts_x3f_5467_ = lean_ctor_get(v_config_5466_, 25);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5467_) == 0)
{
uint8_t v___x_5468_; 
v___x_5468_ = 0;
v___y_5458_ = v_a_5462_;
v_a_5459_ = v___x_5468_;
v_a_5460_ = v_a_5463_;
goto v___jp_5457_;
}
else
{
lean_object* v_val_5469_; uint8_t v___x_5470_; 
v_val_5469_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5467_, 0);
v___x_5470_ = lean_unbox(v_val_5469_);
v___y_5458_ = v_a_5462_;
v_a_5459_ = v___x_5470_;
v_a_5460_ = v_a_5463_;
goto v___jp_5457_;
}
}
else
{
lean_object* v_val_5471_; uint8_t v___x_5472_; 
v_val_5471_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5363_, 0);
v___x_5472_ = lean_unbox(v_val_5471_);
v___y_5458_ = v_a_5462_;
v_a_5459_ = v___x_5472_;
v_a_5460_ = v_a_5463_;
goto v___jp_5457_;
}
}
}
}
else
{
lean_object* v_a_5486_; lean_object* v_a_5487_; lean_object* v_mtime_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; 
lean_del_object(v___x_5274_);
v_a_5486_ = lean_ctor_get(v___x_5306_, 0);
lean_inc(v_a_5486_);
v_a_5487_ = lean_ctor_get(v___x_5306_, 1);
lean_inc(v_a_5487_);
lean_dec_ref(v___x_5306_);
v_mtime_5488_ = lean_ctor_get(v_trace_5271_, 2);
lean_inc_ref(v_trace_5271_);
v___x_5489_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5489_, 0, v_a_5487_);
lean_ctor_set(v___x_5489_, 1, v_trace_5271_);
lean_ctor_set(v___x_5489_, 2, v_buildTime_5272_);
lean_ctor_set_uint8(v___x_5489_, sizeof(void*)*3, v_action_5269_);
lean_ctor_set_uint8(v___x_5489_, sizeof(void*)*3 + 1, v_wantsRebuild_5270_);
v___x_5490_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5261_, v_file_5254_, v_trace_5271_, v_a_5486_, v_mtime_5488_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v___x_5489_);
if (lean_obj_tag(v___x_5490_) == 0)
{
lean_object* v_a_5491_; lean_object* v_a_5492_; uint8_t v___x_5493_; uint8_t v___x_5494_; uint8_t v___x_5495_; 
v_a_5491_ = lean_ctor_get(v___x_5490_, 0);
lean_inc(v_a_5491_);
v_a_5492_ = lean_ctor_get(v___x_5490_, 1);
lean_inc(v_a_5492_);
lean_dec_ref(v___x_5490_);
v___x_5493_ = 0;
v___x_5494_ = lean_unbox(v_a_5491_);
lean_dec(v_a_5491_);
v___x_5495_ = l_Lake_instDecidableEqOutputStatus(v___x_5494_, v___x_5493_);
if (v___x_5495_ == 0)
{
lean_object* v___x_5496_; 
lean_dec_ref(v_trace_5271_);
lean_dec(v_a_5264_);
lean_dec(v_a_5263_);
lean_dec(v_a_5262_);
lean_dec_ref(v_a_5261_);
lean_dec_ref(v_build_5255_);
v___x_5496_ = l_Lake_computeArtifact___redArg(v_file_5254_, v_ext_5257_, v_text_5256_, v_a_5265_, v_a_5492_);
lean_dec_ref(v_a_5265_);
if (lean_obj_tag(v___x_5496_) == 0)
{
lean_object* v_a_5497_; lean_object* v_a_5498_; 
v_a_5497_ = lean_ctor_get(v___x_5496_, 0);
lean_inc(v_a_5497_);
v_a_5498_ = lean_ctor_get(v___x_5496_, 1);
lean_inc(v_a_5498_);
lean_dec_ref(v___x_5496_);
v_art_5279_ = v_a_5497_;
v___y_5280_ = v_a_5498_;
goto v___jp_5278_;
}
else
{
lean_dec_ref(v___x_5277_);
return v___x_5496_;
}
}
else
{
lean_object* v___x_5499_; 
lean_inc_ref(v___x_5277_);
v___x_5499_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5254_, v_build_5255_, v_text_5256_, v_ext_5257_, v_trace_5271_, v___x_5277_, v_a_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5492_);
lean_dec_ref(v_trace_5271_);
if (lean_obj_tag(v___x_5499_) == 0)
{
lean_object* v_a_5500_; lean_object* v_a_5501_; 
v_a_5500_ = lean_ctor_get(v___x_5499_, 0);
lean_inc(v_a_5500_);
v_a_5501_ = lean_ctor_get(v___x_5499_, 1);
lean_inc(v_a_5501_);
lean_dec_ref(v___x_5499_);
v_art_5279_ = v_a_5500_;
v___y_5280_ = v_a_5501_;
goto v___jp_5278_;
}
else
{
lean_dec_ref(v___x_5277_);
return v___x_5499_;
}
}
}
else
{
lean_object* v_a_5502_; lean_object* v_a_5503_; lean_object* v___x_5505_; uint8_t v_isShared_5506_; uint8_t v_isSharedCheck_5510_; 
lean_dec_ref(v___x_5277_);
lean_dec_ref(v_trace_5271_);
lean_dec_ref(v_a_5265_);
lean_dec(v_a_5264_);
lean_dec(v_a_5263_);
lean_dec(v_a_5262_);
lean_dec_ref(v_a_5261_);
lean_dec_ref(v_ext_5257_);
lean_dec_ref(v_build_5255_);
lean_dec_ref(v_file_5254_);
v_a_5502_ = lean_ctor_get(v___x_5490_, 0);
v_a_5503_ = lean_ctor_get(v___x_5490_, 1);
v_isSharedCheck_5510_ = !lean_is_exclusive(v___x_5490_);
if (v_isSharedCheck_5510_ == 0)
{
v___x_5505_ = v___x_5490_;
v_isShared_5506_ = v_isSharedCheck_5510_;
goto v_resetjp_5504_;
}
else
{
lean_inc(v_a_5503_);
lean_inc(v_a_5502_);
lean_dec(v___x_5490_);
v___x_5505_ = lean_box(0);
v_isShared_5506_ = v_isSharedCheck_5510_;
goto v_resetjp_5504_;
}
v_resetjp_5504_:
{
lean_object* v___x_5508_; 
if (v_isShared_5506_ == 0)
{
v___x_5508_ = v___x_5505_;
goto v_reusejp_5507_;
}
else
{
lean_object* v_reuseFailAlloc_5509_; 
v_reuseFailAlloc_5509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5509_, 0, v_a_5502_);
lean_ctor_set(v_reuseFailAlloc_5509_, 1, v_a_5503_);
v___x_5508_ = v_reuseFailAlloc_5509_;
goto v_reusejp_5507_;
}
v_reusejp_5507_:
{
return v___x_5508_;
}
}
}
}
}
else
{
lean_object* v_a_5511_; lean_object* v_a_5512_; lean_object* v___x_5514_; uint8_t v_isShared_5515_; uint8_t v_isSharedCheck_5520_; 
lean_dec_ref(v___x_5277_);
lean_del_object(v___x_5274_);
lean_dec_ref(v_a_5265_);
lean_dec(v_a_5264_);
lean_dec(v_a_5263_);
lean_dec(v_a_5262_);
lean_dec_ref(v_a_5261_);
lean_dec_ref(v_ext_5257_);
lean_dec_ref(v_build_5255_);
lean_dec_ref(v_file_5254_);
v_a_5511_ = lean_ctor_get(v___x_5306_, 0);
v_a_5512_ = lean_ctor_get(v___x_5306_, 1);
v_isSharedCheck_5520_ = !lean_is_exclusive(v___x_5306_);
if (v_isSharedCheck_5520_ == 0)
{
v___x_5514_ = v___x_5306_;
v_isShared_5515_ = v_isSharedCheck_5520_;
goto v_resetjp_5513_;
}
else
{
lean_inc(v_a_5512_);
lean_inc(v_a_5511_);
lean_dec(v___x_5306_);
v___x_5514_ = lean_box(0);
v_isShared_5515_ = v_isSharedCheck_5520_;
goto v_resetjp_5513_;
}
v_resetjp_5513_:
{
lean_object* v___x_5516_; lean_object* v___x_5518_; 
v___x_5516_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5516_, 0, v_a_5512_);
lean_ctor_set(v___x_5516_, 1, v_trace_5271_);
lean_ctor_set(v___x_5516_, 2, v_buildTime_5272_);
lean_ctor_set_uint8(v___x_5516_, sizeof(void*)*3, v_action_5269_);
lean_ctor_set_uint8(v___x_5516_, sizeof(void*)*3 + 1, v_wantsRebuild_5270_);
if (v_isShared_5515_ == 0)
{
lean_ctor_set(v___x_5514_, 1, v___x_5516_);
v___x_5518_ = v___x_5514_;
goto v_reusejp_5517_;
}
else
{
lean_object* v_reuseFailAlloc_5519_; 
v_reuseFailAlloc_5519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_a_5511_);
lean_ctor_set(v_reuseFailAlloc_5519_, 1, v___x_5516_);
v___x_5518_ = v_reuseFailAlloc_5519_;
goto v_reusejp_5517_;
}
v_reusejp_5517_:
{
return v___x_5518_;
}
}
}
v___jp_5278_:
{
lean_object* v_log_5281_; uint8_t v_action_5282_; uint8_t v_wantsRebuild_5283_; lean_object* v_buildTime_5284_; lean_object* v___x_5286_; uint8_t v_isShared_5287_; uint8_t v_isSharedCheck_5293_; 
v_log_5281_ = lean_ctor_get(v___y_5280_, 0);
v_action_5282_ = lean_ctor_get_uint8(v___y_5280_, sizeof(void*)*3);
v_wantsRebuild_5283_ = lean_ctor_get_uint8(v___y_5280_, sizeof(void*)*3 + 1);
v_buildTime_5284_ = lean_ctor_get(v___y_5280_, 2);
v_isSharedCheck_5293_ = !lean_is_exclusive(v___y_5280_);
if (v_isSharedCheck_5293_ == 0)
{
lean_object* v_unused_5294_; 
v_unused_5294_ = lean_ctor_get(v___y_5280_, 1);
lean_dec(v_unused_5294_);
v___x_5286_ = v___y_5280_;
v_isShared_5287_ = v_isSharedCheck_5293_;
goto v_resetjp_5285_;
}
else
{
lean_inc(v_buildTime_5284_);
lean_inc(v_log_5281_);
lean_dec(v___y_5280_);
v___x_5286_ = lean_box(0);
v_isShared_5287_ = v_isSharedCheck_5293_;
goto v_resetjp_5285_;
}
v_resetjp_5285_:
{
lean_object* v___x_5288_; lean_object* v___x_5290_; 
v___x_5288_ = l_Lake_Artifact_trace(v_art_5279_);
if (v_isShared_5287_ == 0)
{
lean_ctor_set(v___x_5286_, 1, v___x_5288_);
v___x_5290_ = v___x_5286_;
goto v_reusejp_5289_;
}
else
{
lean_object* v_reuseFailAlloc_5292_; 
v_reuseFailAlloc_5292_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5292_, 0, v_log_5281_);
lean_ctor_set(v_reuseFailAlloc_5292_, 1, v___x_5288_);
lean_ctor_set(v_reuseFailAlloc_5292_, 2, v_buildTime_5284_);
lean_ctor_set_uint8(v_reuseFailAlloc_5292_, sizeof(void*)*3, v_action_5282_);
lean_ctor_set_uint8(v_reuseFailAlloc_5292_, sizeof(void*)*3 + 1, v_wantsRebuild_5283_);
v___x_5290_ = v_reuseFailAlloc_5292_;
goto v_reusejp_5289_;
}
v_reusejp_5289_:
{
lean_object* v___x_5291_; 
v___x_5291_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_5279_, v___x_5277_, v___x_5290_);
lean_dec_ref(v___x_5277_);
return v___x_5291_;
}
}
}
v___jp_5295_:
{
lean_object* v___x_5301_; lean_object* v___x_5303_; 
v___x_5301_ = l_Lake_Artifact_trace(v___y_5296_);
if (v_isShared_5275_ == 0)
{
lean_ctor_set(v___x_5274_, 2, v_buildTime_5300_);
lean_ctor_set(v___x_5274_, 1, v___x_5301_);
lean_ctor_set(v___x_5274_, 0, v_log_5297_);
v___x_5303_ = v___x_5274_;
goto v_reusejp_5302_;
}
else
{
lean_object* v_reuseFailAlloc_5305_; 
v_reuseFailAlloc_5305_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5305_, 0, v_log_5297_);
lean_ctor_set(v_reuseFailAlloc_5305_, 1, v___x_5301_);
lean_ctor_set(v_reuseFailAlloc_5305_, 2, v_buildTime_5300_);
v___x_5303_ = v_reuseFailAlloc_5305_;
goto v_reusejp_5302_;
}
v_reusejp_5302_:
{
lean_object* v___x_5304_; 
lean_ctor_set_uint8(v___x_5303_, sizeof(void*)*3, v_action_5298_);
lean_ctor_set_uint8(v___x_5303_, sizeof(void*)*3 + 1, v_wantsRebuild_5299_);
v___x_5304_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v___y_5296_, v___x_5277_, v___x_5303_);
lean_dec_ref(v___x_5277_);
return v___x_5304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___boxed(lean_object* v_file_5522_, lean_object* v_build_5523_, lean_object* v_text_5524_, lean_object* v_ext_5525_, lean_object* v_restore_5526_, lean_object* v_exe_5527_, lean_object* v_platformIndependent_5528_, lean_object* v_a_5529_, lean_object* v_a_5530_, lean_object* v_a_5531_, lean_object* v_a_5532_, lean_object* v_a_5533_, lean_object* v_a_5534_, lean_object* v_a_5535_){
_start:
{
uint8_t v_text_boxed_5536_; uint8_t v_restore_boxed_5537_; uint8_t v_exe_boxed_5538_; uint8_t v_platformIndependent_boxed_5539_; lean_object* v_res_5540_; 
v_text_boxed_5536_ = lean_unbox(v_text_5524_);
v_restore_boxed_5537_ = lean_unbox(v_restore_5526_);
v_exe_boxed_5538_ = lean_unbox(v_exe_5527_);
v_platformIndependent_boxed_5539_ = lean_unbox(v_platformIndependent_5528_);
v_res_5540_ = l_Lake_buildArtifactUnlessUpToDate(v_file_5522_, v_build_5523_, v_text_boxed_5536_, v_ext_5525_, v_restore_boxed_5537_, v_exe_boxed_5538_, v_platformIndependent_boxed_5539_, v_a_5529_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_);
return v_res_5540_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(uint8_t v_exe_5541_, lean_object* v___y_5542_, uint64_t v_inputHash_5543_, lean_object* v_pkg_5544_, lean_object* v_a_5545_, lean_object* v_a_5546_, lean_object* v_a_5547_, lean_object* v_a_5548_, lean_object* v_a_5549_){
_start:
{
lean_object* v___x_5551_; 
v___x_5551_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___redArg(v_exe_5541_, v_inputHash_5543_, v_pkg_5544_, v_a_5548_, v_a_5549_);
return v___x_5551_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object* v_exe_5552_, lean_object* v___y_5553_, lean_object* v_inputHash_5554_, lean_object* v_pkg_5555_, lean_object* v_a_5556_, lean_object* v_a_5557_, lean_object* v_a_5558_, lean_object* v_a_5559_, lean_object* v_a_5560_, lean_object* v_a_5561_){
_start:
{
uint8_t v_exe_boxed_5562_; uint64_t v_inputHash_boxed_5563_; lean_object* v_res_5564_; 
v_exe_boxed_5562_ = lean_unbox(v_exe_5552_);
v_inputHash_boxed_5563_ = lean_unbox_uint64(v_inputHash_5554_);
lean_dec_ref(v_inputHash_5554_);
v_res_5564_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(v_exe_boxed_5562_, v___y_5553_, v_inputHash_boxed_5563_, v_pkg_5555_, v_a_5556_, v_a_5557_, v_a_5558_, v_a_5559_, v_a_5560_);
lean_dec(v_a_5558_);
lean_dec(v_a_5557_);
lean_dec(v_a_5556_);
lean_dec_ref(v___y_5553_);
return v_res_5564_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0(lean_object* v_extraDepTrace_5566_, lean_object* v_build_5567_, lean_object* v_file_5568_, uint8_t v_text_5569_, lean_object* v_depInfo_5570_, lean_object* v___y_5571_, lean_object* v___y_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_, lean_object* v___y_5576_){
_start:
{
lean_object* v___x_5578_; 
lean_inc_ref(v___y_5575_);
lean_inc(v___y_5574_);
lean_inc(v___y_5573_);
lean_inc(v___y_5572_);
lean_inc_ref(v___y_5571_);
v___x_5578_ = lean_apply_7(v_extraDepTrace_5566_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_, v___y_5576_, lean_box(0));
if (lean_obj_tag(v___x_5578_) == 0)
{
lean_object* v_a_5579_; lean_object* v_a_5580_; lean_object* v_log_5581_; uint8_t v_action_5582_; uint8_t v_wantsRebuild_5583_; lean_object* v_trace_5584_; lean_object* v_buildTime_5585_; lean_object* v___x_5587_; uint8_t v_isShared_5588_; uint8_t v_isSharedCheck_5616_; 
v_a_5579_ = lean_ctor_get(v___x_5578_, 1);
lean_inc(v_a_5579_);
v_a_5580_ = lean_ctor_get(v___x_5578_, 0);
lean_inc(v_a_5580_);
lean_dec_ref(v___x_5578_);
v_log_5581_ = lean_ctor_get(v_a_5579_, 0);
v_action_5582_ = lean_ctor_get_uint8(v_a_5579_, sizeof(void*)*3);
v_wantsRebuild_5583_ = lean_ctor_get_uint8(v_a_5579_, sizeof(void*)*3 + 1);
v_trace_5584_ = lean_ctor_get(v_a_5579_, 1);
v_buildTime_5585_ = lean_ctor_get(v_a_5579_, 2);
v_isSharedCheck_5616_ = !lean_is_exclusive(v_a_5579_);
if (v_isSharedCheck_5616_ == 0)
{
v___x_5587_ = v_a_5579_;
v_isShared_5588_ = v_isSharedCheck_5616_;
goto v_resetjp_5586_;
}
else
{
lean_inc(v_buildTime_5585_);
lean_inc(v_trace_5584_);
lean_inc(v_log_5581_);
lean_dec(v_a_5579_);
v___x_5587_ = lean_box(0);
v_isShared_5588_ = v_isSharedCheck_5616_;
goto v_resetjp_5586_;
}
v_resetjp_5586_:
{
lean_object* v___x_5589_; lean_object* v___x_5591_; 
v___x_5589_ = l_Lake_BuildTrace_mix(v_trace_5584_, v_a_5580_);
if (v_isShared_5588_ == 0)
{
lean_ctor_set(v___x_5587_, 1, v___x_5589_);
v___x_5591_ = v___x_5587_;
goto v_reusejp_5590_;
}
else
{
lean_object* v_reuseFailAlloc_5615_; 
v_reuseFailAlloc_5615_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5615_, 0, v_log_5581_);
lean_ctor_set(v_reuseFailAlloc_5615_, 1, v___x_5589_);
lean_ctor_set(v_reuseFailAlloc_5615_, 2, v_buildTime_5585_);
lean_ctor_set_uint8(v_reuseFailAlloc_5615_, sizeof(void*)*3, v_action_5582_);
lean_ctor_set_uint8(v_reuseFailAlloc_5615_, sizeof(void*)*3 + 1, v_wantsRebuild_5583_);
v___x_5591_ = v_reuseFailAlloc_5615_;
goto v_reusejp_5590_;
}
v_reusejp_5590_:
{
lean_object* v___x_5592_; lean_object* v___x_5593_; uint8_t v___x_5594_; lean_object* v___x_5595_; 
v___x_5592_ = lean_apply_1(v_build_5567_, v_depInfo_5570_);
v___x_5593_ = ((lean_object*)(l_Lake_buildFileAfterDep___redArg___lam__0___closed__0));
v___x_5594_ = 0;
v___x_5595_ = l_Lake_buildArtifactUnlessUpToDate(v_file_5568_, v___x_5592_, v_text_5569_, v___x_5593_, v___x_5594_, v___x_5594_, v___x_5594_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_, v___x_5591_);
if (lean_obj_tag(v___x_5595_) == 0)
{
lean_object* v_a_5596_; lean_object* v_a_5597_; lean_object* v___x_5599_; uint8_t v_isShared_5600_; uint8_t v_isSharedCheck_5605_; 
v_a_5596_ = lean_ctor_get(v___x_5595_, 0);
v_a_5597_ = lean_ctor_get(v___x_5595_, 1);
v_isSharedCheck_5605_ = !lean_is_exclusive(v___x_5595_);
if (v_isSharedCheck_5605_ == 0)
{
v___x_5599_ = v___x_5595_;
v_isShared_5600_ = v_isSharedCheck_5605_;
goto v_resetjp_5598_;
}
else
{
lean_inc(v_a_5597_);
lean_inc(v_a_5596_);
lean_dec(v___x_5595_);
v___x_5599_ = lean_box(0);
v_isShared_5600_ = v_isSharedCheck_5605_;
goto v_resetjp_5598_;
}
v_resetjp_5598_:
{
lean_object* v_path_5601_; lean_object* v___x_5603_; 
v_path_5601_ = lean_ctor_get(v_a_5596_, 1);
lean_inc_ref(v_path_5601_);
lean_dec(v_a_5596_);
if (v_isShared_5600_ == 0)
{
lean_ctor_set(v___x_5599_, 0, v_path_5601_);
v___x_5603_ = v___x_5599_;
goto v_reusejp_5602_;
}
else
{
lean_object* v_reuseFailAlloc_5604_; 
v_reuseFailAlloc_5604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5604_, 0, v_path_5601_);
lean_ctor_set(v_reuseFailAlloc_5604_, 1, v_a_5597_);
v___x_5603_ = v_reuseFailAlloc_5604_;
goto v_reusejp_5602_;
}
v_reusejp_5602_:
{
return v___x_5603_;
}
}
}
else
{
lean_object* v_a_5606_; lean_object* v_a_5607_; lean_object* v___x_5609_; uint8_t v_isShared_5610_; uint8_t v_isSharedCheck_5614_; 
v_a_5606_ = lean_ctor_get(v___x_5595_, 0);
v_a_5607_ = lean_ctor_get(v___x_5595_, 1);
v_isSharedCheck_5614_ = !lean_is_exclusive(v___x_5595_);
if (v_isSharedCheck_5614_ == 0)
{
v___x_5609_ = v___x_5595_;
v_isShared_5610_ = v_isSharedCheck_5614_;
goto v_resetjp_5608_;
}
else
{
lean_inc(v_a_5607_);
lean_inc(v_a_5606_);
lean_dec(v___x_5595_);
v___x_5609_ = lean_box(0);
v_isShared_5610_ = v_isSharedCheck_5614_;
goto v_resetjp_5608_;
}
v_resetjp_5608_:
{
lean_object* v___x_5612_; 
if (v_isShared_5610_ == 0)
{
v___x_5612_ = v___x_5609_;
goto v_reusejp_5611_;
}
else
{
lean_object* v_reuseFailAlloc_5613_; 
v_reuseFailAlloc_5613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5613_, 0, v_a_5606_);
lean_ctor_set(v_reuseFailAlloc_5613_, 1, v_a_5607_);
v___x_5612_ = v_reuseFailAlloc_5613_;
goto v_reusejp_5611_;
}
v_reusejp_5611_:
{
return v___x_5612_;
}
}
}
}
}
}
else
{
lean_object* v_a_5617_; lean_object* v_a_5618_; lean_object* v___x_5620_; uint8_t v_isShared_5621_; uint8_t v_isSharedCheck_5625_; 
lean_dec_ref(v___y_5575_);
lean_dec(v___y_5574_);
lean_dec(v___y_5573_);
lean_dec(v___y_5572_);
lean_dec_ref(v___y_5571_);
lean_dec(v_depInfo_5570_);
lean_dec_ref(v_file_5568_);
lean_dec_ref(v_build_5567_);
v_a_5617_ = lean_ctor_get(v___x_5578_, 0);
v_a_5618_ = lean_ctor_get(v___x_5578_, 1);
v_isSharedCheck_5625_ = !lean_is_exclusive(v___x_5578_);
if (v_isSharedCheck_5625_ == 0)
{
v___x_5620_ = v___x_5578_;
v_isShared_5621_ = v_isSharedCheck_5625_;
goto v_resetjp_5619_;
}
else
{
lean_inc(v_a_5618_);
lean_inc(v_a_5617_);
lean_dec(v___x_5578_);
v___x_5620_ = lean_box(0);
v_isShared_5621_ = v_isSharedCheck_5625_;
goto v_resetjp_5619_;
}
v_resetjp_5619_:
{
lean_object* v___x_5623_; 
if (v_isShared_5621_ == 0)
{
v___x_5623_ = v___x_5620_;
goto v_reusejp_5622_;
}
else
{
lean_object* v_reuseFailAlloc_5624_; 
v_reuseFailAlloc_5624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5624_, 0, v_a_5617_);
lean_ctor_set(v_reuseFailAlloc_5624_, 1, v_a_5618_);
v___x_5623_ = v_reuseFailAlloc_5624_;
goto v_reusejp_5622_;
}
v_reusejp_5622_:
{
return v___x_5623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___boxed(lean_object* v_extraDepTrace_5626_, lean_object* v_build_5627_, lean_object* v_file_5628_, lean_object* v_text_5629_, lean_object* v_depInfo_5630_, lean_object* v___y_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_){
_start:
{
uint8_t v_text_boxed_5638_; lean_object* v_res_5639_; 
v_text_boxed_5638_ = lean_unbox(v_text_5629_);
v_res_5639_ = l_Lake_buildFileAfterDep___redArg___lam__0(v_extraDepTrace_5626_, v_build_5627_, v_file_5628_, v_text_boxed_5638_, v_depInfo_5630_, v___y_5631_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_, v___y_5636_);
return v_res_5639_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg(lean_object* v_file_5640_, lean_object* v_dep_5641_, lean_object* v_build_5642_, lean_object* v_extraDepTrace_5643_, uint8_t v_text_5644_, lean_object* v_a_5645_, lean_object* v_a_5646_, lean_object* v_a_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_){
_start:
{
lean_object* v___x_5652_; lean_object* v___f_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; uint8_t v___x_5656_; lean_object* v___x_5657_; 
v___x_5652_ = lean_box(v_text_5644_);
v___f_5653_ = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_5653_, 0, v_extraDepTrace_5643_);
lean_closure_set(v___f_5653_, 1, v_build_5642_);
lean_closure_set(v___f_5653_, 2, v_file_5640_);
lean_closure_set(v___f_5653_, 3, v___x_5652_);
v___x_5654_ = l_Lake_instDataKindFilePath;
v___x_5655_ = lean_unsigned_to_nat(0u);
v___x_5656_ = 0;
v___x_5657_ = l_Lake_Job_mapM___redArg(v___x_5654_, v_dep_5641_, v___f_5653_, v___x_5655_, v___x_5656_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_);
return v___x_5657_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___boxed(lean_object* v_file_5658_, lean_object* v_dep_5659_, lean_object* v_build_5660_, lean_object* v_extraDepTrace_5661_, lean_object* v_text_5662_, lean_object* v_a_5663_, lean_object* v_a_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_, lean_object* v_a_5668_, lean_object* v_a_5669_){
_start:
{
uint8_t v_text_boxed_5670_; lean_object* v_res_5671_; 
v_text_boxed_5670_ = lean_unbox(v_text_5662_);
v_res_5671_ = l_Lake_buildFileAfterDep___redArg(v_file_5658_, v_dep_5659_, v_build_5660_, v_extraDepTrace_5661_, v_text_boxed_5670_, v_a_5663_, v_a_5664_, v_a_5665_, v_a_5666_, v_a_5667_, v_a_5668_);
return v_res_5671_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object* v_00_u03b1_5672_, lean_object* v_file_5673_, lean_object* v_dep_5674_, lean_object* v_build_5675_, lean_object* v_extraDepTrace_5676_, uint8_t v_text_5677_, lean_object* v_a_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_, lean_object* v_a_5681_, lean_object* v_a_5682_, lean_object* v_a_5683_){
_start:
{
lean_object* v___x_5685_; lean_object* v___f_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; uint8_t v___x_5689_; lean_object* v___x_5690_; 
v___x_5685_ = lean_box(v_text_5677_);
v___f_5686_ = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_5686_, 0, v_extraDepTrace_5676_);
lean_closure_set(v___f_5686_, 1, v_build_5675_);
lean_closure_set(v___f_5686_, 2, v_file_5673_);
lean_closure_set(v___f_5686_, 3, v___x_5685_);
v___x_5687_ = l_Lake_instDataKindFilePath;
v___x_5688_ = lean_unsigned_to_nat(0u);
v___x_5689_ = 0;
v___x_5690_ = l_Lake_Job_mapM___redArg(v___x_5687_, v_dep_5674_, v___f_5686_, v___x_5688_, v___x_5689_, v_a_5678_, v_a_5679_, v_a_5680_, v_a_5681_, v_a_5682_, v_a_5683_);
return v___x_5690_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___boxed(lean_object* v_00_u03b1_5691_, lean_object* v_file_5692_, lean_object* v_dep_5693_, lean_object* v_build_5694_, lean_object* v_extraDepTrace_5695_, lean_object* v_text_5696_, lean_object* v_a_5697_, lean_object* v_a_5698_, lean_object* v_a_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_, lean_object* v_a_5703_){
_start:
{
uint8_t v_text_boxed_5704_; lean_object* v_res_5705_; 
v_text_boxed_5704_ = lean_unbox(v_text_5696_);
v_res_5705_ = l_Lake_buildFileAfterDep(v_00_u03b1_5691_, v_file_5692_, v_dep_5693_, v_build_5694_, v_extraDepTrace_5695_, v_text_boxed_5704_, v_a_5697_, v_a_5698_, v_a_5699_, v_a_5700_, v_a_5701_, v_a_5702_);
return v_res_5705_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(lean_object* v_info_5706_){
_start:
{
lean_object* v___x_5708_; 
v___x_5708_ = l_Lake_computeBinFileHash(v_info_5706_);
if (lean_obj_tag(v___x_5708_) == 0)
{
lean_object* v_a_5709_; lean_object* v___x_5710_; 
v_a_5709_ = lean_ctor_get(v___x_5708_, 0);
lean_inc(v_a_5709_);
lean_dec_ref(v___x_5708_);
v___x_5710_ = lean_io_metadata(v_info_5706_);
if (lean_obj_tag(v___x_5710_) == 0)
{
lean_object* v_a_5711_; lean_object* v___x_5713_; uint8_t v_isShared_5714_; uint8_t v_isSharedCheck_5722_; 
v_a_5711_ = lean_ctor_get(v___x_5710_, 0);
v_isSharedCheck_5722_ = !lean_is_exclusive(v___x_5710_);
if (v_isSharedCheck_5722_ == 0)
{
v___x_5713_ = v___x_5710_;
v_isShared_5714_ = v_isSharedCheck_5722_;
goto v_resetjp_5712_;
}
else
{
lean_inc(v_a_5711_);
lean_dec(v___x_5710_);
v___x_5713_ = lean_box(0);
v_isShared_5714_ = v_isSharedCheck_5722_;
goto v_resetjp_5712_;
}
v_resetjp_5712_:
{
lean_object* v_modified_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; uint64_t v___x_5718_; lean_object* v___x_5720_; 
v_modified_5715_ = lean_ctor_get(v_a_5711_, 1);
lean_inc_ref(v_modified_5715_);
lean_dec(v_a_5711_);
v___x_5716_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_5717_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_5717_, 0, v_info_5706_);
lean_ctor_set(v___x_5717_, 1, v___x_5716_);
lean_ctor_set(v___x_5717_, 2, v_modified_5715_);
v___x_5718_ = lean_unbox_uint64(v_a_5709_);
lean_dec(v_a_5709_);
lean_ctor_set_uint64(v___x_5717_, sizeof(void*)*3, v___x_5718_);
if (v_isShared_5714_ == 0)
{
lean_ctor_set(v___x_5713_, 0, v___x_5717_);
v___x_5720_ = v___x_5713_;
goto v_reusejp_5719_;
}
else
{
lean_object* v_reuseFailAlloc_5721_; 
v_reuseFailAlloc_5721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5721_, 0, v___x_5717_);
v___x_5720_ = v_reuseFailAlloc_5721_;
goto v_reusejp_5719_;
}
v_reusejp_5719_:
{
return v___x_5720_;
}
}
}
else
{
lean_object* v_a_5723_; lean_object* v___x_5725_; uint8_t v_isShared_5726_; uint8_t v_isSharedCheck_5730_; 
lean_dec(v_a_5709_);
lean_dec_ref(v_info_5706_);
v_a_5723_ = lean_ctor_get(v___x_5710_, 0);
v_isSharedCheck_5730_ = !lean_is_exclusive(v___x_5710_);
if (v_isSharedCheck_5730_ == 0)
{
v___x_5725_ = v___x_5710_;
v_isShared_5726_ = v_isSharedCheck_5730_;
goto v_resetjp_5724_;
}
else
{
lean_inc(v_a_5723_);
lean_dec(v___x_5710_);
v___x_5725_ = lean_box(0);
v_isShared_5726_ = v_isSharedCheck_5730_;
goto v_resetjp_5724_;
}
v_resetjp_5724_:
{
lean_object* v___x_5728_; 
if (v_isShared_5726_ == 0)
{
v___x_5728_ = v___x_5725_;
goto v_reusejp_5727_;
}
else
{
lean_object* v_reuseFailAlloc_5729_; 
v_reuseFailAlloc_5729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5729_, 0, v_a_5723_);
v___x_5728_ = v_reuseFailAlloc_5729_;
goto v_reusejp_5727_;
}
v_reusejp_5727_:
{
return v___x_5728_;
}
}
}
}
else
{
lean_object* v_a_5731_; lean_object* v___x_5733_; uint8_t v_isShared_5734_; uint8_t v_isSharedCheck_5738_; 
lean_dec_ref(v_info_5706_);
v_a_5731_ = lean_ctor_get(v___x_5708_, 0);
v_isSharedCheck_5738_ = !lean_is_exclusive(v___x_5708_);
if (v_isSharedCheck_5738_ == 0)
{
v___x_5733_ = v___x_5708_;
v_isShared_5734_ = v_isSharedCheck_5738_;
goto v_resetjp_5732_;
}
else
{
lean_inc(v_a_5731_);
lean_dec(v___x_5708_);
v___x_5733_ = lean_box(0);
v_isShared_5734_ = v_isSharedCheck_5738_;
goto v_resetjp_5732_;
}
v_resetjp_5732_:
{
lean_object* v___x_5736_; 
if (v_isShared_5734_ == 0)
{
v___x_5736_ = v___x_5733_;
goto v_reusejp_5735_;
}
else
{
lean_object* v_reuseFailAlloc_5737_; 
v_reuseFailAlloc_5737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5737_, 0, v_a_5731_);
v___x_5736_ = v_reuseFailAlloc_5737_;
goto v_reusejp_5735_;
}
v_reusejp_5735_:
{
return v___x_5736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0___boxed(lean_object* v_info_5739_, lean_object* v_a_5740_){
_start:
{
lean_object* v_res_5741_; 
v_res_5741_ = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(v_info_5739_);
return v_res_5741_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0(lean_object* v_path_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_, lean_object* v___y_5745_, lean_object* v___y_5746_, lean_object* v___y_5747_, lean_object* v___y_5748_){
_start:
{
lean_object* v_log_5750_; uint8_t v_action_5751_; uint8_t v_wantsRebuild_5752_; lean_object* v_trace_5753_; lean_object* v_buildTime_5754_; lean_object* v___x_5756_; uint8_t v_isShared_5757_; uint8_t v_isSharedCheck_5774_; 
v_log_5750_ = lean_ctor_get(v___y_5748_, 0);
v_action_5751_ = lean_ctor_get_uint8(v___y_5748_, sizeof(void*)*3);
v_wantsRebuild_5752_ = lean_ctor_get_uint8(v___y_5748_, sizeof(void*)*3 + 1);
v_trace_5753_ = lean_ctor_get(v___y_5748_, 1);
v_buildTime_5754_ = lean_ctor_get(v___y_5748_, 2);
v_isSharedCheck_5774_ = !lean_is_exclusive(v___y_5748_);
if (v_isSharedCheck_5774_ == 0)
{
v___x_5756_ = v___y_5748_;
v_isShared_5757_ = v_isSharedCheck_5774_;
goto v_resetjp_5755_;
}
else
{
lean_inc(v_buildTime_5754_);
lean_inc(v_trace_5753_);
lean_inc(v_log_5750_);
lean_dec(v___y_5748_);
v___x_5756_ = lean_box(0);
v_isShared_5757_ = v_isSharedCheck_5774_;
goto v_resetjp_5755_;
}
v_resetjp_5755_:
{
lean_object* v___x_5758_; 
lean_inc_ref(v_path_5742_);
v___x_5758_ = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(v_path_5742_);
if (lean_obj_tag(v___x_5758_) == 0)
{
lean_object* v_a_5759_; lean_object* v___x_5761_; 
lean_dec_ref(v_trace_5753_);
v_a_5759_ = lean_ctor_get(v___x_5758_, 0);
lean_inc(v_a_5759_);
lean_dec_ref(v___x_5758_);
if (v_isShared_5757_ == 0)
{
lean_ctor_set(v___x_5756_, 1, v_a_5759_);
v___x_5761_ = v___x_5756_;
goto v_reusejp_5760_;
}
else
{
lean_object* v_reuseFailAlloc_5763_; 
v_reuseFailAlloc_5763_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5763_, 0, v_log_5750_);
lean_ctor_set(v_reuseFailAlloc_5763_, 1, v_a_5759_);
lean_ctor_set(v_reuseFailAlloc_5763_, 2, v_buildTime_5754_);
lean_ctor_set_uint8(v_reuseFailAlloc_5763_, sizeof(void*)*3, v_action_5751_);
lean_ctor_set_uint8(v_reuseFailAlloc_5763_, sizeof(void*)*3 + 1, v_wantsRebuild_5752_);
v___x_5761_ = v_reuseFailAlloc_5763_;
goto v_reusejp_5760_;
}
v_reusejp_5760_:
{
lean_object* v___x_5762_; 
v___x_5762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5762_, 0, v_path_5742_);
lean_ctor_set(v___x_5762_, 1, v___x_5761_);
return v___x_5762_;
}
}
else
{
lean_object* v_a_5764_; lean_object* v___x_5765_; uint8_t v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5771_; 
lean_dec_ref(v_path_5742_);
v_a_5764_ = lean_ctor_get(v___x_5758_, 0);
lean_inc(v_a_5764_);
lean_dec_ref(v___x_5758_);
v___x_5765_ = lean_io_error_to_string(v_a_5764_);
v___x_5766_ = 3;
v___x_5767_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5767_, 0, v___x_5765_);
lean_ctor_set_uint8(v___x_5767_, sizeof(void*)*1, v___x_5766_);
v___x_5768_ = lean_array_get_size(v_log_5750_);
v___x_5769_ = lean_array_push(v_log_5750_, v___x_5767_);
if (v_isShared_5757_ == 0)
{
lean_ctor_set(v___x_5756_, 0, v___x_5769_);
v___x_5771_ = v___x_5756_;
goto v_reusejp_5770_;
}
else
{
lean_object* v_reuseFailAlloc_5773_; 
v_reuseFailAlloc_5773_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5773_, 0, v___x_5769_);
lean_ctor_set(v_reuseFailAlloc_5773_, 1, v_trace_5753_);
lean_ctor_set(v_reuseFailAlloc_5773_, 2, v_buildTime_5754_);
lean_ctor_set_uint8(v_reuseFailAlloc_5773_, sizeof(void*)*3, v_action_5751_);
lean_ctor_set_uint8(v_reuseFailAlloc_5773_, sizeof(void*)*3 + 1, v_wantsRebuild_5752_);
v___x_5771_ = v_reuseFailAlloc_5773_;
goto v_reusejp_5770_;
}
v_reusejp_5770_:
{
lean_object* v___x_5772_; 
v___x_5772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5772_, 0, v___x_5768_);
lean_ctor_set(v___x_5772_, 1, v___x_5771_);
return v___x_5772_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0___boxed(lean_object* v_path_5775_, lean_object* v___y_5776_, lean_object* v___y_5777_, lean_object* v___y_5778_, lean_object* v___y_5779_, lean_object* v___y_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_){
_start:
{
lean_object* v_res_5783_; 
v_res_5783_ = l_Lake_inputBinFile___redArg___lam__0(v_path_5775_, v___y_5776_, v___y_5777_, v___y_5778_, v___y_5779_, v___y_5780_, v___y_5781_);
lean_dec_ref(v___y_5780_);
lean_dec(v___y_5779_);
lean_dec(v___y_5778_);
lean_dec(v___y_5777_);
lean_dec_ref(v___y_5776_);
return v_res_5783_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg(lean_object* v_path_5785_, lean_object* v_a_5786_, lean_object* v_a_5787_, lean_object* v_a_5788_, lean_object* v_a_5789_, lean_object* v_a_5790_){
_start:
{
lean_object* v___f_5792_; lean_object* v___x_5793_; lean_object* v___x_5794_; lean_object* v___x_5795_; lean_object* v___x_5796_; 
v___f_5792_ = lean_alloc_closure((void*)(l_Lake_inputBinFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5792_, 0, v_path_5785_);
v___x_5793_ = l_Lake_instDataKindFilePath;
v___x_5794_ = lean_unsigned_to_nat(0u);
v___x_5795_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
v___x_5796_ = l_Lake_Job_async___redArg(v___x_5793_, v___f_5792_, v___x_5794_, v___x_5795_, v_a_5786_, v_a_5787_, v_a_5788_, v_a_5789_, v_a_5790_);
return v___x_5796_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___boxed(lean_object* v_path_5797_, lean_object* v_a_5798_, lean_object* v_a_5799_, lean_object* v_a_5800_, lean_object* v_a_5801_, lean_object* v_a_5802_, lean_object* v_a_5803_){
_start:
{
lean_object* v_res_5804_; 
v_res_5804_ = l_Lake_inputBinFile___redArg(v_path_5797_, v_a_5798_, v_a_5799_, v_a_5800_, v_a_5801_, v_a_5802_);
return v_res_5804_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object* v_path_5805_, lean_object* v_a_5806_, lean_object* v_a_5807_, lean_object* v_a_5808_, lean_object* v_a_5809_, lean_object* v_a_5810_, lean_object* v_a_5811_){
_start:
{
lean_object* v___x_5813_; 
v___x_5813_ = l_Lake_inputBinFile___redArg(v_path_5805_, v_a_5806_, v_a_5807_, v_a_5808_, v_a_5809_, v_a_5810_);
return v___x_5813_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___boxed(lean_object* v_path_5814_, lean_object* v_a_5815_, lean_object* v_a_5816_, lean_object* v_a_5817_, lean_object* v_a_5818_, lean_object* v_a_5819_, lean_object* v_a_5820_, lean_object* v_a_5821_){
_start:
{
lean_object* v_res_5822_; 
v_res_5822_ = l_Lake_inputBinFile(v_path_5814_, v_a_5815_, v_a_5816_, v_a_5817_, v_a_5818_, v_a_5819_, v_a_5820_);
lean_dec_ref(v_a_5820_);
return v_res_5822_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(lean_object* v_info_5823_){
_start:
{
lean_object* v___x_5825_; 
v___x_5825_ = l_Lake_computeTextFileHash(v_info_5823_);
if (lean_obj_tag(v___x_5825_) == 0)
{
lean_object* v_a_5826_; lean_object* v___x_5827_; 
v_a_5826_ = lean_ctor_get(v___x_5825_, 0);
lean_inc(v_a_5826_);
lean_dec_ref(v___x_5825_);
v___x_5827_ = lean_io_metadata(v_info_5823_);
if (lean_obj_tag(v___x_5827_) == 0)
{
lean_object* v_a_5828_; lean_object* v___x_5830_; uint8_t v_isShared_5831_; uint8_t v_isSharedCheck_5839_; 
v_a_5828_ = lean_ctor_get(v___x_5827_, 0);
v_isSharedCheck_5839_ = !lean_is_exclusive(v___x_5827_);
if (v_isSharedCheck_5839_ == 0)
{
v___x_5830_ = v___x_5827_;
v_isShared_5831_ = v_isSharedCheck_5839_;
goto v_resetjp_5829_;
}
else
{
lean_inc(v_a_5828_);
lean_dec(v___x_5827_);
v___x_5830_ = lean_box(0);
v_isShared_5831_ = v_isSharedCheck_5839_;
goto v_resetjp_5829_;
}
v_resetjp_5829_:
{
lean_object* v_modified_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; uint64_t v___x_5835_; lean_object* v___x_5837_; 
v_modified_5832_ = lean_ctor_get(v_a_5828_, 1);
lean_inc_ref(v_modified_5832_);
lean_dec(v_a_5828_);
v___x_5833_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_5834_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_5834_, 0, v_info_5823_);
lean_ctor_set(v___x_5834_, 1, v___x_5833_);
lean_ctor_set(v___x_5834_, 2, v_modified_5832_);
v___x_5835_ = lean_unbox_uint64(v_a_5826_);
lean_dec(v_a_5826_);
lean_ctor_set_uint64(v___x_5834_, sizeof(void*)*3, v___x_5835_);
if (v_isShared_5831_ == 0)
{
lean_ctor_set(v___x_5830_, 0, v___x_5834_);
v___x_5837_ = v___x_5830_;
goto v_reusejp_5836_;
}
else
{
lean_object* v_reuseFailAlloc_5838_; 
v_reuseFailAlloc_5838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5838_, 0, v___x_5834_);
v___x_5837_ = v_reuseFailAlloc_5838_;
goto v_reusejp_5836_;
}
v_reusejp_5836_:
{
return v___x_5837_;
}
}
}
else
{
lean_object* v_a_5840_; lean_object* v___x_5842_; uint8_t v_isShared_5843_; uint8_t v_isSharedCheck_5847_; 
lean_dec(v_a_5826_);
lean_dec_ref(v_info_5823_);
v_a_5840_ = lean_ctor_get(v___x_5827_, 0);
v_isSharedCheck_5847_ = !lean_is_exclusive(v___x_5827_);
if (v_isSharedCheck_5847_ == 0)
{
v___x_5842_ = v___x_5827_;
v_isShared_5843_ = v_isSharedCheck_5847_;
goto v_resetjp_5841_;
}
else
{
lean_inc(v_a_5840_);
lean_dec(v___x_5827_);
v___x_5842_ = lean_box(0);
v_isShared_5843_ = v_isSharedCheck_5847_;
goto v_resetjp_5841_;
}
v_resetjp_5841_:
{
lean_object* v___x_5845_; 
if (v_isShared_5843_ == 0)
{
v___x_5845_ = v___x_5842_;
goto v_reusejp_5844_;
}
else
{
lean_object* v_reuseFailAlloc_5846_; 
v_reuseFailAlloc_5846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5846_, 0, v_a_5840_);
v___x_5845_ = v_reuseFailAlloc_5846_;
goto v_reusejp_5844_;
}
v_reusejp_5844_:
{
return v___x_5845_;
}
}
}
}
else
{
lean_object* v_a_5848_; lean_object* v___x_5850_; uint8_t v_isShared_5851_; uint8_t v_isSharedCheck_5855_; 
lean_dec_ref(v_info_5823_);
v_a_5848_ = lean_ctor_get(v___x_5825_, 0);
v_isSharedCheck_5855_ = !lean_is_exclusive(v___x_5825_);
if (v_isSharedCheck_5855_ == 0)
{
v___x_5850_ = v___x_5825_;
v_isShared_5851_ = v_isSharedCheck_5855_;
goto v_resetjp_5849_;
}
else
{
lean_inc(v_a_5848_);
lean_dec(v___x_5825_);
v___x_5850_ = lean_box(0);
v_isShared_5851_ = v_isSharedCheck_5855_;
goto v_resetjp_5849_;
}
v_resetjp_5849_:
{
lean_object* v___x_5853_; 
if (v_isShared_5851_ == 0)
{
v___x_5853_ = v___x_5850_;
goto v_reusejp_5852_;
}
else
{
lean_object* v_reuseFailAlloc_5854_; 
v_reuseFailAlloc_5854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5854_, 0, v_a_5848_);
v___x_5853_ = v_reuseFailAlloc_5854_;
goto v_reusejp_5852_;
}
v_reusejp_5852_:
{
return v___x_5853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0___boxed(lean_object* v_info_5856_, lean_object* v_a_5857_){
_start:
{
lean_object* v_res_5858_; 
v_res_5858_ = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(v_info_5856_);
return v_res_5858_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0(lean_object* v_path_5859_, lean_object* v___y_5860_, lean_object* v___y_5861_, lean_object* v___y_5862_, lean_object* v___y_5863_, lean_object* v___y_5864_, lean_object* v___y_5865_){
_start:
{
lean_object* v_log_5867_; uint8_t v_action_5868_; uint8_t v_wantsRebuild_5869_; lean_object* v_trace_5870_; lean_object* v_buildTime_5871_; lean_object* v___x_5873_; uint8_t v_isShared_5874_; uint8_t v_isSharedCheck_5891_; 
v_log_5867_ = lean_ctor_get(v___y_5865_, 0);
v_action_5868_ = lean_ctor_get_uint8(v___y_5865_, sizeof(void*)*3);
v_wantsRebuild_5869_ = lean_ctor_get_uint8(v___y_5865_, sizeof(void*)*3 + 1);
v_trace_5870_ = lean_ctor_get(v___y_5865_, 1);
v_buildTime_5871_ = lean_ctor_get(v___y_5865_, 2);
v_isSharedCheck_5891_ = !lean_is_exclusive(v___y_5865_);
if (v_isSharedCheck_5891_ == 0)
{
v___x_5873_ = v___y_5865_;
v_isShared_5874_ = v_isSharedCheck_5891_;
goto v_resetjp_5872_;
}
else
{
lean_inc(v_buildTime_5871_);
lean_inc(v_trace_5870_);
lean_inc(v_log_5867_);
lean_dec(v___y_5865_);
v___x_5873_ = lean_box(0);
v_isShared_5874_ = v_isSharedCheck_5891_;
goto v_resetjp_5872_;
}
v_resetjp_5872_:
{
lean_object* v___x_5875_; 
lean_inc_ref(v_path_5859_);
v___x_5875_ = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(v_path_5859_);
if (lean_obj_tag(v___x_5875_) == 0)
{
lean_object* v_a_5876_; lean_object* v___x_5878_; 
lean_dec_ref(v_trace_5870_);
v_a_5876_ = lean_ctor_get(v___x_5875_, 0);
lean_inc(v_a_5876_);
lean_dec_ref(v___x_5875_);
if (v_isShared_5874_ == 0)
{
lean_ctor_set(v___x_5873_, 1, v_a_5876_);
v___x_5878_ = v___x_5873_;
goto v_reusejp_5877_;
}
else
{
lean_object* v_reuseFailAlloc_5880_; 
v_reuseFailAlloc_5880_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5880_, 0, v_log_5867_);
lean_ctor_set(v_reuseFailAlloc_5880_, 1, v_a_5876_);
lean_ctor_set(v_reuseFailAlloc_5880_, 2, v_buildTime_5871_);
lean_ctor_set_uint8(v_reuseFailAlloc_5880_, sizeof(void*)*3, v_action_5868_);
lean_ctor_set_uint8(v_reuseFailAlloc_5880_, sizeof(void*)*3 + 1, v_wantsRebuild_5869_);
v___x_5878_ = v_reuseFailAlloc_5880_;
goto v_reusejp_5877_;
}
v_reusejp_5877_:
{
lean_object* v___x_5879_; 
v___x_5879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5879_, 0, v_path_5859_);
lean_ctor_set(v___x_5879_, 1, v___x_5878_);
return v___x_5879_;
}
}
else
{
lean_object* v_a_5881_; lean_object* v___x_5882_; uint8_t v___x_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5888_; 
lean_dec_ref(v_path_5859_);
v_a_5881_ = lean_ctor_get(v___x_5875_, 0);
lean_inc(v_a_5881_);
lean_dec_ref(v___x_5875_);
v___x_5882_ = lean_io_error_to_string(v_a_5881_);
v___x_5883_ = 3;
v___x_5884_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5884_, 0, v___x_5882_);
lean_ctor_set_uint8(v___x_5884_, sizeof(void*)*1, v___x_5883_);
v___x_5885_ = lean_array_get_size(v_log_5867_);
v___x_5886_ = lean_array_push(v_log_5867_, v___x_5884_);
if (v_isShared_5874_ == 0)
{
lean_ctor_set(v___x_5873_, 0, v___x_5886_);
v___x_5888_ = v___x_5873_;
goto v_reusejp_5887_;
}
else
{
lean_object* v_reuseFailAlloc_5890_; 
v_reuseFailAlloc_5890_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5890_, 0, v___x_5886_);
lean_ctor_set(v_reuseFailAlloc_5890_, 1, v_trace_5870_);
lean_ctor_set(v_reuseFailAlloc_5890_, 2, v_buildTime_5871_);
lean_ctor_set_uint8(v_reuseFailAlloc_5890_, sizeof(void*)*3, v_action_5868_);
lean_ctor_set_uint8(v_reuseFailAlloc_5890_, sizeof(void*)*3 + 1, v_wantsRebuild_5869_);
v___x_5888_ = v_reuseFailAlloc_5890_;
goto v_reusejp_5887_;
}
v_reusejp_5887_:
{
lean_object* v___x_5889_; 
v___x_5889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5889_, 0, v___x_5885_);
lean_ctor_set(v___x_5889_, 1, v___x_5888_);
return v___x_5889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0___boxed(lean_object* v_path_5892_, lean_object* v___y_5893_, lean_object* v___y_5894_, lean_object* v___y_5895_, lean_object* v___y_5896_, lean_object* v___y_5897_, lean_object* v___y_5898_, lean_object* v___y_5899_){
_start:
{
lean_object* v_res_5900_; 
v_res_5900_ = l_Lake_inputTextFile___redArg___lam__0(v_path_5892_, v___y_5893_, v___y_5894_, v___y_5895_, v___y_5896_, v___y_5897_, v___y_5898_);
lean_dec_ref(v___y_5897_);
lean_dec(v___y_5896_);
lean_dec(v___y_5895_);
lean_dec(v___y_5894_);
lean_dec_ref(v___y_5893_);
return v_res_5900_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg(lean_object* v_path_5901_, lean_object* v_a_5902_, lean_object* v_a_5903_, lean_object* v_a_5904_, lean_object* v_a_5905_, lean_object* v_a_5906_){
_start:
{
lean_object* v___f_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; 
v___f_5908_ = lean_alloc_closure((void*)(l_Lake_inputTextFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5908_, 0, v_path_5901_);
v___x_5909_ = l_Lake_instDataKindFilePath;
v___x_5910_ = lean_unsigned_to_nat(0u);
v___x_5911_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
v___x_5912_ = l_Lake_Job_async___redArg(v___x_5909_, v___f_5908_, v___x_5910_, v___x_5911_, v_a_5902_, v_a_5903_, v_a_5904_, v_a_5905_, v_a_5906_);
return v___x_5912_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___boxed(lean_object* v_path_5913_, lean_object* v_a_5914_, lean_object* v_a_5915_, lean_object* v_a_5916_, lean_object* v_a_5917_, lean_object* v_a_5918_, lean_object* v_a_5919_){
_start:
{
lean_object* v_res_5920_; 
v_res_5920_ = l_Lake_inputTextFile___redArg(v_path_5913_, v_a_5914_, v_a_5915_, v_a_5916_, v_a_5917_, v_a_5918_);
return v_res_5920_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object* v_path_5921_, lean_object* v_a_5922_, lean_object* v_a_5923_, lean_object* v_a_5924_, lean_object* v_a_5925_, lean_object* v_a_5926_, lean_object* v_a_5927_){
_start:
{
lean_object* v___x_5929_; 
v___x_5929_ = l_Lake_inputTextFile___redArg(v_path_5921_, v_a_5922_, v_a_5923_, v_a_5924_, v_a_5925_, v_a_5926_);
return v___x_5929_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___boxed(lean_object* v_path_5930_, lean_object* v_a_5931_, lean_object* v_a_5932_, lean_object* v_a_5933_, lean_object* v_a_5934_, lean_object* v_a_5935_, lean_object* v_a_5936_, lean_object* v_a_5937_){
_start:
{
lean_object* v_res_5938_; 
v_res_5938_ = l_Lake_inputTextFile(v_path_5930_, v_a_5931_, v_a_5932_, v_a_5933_, v_a_5934_, v_a_5935_, v_a_5936_);
lean_dec_ref(v_a_5936_);
return v_res_5938_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg(lean_object* v_path_5939_, uint8_t v_text_5940_, lean_object* v_a_5941_, lean_object* v_a_5942_, lean_object* v_a_5943_, lean_object* v_a_5944_, lean_object* v_a_5945_){
_start:
{
if (v_text_5940_ == 0)
{
lean_object* v___x_5947_; 
v___x_5947_ = l_Lake_inputBinFile___redArg(v_path_5939_, v_a_5941_, v_a_5942_, v_a_5943_, v_a_5944_, v_a_5945_);
return v___x_5947_;
}
else
{
lean_object* v___x_5948_; 
v___x_5948_ = l_Lake_inputTextFile___redArg(v_path_5939_, v_a_5941_, v_a_5942_, v_a_5943_, v_a_5944_, v_a_5945_);
return v___x_5948_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg___boxed(lean_object* v_path_5949_, lean_object* v_text_5950_, lean_object* v_a_5951_, lean_object* v_a_5952_, lean_object* v_a_5953_, lean_object* v_a_5954_, lean_object* v_a_5955_, lean_object* v_a_5956_){
_start:
{
uint8_t v_text_boxed_5957_; lean_object* v_res_5958_; 
v_text_boxed_5957_ = lean_unbox(v_text_5950_);
v_res_5958_ = l_Lake_inputFile___redArg(v_path_5949_, v_text_boxed_5957_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
return v_res_5958_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object* v_path_5959_, uint8_t v_text_5960_, lean_object* v_a_5961_, lean_object* v_a_5962_, lean_object* v_a_5963_, lean_object* v_a_5964_, lean_object* v_a_5965_, lean_object* v_a_5966_){
_start:
{
if (v_text_5960_ == 0)
{
lean_object* v___x_5968_; 
v___x_5968_ = l_Lake_inputBinFile___redArg(v_path_5959_, v_a_5961_, v_a_5962_, v_a_5963_, v_a_5964_, v_a_5965_);
return v___x_5968_;
}
else
{
lean_object* v___x_5969_; 
v___x_5969_ = l_Lake_inputTextFile___redArg(v_path_5959_, v_a_5961_, v_a_5962_, v_a_5963_, v_a_5964_, v_a_5965_);
return v___x_5969_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object* v_path_5970_, lean_object* v_text_5971_, lean_object* v_a_5972_, lean_object* v_a_5973_, lean_object* v_a_5974_, lean_object* v_a_5975_, lean_object* v_a_5976_, lean_object* v_a_5977_, lean_object* v_a_5978_){
_start:
{
uint8_t v_text_boxed_5979_; lean_object* v_res_5980_; 
v_text_boxed_5979_ = lean_unbox(v_text_5971_);
v_res_5980_ = l_Lake_inputFile(v_path_5970_, v_text_boxed_5979_, v_a_5972_, v_a_5973_, v_a_5974_, v_a_5975_, v_a_5976_, v_a_5977_);
lean_dec_ref(v_a_5977_);
return v_res_5980_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0(lean_object* v_x_5981_){
_start:
{
uint8_t v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; 
v___x_5983_ = 1;
v___x_5984_ = lean_box(v___x_5983_);
v___x_5985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5985_, 0, v___x_5984_);
return v___x_5985_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0___boxed(lean_object* v_x_5986_, lean_object* v___y_5987_){
_start:
{
lean_object* v_res_5988_; 
v_res_5988_ = l_Lake_inputDir___lam__0(v_x_5986_);
lean_dec_ref(v_x_5986_);
return v_res_5988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(lean_object* v_filter_5989_, lean_object* v_as_5990_, size_t v_i_5991_, size_t v_stop_5992_, lean_object* v_b_5993_, lean_object* v___y_5994_){
_start:
{
lean_object* v_a_5997_; lean_object* v_a_5998_; uint8_t v___x_6002_; 
v___x_6002_ = lean_usize_dec_eq(v_i_5991_, v_stop_5992_);
if (v___x_6002_ == 0)
{
lean_object* v___x_6003_; uint8_t v___x_6004_; 
v___x_6003_ = lean_array_uget_borrowed(v_as_5990_, v_i_5991_);
v___x_6004_ = l_System_FilePath_isDir(v___x_6003_);
if (v___x_6004_ == 0)
{
lean_object* v___x_6005_; uint8_t v___x_6006_; 
lean_inc_ref(v_filter_5989_);
lean_inc(v___x_6003_);
v___x_6005_ = lean_apply_1(v_filter_5989_, v___x_6003_);
v___x_6006_ = lean_unbox(v___x_6005_);
if (v___x_6006_ == 0)
{
v_a_5997_ = v_b_5993_;
v_a_5998_ = v___y_5994_;
goto v___jp_5996_;
}
else
{
lean_object* v___x_6007_; 
lean_inc(v___x_6003_);
v___x_6007_ = lean_array_push(v_b_5993_, v___x_6003_);
v_a_5997_ = v___x_6007_;
v_a_5998_ = v___y_5994_;
goto v___jp_5996_;
}
}
else
{
v_a_5997_ = v_b_5993_;
v_a_5998_ = v___y_5994_;
goto v___jp_5996_;
}
}
else
{
lean_object* v___x_6008_; 
lean_dec_ref(v_filter_5989_);
v___x_6008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6008_, 0, v_b_5993_);
lean_ctor_set(v___x_6008_, 1, v___y_5994_);
return v___x_6008_;
}
v___jp_5996_:
{
size_t v___x_5999_; size_t v___x_6000_; 
v___x_5999_ = ((size_t)1ULL);
v___x_6000_ = lean_usize_add(v_i_5991_, v___x_5999_);
v_i_5991_ = v___x_6000_;
v_b_5993_ = v_a_5997_;
v___y_5994_ = v_a_5998_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg___boxed(lean_object* v_filter_6009_, lean_object* v_as_6010_, lean_object* v_i_6011_, lean_object* v_stop_6012_, lean_object* v_b_6013_, lean_object* v___y_6014_, lean_object* v___y_6015_){
_start:
{
size_t v_i_boxed_6016_; size_t v_stop_boxed_6017_; lean_object* v_res_6018_; 
v_i_boxed_6016_ = lean_unbox_usize(v_i_6011_);
lean_dec(v_i_6011_);
v_stop_boxed_6017_ = lean_unbox_usize(v_stop_6012_);
lean_dec(v_stop_6012_);
v_res_6018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6009_, v_as_6010_, v_i_boxed_6016_, v_stop_boxed_6017_, v_b_6013_, v___y_6014_);
lean_dec_ref(v_as_6010_);
return v_res_6018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(lean_object* v_as_6020_, lean_object* v_lo_6021_, lean_object* v_hi_6022_){
_start:
{
uint8_t v___x_6023_; 
v___x_6023_ = lean_nat_dec_lt(v_lo_6021_, v_hi_6022_);
if (v___x_6023_ == 0)
{
lean_dec(v_lo_6021_);
return v_as_6020_;
}
else
{
lean_object* v___f_6024_; lean_object* v___x_6025_; lean_object* v_fst_6026_; lean_object* v_snd_6027_; uint8_t v___x_6028_; 
v___f_6024_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___closed__0));
lean_inc(v_lo_6021_);
v___x_6025_ = l_Array_qpartition___redArg(v_as_6020_, v___f_6024_, v_lo_6021_, v_hi_6022_);
v_fst_6026_ = lean_ctor_get(v___x_6025_, 0);
lean_inc(v_fst_6026_);
v_snd_6027_ = lean_ctor_get(v___x_6025_, 1);
lean_inc(v_snd_6027_);
lean_dec_ref(v___x_6025_);
v___x_6028_ = lean_nat_dec_le(v_hi_6022_, v_fst_6026_);
if (v___x_6028_ == 0)
{
lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; 
v___x_6029_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_snd_6027_, v_lo_6021_, v_fst_6026_);
v___x_6030_ = lean_unsigned_to_nat(1u);
v___x_6031_ = lean_nat_add(v_fst_6026_, v___x_6030_);
lean_dec(v_fst_6026_);
v_as_6020_ = v___x_6029_;
v_lo_6021_ = v___x_6031_;
goto _start;
}
else
{
lean_dec(v_fst_6026_);
lean_dec(v_lo_6021_);
return v_snd_6027_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___boxed(lean_object* v_as_6033_, lean_object* v_lo_6034_, lean_object* v_hi_6035_){
_start:
{
lean_object* v_res_6036_; 
v_res_6036_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_as_6033_, v_lo_6034_, v_hi_6035_);
lean_dec(v_hi_6035_);
return v_res_6036_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1(lean_object* v_path_6039_, lean_object* v___f_6040_, lean_object* v_filter_6041_, lean_object* v___y_6042_, lean_object* v___y_6043_, lean_object* v___y_6044_, lean_object* v___y_6045_, lean_object* v___y_6046_, lean_object* v___y_6047_){
_start:
{
lean_object* v___y_6050_; lean_object* v___y_6051_; lean_object* v___y_6054_; lean_object* v___y_6055_; lean_object* v___y_6056_; lean_object* v___y_6057_; lean_object* v___y_6058_; lean_object* v___y_6061_; lean_object* v___y_6062_; lean_object* v___y_6063_; lean_object* v___y_6064_; lean_object* v___y_6065_; lean_object* v_log_6067_; uint8_t v_action_6068_; uint8_t v_wantsRebuild_6069_; lean_object* v_trace_6070_; lean_object* v_buildTime_6071_; lean_object* v___x_6072_; 
v_log_6067_ = lean_ctor_get(v___y_6047_, 0);
v_action_6068_ = lean_ctor_get_uint8(v___y_6047_, sizeof(void*)*3);
v_wantsRebuild_6069_ = lean_ctor_get_uint8(v___y_6047_, sizeof(void*)*3 + 1);
v_trace_6070_ = lean_ctor_get(v___y_6047_, 1);
v_buildTime_6071_ = lean_ctor_get(v___y_6047_, 2);
v___x_6072_ = l_System_FilePath_walkDir(v_path_6039_, v___f_6040_);
if (lean_obj_tag(v___x_6072_) == 0)
{
lean_object* v_a_6073_; lean_object* v___x_6074_; lean_object* v_a_6076_; lean_object* v_a_6077_; lean_object* v___y_6084_; lean_object* v___x_6087_; lean_object* v___x_6088_; uint8_t v___x_6089_; 
v_a_6073_ = lean_ctor_get(v___x_6072_, 0);
lean_inc(v_a_6073_);
lean_dec_ref(v___x_6072_);
v___x_6074_ = lean_unsigned_to_nat(0u);
v___x_6087_ = lean_array_get_size(v_a_6073_);
v___x_6088_ = ((lean_object*)(l_Lake_inputDir___lam__1___closed__0));
v___x_6089_ = lean_nat_dec_lt(v___x_6074_, v___x_6087_);
if (v___x_6089_ == 0)
{
lean_dec(v_a_6073_);
lean_dec_ref(v_filter_6041_);
v_a_6076_ = v___x_6088_;
v_a_6077_ = v___y_6047_;
goto v___jp_6075_;
}
else
{
uint8_t v___x_6090_; 
v___x_6090_ = lean_nat_dec_le(v___x_6087_, v___x_6087_);
if (v___x_6090_ == 0)
{
if (v___x_6089_ == 0)
{
lean_dec(v_a_6073_);
lean_dec_ref(v_filter_6041_);
v_a_6076_ = v___x_6088_;
v_a_6077_ = v___y_6047_;
goto v___jp_6075_;
}
else
{
size_t v___x_6091_; size_t v___x_6092_; lean_object* v___x_6093_; 
v___x_6091_ = ((size_t)0ULL);
v___x_6092_ = lean_usize_of_nat(v___x_6087_);
v___x_6093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6041_, v_a_6073_, v___x_6091_, v___x_6092_, v___x_6088_, v___y_6047_);
lean_dec(v_a_6073_);
v___y_6084_ = v___x_6093_;
goto v___jp_6083_;
}
}
else
{
size_t v___x_6094_; size_t v___x_6095_; lean_object* v___x_6096_; 
v___x_6094_ = ((size_t)0ULL);
v___x_6095_ = lean_usize_of_nat(v___x_6087_);
v___x_6096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6041_, v_a_6073_, v___x_6094_, v___x_6095_, v___x_6088_, v___y_6047_);
lean_dec(v_a_6073_);
v___y_6084_ = v___x_6096_;
goto v___jp_6083_;
}
}
v___jp_6075_:
{
lean_object* v___x_6078_; uint8_t v___x_6079_; 
v___x_6078_ = lean_array_get_size(v_a_6076_);
v___x_6079_ = lean_nat_dec_eq(v___x_6078_, v___x_6074_);
if (v___x_6079_ == 0)
{
lean_object* v___x_6080_; lean_object* v___x_6081_; uint8_t v___x_6082_; 
v___x_6080_ = lean_unsigned_to_nat(1u);
v___x_6081_ = lean_nat_sub(v___x_6078_, v___x_6080_);
v___x_6082_ = lean_nat_dec_le(v___x_6074_, v___x_6081_);
if (v___x_6082_ == 0)
{
lean_inc(v___x_6081_);
v___y_6061_ = v_a_6077_;
v___y_6062_ = v___x_6078_;
v___y_6063_ = v_a_6076_;
v___y_6064_ = v___x_6081_;
v___y_6065_ = v___x_6081_;
goto v___jp_6060_;
}
else
{
v___y_6061_ = v_a_6077_;
v___y_6062_ = v___x_6078_;
v___y_6063_ = v_a_6076_;
v___y_6064_ = v___x_6081_;
v___y_6065_ = v___x_6074_;
goto v___jp_6060_;
}
}
else
{
v___y_6050_ = v_a_6077_;
v___y_6051_ = v_a_6076_;
goto v___jp_6049_;
}
}
v___jp_6083_:
{
if (lean_obj_tag(v___y_6084_) == 0)
{
lean_object* v_a_6085_; lean_object* v_a_6086_; 
v_a_6085_ = lean_ctor_get(v___y_6084_, 0);
lean_inc(v_a_6085_);
v_a_6086_ = lean_ctor_get(v___y_6084_, 1);
lean_inc(v_a_6086_);
lean_dec_ref(v___y_6084_);
v_a_6076_ = v_a_6085_;
v_a_6077_ = v_a_6086_;
goto v___jp_6075_;
}
else
{
return v___y_6084_;
}
}
}
else
{
lean_object* v___x_6098_; uint8_t v_isShared_6099_; uint8_t v_isSharedCheck_6110_; 
lean_inc(v_buildTime_6071_);
lean_inc_ref(v_trace_6070_);
lean_inc_ref(v_log_6067_);
lean_dec_ref(v_filter_6041_);
v_isSharedCheck_6110_ = !lean_is_exclusive(v___y_6047_);
if (v_isSharedCheck_6110_ == 0)
{
lean_object* v_unused_6111_; lean_object* v_unused_6112_; lean_object* v_unused_6113_; 
v_unused_6111_ = lean_ctor_get(v___y_6047_, 2);
lean_dec(v_unused_6111_);
v_unused_6112_ = lean_ctor_get(v___y_6047_, 1);
lean_dec(v_unused_6112_);
v_unused_6113_ = lean_ctor_get(v___y_6047_, 0);
lean_dec(v_unused_6113_);
v___x_6098_ = v___y_6047_;
v_isShared_6099_ = v_isSharedCheck_6110_;
goto v_resetjp_6097_;
}
else
{
lean_dec(v___y_6047_);
v___x_6098_ = lean_box(0);
v_isShared_6099_ = v_isSharedCheck_6110_;
goto v_resetjp_6097_;
}
v_resetjp_6097_:
{
lean_object* v_a_6100_; lean_object* v___x_6101_; uint8_t v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6107_; 
v_a_6100_ = lean_ctor_get(v___x_6072_, 0);
lean_inc(v_a_6100_);
lean_dec_ref(v___x_6072_);
v___x_6101_ = lean_io_error_to_string(v_a_6100_);
v___x_6102_ = 3;
v___x_6103_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6103_, 0, v___x_6101_);
lean_ctor_set_uint8(v___x_6103_, sizeof(void*)*1, v___x_6102_);
v___x_6104_ = lean_array_get_size(v_log_6067_);
v___x_6105_ = lean_array_push(v_log_6067_, v___x_6103_);
if (v_isShared_6099_ == 0)
{
lean_ctor_set(v___x_6098_, 0, v___x_6105_);
v___x_6107_ = v___x_6098_;
goto v_reusejp_6106_;
}
else
{
lean_object* v_reuseFailAlloc_6109_; 
v_reuseFailAlloc_6109_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6109_, 0, v___x_6105_);
lean_ctor_set(v_reuseFailAlloc_6109_, 1, v_trace_6070_);
lean_ctor_set(v_reuseFailAlloc_6109_, 2, v_buildTime_6071_);
lean_ctor_set_uint8(v_reuseFailAlloc_6109_, sizeof(void*)*3, v_action_6068_);
lean_ctor_set_uint8(v_reuseFailAlloc_6109_, sizeof(void*)*3 + 1, v_wantsRebuild_6069_);
v___x_6107_ = v_reuseFailAlloc_6109_;
goto v_reusejp_6106_;
}
v_reusejp_6106_:
{
lean_object* v___x_6108_; 
v___x_6108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6108_, 0, v___x_6104_);
lean_ctor_set(v___x_6108_, 1, v___x_6107_);
return v___x_6108_;
}
}
}
v___jp_6049_:
{
lean_object* v___x_6052_; 
v___x_6052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6052_, 0, v___y_6051_);
lean_ctor_set(v___x_6052_, 1, v___y_6050_);
return v___x_6052_;
}
v___jp_6053_:
{
lean_object* v___x_6059_; 
lean_dec(v___y_6056_);
v___x_6059_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v___y_6057_, v___y_6054_, v___y_6058_);
lean_dec(v___y_6058_);
v___y_6050_ = v___y_6055_;
v___y_6051_ = v___x_6059_;
goto v___jp_6049_;
}
v___jp_6060_:
{
uint8_t v___x_6066_; 
v___x_6066_ = lean_nat_dec_le(v___y_6065_, v___y_6064_);
if (v___x_6066_ == 0)
{
lean_dec(v___y_6064_);
lean_inc(v___y_6065_);
v___y_6054_ = v___y_6065_;
v___y_6055_ = v___y_6061_;
v___y_6056_ = v___y_6062_;
v___y_6057_ = v___y_6063_;
v___y_6058_ = v___y_6065_;
goto v___jp_6053_;
}
else
{
v___y_6054_ = v___y_6065_;
v___y_6055_ = v___y_6061_;
v___y_6056_ = v___y_6062_;
v___y_6057_ = v___y_6063_;
v___y_6058_ = v___y_6064_;
goto v___jp_6053_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1___boxed(lean_object* v_path_6114_, lean_object* v___f_6115_, lean_object* v_filter_6116_, lean_object* v___y_6117_, lean_object* v___y_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_, lean_object* v___y_6122_, lean_object* v___y_6123_){
_start:
{
lean_object* v_res_6124_; 
v_res_6124_ = l_Lake_inputDir___lam__1(v_path_6114_, v___f_6115_, v_filter_6116_, v___y_6117_, v___y_6118_, v___y_6119_, v___y_6120_, v___y_6121_, v___y_6122_);
lean_dec_ref(v___y_6121_);
lean_dec(v___y_6120_);
lean_dec(v___y_6119_);
lean_dec(v___y_6118_);
lean_dec_ref(v___y_6117_);
return v_res_6124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(uint8_t v_text_6125_, size_t v_sz_6126_, size_t v_i_6127_, lean_object* v_bs_6128_, lean_object* v___y_6129_, lean_object* v___y_6130_, lean_object* v___y_6131_, lean_object* v___y_6132_, lean_object* v___y_6133_, lean_object* v___y_6134_){
_start:
{
uint8_t v___x_6136_; 
v___x_6136_ = lean_usize_dec_lt(v_i_6127_, v_sz_6126_);
if (v___x_6136_ == 0)
{
lean_object* v___x_6137_; 
lean_dec_ref(v___y_6133_);
lean_dec(v___y_6132_);
lean_dec(v___y_6131_);
lean_dec(v___y_6130_);
lean_dec_ref(v___y_6129_);
v___x_6137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6137_, 0, v_bs_6128_);
lean_ctor_set(v___x_6137_, 1, v___y_6134_);
return v___x_6137_;
}
else
{
lean_object* v_v_6138_; lean_object* v___x_6139_; lean_object* v_bs_x27_6140_; lean_object* v___y_6142_; 
v_v_6138_ = lean_array_uget(v_bs_6128_, v_i_6127_);
v___x_6139_ = lean_unsigned_to_nat(0u);
v_bs_x27_6140_ = lean_array_uset(v_bs_6128_, v_i_6127_, v___x_6139_);
if (v_text_6125_ == 0)
{
lean_object* v___x_6147_; 
lean_inc_ref(v___y_6133_);
lean_inc(v___y_6132_);
lean_inc(v___y_6131_);
lean_inc(v___y_6130_);
lean_inc_ref(v___y_6129_);
v___x_6147_ = l_Lake_inputBinFile___redArg(v_v_6138_, v___y_6129_, v___y_6130_, v___y_6131_, v___y_6132_, v___y_6133_);
v___y_6142_ = v___x_6147_;
goto v___jp_6141_;
}
else
{
lean_object* v___x_6148_; 
lean_inc_ref(v___y_6133_);
lean_inc(v___y_6132_);
lean_inc(v___y_6131_);
lean_inc(v___y_6130_);
lean_inc_ref(v___y_6129_);
v___x_6148_ = l_Lake_inputTextFile___redArg(v_v_6138_, v___y_6129_, v___y_6130_, v___y_6131_, v___y_6132_, v___y_6133_);
v___y_6142_ = v___x_6148_;
goto v___jp_6141_;
}
v___jp_6141_:
{
size_t v___x_6143_; size_t v___x_6144_; lean_object* v___x_6145_; 
v___x_6143_ = ((size_t)1ULL);
v___x_6144_ = lean_usize_add(v_i_6127_, v___x_6143_);
v___x_6145_ = lean_array_uset(v_bs_x27_6140_, v_i_6127_, v___y_6142_);
v_i_6127_ = v___x_6144_;
v_bs_6128_ = v___x_6145_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0___boxed(lean_object* v_text_6149_, lean_object* v_sz_6150_, lean_object* v_i_6151_, lean_object* v_bs_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_, lean_object* v___y_6158_, lean_object* v___y_6159_){
_start:
{
uint8_t v_text_boxed_6160_; size_t v_sz_boxed_6161_; size_t v_i_boxed_6162_; lean_object* v_res_6163_; 
v_text_boxed_6160_ = lean_unbox(v_text_6149_);
v_sz_boxed_6161_ = lean_unbox_usize(v_sz_6150_);
lean_dec(v_sz_6150_);
v_i_boxed_6162_ = lean_unbox_usize(v_i_6151_);
lean_dec(v_i_6151_);
v_res_6163_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(v_text_boxed_6160_, v_sz_boxed_6161_, v_i_boxed_6162_, v_bs_6152_, v___y_6153_, v___y_6154_, v___y_6155_, v___y_6156_, v___y_6157_, v___y_6158_);
return v_res_6163_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2(uint8_t v_text_6164_, lean_object* v_path_6165_, lean_object* v_ps_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_){
_start:
{
size_t v_sz_6174_; size_t v___x_6175_; lean_object* v___x_6176_; 
v_sz_6174_ = lean_array_size(v_ps_6166_);
v___x_6175_ = ((size_t)0ULL);
v___x_6176_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(v_text_6164_, v_sz_6174_, v___x_6175_, v_ps_6166_, v___y_6167_, v___y_6168_, v___y_6169_, v___y_6170_, v___y_6171_, v___y_6172_);
if (lean_obj_tag(v___x_6176_) == 0)
{
lean_object* v_a_6177_; lean_object* v_a_6178_; lean_object* v___x_6180_; uint8_t v_isShared_6181_; uint8_t v_isSharedCheck_6186_; 
v_a_6177_ = lean_ctor_get(v___x_6176_, 0);
v_a_6178_ = lean_ctor_get(v___x_6176_, 1);
v_isSharedCheck_6186_ = !lean_is_exclusive(v___x_6176_);
if (v_isSharedCheck_6186_ == 0)
{
v___x_6180_ = v___x_6176_;
v_isShared_6181_ = v_isSharedCheck_6186_;
goto v_resetjp_6179_;
}
else
{
lean_inc(v_a_6178_);
lean_inc(v_a_6177_);
lean_dec(v___x_6176_);
v___x_6180_ = lean_box(0);
v_isShared_6181_ = v_isSharedCheck_6186_;
goto v_resetjp_6179_;
}
v_resetjp_6179_:
{
lean_object* v___x_6182_; lean_object* v___x_6184_; 
v___x_6182_ = l_Lake_Job_collectArray___redArg(v_a_6177_, v_path_6165_);
lean_dec(v_a_6177_);
if (v_isShared_6181_ == 0)
{
lean_ctor_set(v___x_6180_, 0, v___x_6182_);
v___x_6184_ = v___x_6180_;
goto v_reusejp_6183_;
}
else
{
lean_object* v_reuseFailAlloc_6185_; 
v_reuseFailAlloc_6185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6185_, 0, v___x_6182_);
lean_ctor_set(v_reuseFailAlloc_6185_, 1, v_a_6178_);
v___x_6184_ = v_reuseFailAlloc_6185_;
goto v_reusejp_6183_;
}
v_reusejp_6183_:
{
return v___x_6184_;
}
}
}
else
{
lean_object* v_a_6187_; lean_object* v_a_6188_; lean_object* v___x_6190_; uint8_t v_isShared_6191_; uint8_t v_isSharedCheck_6195_; 
lean_dec_ref(v_path_6165_);
v_a_6187_ = lean_ctor_get(v___x_6176_, 0);
v_a_6188_ = lean_ctor_get(v___x_6176_, 1);
v_isSharedCheck_6195_ = !lean_is_exclusive(v___x_6176_);
if (v_isSharedCheck_6195_ == 0)
{
v___x_6190_ = v___x_6176_;
v_isShared_6191_ = v_isSharedCheck_6195_;
goto v_resetjp_6189_;
}
else
{
lean_inc(v_a_6188_);
lean_inc(v_a_6187_);
lean_dec(v___x_6176_);
v___x_6190_ = lean_box(0);
v_isShared_6191_ = v_isSharedCheck_6195_;
goto v_resetjp_6189_;
}
v_resetjp_6189_:
{
lean_object* v___x_6193_; 
if (v_isShared_6191_ == 0)
{
v___x_6193_ = v___x_6190_;
goto v_reusejp_6192_;
}
else
{
lean_object* v_reuseFailAlloc_6194_; 
v_reuseFailAlloc_6194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6194_, 0, v_a_6187_);
lean_ctor_set(v_reuseFailAlloc_6194_, 1, v_a_6188_);
v___x_6193_ = v_reuseFailAlloc_6194_;
goto v_reusejp_6192_;
}
v_reusejp_6192_:
{
return v___x_6193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2___boxed(lean_object* v_text_6196_, lean_object* v_path_6197_, lean_object* v_ps_6198_, lean_object* v___y_6199_, lean_object* v___y_6200_, lean_object* v___y_6201_, lean_object* v___y_6202_, lean_object* v___y_6203_, lean_object* v___y_6204_, lean_object* v___y_6205_){
_start:
{
uint8_t v_text_boxed_6206_; lean_object* v_res_6207_; 
v_text_boxed_6206_ = lean_unbox(v_text_6196_);
v_res_6207_ = l_Lake_inputDir___lam__2(v_text_boxed_6206_, v_path_6197_, v_ps_6198_, v___y_6199_, v___y_6200_, v___y_6201_, v___y_6202_, v___y_6203_, v___y_6204_);
return v_res_6207_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir(lean_object* v_path_6209_, uint8_t v_text_6210_, lean_object* v_filter_6211_, lean_object* v_a_6212_, lean_object* v_a_6213_, lean_object* v_a_6214_, lean_object* v_a_6215_, lean_object* v_a_6216_, lean_object* v_a_6217_){
_start:
{
lean_object* v___f_6219_; lean_object* v___f_6220_; lean_object* v___x_6221_; lean_object* v___x_6222_; lean_object* v___x_6223_; lean_object* v___x_6224_; lean_object* v___x_6225_; lean_object* v___f_6226_; uint8_t v___x_6227_; lean_object* v___x_6228_; 
v___f_6219_ = ((lean_object*)(l_Lake_inputDir___closed__0));
lean_inc_ref(v_path_6209_);
v___f_6220_ = lean_alloc_closure((void*)(l_Lake_inputDir___lam__1___boxed), 10, 3);
lean_closure_set(v___f_6220_, 0, v_path_6209_);
lean_closure_set(v___f_6220_, 1, v___f_6219_);
lean_closure_set(v___f_6220_, 2, v_filter_6211_);
v___x_6221_ = lean_box(0);
v___x_6222_ = lean_unsigned_to_nat(0u);
v___x_6223_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
lean_inc_ref(v_a_6216_);
lean_inc(v_a_6215_);
lean_inc(v_a_6214_);
lean_inc(v_a_6213_);
lean_inc_ref(v_a_6212_);
v___x_6224_ = l_Lake_Job_async___redArg(v___x_6221_, v___f_6220_, v___x_6222_, v___x_6223_, v_a_6212_, v_a_6213_, v_a_6214_, v_a_6215_, v_a_6216_);
v___x_6225_ = lean_box(v_text_6210_);
v___f_6226_ = lean_alloc_closure((void*)(l_Lake_inputDir___lam__2___boxed), 10, 2);
lean_closure_set(v___f_6226_, 0, v___x_6225_);
lean_closure_set(v___f_6226_, 1, v_path_6209_);
v___x_6227_ = 0;
v___x_6228_ = l_Lake_Job_bindM___redArg(v___x_6221_, v___x_6224_, v___f_6226_, v___x_6222_, v___x_6227_, v_a_6212_, v_a_6213_, v_a_6214_, v_a_6215_, v_a_6216_, v_a_6217_);
return v___x_6228_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___boxed(lean_object* v_path_6229_, lean_object* v_text_6230_, lean_object* v_filter_6231_, lean_object* v_a_6232_, lean_object* v_a_6233_, lean_object* v_a_6234_, lean_object* v_a_6235_, lean_object* v_a_6236_, lean_object* v_a_6237_, lean_object* v_a_6238_){
_start:
{
uint8_t v_text_boxed_6239_; lean_object* v_res_6240_; 
v_text_boxed_6239_ = lean_unbox(v_text_6230_);
v_res_6240_ = l_Lake_inputDir(v_path_6229_, v_text_boxed_6239_, v_filter_6231_, v_a_6232_, v_a_6233_, v_a_6234_, v_a_6235_, v_a_6236_, v_a_6237_);
return v_res_6240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(lean_object* v_n_6241_, lean_object* v_as_6242_, lean_object* v_lo_6243_, lean_object* v_hi_6244_, lean_object* v_w_6245_, lean_object* v_hlo_6246_, lean_object* v_hhi_6247_){
_start:
{
lean_object* v___x_6248_; 
v___x_6248_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_as_6242_, v_lo_6243_, v_hi_6244_);
return v___x_6248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___boxed(lean_object* v_n_6249_, lean_object* v_as_6250_, lean_object* v_lo_6251_, lean_object* v_hi_6252_, lean_object* v_w_6253_, lean_object* v_hlo_6254_, lean_object* v_hhi_6255_){
_start:
{
lean_object* v_res_6256_; 
v_res_6256_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(v_n_6249_, v_as_6250_, v_lo_6251_, v_hi_6252_, v_w_6253_, v_hlo_6254_, v_hhi_6255_);
lean_dec(v_hi_6252_);
lean_dec(v_n_6249_);
return v_res_6256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(lean_object* v_filter_6257_, lean_object* v_as_6258_, size_t v_i_6259_, size_t v_stop_6260_, lean_object* v_b_6261_, lean_object* v___y_6262_, lean_object* v___y_6263_, lean_object* v___y_6264_, lean_object* v___y_6265_, lean_object* v___y_6266_, lean_object* v___y_6267_){
_start:
{
lean_object* v___x_6269_; 
v___x_6269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6257_, v_as_6258_, v_i_6259_, v_stop_6260_, v_b_6261_, v___y_6267_);
return v___x_6269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___boxed(lean_object* v_filter_6270_, lean_object* v_as_6271_, lean_object* v_i_6272_, lean_object* v_stop_6273_, lean_object* v_b_6274_, lean_object* v___y_6275_, lean_object* v___y_6276_, lean_object* v___y_6277_, lean_object* v___y_6278_, lean_object* v___y_6279_, lean_object* v___y_6280_, lean_object* v___y_6281_){
_start:
{
size_t v_i_boxed_6282_; size_t v_stop_boxed_6283_; lean_object* v_res_6284_; 
v_i_boxed_6282_ = lean_unbox_usize(v_i_6272_);
lean_dec(v_i_6272_);
v_stop_boxed_6283_ = lean_unbox_usize(v_stop_6273_);
lean_dec(v_stop_6273_);
v_res_6284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(v_filter_6270_, v_as_6271_, v_i_boxed_6282_, v_stop_boxed_6283_, v_b_6274_, v___y_6275_, v___y_6276_, v___y_6277_, v___y_6278_, v___y_6279_, v___y_6280_);
lean_dec_ref(v___y_6279_);
lean_dec(v___y_6278_);
lean_dec(v___y_6277_);
lean_dec(v___y_6276_);
lean_dec_ref(v___y_6275_);
lean_dec_ref(v_as_6271_);
return v_res_6284_;
}
}
LEAN_EXPORT uint64_t l_Lake_buildO___lam__0(uint64_t v_ts_6285_, lean_object* v_t_6286_){
_start:
{
uint64_t v___x_6287_; uint64_t v___x_6288_; uint64_t v___x_6289_; uint64_t v___x_6290_; 
v___x_6287_ = l_Lake_Hash_nil;
v___x_6288_ = lean_string_hash(v_t_6286_);
v___x_6289_ = lean_uint64_mix_hash(v___x_6287_, v___x_6288_);
v___x_6290_ = lean_uint64_mix_hash(v_ts_6285_, v___x_6289_);
return v___x_6290_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__0___boxed(lean_object* v_ts_6291_, lean_object* v_t_6292_){
_start:
{
uint64_t v_ts_boxed_6293_; uint64_t v_res_6294_; lean_object* v_r_6295_; 
v_ts_boxed_6293_ = lean_unbox_uint64(v_ts_6291_);
lean_dec_ref(v_ts_6291_);
v_res_6294_ = l_Lake_buildO___lam__0(v_ts_boxed_6293_, v_t_6292_);
lean_dec_ref(v_t_6292_);
v_r_6295_ = lean_box_uint64(v_res_6294_);
return v_r_6295_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1(lean_object* v_oFile_6296_, lean_object* v_srcFile_6297_, lean_object* v___x_6298_, lean_object* v_compiler_6299_, lean_object* v___y_6300_, lean_object* v___y_6301_, lean_object* v___y_6302_, lean_object* v___y_6303_, lean_object* v___y_6304_, lean_object* v___y_6305_){
_start:
{
lean_object* v_log_6307_; uint8_t v_action_6308_; uint8_t v_wantsRebuild_6309_; lean_object* v_trace_6310_; lean_object* v_buildTime_6311_; lean_object* v___x_6313_; uint8_t v_isShared_6314_; uint8_t v_isSharedCheck_6340_; 
v_log_6307_ = lean_ctor_get(v___y_6305_, 0);
v_action_6308_ = lean_ctor_get_uint8(v___y_6305_, sizeof(void*)*3);
v_wantsRebuild_6309_ = lean_ctor_get_uint8(v___y_6305_, sizeof(void*)*3 + 1);
v_trace_6310_ = lean_ctor_get(v___y_6305_, 1);
v_buildTime_6311_ = lean_ctor_get(v___y_6305_, 2);
v_isSharedCheck_6340_ = !lean_is_exclusive(v___y_6305_);
if (v_isSharedCheck_6340_ == 0)
{
v___x_6313_ = v___y_6305_;
v_isShared_6314_ = v_isSharedCheck_6340_;
goto v_resetjp_6312_;
}
else
{
lean_inc(v_buildTime_6311_);
lean_inc(v_trace_6310_);
lean_inc(v_log_6307_);
lean_dec(v___y_6305_);
v___x_6313_ = lean_box(0);
v_isShared_6314_ = v_isSharedCheck_6340_;
goto v_resetjp_6312_;
}
v_resetjp_6312_:
{
lean_object* v___x_6315_; 
v___x_6315_ = l_Lake_compileO(v_oFile_6296_, v_srcFile_6297_, v___x_6298_, v_compiler_6299_, v_log_6307_);
if (lean_obj_tag(v___x_6315_) == 0)
{
lean_object* v_a_6316_; lean_object* v_a_6317_; lean_object* v___x_6319_; uint8_t v_isShared_6320_; uint8_t v_isSharedCheck_6327_; 
v_a_6316_ = lean_ctor_get(v___x_6315_, 0);
v_a_6317_ = lean_ctor_get(v___x_6315_, 1);
v_isSharedCheck_6327_ = !lean_is_exclusive(v___x_6315_);
if (v_isSharedCheck_6327_ == 0)
{
v___x_6319_ = v___x_6315_;
v_isShared_6320_ = v_isSharedCheck_6327_;
goto v_resetjp_6318_;
}
else
{
lean_inc(v_a_6317_);
lean_inc(v_a_6316_);
lean_dec(v___x_6315_);
v___x_6319_ = lean_box(0);
v_isShared_6320_ = v_isSharedCheck_6327_;
goto v_resetjp_6318_;
}
v_resetjp_6318_:
{
lean_object* v___x_6322_; 
if (v_isShared_6314_ == 0)
{
lean_ctor_set(v___x_6313_, 0, v_a_6317_);
v___x_6322_ = v___x_6313_;
goto v_reusejp_6321_;
}
else
{
lean_object* v_reuseFailAlloc_6326_; 
v_reuseFailAlloc_6326_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6326_, 0, v_a_6317_);
lean_ctor_set(v_reuseFailAlloc_6326_, 1, v_trace_6310_);
lean_ctor_set(v_reuseFailAlloc_6326_, 2, v_buildTime_6311_);
lean_ctor_set_uint8(v_reuseFailAlloc_6326_, sizeof(void*)*3, v_action_6308_);
lean_ctor_set_uint8(v_reuseFailAlloc_6326_, sizeof(void*)*3 + 1, v_wantsRebuild_6309_);
v___x_6322_ = v_reuseFailAlloc_6326_;
goto v_reusejp_6321_;
}
v_reusejp_6321_:
{
lean_object* v___x_6324_; 
if (v_isShared_6320_ == 0)
{
lean_ctor_set(v___x_6319_, 1, v___x_6322_);
v___x_6324_ = v___x_6319_;
goto v_reusejp_6323_;
}
else
{
lean_object* v_reuseFailAlloc_6325_; 
v_reuseFailAlloc_6325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6325_, 0, v_a_6316_);
lean_ctor_set(v_reuseFailAlloc_6325_, 1, v___x_6322_);
v___x_6324_ = v_reuseFailAlloc_6325_;
goto v_reusejp_6323_;
}
v_reusejp_6323_:
{
return v___x_6324_;
}
}
}
}
else
{
lean_object* v_a_6328_; lean_object* v_a_6329_; lean_object* v___x_6331_; uint8_t v_isShared_6332_; uint8_t v_isSharedCheck_6339_; 
v_a_6328_ = lean_ctor_get(v___x_6315_, 0);
v_a_6329_ = lean_ctor_get(v___x_6315_, 1);
v_isSharedCheck_6339_ = !lean_is_exclusive(v___x_6315_);
if (v_isSharedCheck_6339_ == 0)
{
v___x_6331_ = v___x_6315_;
v_isShared_6332_ = v_isSharedCheck_6339_;
goto v_resetjp_6330_;
}
else
{
lean_inc(v_a_6329_);
lean_inc(v_a_6328_);
lean_dec(v___x_6315_);
v___x_6331_ = lean_box(0);
v_isShared_6332_ = v_isSharedCheck_6339_;
goto v_resetjp_6330_;
}
v_resetjp_6330_:
{
lean_object* v___x_6334_; 
if (v_isShared_6314_ == 0)
{
lean_ctor_set(v___x_6313_, 0, v_a_6329_);
v___x_6334_ = v___x_6313_;
goto v_reusejp_6333_;
}
else
{
lean_object* v_reuseFailAlloc_6338_; 
v_reuseFailAlloc_6338_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6338_, 0, v_a_6329_);
lean_ctor_set(v_reuseFailAlloc_6338_, 1, v_trace_6310_);
lean_ctor_set(v_reuseFailAlloc_6338_, 2, v_buildTime_6311_);
lean_ctor_set_uint8(v_reuseFailAlloc_6338_, sizeof(void*)*3, v_action_6308_);
lean_ctor_set_uint8(v_reuseFailAlloc_6338_, sizeof(void*)*3 + 1, v_wantsRebuild_6309_);
v___x_6334_ = v_reuseFailAlloc_6338_;
goto v_reusejp_6333_;
}
v_reusejp_6333_:
{
lean_object* v___x_6336_; 
if (v_isShared_6332_ == 0)
{
lean_ctor_set(v___x_6331_, 1, v___x_6334_);
v___x_6336_ = v___x_6331_;
goto v_reusejp_6335_;
}
else
{
lean_object* v_reuseFailAlloc_6337_; 
v_reuseFailAlloc_6337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6337_, 0, v_a_6328_);
lean_ctor_set(v_reuseFailAlloc_6337_, 1, v___x_6334_);
v___x_6336_ = v_reuseFailAlloc_6337_;
goto v_reusejp_6335_;
}
v_reusejp_6335_:
{
return v___x_6336_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1___boxed(lean_object* v_oFile_6341_, lean_object* v_srcFile_6342_, lean_object* v___x_6343_, lean_object* v_compiler_6344_, lean_object* v___y_6345_, lean_object* v___y_6346_, lean_object* v___y_6347_, lean_object* v___y_6348_, lean_object* v___y_6349_, lean_object* v___y_6350_, lean_object* v___y_6351_){
_start:
{
lean_object* v_res_6352_; 
v_res_6352_ = l_Lake_buildO___lam__1(v_oFile_6341_, v_srcFile_6342_, v___x_6343_, v_compiler_6344_, v___y_6345_, v___y_6346_, v___y_6347_, v___y_6348_, v___y_6349_, v___y_6350_);
lean_dec_ref(v___y_6349_);
lean_dec(v___y_6348_);
lean_dec(v___y_6347_);
lean_dec(v___y_6346_);
lean_dec_ref(v___y_6345_);
lean_dec_ref(v___x_6343_);
return v_res_6352_;
}
}
static lean_object* _init_l_Lake_buildO___lam__2___boxed__const__1(void){
_start:
{
uint64_t v___x_6356_; lean_object* v___x_6357_; 
v___x_6356_ = l_Lake_Hash_nil;
v___x_6357_ = lean_box_uint64(v___x_6356_);
return v___x_6357_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2(lean_object* v_traceArgs_6358_, lean_object* v___f_6359_, lean_object* v_extraDepTrace_6360_, lean_object* v_weakArgs_6361_, lean_object* v_oFile_6362_, lean_object* v_compiler_6363_, lean_object* v___x_6364_, lean_object* v___f_6365_, lean_object* v_srcFile_6366_, lean_object* v___y_6367_, lean_object* v___y_6368_, lean_object* v___y_6369_, lean_object* v___y_6370_, lean_object* v___y_6371_, lean_object* v___y_6372_){
_start:
{
lean_object* v_log_6374_; uint8_t v_action_6375_; uint8_t v_wantsRebuild_6376_; lean_object* v_trace_6377_; lean_object* v_buildTime_6378_; lean_object* v___x_6380_; uint8_t v_isShared_6381_; uint8_t v_isSharedCheck_6463_; 
v_log_6374_ = lean_ctor_get(v___y_6372_, 0);
v_action_6375_ = lean_ctor_get_uint8(v___y_6372_, sizeof(void*)*3);
v_wantsRebuild_6376_ = lean_ctor_get_uint8(v___y_6372_, sizeof(void*)*3 + 1);
v_trace_6377_ = lean_ctor_get(v___y_6372_, 1);
v_buildTime_6378_ = lean_ctor_get(v___y_6372_, 2);
v_isSharedCheck_6463_ = !lean_is_exclusive(v___y_6372_);
if (v_isSharedCheck_6463_ == 0)
{
v___x_6380_ = v___y_6372_;
v_isShared_6381_ = v_isSharedCheck_6463_;
goto v_resetjp_6379_;
}
else
{
lean_inc(v_buildTime_6378_);
lean_inc(v_trace_6377_);
lean_inc(v_log_6374_);
lean_dec(v___y_6372_);
v___x_6380_ = lean_box(0);
v_isShared_6381_ = v_isSharedCheck_6463_;
goto v_resetjp_6379_;
}
v_resetjp_6379_:
{
lean_object* v___x_6382_; lean_object* v___x_6383_; uint64_t v___y_6385_; uint64_t v___x_6448_; lean_object* v___x_6449_; lean_object* v___x_6450_; uint8_t v___x_6451_; 
v___x_6382_ = l_Lake_platformTrace;
v___x_6383_ = l_Lake_BuildTrace_mix(v_trace_6377_, v___x_6382_);
v___x_6448_ = l_Lake_Hash_nil;
v___x_6449_ = lean_unsigned_to_nat(0u);
v___x_6450_ = lean_array_get_size(v_traceArgs_6358_);
v___x_6451_ = lean_nat_dec_lt(v___x_6449_, v___x_6450_);
if (v___x_6451_ == 0)
{
lean_dec_ref(v___f_6365_);
lean_dec_ref(v___x_6364_);
v___y_6385_ = v___x_6448_;
goto v___jp_6384_;
}
else
{
uint8_t v___x_6452_; 
v___x_6452_ = lean_nat_dec_le(v___x_6450_, v___x_6450_);
if (v___x_6452_ == 0)
{
if (v___x_6451_ == 0)
{
lean_dec_ref(v___f_6365_);
lean_dec_ref(v___x_6364_);
v___y_6385_ = v___x_6448_;
goto v___jp_6384_;
}
else
{
size_t v___x_6453_; size_t v___x_6454_; lean_object* v___x_6455_; lean_object* v___x_6456_; uint64_t v___x_6457_; 
v___x_6453_ = ((size_t)0ULL);
v___x_6454_ = lean_usize_of_nat(v___x_6450_);
v___x_6455_ = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(v_traceArgs_6358_);
v___x_6456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_6364_, v___f_6365_, v_traceArgs_6358_, v___x_6453_, v___x_6454_, v___x_6455_);
v___x_6457_ = lean_unbox_uint64(v___x_6456_);
lean_dec(v___x_6456_);
v___y_6385_ = v___x_6457_;
goto v___jp_6384_;
}
}
else
{
size_t v___x_6458_; size_t v___x_6459_; lean_object* v___x_6460_; lean_object* v___x_6461_; uint64_t v___x_6462_; 
v___x_6458_ = ((size_t)0ULL);
v___x_6459_ = lean_usize_of_nat(v___x_6450_);
v___x_6460_ = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(v_traceArgs_6358_);
v___x_6461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_6364_, v___f_6365_, v_traceArgs_6358_, v___x_6458_, v___x_6459_, v___x_6460_);
v___x_6462_ = lean_unbox_uint64(v___x_6461_);
lean_dec(v___x_6461_);
v___y_6385_ = v___x_6462_;
goto v___jp_6384_;
}
}
v___jp_6384_:
{
lean_object* v___x_6386_; lean_object* v___x_6387_; lean_object* v___x_6388_; lean_object* v___x_6389_; lean_object* v___x_6390_; lean_object* v___x_6391_; lean_object* v___x_6392_; lean_object* v___x_6393_; lean_object* v___x_6394_; lean_object* v___x_6395_; lean_object* v___x_6397_; 
v___x_6386_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_6387_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_6358_);
v___x_6388_ = lean_array_to_list(v_traceArgs_6358_);
v___x_6389_ = l_List_toString___redArg(v___f_6359_, v___x_6388_);
v___x_6390_ = lean_string_append(v___x_6387_, v___x_6389_);
lean_dec_ref(v___x_6389_);
v___x_6391_ = lean_string_append(v___x_6386_, v___x_6390_);
lean_dec_ref(v___x_6390_);
v___x_6392_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_6393_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_6394_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6394_, 0, v___x_6391_);
lean_ctor_set(v___x_6394_, 1, v___x_6392_);
lean_ctor_set(v___x_6394_, 2, v___x_6393_);
lean_ctor_set_uint64(v___x_6394_, sizeof(void*)*3, v___y_6385_);
v___x_6395_ = l_Lake_BuildTrace_mix(v___x_6383_, v___x_6394_);
if (v_isShared_6381_ == 0)
{
lean_ctor_set(v___x_6380_, 1, v___x_6395_);
v___x_6397_ = v___x_6380_;
goto v_reusejp_6396_;
}
else
{
lean_object* v_reuseFailAlloc_6447_; 
v_reuseFailAlloc_6447_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6447_, 0, v_log_6374_);
lean_ctor_set(v_reuseFailAlloc_6447_, 1, v___x_6395_);
lean_ctor_set(v_reuseFailAlloc_6447_, 2, v_buildTime_6378_);
lean_ctor_set_uint8(v_reuseFailAlloc_6447_, sizeof(void*)*3, v_action_6375_);
lean_ctor_set_uint8(v_reuseFailAlloc_6447_, sizeof(void*)*3 + 1, v_wantsRebuild_6376_);
v___x_6397_ = v_reuseFailAlloc_6447_;
goto v_reusejp_6396_;
}
v_reusejp_6396_:
{
lean_object* v___x_6398_; 
lean_inc_ref(v___y_6371_);
lean_inc(v___y_6370_);
lean_inc(v___y_6369_);
lean_inc(v___y_6368_);
lean_inc_ref(v___y_6367_);
v___x_6398_ = lean_apply_7(v_extraDepTrace_6360_, v___y_6367_, v___y_6368_, v___y_6369_, v___y_6370_, v___y_6371_, v___x_6397_, lean_box(0));
if (lean_obj_tag(v___x_6398_) == 0)
{
lean_object* v_a_6399_; lean_object* v_a_6400_; lean_object* v_log_6401_; uint8_t v_action_6402_; uint8_t v_wantsRebuild_6403_; lean_object* v_trace_6404_; lean_object* v_buildTime_6405_; lean_object* v___x_6407_; uint8_t v_isShared_6408_; uint8_t v_isSharedCheck_6437_; 
v_a_6399_ = lean_ctor_get(v___x_6398_, 1);
lean_inc(v_a_6399_);
v_a_6400_ = lean_ctor_get(v___x_6398_, 0);
lean_inc(v_a_6400_);
lean_dec_ref(v___x_6398_);
v_log_6401_ = lean_ctor_get(v_a_6399_, 0);
v_action_6402_ = lean_ctor_get_uint8(v_a_6399_, sizeof(void*)*3);
v_wantsRebuild_6403_ = lean_ctor_get_uint8(v_a_6399_, sizeof(void*)*3 + 1);
v_trace_6404_ = lean_ctor_get(v_a_6399_, 1);
v_buildTime_6405_ = lean_ctor_get(v_a_6399_, 2);
v_isSharedCheck_6437_ = !lean_is_exclusive(v_a_6399_);
if (v_isSharedCheck_6437_ == 0)
{
v___x_6407_ = v_a_6399_;
v_isShared_6408_ = v_isSharedCheck_6437_;
goto v_resetjp_6406_;
}
else
{
lean_inc(v_buildTime_6405_);
lean_inc(v_trace_6404_);
lean_inc(v_log_6401_);
lean_dec(v_a_6399_);
v___x_6407_ = lean_box(0);
v_isShared_6408_ = v_isSharedCheck_6437_;
goto v_resetjp_6406_;
}
v_resetjp_6406_:
{
lean_object* v___x_6409_; lean_object* v___x_6411_; 
v___x_6409_ = l_Lake_BuildTrace_mix(v_trace_6404_, v_a_6400_);
if (v_isShared_6408_ == 0)
{
lean_ctor_set(v___x_6407_, 1, v___x_6409_);
v___x_6411_ = v___x_6407_;
goto v_reusejp_6410_;
}
else
{
lean_object* v_reuseFailAlloc_6436_; 
v_reuseFailAlloc_6436_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6436_, 0, v_log_6401_);
lean_ctor_set(v_reuseFailAlloc_6436_, 1, v___x_6409_);
lean_ctor_set(v_reuseFailAlloc_6436_, 2, v_buildTime_6405_);
lean_ctor_set_uint8(v_reuseFailAlloc_6436_, sizeof(void*)*3, v_action_6402_);
lean_ctor_set_uint8(v_reuseFailAlloc_6436_, sizeof(void*)*3 + 1, v_wantsRebuild_6403_);
v___x_6411_ = v_reuseFailAlloc_6436_;
goto v_reusejp_6410_;
}
v_reusejp_6410_:
{
lean_object* v___x_6412_; lean_object* v___f_6413_; uint8_t v___x_6414_; lean_object* v___x_6415_; lean_object* v___x_6416_; 
v___x_6412_ = l_Array_append___redArg(v_weakArgs_6361_, v_traceArgs_6358_);
lean_dec_ref(v_traceArgs_6358_);
lean_inc_ref(v_oFile_6362_);
v___f_6413_ = lean_alloc_closure((void*)(l_Lake_buildO___lam__1___boxed), 11, 4);
lean_closure_set(v___f_6413_, 0, v_oFile_6362_);
lean_closure_set(v___f_6413_, 1, v_srcFile_6366_);
lean_closure_set(v___f_6413_, 2, v___x_6412_);
lean_closure_set(v___f_6413_, 3, v_compiler_6363_);
v___x_6414_ = 0;
v___x_6415_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
v___x_6416_ = l_Lake_buildArtifactUnlessUpToDate(v_oFile_6362_, v___f_6413_, v___x_6414_, v___x_6415_, v___x_6414_, v___x_6414_, v___x_6414_, v___y_6367_, v___y_6368_, v___y_6369_, v___y_6370_, v___y_6371_, v___x_6411_);
if (lean_obj_tag(v___x_6416_) == 0)
{
lean_object* v_a_6417_; lean_object* v_a_6418_; lean_object* v___x_6420_; uint8_t v_isShared_6421_; uint8_t v_isSharedCheck_6426_; 
v_a_6417_ = lean_ctor_get(v___x_6416_, 0);
v_a_6418_ = lean_ctor_get(v___x_6416_, 1);
v_isSharedCheck_6426_ = !lean_is_exclusive(v___x_6416_);
if (v_isSharedCheck_6426_ == 0)
{
v___x_6420_ = v___x_6416_;
v_isShared_6421_ = v_isSharedCheck_6426_;
goto v_resetjp_6419_;
}
else
{
lean_inc(v_a_6418_);
lean_inc(v_a_6417_);
lean_dec(v___x_6416_);
v___x_6420_ = lean_box(0);
v_isShared_6421_ = v_isSharedCheck_6426_;
goto v_resetjp_6419_;
}
v_resetjp_6419_:
{
lean_object* v_path_6422_; lean_object* v___x_6424_; 
v_path_6422_ = lean_ctor_get(v_a_6417_, 1);
lean_inc_ref(v_path_6422_);
lean_dec(v_a_6417_);
if (v_isShared_6421_ == 0)
{
lean_ctor_set(v___x_6420_, 0, v_path_6422_);
v___x_6424_ = v___x_6420_;
goto v_reusejp_6423_;
}
else
{
lean_object* v_reuseFailAlloc_6425_; 
v_reuseFailAlloc_6425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6425_, 0, v_path_6422_);
lean_ctor_set(v_reuseFailAlloc_6425_, 1, v_a_6418_);
v___x_6424_ = v_reuseFailAlloc_6425_;
goto v_reusejp_6423_;
}
v_reusejp_6423_:
{
return v___x_6424_;
}
}
}
else
{
lean_object* v_a_6427_; lean_object* v_a_6428_; lean_object* v___x_6430_; uint8_t v_isShared_6431_; uint8_t v_isSharedCheck_6435_; 
v_a_6427_ = lean_ctor_get(v___x_6416_, 0);
v_a_6428_ = lean_ctor_get(v___x_6416_, 1);
v_isSharedCheck_6435_ = !lean_is_exclusive(v___x_6416_);
if (v_isSharedCheck_6435_ == 0)
{
v___x_6430_ = v___x_6416_;
v_isShared_6431_ = v_isSharedCheck_6435_;
goto v_resetjp_6429_;
}
else
{
lean_inc(v_a_6428_);
lean_inc(v_a_6427_);
lean_dec(v___x_6416_);
v___x_6430_ = lean_box(0);
v_isShared_6431_ = v_isSharedCheck_6435_;
goto v_resetjp_6429_;
}
v_resetjp_6429_:
{
lean_object* v___x_6433_; 
if (v_isShared_6431_ == 0)
{
v___x_6433_ = v___x_6430_;
goto v_reusejp_6432_;
}
else
{
lean_object* v_reuseFailAlloc_6434_; 
v_reuseFailAlloc_6434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6434_, 0, v_a_6427_);
lean_ctor_set(v_reuseFailAlloc_6434_, 1, v_a_6428_);
v___x_6433_ = v_reuseFailAlloc_6434_;
goto v_reusejp_6432_;
}
v_reusejp_6432_:
{
return v___x_6433_;
}
}
}
}
}
}
else
{
lean_object* v_a_6438_; lean_object* v_a_6439_; lean_object* v___x_6441_; uint8_t v_isShared_6442_; uint8_t v_isSharedCheck_6446_; 
lean_dec_ref(v___y_6371_);
lean_dec(v___y_6370_);
lean_dec(v___y_6369_);
lean_dec(v___y_6368_);
lean_dec_ref(v___y_6367_);
lean_dec_ref(v_srcFile_6366_);
lean_dec_ref(v_compiler_6363_);
lean_dec_ref(v_oFile_6362_);
lean_dec_ref(v_weakArgs_6361_);
lean_dec_ref(v_traceArgs_6358_);
v_a_6438_ = lean_ctor_get(v___x_6398_, 0);
v_a_6439_ = lean_ctor_get(v___x_6398_, 1);
v_isSharedCheck_6446_ = !lean_is_exclusive(v___x_6398_);
if (v_isSharedCheck_6446_ == 0)
{
v___x_6441_ = v___x_6398_;
v_isShared_6442_ = v_isSharedCheck_6446_;
goto v_resetjp_6440_;
}
else
{
lean_inc(v_a_6439_);
lean_inc(v_a_6438_);
lean_dec(v___x_6398_);
v___x_6441_ = lean_box(0);
v_isShared_6442_ = v_isSharedCheck_6446_;
goto v_resetjp_6440_;
}
v_resetjp_6440_:
{
lean_object* v___x_6444_; 
if (v_isShared_6442_ == 0)
{
v___x_6444_ = v___x_6441_;
goto v_reusejp_6443_;
}
else
{
lean_object* v_reuseFailAlloc_6445_; 
v_reuseFailAlloc_6445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6445_, 0, v_a_6438_);
lean_ctor_set(v_reuseFailAlloc_6445_, 1, v_a_6439_);
v___x_6444_ = v_reuseFailAlloc_6445_;
goto v_reusejp_6443_;
}
v_reusejp_6443_:
{
return v___x_6444_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed(lean_object* v_traceArgs_6464_, lean_object* v___f_6465_, lean_object* v_extraDepTrace_6466_, lean_object* v_weakArgs_6467_, lean_object* v_oFile_6468_, lean_object* v_compiler_6469_, lean_object* v___x_6470_, lean_object* v___f_6471_, lean_object* v_srcFile_6472_, lean_object* v___y_6473_, lean_object* v___y_6474_, lean_object* v___y_6475_, lean_object* v___y_6476_, lean_object* v___y_6477_, lean_object* v___y_6478_, lean_object* v___y_6479_){
_start:
{
lean_object* v_res_6480_; 
v_res_6480_ = l_Lake_buildO___lam__2(v_traceArgs_6464_, v___f_6465_, v_extraDepTrace_6466_, v_weakArgs_6467_, v_oFile_6468_, v_compiler_6469_, v___x_6470_, v___f_6471_, v_srcFile_6472_, v___y_6473_, v___y_6474_, v___y_6475_, v___y_6476_, v___y_6477_, v___y_6478_);
return v_res_6480_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object* v_oFile_6483_, lean_object* v_srcJob_6484_, lean_object* v_weakArgs_6485_, lean_object* v_traceArgs_6486_, lean_object* v_compiler_6487_, lean_object* v_extraDepTrace_6488_, lean_object* v_a_6489_, lean_object* v_a_6490_, lean_object* v_a_6491_, lean_object* v_a_6492_, lean_object* v_a_6493_, lean_object* v_a_6494_){
_start:
{
lean_object* v___f_6496_; lean_object* v___x_6497_; lean_object* v___f_6498_; lean_object* v___x_6499_; lean_object* v___f_6500_; lean_object* v___x_6501_; uint8_t v___x_6502_; lean_object* v___x_6503_; 
v___f_6496_ = ((lean_object*)(l_Lake_buildO___closed__0));
v___x_6497_ = l_Lake_instDataKindFilePath;
v___f_6498_ = ((lean_object*)(l_Lake_buildO___closed__1));
v___x_6499_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__10));
v___f_6500_ = lean_alloc_closure((void*)(l_Lake_buildO___lam__2___boxed), 16, 8);
lean_closure_set(v___f_6500_, 0, v_traceArgs_6486_);
lean_closure_set(v___f_6500_, 1, v___f_6498_);
lean_closure_set(v___f_6500_, 2, v_extraDepTrace_6488_);
lean_closure_set(v___f_6500_, 3, v_weakArgs_6485_);
lean_closure_set(v___f_6500_, 4, v_oFile_6483_);
lean_closure_set(v___f_6500_, 5, v_compiler_6487_);
lean_closure_set(v___f_6500_, 6, v___x_6499_);
lean_closure_set(v___f_6500_, 7, v___f_6496_);
v___x_6501_ = lean_unsigned_to_nat(0u);
v___x_6502_ = 0;
v___x_6503_ = l_Lake_Job_mapM___redArg(v___x_6497_, v_srcJob_6484_, v___f_6500_, v___x_6501_, v___x_6502_, v_a_6489_, v_a_6490_, v_a_6491_, v_a_6492_, v_a_6493_, v_a_6494_);
return v___x_6503_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___boxed(lean_object* v_oFile_6504_, lean_object* v_srcJob_6505_, lean_object* v_weakArgs_6506_, lean_object* v_traceArgs_6507_, lean_object* v_compiler_6508_, lean_object* v_extraDepTrace_6509_, lean_object* v_a_6510_, lean_object* v_a_6511_, lean_object* v_a_6512_, lean_object* v_a_6513_, lean_object* v_a_6514_, lean_object* v_a_6515_, lean_object* v_a_6516_){
_start:
{
lean_object* v_res_6517_; 
v_res_6517_ = l_Lake_buildO(v_oFile_6504_, v_srcJob_6505_, v_weakArgs_6506_, v_traceArgs_6507_, v_compiler_6508_, v_extraDepTrace_6509_, v_a_6510_, v_a_6511_, v_a_6512_, v_a_6513_, v_a_6514_, v_a_6515_);
return v_res_6517_;
}
}
static lean_object* _init_l_Lake_buildLeanO___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6519_; lean_object* v___x_6520_; lean_object* v___x_6521_; lean_object* v___x_6522_; 
v___x_6519_ = ((lean_object*)(l_Lake_buildLeanO___lam__0___closed__0));
v___x_6520_ = lean_unsigned_to_nat(2u);
v___x_6521_ = lean_mk_empty_array_with_capacity(v___x_6520_);
v___x_6522_ = lean_array_push(v___x_6521_, v___x_6519_);
return v___x_6522_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0(lean_object* v_weakArgs_6523_, lean_object* v_traceArgs_6524_, lean_object* v_oFile_6525_, lean_object* v_srcFile_6526_, lean_object* v_leanIncludeDir_x3f_6527_, lean_object* v___y_6528_, lean_object* v___y_6529_, lean_object* v___y_6530_, lean_object* v___y_6531_, lean_object* v___y_6532_, lean_object* v___y_6533_){
_start:
{
lean_object* v_toContext_6535_; lean_object* v_lakeEnv_6536_; lean_object* v_log_6537_; uint8_t v_action_6538_; uint8_t v_wantsRebuild_6539_; lean_object* v_trace_6540_; lean_object* v_buildTime_6541_; lean_object* v___x_6543_; uint8_t v_isShared_6544_; uint8_t v_isSharedCheck_6582_; 
v_toContext_6535_ = lean_ctor_get(v___y_6532_, 1);
lean_inc(v_toContext_6535_);
lean_dec_ref(v___y_6532_);
v_lakeEnv_6536_ = lean_ctor_get(v_toContext_6535_, 1);
lean_inc_ref(v_lakeEnv_6536_);
lean_dec(v_toContext_6535_);
v_log_6537_ = lean_ctor_get(v___y_6533_, 0);
v_action_6538_ = lean_ctor_get_uint8(v___y_6533_, sizeof(void*)*3);
v_wantsRebuild_6539_ = lean_ctor_get_uint8(v___y_6533_, sizeof(void*)*3 + 1);
v_trace_6540_ = lean_ctor_get(v___y_6533_, 1);
v_buildTime_6541_ = lean_ctor_get(v___y_6533_, 2);
v_isSharedCheck_6582_ = !lean_is_exclusive(v___y_6533_);
if (v_isSharedCheck_6582_ == 0)
{
v___x_6543_ = v___y_6533_;
v_isShared_6544_ = v_isSharedCheck_6582_;
goto v_resetjp_6542_;
}
else
{
lean_inc(v_buildTime_6541_);
lean_inc(v_trace_6540_);
lean_inc(v_log_6537_);
lean_dec(v___y_6533_);
v___x_6543_ = lean_box(0);
v_isShared_6544_ = v_isSharedCheck_6582_;
goto v_resetjp_6542_;
}
v_resetjp_6542_:
{
lean_object* v_lean_6545_; lean_object* v___y_6547_; 
v_lean_6545_ = lean_ctor_get(v_lakeEnv_6536_, 1);
lean_inc_ref(v_lean_6545_);
lean_dec_ref(v_lakeEnv_6536_);
if (lean_obj_tag(v_leanIncludeDir_x3f_6527_) == 0)
{
lean_object* v_includeDir_6580_; 
v_includeDir_6580_ = lean_ctor_get(v_lean_6545_, 4);
lean_inc_ref(v_includeDir_6580_);
v___y_6547_ = v_includeDir_6580_;
goto v___jp_6546_;
}
else
{
lean_object* v_val_6581_; 
v_val_6581_ = lean_ctor_get(v_leanIncludeDir_x3f_6527_, 0);
lean_inc(v_val_6581_);
lean_dec_ref(v_leanIncludeDir_x3f_6527_);
v___y_6547_ = v_val_6581_;
goto v___jp_6546_;
}
v___jp_6546_:
{
lean_object* v_cc_6548_; lean_object* v_ccFlags_6549_; lean_object* v___x_6550_; lean_object* v___x_6551_; lean_object* v___x_6552_; lean_object* v___x_6553_; lean_object* v___x_6554_; lean_object* v___x_6555_; 
v_cc_6548_ = lean_ctor_get(v_lean_6545_, 13);
lean_inc_ref(v_cc_6548_);
v_ccFlags_6549_ = lean_ctor_get(v_lean_6545_, 17);
lean_inc_ref(v_ccFlags_6549_);
lean_dec_ref(v_lean_6545_);
v___x_6550_ = lean_obj_once(&l_Lake_buildLeanO___lam__0___closed__1, &l_Lake_buildLeanO___lam__0___closed__1_once, _init_l_Lake_buildLeanO___lam__0___closed__1);
v___x_6551_ = lean_array_push(v___x_6550_, v___y_6547_);
v___x_6552_ = l_Array_append___redArg(v___x_6551_, v_ccFlags_6549_);
lean_dec_ref(v_ccFlags_6549_);
v___x_6553_ = l_Array_append___redArg(v___x_6552_, v_weakArgs_6523_);
v___x_6554_ = l_Array_append___redArg(v___x_6553_, v_traceArgs_6524_);
v___x_6555_ = l_Lake_compileO(v_oFile_6525_, v_srcFile_6526_, v___x_6554_, v_cc_6548_, v_log_6537_);
lean_dec_ref(v___x_6554_);
if (lean_obj_tag(v___x_6555_) == 0)
{
lean_object* v_a_6556_; lean_object* v_a_6557_; lean_object* v___x_6559_; uint8_t v_isShared_6560_; uint8_t v_isSharedCheck_6567_; 
v_a_6556_ = lean_ctor_get(v___x_6555_, 0);
v_a_6557_ = lean_ctor_get(v___x_6555_, 1);
v_isSharedCheck_6567_ = !lean_is_exclusive(v___x_6555_);
if (v_isSharedCheck_6567_ == 0)
{
v___x_6559_ = v___x_6555_;
v_isShared_6560_ = v_isSharedCheck_6567_;
goto v_resetjp_6558_;
}
else
{
lean_inc(v_a_6557_);
lean_inc(v_a_6556_);
lean_dec(v___x_6555_);
v___x_6559_ = lean_box(0);
v_isShared_6560_ = v_isSharedCheck_6567_;
goto v_resetjp_6558_;
}
v_resetjp_6558_:
{
lean_object* v___x_6562_; 
if (v_isShared_6544_ == 0)
{
lean_ctor_set(v___x_6543_, 0, v_a_6557_);
v___x_6562_ = v___x_6543_;
goto v_reusejp_6561_;
}
else
{
lean_object* v_reuseFailAlloc_6566_; 
v_reuseFailAlloc_6566_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6566_, 0, v_a_6557_);
lean_ctor_set(v_reuseFailAlloc_6566_, 1, v_trace_6540_);
lean_ctor_set(v_reuseFailAlloc_6566_, 2, v_buildTime_6541_);
lean_ctor_set_uint8(v_reuseFailAlloc_6566_, sizeof(void*)*3, v_action_6538_);
lean_ctor_set_uint8(v_reuseFailAlloc_6566_, sizeof(void*)*3 + 1, v_wantsRebuild_6539_);
v___x_6562_ = v_reuseFailAlloc_6566_;
goto v_reusejp_6561_;
}
v_reusejp_6561_:
{
lean_object* v___x_6564_; 
if (v_isShared_6560_ == 0)
{
lean_ctor_set(v___x_6559_, 1, v___x_6562_);
v___x_6564_ = v___x_6559_;
goto v_reusejp_6563_;
}
else
{
lean_object* v_reuseFailAlloc_6565_; 
v_reuseFailAlloc_6565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6565_, 0, v_a_6556_);
lean_ctor_set(v_reuseFailAlloc_6565_, 1, v___x_6562_);
v___x_6564_ = v_reuseFailAlloc_6565_;
goto v_reusejp_6563_;
}
v_reusejp_6563_:
{
return v___x_6564_;
}
}
}
}
else
{
lean_object* v_a_6568_; lean_object* v_a_6569_; lean_object* v___x_6571_; uint8_t v_isShared_6572_; uint8_t v_isSharedCheck_6579_; 
v_a_6568_ = lean_ctor_get(v___x_6555_, 0);
v_a_6569_ = lean_ctor_get(v___x_6555_, 1);
v_isSharedCheck_6579_ = !lean_is_exclusive(v___x_6555_);
if (v_isSharedCheck_6579_ == 0)
{
v___x_6571_ = v___x_6555_;
v_isShared_6572_ = v_isSharedCheck_6579_;
goto v_resetjp_6570_;
}
else
{
lean_inc(v_a_6569_);
lean_inc(v_a_6568_);
lean_dec(v___x_6555_);
v___x_6571_ = lean_box(0);
v_isShared_6572_ = v_isSharedCheck_6579_;
goto v_resetjp_6570_;
}
v_resetjp_6570_:
{
lean_object* v___x_6574_; 
if (v_isShared_6544_ == 0)
{
lean_ctor_set(v___x_6543_, 0, v_a_6569_);
v___x_6574_ = v___x_6543_;
goto v_reusejp_6573_;
}
else
{
lean_object* v_reuseFailAlloc_6578_; 
v_reuseFailAlloc_6578_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6578_, 0, v_a_6569_);
lean_ctor_set(v_reuseFailAlloc_6578_, 1, v_trace_6540_);
lean_ctor_set(v_reuseFailAlloc_6578_, 2, v_buildTime_6541_);
lean_ctor_set_uint8(v_reuseFailAlloc_6578_, sizeof(void*)*3, v_action_6538_);
lean_ctor_set_uint8(v_reuseFailAlloc_6578_, sizeof(void*)*3 + 1, v_wantsRebuild_6539_);
v___x_6574_ = v_reuseFailAlloc_6578_;
goto v_reusejp_6573_;
}
v_reusejp_6573_:
{
lean_object* v___x_6576_; 
if (v_isShared_6572_ == 0)
{
lean_ctor_set(v___x_6571_, 1, v___x_6574_);
v___x_6576_ = v___x_6571_;
goto v_reusejp_6575_;
}
else
{
lean_object* v_reuseFailAlloc_6577_; 
v_reuseFailAlloc_6577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6577_, 0, v_a_6568_);
lean_ctor_set(v_reuseFailAlloc_6577_, 1, v___x_6574_);
v___x_6576_ = v_reuseFailAlloc_6577_;
goto v_reusejp_6575_;
}
v_reusejp_6575_:
{
return v___x_6576_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0___boxed(lean_object* v_weakArgs_6583_, lean_object* v_traceArgs_6584_, lean_object* v_oFile_6585_, lean_object* v_srcFile_6586_, lean_object* v_leanIncludeDir_x3f_6587_, lean_object* v___y_6588_, lean_object* v___y_6589_, lean_object* v___y_6590_, lean_object* v___y_6591_, lean_object* v___y_6592_, lean_object* v___y_6593_, lean_object* v___y_6594_){
_start:
{
lean_object* v_res_6595_; 
v_res_6595_ = l_Lake_buildLeanO___lam__0(v_weakArgs_6583_, v_traceArgs_6584_, v_oFile_6585_, v_srcFile_6586_, v_leanIncludeDir_x3f_6587_, v___y_6588_, v___y_6589_, v___y_6590_, v___y_6591_, v___y_6592_, v___y_6593_);
lean_dec(v___y_6591_);
lean_dec(v___y_6590_);
lean_dec(v___y_6589_);
lean_dec_ref(v___y_6588_);
lean_dec_ref(v_traceArgs_6584_);
lean_dec_ref(v_weakArgs_6583_);
return v_res_6595_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(lean_object* v_as_6596_, size_t v_i_6597_, size_t v_stop_6598_, uint64_t v_b_6599_){
_start:
{
uint8_t v___x_6600_; 
v___x_6600_ = lean_usize_dec_eq(v_i_6597_, v_stop_6598_);
if (v___x_6600_ == 0)
{
lean_object* v___x_6601_; uint64_t v___x_6602_; uint64_t v___x_6603_; uint64_t v___x_6604_; uint64_t v___x_6605_; size_t v___x_6606_; size_t v___x_6607_; 
v___x_6601_ = lean_array_uget_borrowed(v_as_6596_, v_i_6597_);
v___x_6602_ = l_Lake_Hash_nil;
v___x_6603_ = lean_string_hash(v___x_6601_);
v___x_6604_ = lean_uint64_mix_hash(v___x_6602_, v___x_6603_);
v___x_6605_ = lean_uint64_mix_hash(v_b_6599_, v___x_6604_);
v___x_6606_ = ((size_t)1ULL);
v___x_6607_ = lean_usize_add(v_i_6597_, v___x_6606_);
v_i_6597_ = v___x_6607_;
v_b_6599_ = v___x_6605_;
goto _start;
}
else
{
return v_b_6599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1___boxed(lean_object* v_as_6609_, lean_object* v_i_6610_, lean_object* v_stop_6611_, lean_object* v_b_6612_){
_start:
{
size_t v_i_boxed_6613_; size_t v_stop_boxed_6614_; uint64_t v_b_boxed_6615_; uint64_t v_res_6616_; lean_object* v_r_6617_; 
v_i_boxed_6613_ = lean_unbox_usize(v_i_6610_);
lean_dec(v_i_6610_);
v_stop_boxed_6614_ = lean_unbox_usize(v_stop_6611_);
lean_dec(v_stop_6611_);
v_b_boxed_6615_ = lean_unbox_uint64(v_b_6612_);
lean_dec_ref(v_b_6612_);
v_res_6616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_as_6609_, v_i_boxed_6613_, v_stop_boxed_6614_, v_b_boxed_6615_);
lean_dec_ref(v_as_6609_);
v_r_6617_ = lean_box_uint64(v_res_6616_);
return v_r_6617_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(lean_object* v_x_6619_, lean_object* v_x_6620_){
_start:
{
if (lean_obj_tag(v_x_6620_) == 0)
{
return v_x_6619_;
}
else
{
lean_object* v_head_6621_; lean_object* v_tail_6622_; lean_object* v___x_6623_; lean_object* v___x_6624_; lean_object* v___x_6625_; 
v_head_6621_ = lean_ctor_get(v_x_6620_, 0);
v_tail_6622_ = lean_ctor_get(v_x_6620_, 1);
v___x_6623_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0));
v___x_6624_ = lean_string_append(v_x_6619_, v___x_6623_);
v___x_6625_ = lean_string_append(v___x_6624_, v_head_6621_);
v_x_6619_ = v___x_6625_;
v_x_6620_ = v_tail_6622_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___boxed(lean_object* v_x_6627_, lean_object* v_x_6628_){
_start:
{
lean_object* v_res_6629_; 
v_res_6629_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(v_x_6627_, v_x_6628_);
lean_dec(v_x_6628_);
return v_res_6629_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0(lean_object* v_x_6633_){
_start:
{
if (lean_obj_tag(v_x_6633_) == 0)
{
lean_object* v___x_6634_; 
v___x_6634_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0));
return v___x_6634_;
}
else
{
lean_object* v_tail_6635_; 
v_tail_6635_ = lean_ctor_get(v_x_6633_, 1);
if (lean_obj_tag(v_tail_6635_) == 0)
{
lean_object* v_head_6636_; lean_object* v___x_6637_; lean_object* v___x_6638_; lean_object* v___x_6639_; lean_object* v___x_6640_; 
v_head_6636_ = lean_ctor_get(v_x_6633_, 0);
v___x_6637_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1));
v___x_6638_ = lean_string_append(v___x_6637_, v_head_6636_);
v___x_6639_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2));
v___x_6640_ = lean_string_append(v___x_6638_, v___x_6639_);
return v___x_6640_;
}
else
{
lean_object* v_head_6641_; lean_object* v___x_6642_; lean_object* v___x_6643_; lean_object* v___x_6644_; uint32_t v___x_6645_; lean_object* v___x_6646_; 
v_head_6641_ = lean_ctor_get(v_x_6633_, 0);
v___x_6642_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1));
v___x_6643_ = lean_string_append(v___x_6642_, v_head_6641_);
v___x_6644_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(v___x_6643_, v_tail_6635_);
v___x_6645_ = 93;
v___x_6646_ = lean_string_push(v___x_6644_, v___x_6645_);
return v___x_6646_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___boxed(lean_object* v_x_6647_){
_start:
{
lean_object* v_res_6648_; 
v_res_6648_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v_x_6647_);
lean_dec(v_x_6647_);
return v_res_6648_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1(lean_object* v_weakArgs_6649_, lean_object* v_traceArgs_6650_, lean_object* v_oFile_6651_, lean_object* v_leanIncludeDir_x3f_6652_, lean_object* v_srcFile_6653_, lean_object* v___y_6654_, lean_object* v___y_6655_, lean_object* v___y_6656_, lean_object* v___y_6657_, lean_object* v___y_6658_, lean_object* v___y_6659_){
_start:
{
lean_object* v_log_6661_; uint8_t v_action_6662_; uint8_t v_wantsRebuild_6663_; lean_object* v_trace_6664_; lean_object* v_buildTime_6665_; lean_object* v___x_6667_; uint8_t v_isShared_6668_; uint8_t v_isSharedCheck_6722_; 
v_log_6661_ = lean_ctor_get(v___y_6659_, 0);
v_action_6662_ = lean_ctor_get_uint8(v___y_6659_, sizeof(void*)*3);
v_wantsRebuild_6663_ = lean_ctor_get_uint8(v___y_6659_, sizeof(void*)*3 + 1);
v_trace_6664_ = lean_ctor_get(v___y_6659_, 1);
v_buildTime_6665_ = lean_ctor_get(v___y_6659_, 2);
v_isSharedCheck_6722_ = !lean_is_exclusive(v___y_6659_);
if (v_isSharedCheck_6722_ == 0)
{
v___x_6667_ = v___y_6659_;
v_isShared_6668_ = v_isSharedCheck_6722_;
goto v_resetjp_6666_;
}
else
{
lean_inc(v_buildTime_6665_);
lean_inc(v_trace_6664_);
lean_inc(v_log_6661_);
lean_dec(v___y_6659_);
v___x_6667_ = lean_box(0);
v_isShared_6668_ = v_isSharedCheck_6722_;
goto v_resetjp_6666_;
}
v_resetjp_6666_:
{
lean_object* v_leanTrace_6669_; lean_object* v___f_6670_; lean_object* v___x_6671_; uint64_t v___y_6673_; uint64_t v___x_6711_; lean_object* v___x_6712_; lean_object* v___x_6713_; uint8_t v___x_6714_; 
v_leanTrace_6669_ = lean_ctor_get(v___y_6658_, 2);
lean_inc_ref(v_oFile_6651_);
lean_inc_ref(v_traceArgs_6650_);
v___f_6670_ = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__0___boxed), 12, 5);
lean_closure_set(v___f_6670_, 0, v_weakArgs_6649_);
lean_closure_set(v___f_6670_, 1, v_traceArgs_6650_);
lean_closure_set(v___f_6670_, 2, v_oFile_6651_);
lean_closure_set(v___f_6670_, 3, v_srcFile_6653_);
lean_closure_set(v___f_6670_, 4, v_leanIncludeDir_x3f_6652_);
lean_inc_ref(v_leanTrace_6669_);
v___x_6671_ = l_Lake_BuildTrace_mix(v_trace_6664_, v_leanTrace_6669_);
v___x_6711_ = l_Lake_Hash_nil;
v___x_6712_ = lean_unsigned_to_nat(0u);
v___x_6713_ = lean_array_get_size(v_traceArgs_6650_);
v___x_6714_ = lean_nat_dec_lt(v___x_6712_, v___x_6713_);
if (v___x_6714_ == 0)
{
v___y_6673_ = v___x_6711_;
goto v___jp_6672_;
}
else
{
uint8_t v___x_6715_; 
v___x_6715_ = lean_nat_dec_le(v___x_6713_, v___x_6713_);
if (v___x_6715_ == 0)
{
if (v___x_6714_ == 0)
{
v___y_6673_ = v___x_6711_;
goto v___jp_6672_;
}
else
{
size_t v___x_6716_; size_t v___x_6717_; uint64_t v___x_6718_; 
v___x_6716_ = ((size_t)0ULL);
v___x_6717_ = lean_usize_of_nat(v___x_6713_);
v___x_6718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_6650_, v___x_6716_, v___x_6717_, v___x_6711_);
v___y_6673_ = v___x_6718_;
goto v___jp_6672_;
}
}
else
{
size_t v___x_6719_; size_t v___x_6720_; uint64_t v___x_6721_; 
v___x_6719_ = ((size_t)0ULL);
v___x_6720_ = lean_usize_of_nat(v___x_6713_);
v___x_6721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_6650_, v___x_6719_, v___x_6720_, v___x_6711_);
v___y_6673_ = v___x_6721_;
goto v___jp_6672_;
}
}
v___jp_6672_:
{
lean_object* v___x_6674_; lean_object* v___x_6675_; lean_object* v___x_6676_; lean_object* v___x_6677_; lean_object* v___x_6678_; lean_object* v___x_6679_; lean_object* v___x_6680_; lean_object* v___x_6681_; lean_object* v___x_6682_; lean_object* v___x_6683_; lean_object* v___x_6684_; lean_object* v___x_6685_; lean_object* v___x_6687_; 
v___x_6674_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_6675_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_6676_ = lean_array_to_list(v_traceArgs_6650_);
v___x_6677_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_6676_);
lean_dec(v___x_6676_);
v___x_6678_ = lean_string_append(v___x_6675_, v___x_6677_);
lean_dec_ref(v___x_6677_);
v___x_6679_ = lean_string_append(v___x_6674_, v___x_6678_);
lean_dec_ref(v___x_6678_);
v___x_6680_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_6681_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_6682_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6682_, 0, v___x_6679_);
lean_ctor_set(v___x_6682_, 1, v___x_6680_);
lean_ctor_set(v___x_6682_, 2, v___x_6681_);
lean_ctor_set_uint64(v___x_6682_, sizeof(void*)*3, v___y_6673_);
v___x_6683_ = l_Lake_BuildTrace_mix(v___x_6671_, v___x_6682_);
v___x_6684_ = l_Lake_platformTrace;
v___x_6685_ = l_Lake_BuildTrace_mix(v___x_6683_, v___x_6684_);
if (v_isShared_6668_ == 0)
{
lean_ctor_set(v___x_6667_, 1, v___x_6685_);
v___x_6687_ = v___x_6667_;
goto v_reusejp_6686_;
}
else
{
lean_object* v_reuseFailAlloc_6710_; 
v_reuseFailAlloc_6710_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6710_, 0, v_log_6661_);
lean_ctor_set(v_reuseFailAlloc_6710_, 1, v___x_6685_);
lean_ctor_set(v_reuseFailAlloc_6710_, 2, v_buildTime_6665_);
lean_ctor_set_uint8(v_reuseFailAlloc_6710_, sizeof(void*)*3, v_action_6662_);
lean_ctor_set_uint8(v_reuseFailAlloc_6710_, sizeof(void*)*3 + 1, v_wantsRebuild_6663_);
v___x_6687_ = v_reuseFailAlloc_6710_;
goto v_reusejp_6686_;
}
v_reusejp_6686_:
{
uint8_t v___x_6688_; lean_object* v___x_6689_; lean_object* v___x_6690_; 
v___x_6688_ = 0;
v___x_6689_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
v___x_6690_ = l_Lake_buildArtifactUnlessUpToDate(v_oFile_6651_, v___f_6670_, v___x_6688_, v___x_6689_, v___x_6688_, v___x_6688_, v___x_6688_, v___y_6654_, v___y_6655_, v___y_6656_, v___y_6657_, v___y_6658_, v___x_6687_);
if (lean_obj_tag(v___x_6690_) == 0)
{
lean_object* v_a_6691_; lean_object* v_a_6692_; lean_object* v___x_6694_; uint8_t v_isShared_6695_; uint8_t v_isSharedCheck_6700_; 
v_a_6691_ = lean_ctor_get(v___x_6690_, 0);
v_a_6692_ = lean_ctor_get(v___x_6690_, 1);
v_isSharedCheck_6700_ = !lean_is_exclusive(v___x_6690_);
if (v_isSharedCheck_6700_ == 0)
{
v___x_6694_ = v___x_6690_;
v_isShared_6695_ = v_isSharedCheck_6700_;
goto v_resetjp_6693_;
}
else
{
lean_inc(v_a_6692_);
lean_inc(v_a_6691_);
lean_dec(v___x_6690_);
v___x_6694_ = lean_box(0);
v_isShared_6695_ = v_isSharedCheck_6700_;
goto v_resetjp_6693_;
}
v_resetjp_6693_:
{
lean_object* v_path_6696_; lean_object* v___x_6698_; 
v_path_6696_ = lean_ctor_get(v_a_6691_, 1);
lean_inc_ref(v_path_6696_);
lean_dec(v_a_6691_);
if (v_isShared_6695_ == 0)
{
lean_ctor_set(v___x_6694_, 0, v_path_6696_);
v___x_6698_ = v___x_6694_;
goto v_reusejp_6697_;
}
else
{
lean_object* v_reuseFailAlloc_6699_; 
v_reuseFailAlloc_6699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6699_, 0, v_path_6696_);
lean_ctor_set(v_reuseFailAlloc_6699_, 1, v_a_6692_);
v___x_6698_ = v_reuseFailAlloc_6699_;
goto v_reusejp_6697_;
}
v_reusejp_6697_:
{
return v___x_6698_;
}
}
}
else
{
lean_object* v_a_6701_; lean_object* v_a_6702_; lean_object* v___x_6704_; uint8_t v_isShared_6705_; uint8_t v_isSharedCheck_6709_; 
v_a_6701_ = lean_ctor_get(v___x_6690_, 0);
v_a_6702_ = lean_ctor_get(v___x_6690_, 1);
v_isSharedCheck_6709_ = !lean_is_exclusive(v___x_6690_);
if (v_isSharedCheck_6709_ == 0)
{
v___x_6704_ = v___x_6690_;
v_isShared_6705_ = v_isSharedCheck_6709_;
goto v_resetjp_6703_;
}
else
{
lean_inc(v_a_6702_);
lean_inc(v_a_6701_);
lean_dec(v___x_6690_);
v___x_6704_ = lean_box(0);
v_isShared_6705_ = v_isSharedCheck_6709_;
goto v_resetjp_6703_;
}
v_resetjp_6703_:
{
lean_object* v___x_6707_; 
if (v_isShared_6705_ == 0)
{
v___x_6707_ = v___x_6704_;
goto v_reusejp_6706_;
}
else
{
lean_object* v_reuseFailAlloc_6708_; 
v_reuseFailAlloc_6708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6708_, 0, v_a_6701_);
lean_ctor_set(v_reuseFailAlloc_6708_, 1, v_a_6702_);
v___x_6707_ = v_reuseFailAlloc_6708_;
goto v_reusejp_6706_;
}
v_reusejp_6706_:
{
return v___x_6707_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1___boxed(lean_object* v_weakArgs_6723_, lean_object* v_traceArgs_6724_, lean_object* v_oFile_6725_, lean_object* v_leanIncludeDir_x3f_6726_, lean_object* v_srcFile_6727_, lean_object* v___y_6728_, lean_object* v___y_6729_, lean_object* v___y_6730_, lean_object* v___y_6731_, lean_object* v___y_6732_, lean_object* v___y_6733_, lean_object* v___y_6734_){
_start:
{
lean_object* v_res_6735_; 
v_res_6735_ = l_Lake_buildLeanO___lam__1(v_weakArgs_6723_, v_traceArgs_6724_, v_oFile_6725_, v_leanIncludeDir_x3f_6726_, v_srcFile_6727_, v___y_6728_, v___y_6729_, v___y_6730_, v___y_6731_, v___y_6732_, v___y_6733_);
return v_res_6735_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object* v_oFile_6736_, lean_object* v_srcJob_6737_, lean_object* v_weakArgs_6738_, lean_object* v_traceArgs_6739_, lean_object* v_leanIncludeDir_x3f_6740_, lean_object* v_a_6741_, lean_object* v_a_6742_, lean_object* v_a_6743_, lean_object* v_a_6744_, lean_object* v_a_6745_, lean_object* v_a_6746_){
_start:
{
lean_object* v___f_6748_; lean_object* v___x_6749_; lean_object* v___x_6750_; uint8_t v___x_6751_; lean_object* v___x_6752_; 
v___f_6748_ = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__1___boxed), 12, 4);
lean_closure_set(v___f_6748_, 0, v_weakArgs_6738_);
lean_closure_set(v___f_6748_, 1, v_traceArgs_6739_);
lean_closure_set(v___f_6748_, 2, v_oFile_6736_);
lean_closure_set(v___f_6748_, 3, v_leanIncludeDir_x3f_6740_);
v___x_6749_ = l_Lake_instDataKindFilePath;
v___x_6750_ = lean_unsigned_to_nat(0u);
v___x_6751_ = 0;
v___x_6752_ = l_Lake_Job_mapM___redArg(v___x_6749_, v_srcJob_6737_, v___f_6748_, v___x_6750_, v___x_6751_, v_a_6741_, v_a_6742_, v_a_6743_, v_a_6744_, v_a_6745_, v_a_6746_);
return v___x_6752_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___boxed(lean_object* v_oFile_6753_, lean_object* v_srcJob_6754_, lean_object* v_weakArgs_6755_, lean_object* v_traceArgs_6756_, lean_object* v_leanIncludeDir_x3f_6757_, lean_object* v_a_6758_, lean_object* v_a_6759_, lean_object* v_a_6760_, lean_object* v_a_6761_, lean_object* v_a_6762_, lean_object* v_a_6763_, lean_object* v_a_6764_){
_start:
{
lean_object* v_res_6765_; 
v_res_6765_ = l_Lake_buildLeanO(v_oFile_6753_, v_srcJob_6754_, v_weakArgs_6755_, v_traceArgs_6756_, v_leanIncludeDir_x3f_6757_, v_a_6758_, v_a_6759_, v_a_6760_, v_a_6761_, v_a_6762_, v_a_6763_);
return v_res_6765_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0(lean_object* v_libFile_6766_, lean_object* v_oFiles_6767_, uint8_t v_thin_6768_, lean_object* v___y_6769_, lean_object* v___y_6770_, lean_object* v___y_6771_, lean_object* v___y_6772_, lean_object* v___y_6773_, lean_object* v___y_6774_){
_start:
{
lean_object* v_toContext_6776_; lean_object* v_lakeEnv_6777_; lean_object* v_lean_6778_; lean_object* v_log_6779_; uint8_t v_action_6780_; uint8_t v_wantsRebuild_6781_; lean_object* v_trace_6782_; lean_object* v_buildTime_6783_; lean_object* v___x_6785_; uint8_t v_isShared_6786_; uint8_t v_isSharedCheck_6813_; 
v_toContext_6776_ = lean_ctor_get(v___y_6773_, 1);
lean_inc(v_toContext_6776_);
lean_dec_ref(v___y_6773_);
v_lakeEnv_6777_ = lean_ctor_get(v_toContext_6776_, 1);
lean_inc_ref(v_lakeEnv_6777_);
lean_dec(v_toContext_6776_);
v_lean_6778_ = lean_ctor_get(v_lakeEnv_6777_, 1);
lean_inc_ref(v_lean_6778_);
lean_dec_ref(v_lakeEnv_6777_);
v_log_6779_ = lean_ctor_get(v___y_6774_, 0);
v_action_6780_ = lean_ctor_get_uint8(v___y_6774_, sizeof(void*)*3);
v_wantsRebuild_6781_ = lean_ctor_get_uint8(v___y_6774_, sizeof(void*)*3 + 1);
v_trace_6782_ = lean_ctor_get(v___y_6774_, 1);
v_buildTime_6783_ = lean_ctor_get(v___y_6774_, 2);
v_isSharedCheck_6813_ = !lean_is_exclusive(v___y_6774_);
if (v_isSharedCheck_6813_ == 0)
{
v___x_6785_ = v___y_6774_;
v_isShared_6786_ = v_isSharedCheck_6813_;
goto v_resetjp_6784_;
}
else
{
lean_inc(v_buildTime_6783_);
lean_inc(v_trace_6782_);
lean_inc(v_log_6779_);
lean_dec(v___y_6774_);
v___x_6785_ = lean_box(0);
v_isShared_6786_ = v_isSharedCheck_6813_;
goto v_resetjp_6784_;
}
v_resetjp_6784_:
{
lean_object* v_ar_6787_; lean_object* v___x_6788_; 
v_ar_6787_ = lean_ctor_get(v_lean_6778_, 12);
lean_inc_ref(v_ar_6787_);
lean_dec_ref(v_lean_6778_);
v___x_6788_ = l_Lake_compileStaticLib(v_libFile_6766_, v_oFiles_6767_, v_ar_6787_, v_thin_6768_, v_log_6779_);
if (lean_obj_tag(v___x_6788_) == 0)
{
lean_object* v_a_6789_; lean_object* v_a_6790_; lean_object* v___x_6792_; uint8_t v_isShared_6793_; uint8_t v_isSharedCheck_6800_; 
v_a_6789_ = lean_ctor_get(v___x_6788_, 0);
v_a_6790_ = lean_ctor_get(v___x_6788_, 1);
v_isSharedCheck_6800_ = !lean_is_exclusive(v___x_6788_);
if (v_isSharedCheck_6800_ == 0)
{
v___x_6792_ = v___x_6788_;
v_isShared_6793_ = v_isSharedCheck_6800_;
goto v_resetjp_6791_;
}
else
{
lean_inc(v_a_6790_);
lean_inc(v_a_6789_);
lean_dec(v___x_6788_);
v___x_6792_ = lean_box(0);
v_isShared_6793_ = v_isSharedCheck_6800_;
goto v_resetjp_6791_;
}
v_resetjp_6791_:
{
lean_object* v___x_6795_; 
if (v_isShared_6786_ == 0)
{
lean_ctor_set(v___x_6785_, 0, v_a_6790_);
v___x_6795_ = v___x_6785_;
goto v_reusejp_6794_;
}
else
{
lean_object* v_reuseFailAlloc_6799_; 
v_reuseFailAlloc_6799_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6799_, 0, v_a_6790_);
lean_ctor_set(v_reuseFailAlloc_6799_, 1, v_trace_6782_);
lean_ctor_set(v_reuseFailAlloc_6799_, 2, v_buildTime_6783_);
lean_ctor_set_uint8(v_reuseFailAlloc_6799_, sizeof(void*)*3, v_action_6780_);
lean_ctor_set_uint8(v_reuseFailAlloc_6799_, sizeof(void*)*3 + 1, v_wantsRebuild_6781_);
v___x_6795_ = v_reuseFailAlloc_6799_;
goto v_reusejp_6794_;
}
v_reusejp_6794_:
{
lean_object* v___x_6797_; 
if (v_isShared_6793_ == 0)
{
lean_ctor_set(v___x_6792_, 1, v___x_6795_);
v___x_6797_ = v___x_6792_;
goto v_reusejp_6796_;
}
else
{
lean_object* v_reuseFailAlloc_6798_; 
v_reuseFailAlloc_6798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6798_, 0, v_a_6789_);
lean_ctor_set(v_reuseFailAlloc_6798_, 1, v___x_6795_);
v___x_6797_ = v_reuseFailAlloc_6798_;
goto v_reusejp_6796_;
}
v_reusejp_6796_:
{
return v___x_6797_;
}
}
}
}
else
{
lean_object* v_a_6801_; lean_object* v_a_6802_; lean_object* v___x_6804_; uint8_t v_isShared_6805_; uint8_t v_isSharedCheck_6812_; 
v_a_6801_ = lean_ctor_get(v___x_6788_, 0);
v_a_6802_ = lean_ctor_get(v___x_6788_, 1);
v_isSharedCheck_6812_ = !lean_is_exclusive(v___x_6788_);
if (v_isSharedCheck_6812_ == 0)
{
v___x_6804_ = v___x_6788_;
v_isShared_6805_ = v_isSharedCheck_6812_;
goto v_resetjp_6803_;
}
else
{
lean_inc(v_a_6802_);
lean_inc(v_a_6801_);
lean_dec(v___x_6788_);
v___x_6804_ = lean_box(0);
v_isShared_6805_ = v_isSharedCheck_6812_;
goto v_resetjp_6803_;
}
v_resetjp_6803_:
{
lean_object* v___x_6807_; 
if (v_isShared_6786_ == 0)
{
lean_ctor_set(v___x_6785_, 0, v_a_6802_);
v___x_6807_ = v___x_6785_;
goto v_reusejp_6806_;
}
else
{
lean_object* v_reuseFailAlloc_6811_; 
v_reuseFailAlloc_6811_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6811_, 0, v_a_6802_);
lean_ctor_set(v_reuseFailAlloc_6811_, 1, v_trace_6782_);
lean_ctor_set(v_reuseFailAlloc_6811_, 2, v_buildTime_6783_);
lean_ctor_set_uint8(v_reuseFailAlloc_6811_, sizeof(void*)*3, v_action_6780_);
lean_ctor_set_uint8(v_reuseFailAlloc_6811_, sizeof(void*)*3 + 1, v_wantsRebuild_6781_);
v___x_6807_ = v_reuseFailAlloc_6811_;
goto v_reusejp_6806_;
}
v_reusejp_6806_:
{
lean_object* v___x_6809_; 
if (v_isShared_6805_ == 0)
{
lean_ctor_set(v___x_6804_, 1, v___x_6807_);
v___x_6809_ = v___x_6804_;
goto v_reusejp_6808_;
}
else
{
lean_object* v_reuseFailAlloc_6810_; 
v_reuseFailAlloc_6810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6810_, 0, v_a_6801_);
lean_ctor_set(v_reuseFailAlloc_6810_, 1, v___x_6807_);
v___x_6809_ = v_reuseFailAlloc_6810_;
goto v_reusejp_6808_;
}
v_reusejp_6808_:
{
return v___x_6809_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0___boxed(lean_object* v_libFile_6814_, lean_object* v_oFiles_6815_, lean_object* v_thin_6816_, lean_object* v___y_6817_, lean_object* v___y_6818_, lean_object* v___y_6819_, lean_object* v___y_6820_, lean_object* v___y_6821_, lean_object* v___y_6822_, lean_object* v___y_6823_){
_start:
{
uint8_t v_thin_boxed_6824_; lean_object* v_res_6825_; 
v_thin_boxed_6824_ = lean_unbox(v_thin_6816_);
v_res_6825_ = l_Lake_buildStaticLib___lam__0(v_libFile_6814_, v_oFiles_6815_, v_thin_boxed_6824_, v___y_6817_, v___y_6818_, v___y_6819_, v___y_6820_, v___y_6821_, v___y_6822_);
lean_dec(v___y_6820_);
lean_dec(v___y_6819_);
lean_dec(v___y_6818_);
lean_dec_ref(v___y_6817_);
return v_res_6825_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1(lean_object* v_libFile_6827_, uint8_t v_thin_6828_, lean_object* v_oFiles_6829_, lean_object* v___y_6830_, lean_object* v___y_6831_, lean_object* v___y_6832_, lean_object* v___y_6833_, lean_object* v___y_6834_, lean_object* v___y_6835_){
_start:
{
lean_object* v___x_6837_; lean_object* v___f_6838_; uint8_t v___x_6839_; lean_object* v___x_6840_; uint8_t v___x_6841_; lean_object* v___x_6842_; 
v___x_6837_ = lean_box(v_thin_6828_);
lean_inc_ref(v_libFile_6827_);
v___f_6838_ = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6838_, 0, v_libFile_6827_);
lean_closure_set(v___f_6838_, 1, v_oFiles_6829_);
lean_closure_set(v___f_6838_, 2, v___x_6837_);
v___x_6839_ = 0;
v___x_6840_ = ((lean_object*)(l_Lake_buildStaticLib___lam__1___closed__0));
v___x_6841_ = 1;
v___x_6842_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_6827_, v___f_6838_, v___x_6839_, v___x_6840_, v___x_6841_, v___x_6839_, v___x_6839_, v___y_6830_, v___y_6831_, v___y_6832_, v___y_6833_, v___y_6834_, v___y_6835_);
if (lean_obj_tag(v___x_6842_) == 0)
{
lean_object* v_a_6843_; lean_object* v_a_6844_; lean_object* v___x_6846_; uint8_t v_isShared_6847_; uint8_t v_isSharedCheck_6852_; 
v_a_6843_ = lean_ctor_get(v___x_6842_, 0);
v_a_6844_ = lean_ctor_get(v___x_6842_, 1);
v_isSharedCheck_6852_ = !lean_is_exclusive(v___x_6842_);
if (v_isSharedCheck_6852_ == 0)
{
v___x_6846_ = v___x_6842_;
v_isShared_6847_ = v_isSharedCheck_6852_;
goto v_resetjp_6845_;
}
else
{
lean_inc(v_a_6844_);
lean_inc(v_a_6843_);
lean_dec(v___x_6842_);
v___x_6846_ = lean_box(0);
v_isShared_6847_ = v_isSharedCheck_6852_;
goto v_resetjp_6845_;
}
v_resetjp_6845_:
{
lean_object* v_path_6848_; lean_object* v___x_6850_; 
v_path_6848_ = lean_ctor_get(v_a_6843_, 1);
lean_inc_ref(v_path_6848_);
lean_dec(v_a_6843_);
if (v_isShared_6847_ == 0)
{
lean_ctor_set(v___x_6846_, 0, v_path_6848_);
v___x_6850_ = v___x_6846_;
goto v_reusejp_6849_;
}
else
{
lean_object* v_reuseFailAlloc_6851_; 
v_reuseFailAlloc_6851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6851_, 0, v_path_6848_);
lean_ctor_set(v_reuseFailAlloc_6851_, 1, v_a_6844_);
v___x_6850_ = v_reuseFailAlloc_6851_;
goto v_reusejp_6849_;
}
v_reusejp_6849_:
{
return v___x_6850_;
}
}
}
else
{
lean_object* v_a_6853_; lean_object* v_a_6854_; lean_object* v___x_6856_; uint8_t v_isShared_6857_; uint8_t v_isSharedCheck_6861_; 
v_a_6853_ = lean_ctor_get(v___x_6842_, 0);
v_a_6854_ = lean_ctor_get(v___x_6842_, 1);
v_isSharedCheck_6861_ = !lean_is_exclusive(v___x_6842_);
if (v_isSharedCheck_6861_ == 0)
{
v___x_6856_ = v___x_6842_;
v_isShared_6857_ = v_isSharedCheck_6861_;
goto v_resetjp_6855_;
}
else
{
lean_inc(v_a_6854_);
lean_inc(v_a_6853_);
lean_dec(v___x_6842_);
v___x_6856_ = lean_box(0);
v_isShared_6857_ = v_isSharedCheck_6861_;
goto v_resetjp_6855_;
}
v_resetjp_6855_:
{
lean_object* v___x_6859_; 
if (v_isShared_6857_ == 0)
{
v___x_6859_ = v___x_6856_;
goto v_reusejp_6858_;
}
else
{
lean_object* v_reuseFailAlloc_6860_; 
v_reuseFailAlloc_6860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6860_, 0, v_a_6853_);
lean_ctor_set(v_reuseFailAlloc_6860_, 1, v_a_6854_);
v___x_6859_ = v_reuseFailAlloc_6860_;
goto v_reusejp_6858_;
}
v_reusejp_6858_:
{
return v___x_6859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1___boxed(lean_object* v_libFile_6862_, lean_object* v_thin_6863_, lean_object* v_oFiles_6864_, lean_object* v___y_6865_, lean_object* v___y_6866_, lean_object* v___y_6867_, lean_object* v___y_6868_, lean_object* v___y_6869_, lean_object* v___y_6870_, lean_object* v___y_6871_){
_start:
{
uint8_t v_thin_boxed_6872_; lean_object* v_res_6873_; 
v_thin_boxed_6872_ = lean_unbox(v_thin_6863_);
v_res_6873_ = l_Lake_buildStaticLib___lam__1(v_libFile_6862_, v_thin_boxed_6872_, v_oFiles_6864_, v___y_6865_, v___y_6866_, v___y_6867_, v___y_6868_, v___y_6869_, v___y_6870_);
return v_res_6873_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object* v_libFile_6875_, lean_object* v_oFileJobs_6876_, uint8_t v_thin_6877_, lean_object* v_a_6878_, lean_object* v_a_6879_, lean_object* v_a_6880_, lean_object* v_a_6881_, lean_object* v_a_6882_, lean_object* v_a_6883_){
_start:
{
lean_object* v___x_6885_; lean_object* v___f_6886_; lean_object* v___x_6887_; lean_object* v___x_6888_; lean_object* v___x_6889_; lean_object* v___x_6890_; uint8_t v___x_6891_; lean_object* v___x_6892_; 
v___x_6885_ = lean_box(v_thin_6877_);
v___f_6886_ = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__1___boxed), 10, 2);
lean_closure_set(v___f_6886_, 0, v_libFile_6875_);
lean_closure_set(v___f_6886_, 1, v___x_6885_);
v___x_6887_ = l_Lake_instDataKindFilePath;
v___x_6888_ = ((lean_object*)(l_Lake_buildStaticLib___closed__0));
v___x_6889_ = l_Lake_Job_collectArray___redArg(v_oFileJobs_6876_, v___x_6888_);
v___x_6890_ = lean_unsigned_to_nat(0u);
v___x_6891_ = 0;
v___x_6892_ = l_Lake_Job_mapM___redArg(v___x_6887_, v___x_6889_, v___f_6886_, v___x_6890_, v___x_6891_, v_a_6878_, v_a_6879_, v_a_6880_, v_a_6881_, v_a_6882_, v_a_6883_);
return v___x_6892_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object* v_libFile_6893_, lean_object* v_oFileJobs_6894_, lean_object* v_thin_6895_, lean_object* v_a_6896_, lean_object* v_a_6897_, lean_object* v_a_6898_, lean_object* v_a_6899_, lean_object* v_a_6900_, lean_object* v_a_6901_, lean_object* v_a_6902_){
_start:
{
uint8_t v_thin_boxed_6903_; lean_object* v_res_6904_; 
v_thin_boxed_6903_ = lean_unbox(v_thin_6895_);
v_res_6904_ = l_Lake_buildStaticLib(v_libFile_6893_, v_oFileJobs_6894_, v_thin_boxed_6903_, v_a_6896_, v_a_6897_, v_a_6898_, v_a_6899_, v_a_6900_, v_a_6901_);
lean_dec_ref(v_oFileJobs_6894_);
return v_res_6904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(lean_object* v_as_6905_, size_t v_sz_6906_, size_t v_i_6907_, lean_object* v_b_6908_){
_start:
{
uint8_t v___x_6909_; 
v___x_6909_ = lean_usize_dec_lt(v_i_6907_, v_sz_6906_);
if (v___x_6909_ == 0)
{
return v_b_6908_;
}
else
{
lean_object* v_a_6910_; lean_object* v___x_6911_; size_t v___x_6912_; size_t v___x_6913_; 
v_a_6910_ = lean_array_uget_borrowed(v_as_6905_, v_i_6907_);
lean_inc(v_a_6910_);
v___x_6911_ = lean_array_push(v_b_6908_, v_a_6910_);
v___x_6912_ = ((size_t)1ULL);
v___x_6913_ = lean_usize_add(v_i_6907_, v___x_6912_);
v_i_6907_ = v___x_6913_;
v_b_6908_ = v___x_6911_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0___boxed(lean_object* v_as_6915_, lean_object* v_sz_6916_, lean_object* v_i_6917_, lean_object* v_b_6918_){
_start:
{
size_t v_sz_boxed_6919_; size_t v_i_boxed_6920_; lean_object* v_res_6921_; 
v_sz_boxed_6919_ = lean_unbox_usize(v_sz_6916_);
lean_dec(v_sz_6916_);
v_i_boxed_6920_ = lean_unbox_usize(v_i_6917_);
lean_dec(v_i_6917_);
v_res_6921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(v_as_6915_, v_sz_boxed_6919_, v_i_boxed_6920_, v_b_6918_);
lean_dec_ref(v_as_6915_);
return v_res_6921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(lean_object* v_as_6924_, size_t v_sz_6925_, size_t v_i_6926_, lean_object* v_b_6927_){
_start:
{
uint8_t v___x_6928_; 
v___x_6928_ = lean_usize_dec_lt(v_i_6926_, v_sz_6925_);
if (v___x_6928_ == 0)
{
return v_b_6927_;
}
else
{
lean_object* v_a_6929_; lean_object* v_args_6931_; lean_object* v___x_6939_; 
v_a_6929_ = lean_array_uget_borrowed(v_as_6924_, v_i_6926_);
lean_inc(v_a_6929_);
v___x_6939_ = l_Lake_Dynlib_dir_x3f(v_a_6929_);
if (lean_obj_tag(v___x_6939_) == 1)
{
lean_object* v_val_6940_; lean_object* v___x_6941_; lean_object* v___x_6942_; lean_object* v___x_6943_; 
v_val_6940_ = lean_ctor_get(v___x_6939_, 0);
lean_inc(v_val_6940_);
lean_dec_ref(v___x_6939_);
v___x_6941_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
v___x_6942_ = lean_string_append(v___x_6941_, v_val_6940_);
lean_dec(v_val_6940_);
v___x_6943_ = lean_array_push(v_b_6927_, v___x_6942_);
v_args_6931_ = v___x_6943_;
goto v___jp_6930_;
}
else
{
lean_dec(v___x_6939_);
v_args_6931_ = v_b_6927_;
goto v___jp_6930_;
}
v___jp_6930_:
{
lean_object* v_name_6932_; lean_object* v___x_6933_; lean_object* v___x_6934_; lean_object* v___x_6935_; size_t v___x_6936_; size_t v___x_6937_; 
v_name_6932_ = lean_ctor_get(v_a_6929_, 1);
v___x_6933_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0));
v___x_6934_ = lean_string_append(v___x_6933_, v_name_6932_);
v___x_6935_ = lean_array_push(v_args_6931_, v___x_6934_);
v___x_6936_ = ((size_t)1ULL);
v___x_6937_ = lean_usize_add(v_i_6926_, v___x_6936_);
v_i_6926_ = v___x_6937_;
v_b_6927_ = v___x_6935_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___boxed(lean_object* v_as_6944_, lean_object* v_sz_6945_, lean_object* v_i_6946_, lean_object* v_b_6947_){
_start:
{
size_t v_sz_boxed_6948_; size_t v_i_boxed_6949_; lean_object* v_res_6950_; 
v_sz_boxed_6948_ = lean_unbox_usize(v_sz_6945_);
lean_dec(v_sz_6945_);
v_i_boxed_6949_ = lean_unbox_usize(v_i_6946_);
lean_dec(v_i_6946_);
v_res_6950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(v_as_6944_, v_sz_boxed_6948_, v_i_boxed_6949_, v_b_6947_);
lean_dec_ref(v_as_6944_);
return v_res_6950_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(lean_object* v_objs_6951_, lean_object* v_libs_6952_){
_start:
{
lean_object* v_args_6953_; size_t v_sz_6954_; size_t v___x_6955_; lean_object* v___x_6956_; size_t v_sz_6957_; lean_object* v___x_6958_; 
v_args_6953_ = ((lean_object*)(l_Lake_inputDir___lam__1___closed__0));
v_sz_6954_ = lean_array_size(v_objs_6951_);
v___x_6955_ = ((size_t)0ULL);
v___x_6956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(v_objs_6951_, v_sz_6954_, v___x_6955_, v_args_6953_);
v_sz_6957_ = lean_array_size(v_libs_6952_);
v___x_6958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(v_libs_6952_, v_sz_6957_, v___x_6955_, v___x_6956_);
return v___x_6958_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs___boxed(lean_object* v_objs_6959_, lean_object* v_libs_6960_){
_start:
{
lean_object* v_res_6961_; 
v_res_6961_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_6959_, v_libs_6960_);
lean_dec_ref(v_libs_6960_);
lean_dec_ref(v_objs_6959_);
return v_res_6961_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(lean_object* v_k_6962_, lean_object* v_t_6963_){
_start:
{
if (lean_obj_tag(v_t_6963_) == 0)
{
lean_object* v_k_6964_; lean_object* v_l_6965_; lean_object* v_r_6966_; uint8_t v___x_6967_; 
v_k_6964_ = lean_ctor_get(v_t_6963_, 1);
v_l_6965_ = lean_ctor_get(v_t_6963_, 3);
v_r_6966_ = lean_ctor_get(v_t_6963_, 4);
v___x_6967_ = lean_string_dec_lt(v_k_6962_, v_k_6964_);
if (v___x_6967_ == 0)
{
uint8_t v___x_6968_; 
v___x_6968_ = lean_string_dec_eq(v_k_6962_, v_k_6964_);
if (v___x_6968_ == 0)
{
v_t_6963_ = v_r_6966_;
goto _start;
}
else
{
return v___x_6968_;
}
}
else
{
v_t_6963_ = v_l_6965_;
goto _start;
}
}
else
{
uint8_t v___x_6971_; 
v___x_6971_ = 0;
return v___x_6971_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg___boxed(lean_object* v_k_6972_, lean_object* v_t_6973_){
_start:
{
uint8_t v_res_6974_; lean_object* v_r_6975_; 
v_res_6974_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_k_6972_, v_t_6973_);
lean_dec(v_t_6973_);
lean_dec_ref(v_k_6972_);
v_r_6975_ = lean_box(v_res_6974_);
return v_r_6975_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(lean_object* v_a_6976_, lean_object* v_x_6977_){
_start:
{
if (lean_obj_tag(v_x_6977_) == 0)
{
uint8_t v___x_6978_; 
v___x_6978_ = 0;
return v___x_6978_;
}
else
{
lean_object* v_head_6979_; lean_object* v_tail_6980_; uint8_t v___x_6981_; 
v_head_6979_ = lean_ctor_get(v_x_6977_, 0);
v_tail_6980_ = lean_ctor_get(v_x_6977_, 1);
v___x_6981_ = lean_string_dec_eq(v_a_6976_, v_head_6979_);
if (v___x_6981_ == 0)
{
v_x_6977_ = v_tail_6980_;
goto _start;
}
else
{
return v___x_6981_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1___boxed(lean_object* v_a_6983_, lean_object* v_x_6984_){
_start:
{
uint8_t v_res_6985_; lean_object* v_r_6986_; 
v_res_6985_ = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(v_a_6983_, v_x_6984_);
lean_dec(v_x_6984_);
lean_dec_ref(v_a_6983_);
v_r_6986_ = lean_box(v_res_6985_);
return v_r_6986_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(lean_object* v_k_6987_, lean_object* v_v_6988_, lean_object* v_t_6989_){
_start:
{
if (lean_obj_tag(v_t_6989_) == 0)
{
lean_object* v_size_6990_; lean_object* v_k_6991_; lean_object* v_v_6992_; lean_object* v_l_6993_; lean_object* v_r_6994_; lean_object* v___x_6996_; uint8_t v_isShared_6997_; uint8_t v_isSharedCheck_7275_; 
v_size_6990_ = lean_ctor_get(v_t_6989_, 0);
v_k_6991_ = lean_ctor_get(v_t_6989_, 1);
v_v_6992_ = lean_ctor_get(v_t_6989_, 2);
v_l_6993_ = lean_ctor_get(v_t_6989_, 3);
v_r_6994_ = lean_ctor_get(v_t_6989_, 4);
v_isSharedCheck_7275_ = !lean_is_exclusive(v_t_6989_);
if (v_isSharedCheck_7275_ == 0)
{
v___x_6996_ = v_t_6989_;
v_isShared_6997_ = v_isSharedCheck_7275_;
goto v_resetjp_6995_;
}
else
{
lean_inc(v_r_6994_);
lean_inc(v_l_6993_);
lean_inc(v_v_6992_);
lean_inc(v_k_6991_);
lean_inc(v_size_6990_);
lean_dec(v_t_6989_);
v___x_6996_ = lean_box(0);
v_isShared_6997_ = v_isSharedCheck_7275_;
goto v_resetjp_6995_;
}
v_resetjp_6995_:
{
uint8_t v___x_6998_; 
v___x_6998_ = lean_string_dec_lt(v_k_6987_, v_k_6991_);
if (v___x_6998_ == 0)
{
uint8_t v___x_6999_; 
v___x_6999_ = lean_string_dec_eq(v_k_6987_, v_k_6991_);
if (v___x_6999_ == 0)
{
lean_object* v_impl_7000_; lean_object* v___x_7001_; 
lean_dec(v_size_6990_);
v_impl_7000_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_6987_, v_v_6988_, v_r_6994_);
v___x_7001_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_6993_) == 0)
{
lean_object* v_size_7002_; lean_object* v_size_7003_; lean_object* v_k_7004_; lean_object* v_v_7005_; lean_object* v_l_7006_; lean_object* v_r_7007_; lean_object* v___x_7008_; lean_object* v___x_7009_; uint8_t v___x_7010_; 
v_size_7002_ = lean_ctor_get(v_l_6993_, 0);
v_size_7003_ = lean_ctor_get(v_impl_7000_, 0);
lean_inc(v_size_7003_);
v_k_7004_ = lean_ctor_get(v_impl_7000_, 1);
lean_inc(v_k_7004_);
v_v_7005_ = lean_ctor_get(v_impl_7000_, 2);
lean_inc(v_v_7005_);
v_l_7006_ = lean_ctor_get(v_impl_7000_, 3);
lean_inc(v_l_7006_);
v_r_7007_ = lean_ctor_get(v_impl_7000_, 4);
lean_inc(v_r_7007_);
v___x_7008_ = lean_unsigned_to_nat(3u);
v___x_7009_ = lean_nat_mul(v___x_7008_, v_size_7002_);
v___x_7010_ = lean_nat_dec_lt(v___x_7009_, v_size_7003_);
lean_dec(v___x_7009_);
if (v___x_7010_ == 0)
{
lean_object* v___x_7011_; lean_object* v___x_7012_; lean_object* v___x_7014_; 
lean_dec(v_r_7007_);
lean_dec(v_l_7006_);
lean_dec(v_v_7005_);
lean_dec(v_k_7004_);
v___x_7011_ = lean_nat_add(v___x_7001_, v_size_7002_);
v___x_7012_ = lean_nat_add(v___x_7011_, v_size_7003_);
lean_dec(v_size_7003_);
lean_dec(v___x_7011_);
if (v_isShared_6997_ == 0)
{
lean_ctor_set(v___x_6996_, 4, v_impl_7000_);
lean_ctor_set(v___x_6996_, 0, v___x_7012_);
v___x_7014_ = v___x_6996_;
goto v_reusejp_7013_;
}
else
{
lean_object* v_reuseFailAlloc_7015_; 
v_reuseFailAlloc_7015_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7015_, 0, v___x_7012_);
lean_ctor_set(v_reuseFailAlloc_7015_, 1, v_k_6991_);
lean_ctor_set(v_reuseFailAlloc_7015_, 2, v_v_6992_);
lean_ctor_set(v_reuseFailAlloc_7015_, 3, v_l_6993_);
lean_ctor_set(v_reuseFailAlloc_7015_, 4, v_impl_7000_);
v___x_7014_ = v_reuseFailAlloc_7015_;
goto v_reusejp_7013_;
}
v_reusejp_7013_:
{
return v___x_7014_;
}
}
else
{
lean_object* v___x_7017_; uint8_t v_isShared_7018_; uint8_t v_isSharedCheck_7079_; 
v_isSharedCheck_7079_ = !lean_is_exclusive(v_impl_7000_);
if (v_isSharedCheck_7079_ == 0)
{
lean_object* v_unused_7080_; lean_object* v_unused_7081_; lean_object* v_unused_7082_; lean_object* v_unused_7083_; lean_object* v_unused_7084_; 
v_unused_7080_ = lean_ctor_get(v_impl_7000_, 4);
lean_dec(v_unused_7080_);
v_unused_7081_ = lean_ctor_get(v_impl_7000_, 3);
lean_dec(v_unused_7081_);
v_unused_7082_ = lean_ctor_get(v_impl_7000_, 2);
lean_dec(v_unused_7082_);
v_unused_7083_ = lean_ctor_get(v_impl_7000_, 1);
lean_dec(v_unused_7083_);
v_unused_7084_ = lean_ctor_get(v_impl_7000_, 0);
lean_dec(v_unused_7084_);
v___x_7017_ = v_impl_7000_;
v_isShared_7018_ = v_isSharedCheck_7079_;
goto v_resetjp_7016_;
}
else
{
lean_dec(v_impl_7000_);
v___x_7017_ = lean_box(0);
v_isShared_7018_ = v_isSharedCheck_7079_;
goto v_resetjp_7016_;
}
v_resetjp_7016_:
{
lean_object* v_size_7019_; lean_object* v_k_7020_; lean_object* v_v_7021_; lean_object* v_l_7022_; lean_object* v_r_7023_; lean_object* v_size_7024_; lean_object* v___x_7025_; lean_object* v___x_7026_; uint8_t v___x_7027_; 
v_size_7019_ = lean_ctor_get(v_l_7006_, 0);
v_k_7020_ = lean_ctor_get(v_l_7006_, 1);
v_v_7021_ = lean_ctor_get(v_l_7006_, 2);
v_l_7022_ = lean_ctor_get(v_l_7006_, 3);
v_r_7023_ = lean_ctor_get(v_l_7006_, 4);
v_size_7024_ = lean_ctor_get(v_r_7007_, 0);
v___x_7025_ = lean_unsigned_to_nat(2u);
v___x_7026_ = lean_nat_mul(v___x_7025_, v_size_7024_);
v___x_7027_ = lean_nat_dec_lt(v_size_7019_, v___x_7026_);
lean_dec(v___x_7026_);
if (v___x_7027_ == 0)
{
lean_object* v___x_7029_; uint8_t v_isShared_7030_; uint8_t v_isSharedCheck_7055_; 
lean_inc(v_r_7023_);
lean_inc(v_l_7022_);
lean_inc(v_v_7021_);
lean_inc(v_k_7020_);
v_isSharedCheck_7055_ = !lean_is_exclusive(v_l_7006_);
if (v_isSharedCheck_7055_ == 0)
{
lean_object* v_unused_7056_; lean_object* v_unused_7057_; lean_object* v_unused_7058_; lean_object* v_unused_7059_; lean_object* v_unused_7060_; 
v_unused_7056_ = lean_ctor_get(v_l_7006_, 4);
lean_dec(v_unused_7056_);
v_unused_7057_ = lean_ctor_get(v_l_7006_, 3);
lean_dec(v_unused_7057_);
v_unused_7058_ = lean_ctor_get(v_l_7006_, 2);
lean_dec(v_unused_7058_);
v_unused_7059_ = lean_ctor_get(v_l_7006_, 1);
lean_dec(v_unused_7059_);
v_unused_7060_ = lean_ctor_get(v_l_7006_, 0);
lean_dec(v_unused_7060_);
v___x_7029_ = v_l_7006_;
v_isShared_7030_ = v_isSharedCheck_7055_;
goto v_resetjp_7028_;
}
else
{
lean_dec(v_l_7006_);
v___x_7029_ = lean_box(0);
v_isShared_7030_ = v_isSharedCheck_7055_;
goto v_resetjp_7028_;
}
v_resetjp_7028_:
{
lean_object* v___x_7031_; lean_object* v___x_7032_; lean_object* v___y_7034_; lean_object* v___y_7035_; lean_object* v___y_7036_; lean_object* v___y_7045_; 
v___x_7031_ = lean_nat_add(v___x_7001_, v_size_7002_);
v___x_7032_ = lean_nat_add(v___x_7031_, v_size_7003_);
lean_dec(v_size_7003_);
if (lean_obj_tag(v_l_7022_) == 0)
{
lean_object* v_size_7053_; 
v_size_7053_ = lean_ctor_get(v_l_7022_, 0);
lean_inc(v_size_7053_);
v___y_7045_ = v_size_7053_;
goto v___jp_7044_;
}
else
{
lean_object* v___x_7054_; 
v___x_7054_ = lean_unsigned_to_nat(0u);
v___y_7045_ = v___x_7054_;
goto v___jp_7044_;
}
v___jp_7033_:
{
lean_object* v___x_7037_; lean_object* v___x_7039_; 
v___x_7037_ = lean_nat_add(v___y_7034_, v___y_7036_);
lean_dec(v___y_7036_);
lean_dec(v___y_7034_);
if (v_isShared_7030_ == 0)
{
lean_ctor_set(v___x_7029_, 4, v_r_7007_);
lean_ctor_set(v___x_7029_, 3, v_r_7023_);
lean_ctor_set(v___x_7029_, 2, v_v_7005_);
lean_ctor_set(v___x_7029_, 1, v_k_7004_);
lean_ctor_set(v___x_7029_, 0, v___x_7037_);
v___x_7039_ = v___x_7029_;
goto v_reusejp_7038_;
}
else
{
lean_object* v_reuseFailAlloc_7043_; 
v_reuseFailAlloc_7043_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7043_, 0, v___x_7037_);
lean_ctor_set(v_reuseFailAlloc_7043_, 1, v_k_7004_);
lean_ctor_set(v_reuseFailAlloc_7043_, 2, v_v_7005_);
lean_ctor_set(v_reuseFailAlloc_7043_, 3, v_r_7023_);
lean_ctor_set(v_reuseFailAlloc_7043_, 4, v_r_7007_);
v___x_7039_ = v_reuseFailAlloc_7043_;
goto v_reusejp_7038_;
}
v_reusejp_7038_:
{
lean_object* v___x_7041_; 
if (v_isShared_7018_ == 0)
{
lean_ctor_set(v___x_7017_, 4, v___x_7039_);
lean_ctor_set(v___x_7017_, 3, v___y_7035_);
lean_ctor_set(v___x_7017_, 2, v_v_7021_);
lean_ctor_set(v___x_7017_, 1, v_k_7020_);
lean_ctor_set(v___x_7017_, 0, v___x_7032_);
v___x_7041_ = v___x_7017_;
goto v_reusejp_7040_;
}
else
{
lean_object* v_reuseFailAlloc_7042_; 
v_reuseFailAlloc_7042_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7042_, 0, v___x_7032_);
lean_ctor_set(v_reuseFailAlloc_7042_, 1, v_k_7020_);
lean_ctor_set(v_reuseFailAlloc_7042_, 2, v_v_7021_);
lean_ctor_set(v_reuseFailAlloc_7042_, 3, v___y_7035_);
lean_ctor_set(v_reuseFailAlloc_7042_, 4, v___x_7039_);
v___x_7041_ = v_reuseFailAlloc_7042_;
goto v_reusejp_7040_;
}
v_reusejp_7040_:
{
return v___x_7041_;
}
}
}
v___jp_7044_:
{
lean_object* v___x_7046_; lean_object* v___x_7048_; 
v___x_7046_ = lean_nat_add(v___x_7031_, v___y_7045_);
lean_dec(v___y_7045_);
lean_dec(v___x_7031_);
if (v_isShared_6997_ == 0)
{
lean_ctor_set(v___x_6996_, 4, v_l_7022_);
lean_ctor_set(v___x_6996_, 0, v___x_7046_);
v___x_7048_ = v___x_6996_;
goto v_reusejp_7047_;
}
else
{
lean_object* v_reuseFailAlloc_7052_; 
v_reuseFailAlloc_7052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7052_, 0, v___x_7046_);
lean_ctor_set(v_reuseFailAlloc_7052_, 1, v_k_6991_);
lean_ctor_set(v_reuseFailAlloc_7052_, 2, v_v_6992_);
lean_ctor_set(v_reuseFailAlloc_7052_, 3, v_l_6993_);
lean_ctor_set(v_reuseFailAlloc_7052_, 4, v_l_7022_);
v___x_7048_ = v_reuseFailAlloc_7052_;
goto v_reusejp_7047_;
}
v_reusejp_7047_:
{
lean_object* v___x_7049_; 
v___x_7049_ = lean_nat_add(v___x_7001_, v_size_7024_);
if (lean_obj_tag(v_r_7023_) == 0)
{
lean_object* v_size_7050_; 
v_size_7050_ = lean_ctor_get(v_r_7023_, 0);
lean_inc(v_size_7050_);
v___y_7034_ = v___x_7049_;
v___y_7035_ = v___x_7048_;
v___y_7036_ = v_size_7050_;
goto v___jp_7033_;
}
else
{
lean_object* v___x_7051_; 
v___x_7051_ = lean_unsigned_to_nat(0u);
v___y_7034_ = v___x_7049_;
v___y_7035_ = v___x_7048_;
v___y_7036_ = v___x_7051_;
goto v___jp_7033_;
}
}
}
}
}
else
{
lean_object* v___x_7061_; lean_object* v___x_7062_; lean_object* v___x_7063_; lean_object* v___x_7065_; 
lean_del_object(v___x_6996_);
v___x_7061_ = lean_nat_add(v___x_7001_, v_size_7002_);
v___x_7062_ = lean_nat_add(v___x_7061_, v_size_7003_);
lean_dec(v_size_7003_);
v___x_7063_ = lean_nat_add(v___x_7061_, v_size_7019_);
lean_dec(v___x_7061_);
lean_inc_ref(v_l_6993_);
if (v_isShared_7018_ == 0)
{
lean_ctor_set(v___x_7017_, 4, v_l_7006_);
lean_ctor_set(v___x_7017_, 3, v_l_6993_);
lean_ctor_set(v___x_7017_, 2, v_v_6992_);
lean_ctor_set(v___x_7017_, 1, v_k_6991_);
lean_ctor_set(v___x_7017_, 0, v___x_7063_);
v___x_7065_ = v___x_7017_;
goto v_reusejp_7064_;
}
else
{
lean_object* v_reuseFailAlloc_7078_; 
v_reuseFailAlloc_7078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7078_, 0, v___x_7063_);
lean_ctor_set(v_reuseFailAlloc_7078_, 1, v_k_6991_);
lean_ctor_set(v_reuseFailAlloc_7078_, 2, v_v_6992_);
lean_ctor_set(v_reuseFailAlloc_7078_, 3, v_l_6993_);
lean_ctor_set(v_reuseFailAlloc_7078_, 4, v_l_7006_);
v___x_7065_ = v_reuseFailAlloc_7078_;
goto v_reusejp_7064_;
}
v_reusejp_7064_:
{
lean_object* v___x_7067_; uint8_t v_isShared_7068_; uint8_t v_isSharedCheck_7072_; 
v_isSharedCheck_7072_ = !lean_is_exclusive(v_l_6993_);
if (v_isSharedCheck_7072_ == 0)
{
lean_object* v_unused_7073_; lean_object* v_unused_7074_; lean_object* v_unused_7075_; lean_object* v_unused_7076_; lean_object* v_unused_7077_; 
v_unused_7073_ = lean_ctor_get(v_l_6993_, 4);
lean_dec(v_unused_7073_);
v_unused_7074_ = lean_ctor_get(v_l_6993_, 3);
lean_dec(v_unused_7074_);
v_unused_7075_ = lean_ctor_get(v_l_6993_, 2);
lean_dec(v_unused_7075_);
v_unused_7076_ = lean_ctor_get(v_l_6993_, 1);
lean_dec(v_unused_7076_);
v_unused_7077_ = lean_ctor_get(v_l_6993_, 0);
lean_dec(v_unused_7077_);
v___x_7067_ = v_l_6993_;
v_isShared_7068_ = v_isSharedCheck_7072_;
goto v_resetjp_7066_;
}
else
{
lean_dec(v_l_6993_);
v___x_7067_ = lean_box(0);
v_isShared_7068_ = v_isSharedCheck_7072_;
goto v_resetjp_7066_;
}
v_resetjp_7066_:
{
lean_object* v___x_7070_; 
if (v_isShared_7068_ == 0)
{
lean_ctor_set(v___x_7067_, 4, v_r_7007_);
lean_ctor_set(v___x_7067_, 3, v___x_7065_);
lean_ctor_set(v___x_7067_, 2, v_v_7005_);
lean_ctor_set(v___x_7067_, 1, v_k_7004_);
lean_ctor_set(v___x_7067_, 0, v___x_7062_);
v___x_7070_ = v___x_7067_;
goto v_reusejp_7069_;
}
else
{
lean_object* v_reuseFailAlloc_7071_; 
v_reuseFailAlloc_7071_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7071_, 0, v___x_7062_);
lean_ctor_set(v_reuseFailAlloc_7071_, 1, v_k_7004_);
lean_ctor_set(v_reuseFailAlloc_7071_, 2, v_v_7005_);
lean_ctor_set(v_reuseFailAlloc_7071_, 3, v___x_7065_);
lean_ctor_set(v_reuseFailAlloc_7071_, 4, v_r_7007_);
v___x_7070_ = v_reuseFailAlloc_7071_;
goto v_reusejp_7069_;
}
v_reusejp_7069_:
{
return v___x_7070_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_7085_; 
v_l_7085_ = lean_ctor_get(v_impl_7000_, 3);
lean_inc(v_l_7085_);
if (lean_obj_tag(v_l_7085_) == 0)
{
lean_object* v_r_7086_; lean_object* v_k_7087_; lean_object* v_v_7088_; lean_object* v___x_7090_; uint8_t v_isShared_7091_; uint8_t v_isSharedCheck_7111_; 
v_r_7086_ = lean_ctor_get(v_impl_7000_, 4);
v_k_7087_ = lean_ctor_get(v_impl_7000_, 1);
v_v_7088_ = lean_ctor_get(v_impl_7000_, 2);
v_isSharedCheck_7111_ = !lean_is_exclusive(v_impl_7000_);
if (v_isSharedCheck_7111_ == 0)
{
lean_object* v_unused_7112_; lean_object* v_unused_7113_; 
v_unused_7112_ = lean_ctor_get(v_impl_7000_, 3);
lean_dec(v_unused_7112_);
v_unused_7113_ = lean_ctor_get(v_impl_7000_, 0);
lean_dec(v_unused_7113_);
v___x_7090_ = v_impl_7000_;
v_isShared_7091_ = v_isSharedCheck_7111_;
goto v_resetjp_7089_;
}
else
{
lean_inc(v_r_7086_);
lean_inc(v_v_7088_);
lean_inc(v_k_7087_);
lean_dec(v_impl_7000_);
v___x_7090_ = lean_box(0);
v_isShared_7091_ = v_isSharedCheck_7111_;
goto v_resetjp_7089_;
}
v_resetjp_7089_:
{
lean_object* v_k_7092_; lean_object* v_v_7093_; lean_object* v___x_7095_; uint8_t v_isShared_7096_; uint8_t v_isSharedCheck_7107_; 
v_k_7092_ = lean_ctor_get(v_l_7085_, 1);
v_v_7093_ = lean_ctor_get(v_l_7085_, 2);
v_isSharedCheck_7107_ = !lean_is_exclusive(v_l_7085_);
if (v_isSharedCheck_7107_ == 0)
{
lean_object* v_unused_7108_; lean_object* v_unused_7109_; lean_object* v_unused_7110_; 
v_unused_7108_ = lean_ctor_get(v_l_7085_, 4);
lean_dec(v_unused_7108_);
v_unused_7109_ = lean_ctor_get(v_l_7085_, 3);
lean_dec(v_unused_7109_);
v_unused_7110_ = lean_ctor_get(v_l_7085_, 0);
lean_dec(v_unused_7110_);
v___x_7095_ = v_l_7085_;
v_isShared_7096_ = v_isSharedCheck_7107_;
goto v_resetjp_7094_;
}
else
{
lean_inc(v_v_7093_);
lean_inc(v_k_7092_);
lean_dec(v_l_7085_);
v___x_7095_ = lean_box(0);
v_isShared_7096_ = v_isSharedCheck_7107_;
goto v_resetjp_7094_;
}
v_resetjp_7094_:
{
lean_object* v___x_7097_; lean_object* v___x_7099_; 
v___x_7097_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_7086_, 2);
if (v_isShared_7096_ == 0)
{
lean_ctor_set(v___x_7095_, 4, v_r_7086_);
lean_ctor_set(v___x_7095_, 3, v_r_7086_);
lean_ctor_set(v___x_7095_, 2, v_v_6992_);
lean_ctor_set(v___x_7095_, 1, v_k_6991_);
lean_ctor_set(v___x_7095_, 0, v___x_7001_);
v___x_7099_ = v___x_7095_;
goto v_reusejp_7098_;
}
else
{
lean_object* v_reuseFailAlloc_7106_; 
v_reuseFailAlloc_7106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7106_, 0, v___x_7001_);
lean_ctor_set(v_reuseFailAlloc_7106_, 1, v_k_6991_);
lean_ctor_set(v_reuseFailAlloc_7106_, 2, v_v_6992_);
lean_ctor_set(v_reuseFailAlloc_7106_, 3, v_r_7086_);
lean_ctor_set(v_reuseFailAlloc_7106_, 4, v_r_7086_);
v___x_7099_ = v_reuseFailAlloc_7106_;
goto v_reusejp_7098_;
}
v_reusejp_7098_:
{
lean_object* v___x_7101_; 
lean_inc(v_r_7086_);
if (v_isShared_7091_ == 0)
{
lean_ctor_set(v___x_7090_, 3, v_r_7086_);
lean_ctor_set(v___x_7090_, 0, v___x_7001_);
v___x_7101_ = v___x_7090_;
goto v_reusejp_7100_;
}
else
{
lean_object* v_reuseFailAlloc_7105_; 
v_reuseFailAlloc_7105_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7105_, 0, v___x_7001_);
lean_ctor_set(v_reuseFailAlloc_7105_, 1, v_k_7087_);
lean_ctor_set(v_reuseFailAlloc_7105_, 2, v_v_7088_);
lean_ctor_set(v_reuseFailAlloc_7105_, 3, v_r_7086_);
lean_ctor_set(v_reuseFailAlloc_7105_, 4, v_r_7086_);
v___x_7101_ = v_reuseFailAlloc_7105_;
goto v_reusejp_7100_;
}
v_reusejp_7100_:
{
lean_object* v___x_7103_; 
if (v_isShared_6997_ == 0)
{
lean_ctor_set(v___x_6996_, 4, v___x_7101_);
lean_ctor_set(v___x_6996_, 3, v___x_7099_);
lean_ctor_set(v___x_6996_, 2, v_v_7093_);
lean_ctor_set(v___x_6996_, 1, v_k_7092_);
lean_ctor_set(v___x_6996_, 0, v___x_7097_);
v___x_7103_ = v___x_6996_;
goto v_reusejp_7102_;
}
else
{
lean_object* v_reuseFailAlloc_7104_; 
v_reuseFailAlloc_7104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7104_, 0, v___x_7097_);
lean_ctor_set(v_reuseFailAlloc_7104_, 1, v_k_7092_);
lean_ctor_set(v_reuseFailAlloc_7104_, 2, v_v_7093_);
lean_ctor_set(v_reuseFailAlloc_7104_, 3, v___x_7099_);
lean_ctor_set(v_reuseFailAlloc_7104_, 4, v___x_7101_);
v___x_7103_ = v_reuseFailAlloc_7104_;
goto v_reusejp_7102_;
}
v_reusejp_7102_:
{
return v___x_7103_;
}
}
}
}
}
}
else
{
lean_object* v_r_7114_; 
v_r_7114_ = lean_ctor_get(v_impl_7000_, 4);
lean_inc(v_r_7114_);
if (lean_obj_tag(v_r_7114_) == 0)
{
lean_object* v_k_7115_; lean_object* v_v_7116_; lean_object* v___x_7118_; uint8_t v_isShared_7119_; uint8_t v_isSharedCheck_7127_; 
v_k_7115_ = lean_ctor_get(v_impl_7000_, 1);
v_v_7116_ = lean_ctor_get(v_impl_7000_, 2);
v_isSharedCheck_7127_ = !lean_is_exclusive(v_impl_7000_);
if (v_isSharedCheck_7127_ == 0)
{
lean_object* v_unused_7128_; lean_object* v_unused_7129_; lean_object* v_unused_7130_; 
v_unused_7128_ = lean_ctor_get(v_impl_7000_, 4);
lean_dec(v_unused_7128_);
v_unused_7129_ = lean_ctor_get(v_impl_7000_, 3);
lean_dec(v_unused_7129_);
v_unused_7130_ = lean_ctor_get(v_impl_7000_, 0);
lean_dec(v_unused_7130_);
v___x_7118_ = v_impl_7000_;
v_isShared_7119_ = v_isSharedCheck_7127_;
goto v_resetjp_7117_;
}
else
{
lean_inc(v_v_7116_);
lean_inc(v_k_7115_);
lean_dec(v_impl_7000_);
v___x_7118_ = lean_box(0);
v_isShared_7119_ = v_isSharedCheck_7127_;
goto v_resetjp_7117_;
}
v_resetjp_7117_:
{
lean_object* v___x_7120_; lean_object* v___x_7122_; 
v___x_7120_ = lean_unsigned_to_nat(3u);
if (v_isShared_7119_ == 0)
{
lean_ctor_set(v___x_7118_, 4, v_l_7085_);
lean_ctor_set(v___x_7118_, 2, v_v_6992_);
lean_ctor_set(v___x_7118_, 1, v_k_6991_);
lean_ctor_set(v___x_7118_, 0, v___x_7001_);
v___x_7122_ = v___x_7118_;
goto v_reusejp_7121_;
}
else
{
lean_object* v_reuseFailAlloc_7126_; 
v_reuseFailAlloc_7126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7126_, 0, v___x_7001_);
lean_ctor_set(v_reuseFailAlloc_7126_, 1, v_k_6991_);
lean_ctor_set(v_reuseFailAlloc_7126_, 2, v_v_6992_);
lean_ctor_set(v_reuseFailAlloc_7126_, 3, v_l_7085_);
lean_ctor_set(v_reuseFailAlloc_7126_, 4, v_l_7085_);
v___x_7122_ = v_reuseFailAlloc_7126_;
goto v_reusejp_7121_;
}
v_reusejp_7121_:
{
lean_object* v___x_7124_; 
if (v_isShared_6997_ == 0)
{
lean_ctor_set(v___x_6996_, 4, v_r_7114_);
lean_ctor_set(v___x_6996_, 3, v___x_7122_);
lean_ctor_set(v___x_6996_, 2, v_v_7116_);
lean_ctor_set(v___x_6996_, 1, v_k_7115_);
lean_ctor_set(v___x_6996_, 0, v___x_7120_);
v___x_7124_ = v___x_6996_;
goto v_reusejp_7123_;
}
else
{
lean_object* v_reuseFailAlloc_7125_; 
v_reuseFailAlloc_7125_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7125_, 0, v___x_7120_);
lean_ctor_set(v_reuseFailAlloc_7125_, 1, v_k_7115_);
lean_ctor_set(v_reuseFailAlloc_7125_, 2, v_v_7116_);
lean_ctor_set(v_reuseFailAlloc_7125_, 3, v___x_7122_);
lean_ctor_set(v_reuseFailAlloc_7125_, 4, v_r_7114_);
v___x_7124_ = v_reuseFailAlloc_7125_;
goto v_reusejp_7123_;
}
v_reusejp_7123_:
{
return v___x_7124_;
}
}
}
}
else
{
lean_object* v___x_7131_; lean_object* v___x_7133_; 
v___x_7131_ = lean_unsigned_to_nat(2u);
if (v_isShared_6997_ == 0)
{
lean_ctor_set(v___x_6996_, 4, v_impl_7000_);
lean_ctor_set(v___x_6996_, 3, v_r_7114_);
lean_ctor_set(v___x_6996_, 0, v___x_7131_);
v___x_7133_ = v___x_6996_;
goto v_reusejp_7132_;
}
else
{
lean_object* v_reuseFailAlloc_7134_; 
v_reuseFailAlloc_7134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7134_, 0, v___x_7131_);
lean_ctor_set(v_reuseFailAlloc_7134_, 1, v_k_6991_);
lean_ctor_set(v_reuseFailAlloc_7134_, 2, v_v_6992_);
lean_ctor_set(v_reuseFailAlloc_7134_, 3, v_r_7114_);
lean_ctor_set(v_reuseFailAlloc_7134_, 4, v_impl_7000_);
v___x_7133_ = v_reuseFailAlloc_7134_;
goto v_reusejp_7132_;
}
v_reusejp_7132_:
{
return v___x_7133_;
}
}
}
}
}
else
{
lean_object* v___x_7136_; 
lean_dec(v_v_6992_);
lean_dec(v_k_6991_);
if (v_isShared_6997_ == 0)
{
lean_ctor_set(v___x_6996_, 2, v_v_6988_);
lean_ctor_set(v___x_6996_, 1, v_k_6987_);
v___x_7136_ = v___x_6996_;
goto v_reusejp_7135_;
}
else
{
lean_object* v_reuseFailAlloc_7137_; 
v_reuseFailAlloc_7137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7137_, 0, v_size_6990_);
lean_ctor_set(v_reuseFailAlloc_7137_, 1, v_k_6987_);
lean_ctor_set(v_reuseFailAlloc_7137_, 2, v_v_6988_);
lean_ctor_set(v_reuseFailAlloc_7137_, 3, v_l_6993_);
lean_ctor_set(v_reuseFailAlloc_7137_, 4, v_r_6994_);
v___x_7136_ = v_reuseFailAlloc_7137_;
goto v_reusejp_7135_;
}
v_reusejp_7135_:
{
return v___x_7136_;
}
}
}
else
{
lean_object* v_impl_7138_; lean_object* v___x_7139_; 
lean_dec(v_size_6990_);
v_impl_7138_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_6987_, v_v_6988_, v_l_6993_);
v___x_7139_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_6994_) == 0)
{
lean_object* v_size_7140_; lean_object* v_size_7141_; lean_object* v_k_7142_; lean_object* v_v_7143_; lean_object* v_l_7144_; lean_object* v_r_7145_; lean_object* v___x_7146_; lean_object* v___x_7147_; uint8_t v___x_7148_; 
v_size_7140_ = lean_ctor_get(v_r_6994_, 0);
v_size_7141_ = lean_ctor_get(v_impl_7138_, 0);
lean_inc(v_size_7141_);
v_k_7142_ = lean_ctor_get(v_impl_7138_, 1);
lean_inc(v_k_7142_);
v_v_7143_ = lean_ctor_get(v_impl_7138_, 2);
lean_inc(v_v_7143_);
v_l_7144_ = lean_ctor_get(v_impl_7138_, 3);
lean_inc(v_l_7144_);
v_r_7145_ = lean_ctor_get(v_impl_7138_, 4);
lean_inc(v_r_7145_);
v___x_7146_ = lean_unsigned_to_nat(3u);
v___x_7147_ = lean_nat_mul(v___x_7146_, v_size_7140_);
v___x_7148_ = lean_nat_dec_lt(v___x_7147_, v_size_7141_);
lean_dec(v___x_7147_);
if (v___x_7148_ == 0)
{
lean_object* v___x_7149_; lean_object* v___x_7150_; lean_object* v___x_7152_; 
lean_dec(v_r_7145_);
lean_dec(v_l_7144_);
lean_dec(v_v_7143_);
lean_dec(v_k_7142_);
v___x_7149_ = lean_nat_add(v___x_7139_, v_size_7141_);
lean_dec(v_size_7141_);
v___x_7150_ = lean_nat_add(v___x_7149_, v_size_7140_);
lean_dec(v___x_7149_);
if (v_isShared_6997_ == 0)
{
lean_ctor_set(v___x_6996_, 3, v_impl_7138_);
lean_ctor_set(v___x_6996_, 0, v___x_7150_);
v___x_7152_ = v___x_6996_;
goto v_reusejp_7151_;
}
else
{
lean_object* v_reuseFailAlloc_7153_; 
v_reuseFailAlloc_7153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7153_, 0, v___x_7150_);
lean_ctor_set(v_reuseFailAlloc_7153_, 1, v_k_6991_);
lean_ctor_set(v_reuseFailAlloc_7153_, 2, v_v_6992_);
lean_ctor_set(v_reuseFailAlloc_7153_, 3, v_impl_7138_);
lean_ctor_set(v_reuseFailAlloc_7153_, 4, v_r_6994_);
v___x_7152_ = v_reuseFailAlloc_7153_;
goto v_reusejp_7151_;
}
v_reusejp_7151_:
{
return v___x_7152_;
}
}
else
{
lean_object* v___x_7155_; uint8_t v_isShared_7156_; uint8_t v_isSharedCheck_7219_; 
v_isSharedCheck_7219_ = !lean_is_exclusive(v_impl_7138_);
if (v_isSharedCheck_7219_ == 0)
{
lean_object* v_unused_7220_; lean_object* v_unused_7221_; lean_object* v_unused_7222_; lean_object* v_unused_7223_; lean_object* v_unused_7224_; 
v_unused_7220_ = lean_ctor_get(v_impl_7138_, 4);
lean_dec(v_unused_7220_);
v_unused_7221_ = lean_ctor_get(v_impl_7138_, 3);
lean_dec(v_unused_7221_);
v_unused_7222_ = lean_ctor_get(v_impl_7138_, 2);
lean_dec(v_unused_7222_);
v_unused_7223_ = lean_ctor_get(v_impl_7138_, 1);
lean_dec(v_unused_7223_);
v_unused_7224_ = lean_ctor_get(v_impl_7138_, 0);
lean_dec(v_unused_7224_);
v___x_7155_ = v_impl_7138_;
v_isShared_7156_ = v_isSharedCheck_7219_;
goto v_resetjp_7154_;
}
else
{
lean_dec(v_impl_7138_);
v___x_7155_ = lean_box(0);
v_isShared_7156_ = v_isSharedCheck_7219_;
goto v_resetjp_7154_;
}
v_resetjp_7154_:
{
lean_object* v_size_7157_; lean_object* v_size_7158_; lean_object* v_k_7159_; lean_object* v_v_7160_; lean_object* v_l_7161_; lean_object* v_r_7162_; lean_object* v___x_7163_; lean_object* v___x_7164_; uint8_t v___x_7165_; 
v_size_7157_ = lean_ctor_get(v_l_7144_, 0);
v_size_7158_ = lean_ctor_get(v_r_7145_, 0);
v_k_7159_ = lean_ctor_get(v_r_7145_, 1);
v_v_7160_ = lean_ctor_get(v_r_7145_, 2);
v_l_7161_ = lean_ctor_get(v_r_7145_, 3);
v_r_7162_ = lean_ctor_get(v_r_7145_, 4);
v___x_7163_ = lean_unsigned_to_nat(2u);
v___x_7164_ = lean_nat_mul(v___x_7163_, v_size_7157_);
v___x_7165_ = lean_nat_dec_lt(v_size_7158_, v___x_7164_);
lean_dec(v___x_7164_);
if (v___x_7165_ == 0)
{
lean_object* v___x_7167_; uint8_t v_isShared_7168_; uint8_t v_isSharedCheck_7194_; 
lean_inc(v_r_7162_);
lean_inc(v_l_7161_);
lean_inc(v_v_7160_);
lean_inc(v_k_7159_);
v_isSharedCheck_7194_ = !lean_is_exclusive(v_r_7145_);
if (v_isSharedCheck_7194_ == 0)
{
lean_object* v_unused_7195_; lean_object* v_unused_7196_; lean_object* v_unused_7197_; lean_object* v_unused_7198_; lean_object* v_unused_7199_; 
v_unused_7195_ = lean_ctor_get(v_r_7145_, 4);
lean_dec(v_unused_7195_);
v_unused_7196_ = lean_ctor_get(v_r_7145_, 3);
lean_dec(v_unused_7196_);
v_unused_7197_ = lean_ctor_get(v_r_7145_, 2);
lean_dec(v_unused_7197_);
v_unused_7198_ = lean_ctor_get(v_r_7145_, 1);
lean_dec(v_unused_7198_);
v_unused_7199_ = lean_ctor_get(v_r_7145_, 0);
lean_dec(v_unused_7199_);
v___x_7167_ = v_r_7145_;
v_isShared_7168_ = v_isSharedCheck_7194_;
goto v_resetjp_7166_;
}
else
{
lean_dec(v_r_7145_);
v___x_7167_ = lean_box(0);
v_isShared_7168_ = v_isSharedCheck_7194_;
goto v_resetjp_7166_;
}
v_resetjp_7166_:
{
lean_object* v___x_7169_; lean_object* v___x_7170_; lean_object* v___y_7172_; lean_object* v___y_7173_; lean_object* v___y_7174_; lean_object* v___x_7182_; lean_object* v___y_7184_; 
v___x_7169_ = lean_nat_add(v___x_7139_, v_size_7141_);
lean_dec(v_size_7141_);
v___x_7170_ = lean_nat_add(v___x_7169_, v_size_7140_);
lean_dec(v___x_7169_);
v___x_7182_ = lean_nat_add(v___x_7139_, v_size_7157_);
if (lean_obj_tag(v_l_7161_) == 0)
{
lean_object* v_size_7192_; 
v_size_7192_ = lean_ctor_get(v_l_7161_, 0);
lean_inc(v_size_7192_);
v___y_7184_ = v_size_7192_;
goto v___jp_7183_;
}
else
{
lean_object* v___x_7193_; 
v___x_7193_ = lean_unsigned_to_nat(0u);
v___y_7184_ = v___x_7193_;
goto v___jp_7183_;
}
v___jp_7171_:
{
lean_object* v___x_7175_; lean_object* v___x_7177_; 
v___x_7175_ = lean_nat_add(v___y_7173_, v___y_7174_);
lean_dec(v___y_7174_);
lean_dec(v___y_7173_);
if (v_isShared_7168_ == 0)
{
lean_ctor_set(v___x_7167_, 4, v_r_6994_);
lean_ctor_set(v___x_7167_, 3, v_r_7162_);
lean_ctor_set(v___x_7167_, 2, v_v_6992_);
lean_ctor_set(v___x_7167_, 1, v_k_6991_);
lean_ctor_set(v___x_7167_, 0, v___x_7175_);
v___x_7177_ = v___x_7167_;
goto v_reusejp_7176_;
}
else
{
lean_object* v_reuseFailAlloc_7181_; 
v_reuseFailAlloc_7181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7181_, 0, v___x_7175_);
lean_ctor_set(v_reuseFailAlloc_7181_, 1, v_k_6991_);
lean_ctor_set(v_reuseFailAlloc_7181_, 2, v_v_6992_);
lean_ctor_set(v_reuseFailAlloc_7181_, 3, v_r_7162_);
lean_ctor_set(v_reuseFailAlloc_7181_, 4, v_r_6994_);
v___x_7177_ = v_reuseFailAlloc_7181_;
goto v_reusejp_7176_;
}
v_reusejp_7176_:
{
lean_object* v___x_7179_; 
if (v_isShared_7156_ == 0)
{
lean_ctor_set(v___x_7155_, 4, v___x_7177_);
lean_ctor_set(v___x_7155_, 3, v___y_7172_);
lean_ctor_set(v___x_7155_, 2, v_v_7160_);
lean_ctor_set(v___x_7155_, 1, v_k_7159_);
lean_ctor_set(v___x_7155_, 0, v___x_7170_);
v___x_7179_ = v___x_7155_;
goto v_reusejp_7178_;
}
else
{
lean_object* v_reuseFailAlloc_7180_; 
v_reuseFailAlloc_7180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7180_, 0, v___x_7170_);
lean_ctor_set(v_reuseFailAlloc_7180_, 1, v_k_7159_);
lean_ctor_set(v_reuseFailAlloc_7180_, 2, v_v_7160_);
lean_ctor_set(v_reuseFailAlloc_7180_, 3, v___y_7172_);
lean_ctor_set(v_reuseFailAlloc_7180_, 4, v___x_7177_);
v___x_7179_ = v_reuseFailAlloc_7180_;
goto v_reusejp_7178_;
}
v_reusejp_7178_:
{
return v___x_7179_;
}
}
}
v___jp_7183_:
{
lean_object* v___x_7185_; lean_object* v___x_7187_; 
v___x_7185_ = lean_nat_add(v___x_7182_, v___y_7184_);
lean_dec(v___y_7184_);
lean_dec(v___x_7182_);
if (v_isShared_6997_ == 0)
{
lean_ctor_set(v___x_6996_, 4, v_l_7161_);
lean_ctor_set(v___x_6996_, 3, v_l_7144_);
lean_ctor_set(v___x_6996_, 2, v_v_7143_);
lean_ctor_set(v___x_6996_, 1, v_k_7142_);
lean_ctor_set(v___x_6996_, 0, v___x_7185_);
v___x_7187_ = v___x_6996_;
goto v_reusejp_7186_;
}
else
{
lean_object* v_reuseFailAlloc_7191_; 
v_reuseFailAlloc_7191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7191_, 0, v___x_7185_);
lean_ctor_set(v_reuseFailAlloc_7191_, 1, v_k_7142_);
lean_ctor_set(v_reuseFailAlloc_7191_, 2, v_v_7143_);
lean_ctor_set(v_reuseFailAlloc_7191_, 3, v_l_7144_);
lean_ctor_set(v_reuseFailAlloc_7191_, 4, v_l_7161_);
v___x_7187_ = v_reuseFailAlloc_7191_;
goto v_reusejp_7186_;
}
v_reusejp_7186_:
{
lean_object* v___x_7188_; 
v___x_7188_ = lean_nat_add(v___x_7139_, v_size_7140_);
if (lean_obj_tag(v_r_7162_) == 0)
{
lean_object* v_size_7189_; 
v_size_7189_ = lean_ctor_get(v_r_7162_, 0);
lean_inc(v_size_7189_);
v___y_7172_ = v___x_7187_;
v___y_7173_ = v___x_7188_;
v___y_7174_ = v_size_7189_;
goto v___jp_7171_;
}
else
{
lean_object* v___x_7190_; 
v___x_7190_ = lean_unsigned_to_nat(0u);
v___y_7172_ = v___x_7187_;
v___y_7173_ = v___x_7188_;
v___y_7174_ = v___x_7190_;
goto v___jp_7171_;
}
}
}
}
}
else
{
lean_object* v___x_7200_; lean_object* v___x_7201_; lean_object* v___x_7202_; lean_object* v___x_7203_; lean_object* v___x_7205_; 
lean_del_object(v___x_6996_);
v___x_7200_ = lean_nat_add(v___x_7139_, v_size_7141_);
lean_dec(v_size_7141_);
v___x_7201_ = lean_nat_add(v___x_7200_, v_size_7140_);
lean_dec(v___x_7200_);
v___x_7202_ = lean_nat_add(v___x_7139_, v_size_7140_);
v___x_7203_ = lean_nat_add(v___x_7202_, v_size_7158_);
lean_dec(v___x_7202_);
lean_inc_ref(v_r_6994_);
if (v_isShared_7156_ == 0)
{
lean_ctor_set(v___x_7155_, 4, v_r_6994_);
lean_ctor_set(v___x_7155_, 3, v_r_7145_);
lean_ctor_set(v___x_7155_, 2, v_v_6992_);
lean_ctor_set(v___x_7155_, 1, v_k_6991_);
lean_ctor_set(v___x_7155_, 0, v___x_7203_);
v___x_7205_ = v___x_7155_;
goto v_reusejp_7204_;
}
else
{
lean_object* v_reuseFailAlloc_7218_; 
v_reuseFailAlloc_7218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7218_, 0, v___x_7203_);
lean_ctor_set(v_reuseFailAlloc_7218_, 1, v_k_6991_);
lean_ctor_set(v_reuseFailAlloc_7218_, 2, v_v_6992_);
lean_ctor_set(v_reuseFailAlloc_7218_, 3, v_r_7145_);
lean_ctor_set(v_reuseFailAlloc_7218_, 4, v_r_6994_);
v___x_7205_ = v_reuseFailAlloc_7218_;
goto v_reusejp_7204_;
}
v_reusejp_7204_:
{
lean_object* v___x_7207_; uint8_t v_isShared_7208_; uint8_t v_isSharedCheck_7212_; 
v_isSharedCheck_7212_ = !lean_is_exclusive(v_r_6994_);
if (v_isSharedCheck_7212_ == 0)
{
lean_object* v_unused_7213_; lean_object* v_unused_7214_; lean_object* v_unused_7215_; lean_object* v_unused_7216_; lean_object* v_unused_7217_; 
v_unused_7213_ = lean_ctor_get(v_r_6994_, 4);
lean_dec(v_unused_7213_);
v_unused_7214_ = lean_ctor_get(v_r_6994_, 3);
lean_dec(v_unused_7214_);
v_unused_7215_ = lean_ctor_get(v_r_6994_, 2);
lean_dec(v_unused_7215_);
v_unused_7216_ = lean_ctor_get(v_r_6994_, 1);
lean_dec(v_unused_7216_);
v_unused_7217_ = lean_ctor_get(v_r_6994_, 0);
lean_dec(v_unused_7217_);
v___x_7207_ = v_r_6994_;
v_isShared_7208_ = v_isSharedCheck_7212_;
goto v_resetjp_7206_;
}
else
{
lean_dec(v_r_6994_);
v___x_7207_ = lean_box(0);
v_isShared_7208_ = v_isSharedCheck_7212_;
goto v_resetjp_7206_;
}
v_resetjp_7206_:
{
lean_object* v___x_7210_; 
if (v_isShared_7208_ == 0)
{
lean_ctor_set(v___x_7207_, 4, v___x_7205_);
lean_ctor_set(v___x_7207_, 3, v_l_7144_);
lean_ctor_set(v___x_7207_, 2, v_v_7143_);
lean_ctor_set(v___x_7207_, 1, v_k_7142_);
lean_ctor_set(v___x_7207_, 0, v___x_7201_);
v___x_7210_ = v___x_7207_;
goto v_reusejp_7209_;
}
else
{
lean_object* v_reuseFailAlloc_7211_; 
v_reuseFailAlloc_7211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7211_, 0, v___x_7201_);
lean_ctor_set(v_reuseFailAlloc_7211_, 1, v_k_7142_);
lean_ctor_set(v_reuseFailAlloc_7211_, 2, v_v_7143_);
lean_ctor_set(v_reuseFailAlloc_7211_, 3, v_l_7144_);
lean_ctor_set(v_reuseFailAlloc_7211_, 4, v___x_7205_);
v___x_7210_ = v_reuseFailAlloc_7211_;
goto v_reusejp_7209_;
}
v_reusejp_7209_:
{
return v___x_7210_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_7225_; 
v_l_7225_ = lean_ctor_get(v_impl_7138_, 3);
lean_inc(v_l_7225_);
if (lean_obj_tag(v_l_7225_) == 0)
{
lean_object* v_r_7226_; lean_object* v_k_7227_; lean_object* v_v_7228_; lean_object* v___x_7230_; uint8_t v_isShared_7231_; uint8_t v_isSharedCheck_7239_; 
v_r_7226_ = lean_ctor_get(v_impl_7138_, 4);
v_k_7227_ = lean_ctor_get(v_impl_7138_, 1);
v_v_7228_ = lean_ctor_get(v_impl_7138_, 2);
v_isSharedCheck_7239_ = !lean_is_exclusive(v_impl_7138_);
if (v_isSharedCheck_7239_ == 0)
{
lean_object* v_unused_7240_; lean_object* v_unused_7241_; 
v_unused_7240_ = lean_ctor_get(v_impl_7138_, 3);
lean_dec(v_unused_7240_);
v_unused_7241_ = lean_ctor_get(v_impl_7138_, 0);
lean_dec(v_unused_7241_);
v___x_7230_ = v_impl_7138_;
v_isShared_7231_ = v_isSharedCheck_7239_;
goto v_resetjp_7229_;
}
else
{
lean_inc(v_r_7226_);
lean_inc(v_v_7228_);
lean_inc(v_k_7227_);
lean_dec(v_impl_7138_);
v___x_7230_ = lean_box(0);
v_isShared_7231_ = v_isSharedCheck_7239_;
goto v_resetjp_7229_;
}
v_resetjp_7229_:
{
lean_object* v___x_7232_; lean_object* v___x_7234_; 
v___x_7232_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_7226_);
if (v_isShared_7231_ == 0)
{
lean_ctor_set(v___x_7230_, 3, v_r_7226_);
lean_ctor_set(v___x_7230_, 2, v_v_6992_);
lean_ctor_set(v___x_7230_, 1, v_k_6991_);
lean_ctor_set(v___x_7230_, 0, v___x_7139_);
v___x_7234_ = v___x_7230_;
goto v_reusejp_7233_;
}
else
{
lean_object* v_reuseFailAlloc_7238_; 
v_reuseFailAlloc_7238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7238_, 0, v___x_7139_);
lean_ctor_set(v_reuseFailAlloc_7238_, 1, v_k_6991_);
lean_ctor_set(v_reuseFailAlloc_7238_, 2, v_v_6992_);
lean_ctor_set(v_reuseFailAlloc_7238_, 3, v_r_7226_);
lean_ctor_set(v_reuseFailAlloc_7238_, 4, v_r_7226_);
v___x_7234_ = v_reuseFailAlloc_7238_;
goto v_reusejp_7233_;
}
v_reusejp_7233_:
{
lean_object* v___x_7236_; 
if (v_isShared_6997_ == 0)
{
lean_ctor_set(v___x_6996_, 4, v___x_7234_);
lean_ctor_set(v___x_6996_, 3, v_l_7225_);
lean_ctor_set(v___x_6996_, 2, v_v_7228_);
lean_ctor_set(v___x_6996_, 1, v_k_7227_);
lean_ctor_set(v___x_6996_, 0, v___x_7232_);
v___x_7236_ = v___x_6996_;
goto v_reusejp_7235_;
}
else
{
lean_object* v_reuseFailAlloc_7237_; 
v_reuseFailAlloc_7237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7237_, 0, v___x_7232_);
lean_ctor_set(v_reuseFailAlloc_7237_, 1, v_k_7227_);
lean_ctor_set(v_reuseFailAlloc_7237_, 2, v_v_7228_);
lean_ctor_set(v_reuseFailAlloc_7237_, 3, v_l_7225_);
lean_ctor_set(v_reuseFailAlloc_7237_, 4, v___x_7234_);
v___x_7236_ = v_reuseFailAlloc_7237_;
goto v_reusejp_7235_;
}
v_reusejp_7235_:
{
return v___x_7236_;
}
}
}
}
else
{
lean_object* v_r_7242_; 
v_r_7242_ = lean_ctor_get(v_impl_7138_, 4);
lean_inc(v_r_7242_);
if (lean_obj_tag(v_r_7242_) == 0)
{
lean_object* v_k_7243_; lean_object* v_v_7244_; lean_object* v___x_7246_; uint8_t v_isShared_7247_; uint8_t v_isSharedCheck_7267_; 
v_k_7243_ = lean_ctor_get(v_impl_7138_, 1);
v_v_7244_ = lean_ctor_get(v_impl_7138_, 2);
v_isSharedCheck_7267_ = !lean_is_exclusive(v_impl_7138_);
if (v_isSharedCheck_7267_ == 0)
{
lean_object* v_unused_7268_; lean_object* v_unused_7269_; lean_object* v_unused_7270_; 
v_unused_7268_ = lean_ctor_get(v_impl_7138_, 4);
lean_dec(v_unused_7268_);
v_unused_7269_ = lean_ctor_get(v_impl_7138_, 3);
lean_dec(v_unused_7269_);
v_unused_7270_ = lean_ctor_get(v_impl_7138_, 0);
lean_dec(v_unused_7270_);
v___x_7246_ = v_impl_7138_;
v_isShared_7247_ = v_isSharedCheck_7267_;
goto v_resetjp_7245_;
}
else
{
lean_inc(v_v_7244_);
lean_inc(v_k_7243_);
lean_dec(v_impl_7138_);
v___x_7246_ = lean_box(0);
v_isShared_7247_ = v_isSharedCheck_7267_;
goto v_resetjp_7245_;
}
v_resetjp_7245_:
{
lean_object* v_k_7248_; lean_object* v_v_7249_; lean_object* v___x_7251_; uint8_t v_isShared_7252_; uint8_t v_isSharedCheck_7263_; 
v_k_7248_ = lean_ctor_get(v_r_7242_, 1);
v_v_7249_ = lean_ctor_get(v_r_7242_, 2);
v_isSharedCheck_7263_ = !lean_is_exclusive(v_r_7242_);
if (v_isSharedCheck_7263_ == 0)
{
lean_object* v_unused_7264_; lean_object* v_unused_7265_; lean_object* v_unused_7266_; 
v_unused_7264_ = lean_ctor_get(v_r_7242_, 4);
lean_dec(v_unused_7264_);
v_unused_7265_ = lean_ctor_get(v_r_7242_, 3);
lean_dec(v_unused_7265_);
v_unused_7266_ = lean_ctor_get(v_r_7242_, 0);
lean_dec(v_unused_7266_);
v___x_7251_ = v_r_7242_;
v_isShared_7252_ = v_isSharedCheck_7263_;
goto v_resetjp_7250_;
}
else
{
lean_inc(v_v_7249_);
lean_inc(v_k_7248_);
lean_dec(v_r_7242_);
v___x_7251_ = lean_box(0);
v_isShared_7252_ = v_isSharedCheck_7263_;
goto v_resetjp_7250_;
}
v_resetjp_7250_:
{
lean_object* v___x_7253_; lean_object* v___x_7255_; 
v___x_7253_ = lean_unsigned_to_nat(3u);
if (v_isShared_7252_ == 0)
{
lean_ctor_set(v___x_7251_, 4, v_l_7225_);
lean_ctor_set(v___x_7251_, 3, v_l_7225_);
lean_ctor_set(v___x_7251_, 2, v_v_7244_);
lean_ctor_set(v___x_7251_, 1, v_k_7243_);
lean_ctor_set(v___x_7251_, 0, v___x_7139_);
v___x_7255_ = v___x_7251_;
goto v_reusejp_7254_;
}
else
{
lean_object* v_reuseFailAlloc_7262_; 
v_reuseFailAlloc_7262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7262_, 0, v___x_7139_);
lean_ctor_set(v_reuseFailAlloc_7262_, 1, v_k_7243_);
lean_ctor_set(v_reuseFailAlloc_7262_, 2, v_v_7244_);
lean_ctor_set(v_reuseFailAlloc_7262_, 3, v_l_7225_);
lean_ctor_set(v_reuseFailAlloc_7262_, 4, v_l_7225_);
v___x_7255_ = v_reuseFailAlloc_7262_;
goto v_reusejp_7254_;
}
v_reusejp_7254_:
{
lean_object* v___x_7257_; 
if (v_isShared_7247_ == 0)
{
lean_ctor_set(v___x_7246_, 4, v_l_7225_);
lean_ctor_set(v___x_7246_, 2, v_v_6992_);
lean_ctor_set(v___x_7246_, 1, v_k_6991_);
lean_ctor_set(v___x_7246_, 0, v___x_7139_);
v___x_7257_ = v___x_7246_;
goto v_reusejp_7256_;
}
else
{
lean_object* v_reuseFailAlloc_7261_; 
v_reuseFailAlloc_7261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7261_, 0, v___x_7139_);
lean_ctor_set(v_reuseFailAlloc_7261_, 1, v_k_6991_);
lean_ctor_set(v_reuseFailAlloc_7261_, 2, v_v_6992_);
lean_ctor_set(v_reuseFailAlloc_7261_, 3, v_l_7225_);
lean_ctor_set(v_reuseFailAlloc_7261_, 4, v_l_7225_);
v___x_7257_ = v_reuseFailAlloc_7261_;
goto v_reusejp_7256_;
}
v_reusejp_7256_:
{
lean_object* v___x_7259_; 
if (v_isShared_6997_ == 0)
{
lean_ctor_set(v___x_6996_, 4, v___x_7257_);
lean_ctor_set(v___x_6996_, 3, v___x_7255_);
lean_ctor_set(v___x_6996_, 2, v_v_7249_);
lean_ctor_set(v___x_6996_, 1, v_k_7248_);
lean_ctor_set(v___x_6996_, 0, v___x_7253_);
v___x_7259_ = v___x_6996_;
goto v_reusejp_7258_;
}
else
{
lean_object* v_reuseFailAlloc_7260_; 
v_reuseFailAlloc_7260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7260_, 0, v___x_7253_);
lean_ctor_set(v_reuseFailAlloc_7260_, 1, v_k_7248_);
lean_ctor_set(v_reuseFailAlloc_7260_, 2, v_v_7249_);
lean_ctor_set(v_reuseFailAlloc_7260_, 3, v___x_7255_);
lean_ctor_set(v_reuseFailAlloc_7260_, 4, v___x_7257_);
v___x_7259_ = v_reuseFailAlloc_7260_;
goto v_reusejp_7258_;
}
v_reusejp_7258_:
{
return v___x_7259_;
}
}
}
}
}
}
else
{
lean_object* v___x_7271_; lean_object* v___x_7273_; 
v___x_7271_ = lean_unsigned_to_nat(2u);
if (v_isShared_6997_ == 0)
{
lean_ctor_set(v___x_6996_, 4, v_r_7242_);
lean_ctor_set(v___x_6996_, 3, v_impl_7138_);
lean_ctor_set(v___x_6996_, 0, v___x_7271_);
v___x_7273_ = v___x_6996_;
goto v_reusejp_7272_;
}
else
{
lean_object* v_reuseFailAlloc_7274_; 
v_reuseFailAlloc_7274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7274_, 0, v___x_7271_);
lean_ctor_set(v_reuseFailAlloc_7274_, 1, v_k_6991_);
lean_ctor_set(v_reuseFailAlloc_7274_, 2, v_v_6992_);
lean_ctor_set(v_reuseFailAlloc_7274_, 3, v_impl_7138_);
lean_ctor_set(v_reuseFailAlloc_7274_, 4, v_r_7242_);
v___x_7273_ = v_reuseFailAlloc_7274_;
goto v_reusejp_7272_;
}
v_reusejp_7272_:
{
return v___x_7273_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_7276_; lean_object* v___x_7277_; 
v___x_7276_ = lean_unsigned_to_nat(1u);
v___x_7277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_7277_, 0, v___x_7276_);
lean_ctor_set(v___x_7277_, 1, v_k_6987_);
lean_ctor_set(v___x_7277_, 2, v_v_6988_);
lean_ctor_set(v___x_7277_, 3, v_t_6989_);
lean_ctor_set(v___x_7277_, 4, v_t_6989_);
return v___x_7277_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(lean_object* v_lib_7278_, lean_object* v_ps_7279_, lean_object* v_v_7280_, lean_object* v_o_7281_){
_start:
{
lean_object* v_name_7282_; lean_object* v_deps_7283_; lean_object* v_o_7284_; uint8_t v___x_7285_; 
v_name_7282_ = lean_ctor_get(v_lib_7278_, 1);
lean_inc_ref(v_name_7282_);
v_deps_7283_ = lean_ctor_get(v_lib_7278_, 2);
lean_inc_ref(v_deps_7283_);
v_o_7284_ = lean_array_push(v_o_7281_, v_lib_7278_);
v___x_7285_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_name_7282_, v_v_7280_);
if (v___x_7285_ == 0)
{
uint8_t v___x_7286_; 
v___x_7286_ = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(v_name_7282_, v_ps_7279_);
if (v___x_7286_ == 0)
{
lean_object* v_ps_7287_; lean_object* v___y_7289_; 
lean_inc_ref(v_name_7282_);
v_ps_7287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_ps_7287_, 0, v_name_7282_);
lean_ctor_set(v_ps_7287_, 1, v_ps_7279_);
if (v___x_7285_ == 0)
{
lean_object* v___x_7303_; lean_object* v___x_7304_; 
v___x_7303_ = lean_box(0);
v___x_7304_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_name_7282_, v___x_7303_, v_v_7280_);
v___y_7289_ = v___x_7304_;
goto v___jp_7288_;
}
else
{
lean_dec_ref(v_name_7282_);
v___y_7289_ = v_v_7280_;
goto v___jp_7288_;
}
v___jp_7288_:
{
lean_object* v___x_7290_; lean_object* v___x_7291_; lean_object* v___x_7292_; uint8_t v___x_7293_; 
v___x_7290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7290_, 0, v___y_7289_);
lean_ctor_set(v___x_7290_, 1, v_o_7284_);
v___x_7291_ = lean_unsigned_to_nat(0u);
v___x_7292_ = lean_array_get_size(v_deps_7283_);
v___x_7293_ = lean_nat_dec_lt(v___x_7291_, v___x_7292_);
if (v___x_7293_ == 0)
{
lean_object* v___x_7294_; 
lean_dec_ref(v_ps_7287_);
lean_dec_ref(v_deps_7283_);
v___x_7294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7294_, 0, v___x_7290_);
return v___x_7294_;
}
else
{
uint8_t v___x_7295_; 
v___x_7295_ = lean_nat_dec_le(v___x_7292_, v___x_7292_);
if (v___x_7295_ == 0)
{
if (v___x_7293_ == 0)
{
lean_object* v___x_7296_; 
lean_dec_ref(v_ps_7287_);
lean_dec_ref(v_deps_7283_);
v___x_7296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7296_, 0, v___x_7290_);
return v___x_7296_;
}
else
{
size_t v___x_7297_; size_t v___x_7298_; lean_object* v___x_7299_; 
v___x_7297_ = ((size_t)0ULL);
v___x_7298_ = lean_usize_of_nat(v___x_7292_);
v___x_7299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7287_, v_deps_7283_, v___x_7297_, v___x_7298_, v___x_7290_);
lean_dec_ref(v_deps_7283_);
return v___x_7299_;
}
}
else
{
size_t v___x_7300_; size_t v___x_7301_; lean_object* v___x_7302_; 
v___x_7300_ = ((size_t)0ULL);
v___x_7301_ = lean_usize_of_nat(v___x_7292_);
v___x_7302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7287_, v_deps_7283_, v___x_7300_, v___x_7301_, v___x_7290_);
lean_dec_ref(v_deps_7283_);
return v___x_7302_;
}
}
}
}
else
{
lean_object* v___x_7305_; lean_object* v___x_7306_; 
lean_dec_ref(v_o_7284_);
lean_dec_ref(v_deps_7283_);
lean_dec(v_v_7280_);
v___x_7305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7305_, 0, v_name_7282_);
lean_ctor_set(v___x_7305_, 1, v_ps_7279_);
v___x_7306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7306_, 0, v___x_7305_);
return v___x_7306_;
}
}
else
{
lean_object* v___x_7307_; lean_object* v___x_7308_; 
lean_dec_ref(v_deps_7283_);
lean_dec_ref(v_name_7282_);
lean_dec(v_ps_7279_);
v___x_7307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7307_, 0, v_v_7280_);
lean_ctor_set(v___x_7307_, 1, v_o_7284_);
v___x_7308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7308_, 0, v___x_7307_);
return v___x_7308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(lean_object* v_ps_7309_, lean_object* v_as_7310_, size_t v_i_7311_, size_t v_stop_7312_, lean_object* v_b_7313_){
_start:
{
uint8_t v___x_7314_; 
v___x_7314_ = lean_usize_dec_eq(v_i_7311_, v_stop_7312_);
if (v___x_7314_ == 0)
{
lean_object* v_fst_7315_; lean_object* v_snd_7316_; lean_object* v___x_7317_; lean_object* v___x_7318_; 
v_fst_7315_ = lean_ctor_get(v_b_7313_, 0);
lean_inc(v_fst_7315_);
v_snd_7316_ = lean_ctor_get(v_b_7313_, 1);
lean_inc(v_snd_7316_);
lean_dec_ref(v_b_7313_);
v___x_7317_ = lean_array_uget_borrowed(v_as_7310_, v_i_7311_);
lean_inc(v_ps_7309_);
lean_inc(v___x_7317_);
v___x_7318_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(v___x_7317_, v_ps_7309_, v_fst_7315_, v_snd_7316_);
if (lean_obj_tag(v___x_7318_) == 0)
{
lean_dec(v_ps_7309_);
return v___x_7318_;
}
else
{
lean_object* v_a_7319_; size_t v___x_7320_; size_t v___x_7321_; 
v_a_7319_ = lean_ctor_get(v___x_7318_, 0);
lean_inc(v_a_7319_);
lean_dec_ref(v___x_7318_);
v___x_7320_ = ((size_t)1ULL);
v___x_7321_ = lean_usize_add(v_i_7311_, v___x_7320_);
v_i_7311_ = v___x_7321_;
v_b_7313_ = v_a_7319_;
goto _start;
}
}
else
{
lean_object* v___x_7323_; 
lean_dec(v_ps_7309_);
v___x_7323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7323_, 0, v_b_7313_);
return v___x_7323_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2___boxed(lean_object* v_ps_7324_, lean_object* v_as_7325_, lean_object* v_i_7326_, lean_object* v_stop_7327_, lean_object* v_b_7328_){
_start:
{
size_t v_i_boxed_7329_; size_t v_stop_boxed_7330_; lean_object* v_res_7331_; 
v_i_boxed_7329_ = lean_unbox_usize(v_i_7326_);
lean_dec(v_i_7326_);
v_stop_boxed_7330_ = lean_unbox_usize(v_stop_7327_);
lean_dec(v_stop_7327_);
v_res_7331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7324_, v_as_7325_, v_i_boxed_7329_, v_stop_boxed_7330_, v_b_7328_);
lean_dec_ref(v_as_7325_);
return v_res_7331_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(lean_object* v_00_u03b2_7332_, lean_object* v_k_7333_, lean_object* v_t_7334_){
_start:
{
uint8_t v___x_7335_; 
v___x_7335_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_k_7333_, v_t_7334_);
return v___x_7335_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___boxed(lean_object* v_00_u03b2_7336_, lean_object* v_k_7337_, lean_object* v_t_7338_){
_start:
{
uint8_t v_res_7339_; lean_object* v_r_7340_; 
v_res_7339_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(v_00_u03b2_7336_, v_k_7337_, v_t_7338_);
lean_dec(v_t_7338_);
lean_dec_ref(v_k_7337_);
v_r_7340_ = lean_box(v_res_7339_);
return v_r_7340_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3(lean_object* v_00_u03b2_7341_, lean_object* v_k_7342_, lean_object* v_v_7343_, lean_object* v_t_7344_, lean_object* v_hl_7345_){
_start:
{
lean_object* v___x_7346_; 
v___x_7346_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7342_, v_v_7343_, v_t_7344_);
return v___x_7346_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0(lean_object* v_a_7348_, lean_object* v_a_7349_){
_start:
{
if (lean_obj_tag(v_a_7348_) == 0)
{
lean_object* v___x_7350_; 
v___x_7350_ = l_List_reverse___redArg(v_a_7349_);
return v___x_7350_;
}
else
{
lean_object* v_head_7351_; lean_object* v_tail_7352_; lean_object* v___x_7354_; uint8_t v_isShared_7355_; uint8_t v_isSharedCheck_7362_; 
v_head_7351_ = lean_ctor_get(v_a_7348_, 0);
v_tail_7352_ = lean_ctor_get(v_a_7348_, 1);
v_isSharedCheck_7362_ = !lean_is_exclusive(v_a_7348_);
if (v_isSharedCheck_7362_ == 0)
{
v___x_7354_ = v_a_7348_;
v_isShared_7355_ = v_isSharedCheck_7362_;
goto v_resetjp_7353_;
}
else
{
lean_inc(v_tail_7352_);
lean_inc(v_head_7351_);
lean_dec(v_a_7348_);
v___x_7354_ = lean_box(0);
v_isShared_7355_ = v_isSharedCheck_7362_;
goto v_resetjp_7353_;
}
v_resetjp_7353_:
{
lean_object* v___x_7356_; lean_object* v___x_7357_; lean_object* v___x_7359_; 
v___x_7356_ = ((lean_object*)(l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0));
v___x_7357_ = lean_string_append(v___x_7356_, v_head_7351_);
lean_dec(v_head_7351_);
if (v_isShared_7355_ == 0)
{
lean_ctor_set(v___x_7354_, 1, v_a_7349_);
lean_ctor_set(v___x_7354_, 0, v___x_7357_);
v___x_7359_ = v___x_7354_;
goto v_reusejp_7358_;
}
else
{
lean_object* v_reuseFailAlloc_7361_; 
v_reuseFailAlloc_7361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7361_, 0, v___x_7357_);
lean_ctor_set(v_reuseFailAlloc_7361_, 1, v_a_7349_);
v___x_7359_ = v_reuseFailAlloc_7361_;
goto v_reusejp_7358_;
}
v_reusejp_7358_:
{
v_a_7348_ = v_tail_7352_;
v_a_7349_ = v___x_7359_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(lean_object* v_cycle_7363_){
_start:
{
lean_object* v___x_7364_; lean_object* v___x_7365_; lean_object* v___x_7366_; lean_object* v___x_7367_; 
v___x_7364_ = ((lean_object*)(l_Lake_resolveArtifactOutput___redArg___closed__1));
v___x_7365_ = lean_box(0);
v___x_7366_ = l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0(v_cycle_7363_, v___x_7365_);
v___x_7367_ = l_String_intercalate(v___x_7364_, v___x_7366_);
return v___x_7367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(lean_object* v_as_7368_, size_t v_i_7369_, size_t v_stop_7370_, lean_object* v_b_7371_){
_start:
{
uint8_t v___x_7372_; 
v___x_7372_ = lean_usize_dec_eq(v_i_7369_, v_stop_7370_);
if (v___x_7372_ == 0)
{
lean_object* v_fst_7373_; lean_object* v_snd_7374_; lean_object* v___x_7375_; lean_object* v___x_7376_; lean_object* v___x_7377_; 
v_fst_7373_ = lean_ctor_get(v_b_7371_, 0);
lean_inc(v_fst_7373_);
v_snd_7374_ = lean_ctor_get(v_b_7371_, 1);
lean_inc(v_snd_7374_);
lean_dec_ref(v_b_7371_);
v___x_7375_ = lean_array_uget_borrowed(v_as_7368_, v_i_7369_);
v___x_7376_ = lean_box(0);
lean_inc(v___x_7375_);
v___x_7377_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(v___x_7375_, v___x_7376_, v_fst_7373_, v_snd_7374_);
if (lean_obj_tag(v___x_7377_) == 0)
{
return v___x_7377_;
}
else
{
lean_object* v_a_7378_; size_t v___x_7379_; size_t v___x_7380_; 
v_a_7378_ = lean_ctor_get(v___x_7377_, 0);
lean_inc(v_a_7378_);
lean_dec_ref(v___x_7377_);
v___x_7379_ = ((size_t)1ULL);
v___x_7380_ = lean_usize_add(v_i_7369_, v___x_7379_);
v_i_7369_ = v___x_7380_;
v_b_7371_ = v_a_7378_;
goto _start;
}
}
else
{
lean_object* v___x_7382_; 
v___x_7382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7382_, 0, v_b_7371_);
return v___x_7382_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1___boxed(lean_object* v_as_7383_, lean_object* v_i_7384_, lean_object* v_stop_7385_, lean_object* v_b_7386_){
_start:
{
size_t v_i_boxed_7387_; size_t v_stop_boxed_7388_; lean_object* v_res_7389_; 
v_i_boxed_7387_ = lean_unbox_usize(v_i_7384_);
lean_dec(v_i_7384_);
v_stop_boxed_7388_ = lean_unbox_usize(v_stop_7385_);
lean_dec(v_stop_7385_);
v_res_7389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(v_as_7383_, v_i_boxed_7387_, v_stop_boxed_7388_, v_b_7386_);
lean_dec_ref(v_as_7383_);
return v_res_7389_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(lean_object* v_libs_7396_, lean_object* v_a_7397_){
_start:
{
lean_object* v_snd_7400_; lean_object* v___y_7403_; lean_object* v___x_7427_; lean_object* v___x_7428_; lean_object* v___x_7429_; uint8_t v___x_7430_; 
v___x_7427_ = lean_unsigned_to_nat(0u);
v___x_7428_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1));
v___x_7429_ = lean_array_get_size(v_libs_7396_);
v___x_7430_ = lean_nat_dec_lt(v___x_7427_, v___x_7429_);
if (v___x_7430_ == 0)
{
v_snd_7400_ = v___x_7428_;
goto v___jp_7399_;
}
else
{
lean_object* v___x_7431_; uint8_t v___x_7432_; 
v___x_7431_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2));
v___x_7432_ = lean_nat_dec_le(v___x_7429_, v___x_7429_);
if (v___x_7432_ == 0)
{
if (v___x_7430_ == 0)
{
v_snd_7400_ = v___x_7428_;
goto v___jp_7399_;
}
else
{
size_t v___x_7433_; size_t v___x_7434_; lean_object* v___x_7435_; 
v___x_7433_ = ((size_t)0ULL);
v___x_7434_ = lean_usize_of_nat(v___x_7429_);
v___x_7435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(v_libs_7396_, v___x_7433_, v___x_7434_, v___x_7431_);
v___y_7403_ = v___x_7435_;
goto v___jp_7402_;
}
}
else
{
size_t v___x_7436_; size_t v___x_7437_; lean_object* v___x_7438_; 
v___x_7436_ = ((size_t)0ULL);
v___x_7437_ = lean_usize_of_nat(v___x_7429_);
v___x_7438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(v_libs_7396_, v___x_7436_, v___x_7437_, v___x_7431_);
v___y_7403_ = v___x_7438_;
goto v___jp_7402_;
}
}
v___jp_7399_:
{
lean_object* v___x_7401_; 
v___x_7401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7401_, 0, v_snd_7400_);
lean_ctor_set(v___x_7401_, 1, v_a_7397_);
return v___x_7401_;
}
v___jp_7402_:
{
if (lean_obj_tag(v___y_7403_) == 0)
{
lean_object* v_a_7404_; lean_object* v_log_7405_; uint8_t v_action_7406_; uint8_t v_wantsRebuild_7407_; lean_object* v_trace_7408_; lean_object* v_buildTime_7409_; lean_object* v___x_7411_; uint8_t v_isShared_7412_; uint8_t v_isSharedCheck_7424_; 
v_a_7404_ = lean_ctor_get(v___y_7403_, 0);
lean_inc(v_a_7404_);
lean_dec_ref(v___y_7403_);
v_log_7405_ = lean_ctor_get(v_a_7397_, 0);
v_action_7406_ = lean_ctor_get_uint8(v_a_7397_, sizeof(void*)*3);
v_wantsRebuild_7407_ = lean_ctor_get_uint8(v_a_7397_, sizeof(void*)*3 + 1);
v_trace_7408_ = lean_ctor_get(v_a_7397_, 1);
v_buildTime_7409_ = lean_ctor_get(v_a_7397_, 2);
v_isSharedCheck_7424_ = !lean_is_exclusive(v_a_7397_);
if (v_isSharedCheck_7424_ == 0)
{
v___x_7411_ = v_a_7397_;
v_isShared_7412_ = v_isSharedCheck_7424_;
goto v_resetjp_7410_;
}
else
{
lean_inc(v_buildTime_7409_);
lean_inc(v_trace_7408_);
lean_inc(v_log_7405_);
lean_dec(v_a_7397_);
v___x_7411_ = lean_box(0);
v_isShared_7412_ = v_isSharedCheck_7424_;
goto v_resetjp_7410_;
}
v_resetjp_7410_:
{
lean_object* v___x_7413_; lean_object* v___x_7414_; lean_object* v___x_7415_; uint8_t v___x_7416_; lean_object* v___x_7417_; lean_object* v___x_7418_; lean_object* v___x_7419_; lean_object* v___x_7421_; 
v___x_7413_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0));
v___x_7414_ = l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(v_a_7404_);
v___x_7415_ = lean_string_append(v___x_7413_, v___x_7414_);
lean_dec_ref(v___x_7414_);
v___x_7416_ = 3;
v___x_7417_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7417_, 0, v___x_7415_);
lean_ctor_set_uint8(v___x_7417_, sizeof(void*)*1, v___x_7416_);
v___x_7418_ = lean_array_get_size(v_log_7405_);
v___x_7419_ = lean_array_push(v_log_7405_, v___x_7417_);
if (v_isShared_7412_ == 0)
{
lean_ctor_set(v___x_7411_, 0, v___x_7419_);
v___x_7421_ = v___x_7411_;
goto v_reusejp_7420_;
}
else
{
lean_object* v_reuseFailAlloc_7423_; 
v_reuseFailAlloc_7423_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7423_, 0, v___x_7419_);
lean_ctor_set(v_reuseFailAlloc_7423_, 1, v_trace_7408_);
lean_ctor_set(v_reuseFailAlloc_7423_, 2, v_buildTime_7409_);
lean_ctor_set_uint8(v_reuseFailAlloc_7423_, sizeof(void*)*3, v_action_7406_);
lean_ctor_set_uint8(v_reuseFailAlloc_7423_, sizeof(void*)*3 + 1, v_wantsRebuild_7407_);
v___x_7421_ = v_reuseFailAlloc_7423_;
goto v_reusejp_7420_;
}
v_reusejp_7420_:
{
lean_object* v___x_7422_; 
v___x_7422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7422_, 0, v___x_7418_);
lean_ctor_set(v___x_7422_, 1, v___x_7421_);
return v___x_7422_;
}
}
}
else
{
lean_object* v_a_7425_; lean_object* v_snd_7426_; 
v_a_7425_ = lean_ctor_get(v___y_7403_, 0);
lean_inc(v_a_7425_);
lean_dec_ref(v___y_7403_);
v_snd_7426_ = lean_ctor_get(v_a_7425_, 1);
lean_inc(v_snd_7426_);
lean_dec(v_a_7425_);
v_snd_7400_ = v_snd_7426_;
goto v___jp_7399_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___boxed(lean_object* v_libs_7439_, lean_object* v_a_7440_, lean_object* v_a_7441_){
_start:
{
lean_object* v_res_7442_; 
v_res_7442_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7439_, v_a_7440_);
lean_dec_ref(v_libs_7439_);
return v_res_7442_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder(lean_object* v_libs_7443_, lean_object* v_a_7444_, lean_object* v_a_7445_, lean_object* v_a_7446_, lean_object* v_a_7447_, lean_object* v_a_7448_, lean_object* v_a_7449_){
_start:
{
lean_object* v___x_7451_; 
v___x_7451_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7443_, v_a_7449_);
return v___x_7451_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___boxed(lean_object* v_libs_7452_, lean_object* v_a_7453_, lean_object* v_a_7454_, lean_object* v_a_7455_, lean_object* v_a_7456_, lean_object* v_a_7457_, lean_object* v_a_7458_, lean_object* v_a_7459_){
_start:
{
lean_object* v_res_7460_; 
v_res_7460_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder(v_libs_7452_, v_a_7453_, v_a_7454_, v_a_7455_, v_a_7456_, v_a_7457_, v_a_7458_);
lean_dec_ref(v_a_7457_);
lean_dec(v_a_7456_);
lean_dec(v_a_7455_);
lean_dec(v_a_7454_);
lean_dec_ref(v_a_7453_);
lean_dec_ref(v_libs_7452_);
return v_res_7460_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0(lean_object* v_objs_7461_, lean_object* v_weakArgs_7462_, lean_object* v_traceArgs_7463_, lean_object* v_libFile_7464_, lean_object* v_linker_7465_, lean_object* v_libs_7466_, lean_object* v___y_7467_, lean_object* v___y_7468_, lean_object* v___y_7469_, lean_object* v___y_7470_, lean_object* v___y_7471_, lean_object* v___y_7472_){
_start:
{
lean_object* v_log_7474_; uint8_t v_action_7475_; uint8_t v_wantsRebuild_7476_; lean_object* v_trace_7477_; lean_object* v_buildTime_7478_; lean_object* v___x_7480_; uint8_t v_isShared_7481_; uint8_t v_isSharedCheck_7510_; 
v_log_7474_ = lean_ctor_get(v___y_7472_, 0);
v_action_7475_ = lean_ctor_get_uint8(v___y_7472_, sizeof(void*)*3);
v_wantsRebuild_7476_ = lean_ctor_get_uint8(v___y_7472_, sizeof(void*)*3 + 1);
v_trace_7477_ = lean_ctor_get(v___y_7472_, 1);
v_buildTime_7478_ = lean_ctor_get(v___y_7472_, 2);
v_isSharedCheck_7510_ = !lean_is_exclusive(v___y_7472_);
if (v_isSharedCheck_7510_ == 0)
{
v___x_7480_ = v___y_7472_;
v_isShared_7481_ = v_isSharedCheck_7510_;
goto v_resetjp_7479_;
}
else
{
lean_inc(v_buildTime_7478_);
lean_inc(v_trace_7477_);
lean_inc(v_log_7474_);
lean_dec(v___y_7472_);
v___x_7480_ = lean_box(0);
v_isShared_7481_ = v_isSharedCheck_7510_;
goto v_resetjp_7479_;
}
v_resetjp_7479_:
{
lean_object* v___x_7482_; lean_object* v___x_7483_; lean_object* v___x_7484_; lean_object* v___x_7485_; 
v___x_7482_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7461_, v_libs_7466_);
v___x_7483_ = l_Array_append___redArg(v___x_7482_, v_weakArgs_7462_);
v___x_7484_ = l_Array_append___redArg(v___x_7483_, v_traceArgs_7463_);
v___x_7485_ = l_Lake_compileSharedLib(v_libFile_7464_, v___x_7484_, v_linker_7465_, v_log_7474_);
lean_dec_ref(v___x_7484_);
if (lean_obj_tag(v___x_7485_) == 0)
{
lean_object* v_a_7486_; lean_object* v_a_7487_; lean_object* v___x_7489_; uint8_t v_isShared_7490_; uint8_t v_isSharedCheck_7497_; 
v_a_7486_ = lean_ctor_get(v___x_7485_, 0);
v_a_7487_ = lean_ctor_get(v___x_7485_, 1);
v_isSharedCheck_7497_ = !lean_is_exclusive(v___x_7485_);
if (v_isSharedCheck_7497_ == 0)
{
v___x_7489_ = v___x_7485_;
v_isShared_7490_ = v_isSharedCheck_7497_;
goto v_resetjp_7488_;
}
else
{
lean_inc(v_a_7487_);
lean_inc(v_a_7486_);
lean_dec(v___x_7485_);
v___x_7489_ = lean_box(0);
v_isShared_7490_ = v_isSharedCheck_7497_;
goto v_resetjp_7488_;
}
v_resetjp_7488_:
{
lean_object* v___x_7492_; 
if (v_isShared_7481_ == 0)
{
lean_ctor_set(v___x_7480_, 0, v_a_7487_);
v___x_7492_ = v___x_7480_;
goto v_reusejp_7491_;
}
else
{
lean_object* v_reuseFailAlloc_7496_; 
v_reuseFailAlloc_7496_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7496_, 0, v_a_7487_);
lean_ctor_set(v_reuseFailAlloc_7496_, 1, v_trace_7477_);
lean_ctor_set(v_reuseFailAlloc_7496_, 2, v_buildTime_7478_);
lean_ctor_set_uint8(v_reuseFailAlloc_7496_, sizeof(void*)*3, v_action_7475_);
lean_ctor_set_uint8(v_reuseFailAlloc_7496_, sizeof(void*)*3 + 1, v_wantsRebuild_7476_);
v___x_7492_ = v_reuseFailAlloc_7496_;
goto v_reusejp_7491_;
}
v_reusejp_7491_:
{
lean_object* v___x_7494_; 
if (v_isShared_7490_ == 0)
{
lean_ctor_set(v___x_7489_, 1, v___x_7492_);
v___x_7494_ = v___x_7489_;
goto v_reusejp_7493_;
}
else
{
lean_object* v_reuseFailAlloc_7495_; 
v_reuseFailAlloc_7495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7495_, 0, v_a_7486_);
lean_ctor_set(v_reuseFailAlloc_7495_, 1, v___x_7492_);
v___x_7494_ = v_reuseFailAlloc_7495_;
goto v_reusejp_7493_;
}
v_reusejp_7493_:
{
return v___x_7494_;
}
}
}
}
else
{
lean_object* v_a_7498_; lean_object* v_a_7499_; lean_object* v___x_7501_; uint8_t v_isShared_7502_; uint8_t v_isSharedCheck_7509_; 
v_a_7498_ = lean_ctor_get(v___x_7485_, 0);
v_a_7499_ = lean_ctor_get(v___x_7485_, 1);
v_isSharedCheck_7509_ = !lean_is_exclusive(v___x_7485_);
if (v_isSharedCheck_7509_ == 0)
{
v___x_7501_ = v___x_7485_;
v_isShared_7502_ = v_isSharedCheck_7509_;
goto v_resetjp_7500_;
}
else
{
lean_inc(v_a_7499_);
lean_inc(v_a_7498_);
lean_dec(v___x_7485_);
v___x_7501_ = lean_box(0);
v_isShared_7502_ = v_isSharedCheck_7509_;
goto v_resetjp_7500_;
}
v_resetjp_7500_:
{
lean_object* v___x_7504_; 
if (v_isShared_7481_ == 0)
{
lean_ctor_set(v___x_7480_, 0, v_a_7499_);
v___x_7504_ = v___x_7480_;
goto v_reusejp_7503_;
}
else
{
lean_object* v_reuseFailAlloc_7508_; 
v_reuseFailAlloc_7508_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7508_, 0, v_a_7499_);
lean_ctor_set(v_reuseFailAlloc_7508_, 1, v_trace_7477_);
lean_ctor_set(v_reuseFailAlloc_7508_, 2, v_buildTime_7478_);
lean_ctor_set_uint8(v_reuseFailAlloc_7508_, sizeof(void*)*3, v_action_7475_);
lean_ctor_set_uint8(v_reuseFailAlloc_7508_, sizeof(void*)*3 + 1, v_wantsRebuild_7476_);
v___x_7504_ = v_reuseFailAlloc_7508_;
goto v_reusejp_7503_;
}
v_reusejp_7503_:
{
lean_object* v___x_7506_; 
if (v_isShared_7502_ == 0)
{
lean_ctor_set(v___x_7501_, 1, v___x_7504_);
v___x_7506_ = v___x_7501_;
goto v_reusejp_7505_;
}
else
{
lean_object* v_reuseFailAlloc_7507_; 
v_reuseFailAlloc_7507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7507_, 0, v_a_7498_);
lean_ctor_set(v_reuseFailAlloc_7507_, 1, v___x_7504_);
v___x_7506_ = v_reuseFailAlloc_7507_;
goto v_reusejp_7505_;
}
v_reusejp_7505_:
{
return v___x_7506_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object* v_objs_7511_, lean_object* v_weakArgs_7512_, lean_object* v_traceArgs_7513_, lean_object* v_libFile_7514_, lean_object* v_linker_7515_, lean_object* v_libs_7516_, lean_object* v___y_7517_, lean_object* v___y_7518_, lean_object* v___y_7519_, lean_object* v___y_7520_, lean_object* v___y_7521_, lean_object* v___y_7522_, lean_object* v___y_7523_){
_start:
{
lean_object* v_res_7524_; 
v_res_7524_ = l_Lake_buildSharedLib___lam__0(v_objs_7511_, v_weakArgs_7512_, v_traceArgs_7513_, v_libFile_7514_, v_linker_7515_, v_libs_7516_, v___y_7517_, v___y_7518_, v___y_7519_, v___y_7520_, v___y_7521_, v___y_7522_);
lean_dec_ref(v___y_7521_);
lean_dec(v___y_7520_);
lean_dec(v___y_7519_);
lean_dec(v___y_7518_);
lean_dec_ref(v___y_7517_);
lean_dec_ref(v_libs_7516_);
lean_dec_ref(v_traceArgs_7513_);
lean_dec_ref(v_weakArgs_7512_);
lean_dec_ref(v_objs_7511_);
return v_res_7524_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1(uint8_t v_linkDeps_7525_, lean_object* v___x_7526_, lean_object* v___f_7527_, lean_object* v_libs_7528_, lean_object* v___y_7529_, lean_object* v___y_7530_, lean_object* v___y_7531_, lean_object* v___y_7532_, lean_object* v___y_7533_, lean_object* v___y_7534_){
_start:
{
if (v_linkDeps_7525_ == 0)
{
lean_object* v___x_7536_; lean_object* v___x_7537_; 
v___x_7536_ = lean_mk_empty_array_with_capacity(v___x_7526_);
v___x_7537_ = lean_apply_8(v___f_7527_, v___x_7536_, v___y_7529_, v___y_7530_, v___y_7531_, v___y_7532_, v___y_7533_, v___y_7534_, lean_box(0));
return v___x_7537_;
}
else
{
lean_object* v___x_7538_; 
v___x_7538_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7528_, v___y_7534_);
if (lean_obj_tag(v___x_7538_) == 0)
{
lean_object* v_a_7539_; lean_object* v_a_7540_; lean_object* v___x_7541_; 
v_a_7539_ = lean_ctor_get(v___x_7538_, 0);
lean_inc(v_a_7539_);
v_a_7540_ = lean_ctor_get(v___x_7538_, 1);
lean_inc(v_a_7540_);
lean_dec_ref(v___x_7538_);
v___x_7541_ = lean_apply_8(v___f_7527_, v_a_7539_, v___y_7529_, v___y_7530_, v___y_7531_, v___y_7532_, v___y_7533_, v_a_7540_, lean_box(0));
return v___x_7541_;
}
else
{
lean_object* v_a_7542_; lean_object* v_a_7543_; lean_object* v___x_7545_; uint8_t v_isShared_7546_; uint8_t v_isSharedCheck_7550_; 
lean_dec_ref(v___y_7533_);
lean_dec(v___y_7532_);
lean_dec(v___y_7531_);
lean_dec(v___y_7530_);
lean_dec_ref(v___y_7529_);
lean_dec_ref(v___f_7527_);
v_a_7542_ = lean_ctor_get(v___x_7538_, 0);
v_a_7543_ = lean_ctor_get(v___x_7538_, 1);
v_isSharedCheck_7550_ = !lean_is_exclusive(v___x_7538_);
if (v_isSharedCheck_7550_ == 0)
{
v___x_7545_ = v___x_7538_;
v_isShared_7546_ = v_isSharedCheck_7550_;
goto v_resetjp_7544_;
}
else
{
lean_inc(v_a_7543_);
lean_inc(v_a_7542_);
lean_dec(v___x_7538_);
v___x_7545_ = lean_box(0);
v_isShared_7546_ = v_isSharedCheck_7550_;
goto v_resetjp_7544_;
}
v_resetjp_7544_:
{
lean_object* v___x_7548_; 
if (v_isShared_7546_ == 0)
{
v___x_7548_ = v___x_7545_;
goto v_reusejp_7547_;
}
else
{
lean_object* v_reuseFailAlloc_7549_; 
v_reuseFailAlloc_7549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7549_, 0, v_a_7542_);
lean_ctor_set(v_reuseFailAlloc_7549_, 1, v_a_7543_);
v___x_7548_ = v_reuseFailAlloc_7549_;
goto v_reusejp_7547_;
}
v_reusejp_7547_:
{
return v___x_7548_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1___boxed(lean_object* v_linkDeps_7551_, lean_object* v___x_7552_, lean_object* v___f_7553_, lean_object* v_libs_7554_, lean_object* v___y_7555_, lean_object* v___y_7556_, lean_object* v___y_7557_, lean_object* v___y_7558_, lean_object* v___y_7559_, lean_object* v___y_7560_, lean_object* v___y_7561_){
_start:
{
uint8_t v_linkDeps_boxed_7562_; lean_object* v_res_7563_; 
v_linkDeps_boxed_7562_ = lean_unbox(v_linkDeps_7551_);
v_res_7563_ = l_Lake_buildSharedLib___lam__1(v_linkDeps_boxed_7562_, v___x_7552_, v___f_7553_, v_libs_7554_, v___y_7555_, v___y_7556_, v___y_7557_, v___y_7558_, v___y_7559_, v___y_7560_);
lean_dec_ref(v_libs_7554_);
lean_dec(v___x_7552_);
return v_res_7563_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2(lean_object* v_traceArgs_7564_, lean_object* v_extraDepTrace_7565_, uint8_t v_linkDeps_7566_, lean_object* v___f_7567_, lean_object* v_libFile_7568_, lean_object* v_libName_7569_, uint8_t v_plugin_7570_, lean_object* v_libs_7571_, lean_object* v___y_7572_, lean_object* v___y_7573_, lean_object* v___y_7574_, lean_object* v___y_7575_, lean_object* v___y_7576_, lean_object* v___y_7577_){
_start:
{
uint64_t v___y_7580_; uint64_t v___x_7657_; lean_object* v___x_7658_; lean_object* v___x_7659_; uint8_t v___x_7660_; 
v___x_7657_ = l_Lake_Hash_nil;
v___x_7658_ = lean_unsigned_to_nat(0u);
v___x_7659_ = lean_array_get_size(v_traceArgs_7564_);
v___x_7660_ = lean_nat_dec_lt(v___x_7658_, v___x_7659_);
if (v___x_7660_ == 0)
{
v___y_7580_ = v___x_7657_;
goto v___jp_7579_;
}
else
{
uint8_t v___x_7661_; 
v___x_7661_ = lean_nat_dec_le(v___x_7659_, v___x_7659_);
if (v___x_7661_ == 0)
{
if (v___x_7660_ == 0)
{
v___y_7580_ = v___x_7657_;
goto v___jp_7579_;
}
else
{
size_t v___x_7662_; size_t v___x_7663_; uint64_t v___x_7664_; 
v___x_7662_ = ((size_t)0ULL);
v___x_7663_ = lean_usize_of_nat(v___x_7659_);
v___x_7664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7564_, v___x_7662_, v___x_7663_, v___x_7657_);
v___y_7580_ = v___x_7664_;
goto v___jp_7579_;
}
}
else
{
size_t v___x_7665_; size_t v___x_7666_; uint64_t v___x_7667_; 
v___x_7665_ = ((size_t)0ULL);
v___x_7666_ = lean_usize_of_nat(v___x_7659_);
v___x_7667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7564_, v___x_7665_, v___x_7666_, v___x_7657_);
v___y_7580_ = v___x_7667_;
goto v___jp_7579_;
}
}
v___jp_7579_:
{
lean_object* v_log_7581_; uint8_t v_action_7582_; uint8_t v_wantsRebuild_7583_; lean_object* v_trace_7584_; lean_object* v_buildTime_7585_; lean_object* v___x_7587_; uint8_t v_isShared_7588_; uint8_t v_isSharedCheck_7656_; 
v_log_7581_ = lean_ctor_get(v___y_7577_, 0);
v_action_7582_ = lean_ctor_get_uint8(v___y_7577_, sizeof(void*)*3);
v_wantsRebuild_7583_ = lean_ctor_get_uint8(v___y_7577_, sizeof(void*)*3 + 1);
v_trace_7584_ = lean_ctor_get(v___y_7577_, 1);
v_buildTime_7585_ = lean_ctor_get(v___y_7577_, 2);
v_isSharedCheck_7656_ = !lean_is_exclusive(v___y_7577_);
if (v_isSharedCheck_7656_ == 0)
{
v___x_7587_ = v___y_7577_;
v_isShared_7588_ = v_isSharedCheck_7656_;
goto v_resetjp_7586_;
}
else
{
lean_inc(v_buildTime_7585_);
lean_inc(v_trace_7584_);
lean_inc(v_log_7581_);
lean_dec(v___y_7577_);
v___x_7587_ = lean_box(0);
v_isShared_7588_ = v_isSharedCheck_7656_;
goto v_resetjp_7586_;
}
v_resetjp_7586_:
{
lean_object* v___x_7589_; lean_object* v___x_7590_; lean_object* v___x_7591_; lean_object* v___x_7592_; lean_object* v___x_7593_; lean_object* v___x_7594_; lean_object* v___x_7595_; lean_object* v___x_7596_; lean_object* v___x_7597_; lean_object* v___x_7598_; lean_object* v___x_7599_; lean_object* v___x_7600_; lean_object* v___x_7601_; lean_object* v___x_7603_; 
v___x_7589_ = lean_unsigned_to_nat(0u);
v___x_7590_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_7591_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_7592_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_7593_ = lean_array_to_list(v_traceArgs_7564_);
v___x_7594_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_7593_);
lean_dec(v___x_7593_);
v___x_7595_ = lean_string_append(v___x_7592_, v___x_7594_);
lean_dec_ref(v___x_7594_);
v___x_7596_ = lean_string_append(v___x_7591_, v___x_7595_);
lean_dec_ref(v___x_7595_);
v___x_7597_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_7598_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_7598_, 0, v___x_7596_);
lean_ctor_set(v___x_7598_, 1, v___x_7590_);
lean_ctor_set(v___x_7598_, 2, v___x_7597_);
lean_ctor_set_uint64(v___x_7598_, sizeof(void*)*3, v___y_7580_);
v___x_7599_ = l_Lake_BuildTrace_mix(v_trace_7584_, v___x_7598_);
v___x_7600_ = l_Lake_platformTrace;
v___x_7601_ = l_Lake_BuildTrace_mix(v___x_7599_, v___x_7600_);
if (v_isShared_7588_ == 0)
{
lean_ctor_set(v___x_7587_, 1, v___x_7601_);
v___x_7603_ = v___x_7587_;
goto v_reusejp_7602_;
}
else
{
lean_object* v_reuseFailAlloc_7655_; 
v_reuseFailAlloc_7655_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7655_, 0, v_log_7581_);
lean_ctor_set(v_reuseFailAlloc_7655_, 1, v___x_7601_);
lean_ctor_set(v_reuseFailAlloc_7655_, 2, v_buildTime_7585_);
lean_ctor_set_uint8(v_reuseFailAlloc_7655_, sizeof(void*)*3, v_action_7582_);
lean_ctor_set_uint8(v_reuseFailAlloc_7655_, sizeof(void*)*3 + 1, v_wantsRebuild_7583_);
v___x_7603_ = v_reuseFailAlloc_7655_;
goto v_reusejp_7602_;
}
v_reusejp_7602_:
{
lean_object* v___x_7604_; 
lean_inc_ref(v___y_7576_);
lean_inc(v___y_7575_);
lean_inc(v___y_7574_);
lean_inc(v___y_7573_);
lean_inc_ref(v___y_7572_);
v___x_7604_ = lean_apply_7(v_extraDepTrace_7565_, v___y_7572_, v___y_7573_, v___y_7574_, v___y_7575_, v___y_7576_, v___x_7603_, lean_box(0));
if (lean_obj_tag(v___x_7604_) == 0)
{
lean_object* v_a_7605_; lean_object* v_a_7606_; lean_object* v_log_7607_; uint8_t v_action_7608_; uint8_t v_wantsRebuild_7609_; lean_object* v_trace_7610_; lean_object* v_buildTime_7611_; lean_object* v___x_7613_; uint8_t v_isShared_7614_; uint8_t v_isSharedCheck_7645_; 
v_a_7605_ = lean_ctor_get(v___x_7604_, 1);
lean_inc(v_a_7605_);
v_a_7606_ = lean_ctor_get(v___x_7604_, 0);
lean_inc(v_a_7606_);
lean_dec_ref(v___x_7604_);
v_log_7607_ = lean_ctor_get(v_a_7605_, 0);
v_action_7608_ = lean_ctor_get_uint8(v_a_7605_, sizeof(void*)*3);
v_wantsRebuild_7609_ = lean_ctor_get_uint8(v_a_7605_, sizeof(void*)*3 + 1);
v_trace_7610_ = lean_ctor_get(v_a_7605_, 1);
v_buildTime_7611_ = lean_ctor_get(v_a_7605_, 2);
v_isSharedCheck_7645_ = !lean_is_exclusive(v_a_7605_);
if (v_isSharedCheck_7645_ == 0)
{
v___x_7613_ = v_a_7605_;
v_isShared_7614_ = v_isSharedCheck_7645_;
goto v_resetjp_7612_;
}
else
{
lean_inc(v_buildTime_7611_);
lean_inc(v_trace_7610_);
lean_inc(v_log_7607_);
lean_dec(v_a_7605_);
v___x_7613_ = lean_box(0);
v_isShared_7614_ = v_isSharedCheck_7645_;
goto v_resetjp_7612_;
}
v_resetjp_7612_:
{
lean_object* v___x_7615_; lean_object* v___y_7616_; lean_object* v___x_7617_; lean_object* v___x_7619_; 
v___x_7615_ = lean_box(v_linkDeps_7566_);
lean_inc_ref(v_libs_7571_);
v___y_7616_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__1___boxed), 11, 4);
lean_closure_set(v___y_7616_, 0, v___x_7615_);
lean_closure_set(v___y_7616_, 1, v___x_7589_);
lean_closure_set(v___y_7616_, 2, v___f_7567_);
lean_closure_set(v___y_7616_, 3, v_libs_7571_);
v___x_7617_ = l_Lake_BuildTrace_mix(v_trace_7610_, v_a_7606_);
if (v_isShared_7614_ == 0)
{
lean_ctor_set(v___x_7613_, 1, v___x_7617_);
v___x_7619_ = v___x_7613_;
goto v_reusejp_7618_;
}
else
{
lean_object* v_reuseFailAlloc_7644_; 
v_reuseFailAlloc_7644_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7644_, 0, v_log_7607_);
lean_ctor_set(v_reuseFailAlloc_7644_, 1, v___x_7617_);
lean_ctor_set(v_reuseFailAlloc_7644_, 2, v_buildTime_7611_);
lean_ctor_set_uint8(v_reuseFailAlloc_7644_, sizeof(void*)*3, v_action_7608_);
lean_ctor_set_uint8(v_reuseFailAlloc_7644_, sizeof(void*)*3 + 1, v_wantsRebuild_7609_);
v___x_7619_ = v_reuseFailAlloc_7644_;
goto v_reusejp_7618_;
}
v_reusejp_7618_:
{
uint8_t v___x_7620_; uint8_t v___x_7621_; lean_object* v___x_7622_; lean_object* v___x_7623_; 
v___x_7620_ = 1;
v___x_7621_ = 0;
v___x_7622_ = l_Lake_sharedLibExt;
v___x_7623_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_7568_, v___y_7616_, v___x_7621_, v___x_7622_, v___x_7620_, v___x_7621_, v___x_7621_, v___y_7572_, v___y_7573_, v___y_7574_, v___y_7575_, v___y_7576_, v___x_7619_);
if (lean_obj_tag(v___x_7623_) == 0)
{
lean_object* v_a_7624_; lean_object* v_a_7625_; lean_object* v___x_7627_; uint8_t v_isShared_7628_; uint8_t v_isSharedCheck_7634_; 
v_a_7624_ = lean_ctor_get(v___x_7623_, 0);
v_a_7625_ = lean_ctor_get(v___x_7623_, 1);
v_isSharedCheck_7634_ = !lean_is_exclusive(v___x_7623_);
if (v_isSharedCheck_7634_ == 0)
{
v___x_7627_ = v___x_7623_;
v_isShared_7628_ = v_isSharedCheck_7634_;
goto v_resetjp_7626_;
}
else
{
lean_inc(v_a_7625_);
lean_inc(v_a_7624_);
lean_dec(v___x_7623_);
v___x_7627_ = lean_box(0);
v_isShared_7628_ = v_isSharedCheck_7634_;
goto v_resetjp_7626_;
}
v_resetjp_7626_:
{
lean_object* v_path_7629_; lean_object* v___x_7630_; lean_object* v___x_7632_; 
v_path_7629_ = lean_ctor_get(v_a_7624_, 1);
lean_inc_ref(v_path_7629_);
lean_dec(v_a_7624_);
v___x_7630_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_7630_, 0, v_path_7629_);
lean_ctor_set(v___x_7630_, 1, v_libName_7569_);
lean_ctor_set(v___x_7630_, 2, v_libs_7571_);
lean_ctor_set_uint8(v___x_7630_, sizeof(void*)*3, v_plugin_7570_);
if (v_isShared_7628_ == 0)
{
lean_ctor_set(v___x_7627_, 0, v___x_7630_);
v___x_7632_ = v___x_7627_;
goto v_reusejp_7631_;
}
else
{
lean_object* v_reuseFailAlloc_7633_; 
v_reuseFailAlloc_7633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7633_, 0, v___x_7630_);
lean_ctor_set(v_reuseFailAlloc_7633_, 1, v_a_7625_);
v___x_7632_ = v_reuseFailAlloc_7633_;
goto v_reusejp_7631_;
}
v_reusejp_7631_:
{
return v___x_7632_;
}
}
}
else
{
lean_object* v_a_7635_; lean_object* v_a_7636_; lean_object* v___x_7638_; uint8_t v_isShared_7639_; uint8_t v_isSharedCheck_7643_; 
lean_dec_ref(v_libs_7571_);
lean_dec_ref(v_libName_7569_);
v_a_7635_ = lean_ctor_get(v___x_7623_, 0);
v_a_7636_ = lean_ctor_get(v___x_7623_, 1);
v_isSharedCheck_7643_ = !lean_is_exclusive(v___x_7623_);
if (v_isSharedCheck_7643_ == 0)
{
v___x_7638_ = v___x_7623_;
v_isShared_7639_ = v_isSharedCheck_7643_;
goto v_resetjp_7637_;
}
else
{
lean_inc(v_a_7636_);
lean_inc(v_a_7635_);
lean_dec(v___x_7623_);
v___x_7638_ = lean_box(0);
v_isShared_7639_ = v_isSharedCheck_7643_;
goto v_resetjp_7637_;
}
v_resetjp_7637_:
{
lean_object* v___x_7641_; 
if (v_isShared_7639_ == 0)
{
v___x_7641_ = v___x_7638_;
goto v_reusejp_7640_;
}
else
{
lean_object* v_reuseFailAlloc_7642_; 
v_reuseFailAlloc_7642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7642_, 0, v_a_7635_);
lean_ctor_set(v_reuseFailAlloc_7642_, 1, v_a_7636_);
v___x_7641_ = v_reuseFailAlloc_7642_;
goto v_reusejp_7640_;
}
v_reusejp_7640_:
{
return v___x_7641_;
}
}
}
}
}
}
else
{
lean_object* v_a_7646_; lean_object* v_a_7647_; lean_object* v___x_7649_; uint8_t v_isShared_7650_; uint8_t v_isSharedCheck_7654_; 
lean_dec_ref(v___y_7576_);
lean_dec(v___y_7575_);
lean_dec(v___y_7574_);
lean_dec(v___y_7573_);
lean_dec_ref(v___y_7572_);
lean_dec_ref(v_libs_7571_);
lean_dec_ref(v_libName_7569_);
lean_dec_ref(v_libFile_7568_);
lean_dec_ref(v___f_7567_);
v_a_7646_ = lean_ctor_get(v___x_7604_, 0);
v_a_7647_ = lean_ctor_get(v___x_7604_, 1);
v_isSharedCheck_7654_ = !lean_is_exclusive(v___x_7604_);
if (v_isSharedCheck_7654_ == 0)
{
v___x_7649_ = v___x_7604_;
v_isShared_7650_ = v_isSharedCheck_7654_;
goto v_resetjp_7648_;
}
else
{
lean_inc(v_a_7647_);
lean_inc(v_a_7646_);
lean_dec(v___x_7604_);
v___x_7649_ = lean_box(0);
v_isShared_7650_ = v_isSharedCheck_7654_;
goto v_resetjp_7648_;
}
v_resetjp_7648_:
{
lean_object* v___x_7652_; 
if (v_isShared_7650_ == 0)
{
v___x_7652_ = v___x_7649_;
goto v_reusejp_7651_;
}
else
{
lean_object* v_reuseFailAlloc_7653_; 
v_reuseFailAlloc_7653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7653_, 0, v_a_7646_);
lean_ctor_set(v_reuseFailAlloc_7653_, 1, v_a_7647_);
v___x_7652_ = v_reuseFailAlloc_7653_;
goto v_reusejp_7651_;
}
v_reusejp_7651_:
{
return v___x_7652_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2___boxed(lean_object* v_traceArgs_7668_, lean_object* v_extraDepTrace_7669_, lean_object* v_linkDeps_7670_, lean_object* v___f_7671_, lean_object* v_libFile_7672_, lean_object* v_libName_7673_, lean_object* v_plugin_7674_, lean_object* v_libs_7675_, lean_object* v___y_7676_, lean_object* v___y_7677_, lean_object* v___y_7678_, lean_object* v___y_7679_, lean_object* v___y_7680_, lean_object* v___y_7681_, lean_object* v___y_7682_){
_start:
{
uint8_t v_linkDeps_boxed_7683_; uint8_t v_plugin_boxed_7684_; lean_object* v_res_7685_; 
v_linkDeps_boxed_7683_ = lean_unbox(v_linkDeps_7670_);
v_plugin_boxed_7684_ = lean_unbox(v_plugin_7674_);
v_res_7685_ = l_Lake_buildSharedLib___lam__2(v_traceArgs_7668_, v_extraDepTrace_7669_, v_linkDeps_boxed_7683_, v___f_7671_, v_libFile_7672_, v_libName_7673_, v_plugin_boxed_7684_, v_libs_7675_, v___y_7676_, v___y_7677_, v___y_7678_, v___y_7679_, v___y_7680_, v___y_7681_);
return v_res_7685_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3(lean_object* v_weakArgs_7687_, lean_object* v_traceArgs_7688_, lean_object* v_libFile_7689_, lean_object* v_linker_7690_, lean_object* v_extraDepTrace_7691_, uint8_t v_linkDeps_7692_, lean_object* v_libName_7693_, uint8_t v_plugin_7694_, lean_object* v_linkLibs_7695_, lean_object* v___x_7696_, lean_object* v_objs_7697_, lean_object* v___y_7698_, lean_object* v___y_7699_, lean_object* v___y_7700_, lean_object* v___y_7701_, lean_object* v___y_7702_, lean_object* v___y_7703_){
_start:
{
lean_object* v_trace_7705_; lean_object* v___f_7706_; lean_object* v___x_7707_; lean_object* v___x_7708_; lean_object* v___f_7709_; lean_object* v___x_7710_; lean_object* v___x_7711_; lean_object* v___x_7712_; uint8_t v___x_7713_; lean_object* v___x_7714_; lean_object* v___x_7715_; 
v_trace_7705_ = lean_ctor_get(v___y_7703_, 1);
lean_inc_ref(v_libFile_7689_);
lean_inc_ref(v_traceArgs_7688_);
v___f_7706_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__0___boxed), 13, 5);
lean_closure_set(v___f_7706_, 0, v_objs_7697_);
lean_closure_set(v___f_7706_, 1, v_weakArgs_7687_);
lean_closure_set(v___f_7706_, 2, v_traceArgs_7688_);
lean_closure_set(v___f_7706_, 3, v_libFile_7689_);
lean_closure_set(v___f_7706_, 4, v_linker_7690_);
v___x_7707_ = lean_box(v_linkDeps_7692_);
v___x_7708_ = lean_box(v_plugin_7694_);
v___f_7709_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__2___boxed), 15, 7);
lean_closure_set(v___f_7709_, 0, v_traceArgs_7688_);
lean_closure_set(v___f_7709_, 1, v_extraDepTrace_7691_);
lean_closure_set(v___f_7709_, 2, v___x_7707_);
lean_closure_set(v___f_7709_, 3, v___f_7706_);
lean_closure_set(v___f_7709_, 4, v_libFile_7689_);
lean_closure_set(v___f_7709_, 5, v_libName_7693_);
lean_closure_set(v___f_7709_, 6, v___x_7708_);
v___x_7710_ = ((lean_object*)(l_Lake_buildSharedLib___lam__3___closed__0));
v___x_7711_ = l_Lake_Job_collectArray___redArg(v_linkLibs_7695_, v___x_7710_);
v___x_7712_ = lean_unsigned_to_nat(0u);
v___x_7713_ = 0;
lean_inc_ref(v_trace_7705_);
v___x_7714_ = l_Lake_Job_mapM___redArg(v___x_7696_, v___x_7711_, v___f_7709_, v___x_7712_, v___x_7713_, v___y_7698_, v___y_7699_, v___y_7700_, v___y_7701_, v___y_7702_, v_trace_7705_);
v___x_7715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7715_, 0, v___x_7714_);
lean_ctor_set(v___x_7715_, 1, v___y_7703_);
return v___x_7715_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3___boxed(lean_object** _args){
lean_object* v_weakArgs_7716_ = _args[0];
lean_object* v_traceArgs_7717_ = _args[1];
lean_object* v_libFile_7718_ = _args[2];
lean_object* v_linker_7719_ = _args[3];
lean_object* v_extraDepTrace_7720_ = _args[4];
lean_object* v_linkDeps_7721_ = _args[5];
lean_object* v_libName_7722_ = _args[6];
lean_object* v_plugin_7723_ = _args[7];
lean_object* v_linkLibs_7724_ = _args[8];
lean_object* v___x_7725_ = _args[9];
lean_object* v_objs_7726_ = _args[10];
lean_object* v___y_7727_ = _args[11];
lean_object* v___y_7728_ = _args[12];
lean_object* v___y_7729_ = _args[13];
lean_object* v___y_7730_ = _args[14];
lean_object* v___y_7731_ = _args[15];
lean_object* v___y_7732_ = _args[16];
lean_object* v___y_7733_ = _args[17];
_start:
{
uint8_t v_linkDeps_boxed_7734_; uint8_t v_plugin_boxed_7735_; lean_object* v_res_7736_; 
v_linkDeps_boxed_7734_ = lean_unbox(v_linkDeps_7721_);
v_plugin_boxed_7735_ = lean_unbox(v_plugin_7723_);
v_res_7736_ = l_Lake_buildSharedLib___lam__3(v_weakArgs_7716_, v_traceArgs_7717_, v_libFile_7718_, v_linker_7719_, v_extraDepTrace_7720_, v_linkDeps_boxed_7734_, v_libName_7722_, v_plugin_boxed_7735_, v_linkLibs_7724_, v___x_7725_, v_objs_7726_, v___y_7727_, v___y_7728_, v___y_7729_, v___y_7730_, v___y_7731_, v___y_7732_);
lean_dec_ref(v_linkLibs_7724_);
return v_res_7736_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib(lean_object* v_libName_7738_, lean_object* v_libFile_7739_, lean_object* v_linkObjs_7740_, lean_object* v_linkLibs_7741_, lean_object* v_weakArgs_7742_, lean_object* v_traceArgs_7743_, lean_object* v_linker_7744_, lean_object* v_extraDepTrace_7745_, uint8_t v_plugin_7746_, uint8_t v_linkDeps_7747_, lean_object* v_a_7748_, lean_object* v_a_7749_, lean_object* v_a_7750_, lean_object* v_a_7751_, lean_object* v_a_7752_, lean_object* v_a_7753_){
_start:
{
lean_object* v___x_7755_; lean_object* v___x_7756_; lean_object* v___x_7757_; lean_object* v___f_7758_; lean_object* v___x_7759_; lean_object* v___x_7760_; lean_object* v___x_7761_; uint8_t v___x_7762_; lean_object* v___x_7763_; 
v___x_7755_ = l_Lake_instDataKindDynlib;
v___x_7756_ = lean_box(v_linkDeps_7747_);
v___x_7757_ = lean_box(v_plugin_7746_);
v___f_7758_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__3___boxed), 18, 10);
lean_closure_set(v___f_7758_, 0, v_weakArgs_7742_);
lean_closure_set(v___f_7758_, 1, v_traceArgs_7743_);
lean_closure_set(v___f_7758_, 2, v_libFile_7739_);
lean_closure_set(v___f_7758_, 3, v_linker_7744_);
lean_closure_set(v___f_7758_, 4, v_extraDepTrace_7745_);
lean_closure_set(v___f_7758_, 5, v___x_7756_);
lean_closure_set(v___f_7758_, 6, v_libName_7738_);
lean_closure_set(v___f_7758_, 7, v___x_7757_);
lean_closure_set(v___f_7758_, 8, v_linkLibs_7741_);
lean_closure_set(v___f_7758_, 9, v___x_7755_);
v___x_7759_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_7760_ = l_Lake_Job_collectArray___redArg(v_linkObjs_7740_, v___x_7759_);
v___x_7761_ = lean_unsigned_to_nat(0u);
v___x_7762_ = 1;
v___x_7763_ = l_Lake_Job_bindM___redArg(v___x_7755_, v___x_7760_, v___f_7758_, v___x_7761_, v___x_7762_, v_a_7748_, v_a_7749_, v_a_7750_, v_a_7751_, v_a_7752_, v_a_7753_);
return v___x_7763_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___boxed(lean_object** _args){
lean_object* v_libName_7764_ = _args[0];
lean_object* v_libFile_7765_ = _args[1];
lean_object* v_linkObjs_7766_ = _args[2];
lean_object* v_linkLibs_7767_ = _args[3];
lean_object* v_weakArgs_7768_ = _args[4];
lean_object* v_traceArgs_7769_ = _args[5];
lean_object* v_linker_7770_ = _args[6];
lean_object* v_extraDepTrace_7771_ = _args[7];
lean_object* v_plugin_7772_ = _args[8];
lean_object* v_linkDeps_7773_ = _args[9];
lean_object* v_a_7774_ = _args[10];
lean_object* v_a_7775_ = _args[11];
lean_object* v_a_7776_ = _args[12];
lean_object* v_a_7777_ = _args[13];
lean_object* v_a_7778_ = _args[14];
lean_object* v_a_7779_ = _args[15];
lean_object* v_a_7780_ = _args[16];
_start:
{
uint8_t v_plugin_boxed_7781_; uint8_t v_linkDeps_boxed_7782_; lean_object* v_res_7783_; 
v_plugin_boxed_7781_ = lean_unbox(v_plugin_7772_);
v_linkDeps_boxed_7782_ = lean_unbox(v_linkDeps_7773_);
v_res_7783_ = l_Lake_buildSharedLib(v_libName_7764_, v_libFile_7765_, v_linkObjs_7766_, v_linkLibs_7767_, v_weakArgs_7768_, v_traceArgs_7769_, v_linker_7770_, v_extraDepTrace_7771_, v_plugin_boxed_7781_, v_linkDeps_boxed_7782_, v_a_7774_, v_a_7775_, v_a_7776_, v_a_7777_, v_a_7778_, v_a_7779_);
lean_dec_ref(v_linkObjs_7766_);
return v_res_7783_;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLib___lam__0___closed__0(void){
_start:
{
lean_object* v___x_7784_; lean_object* v___x_7785_; lean_object* v___x_7786_; lean_object* v___x_7787_; 
v___x_7784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
v___x_7785_ = lean_unsigned_to_nat(2u);
v___x_7786_ = lean_mk_empty_array_with_capacity(v___x_7785_);
v___x_7787_ = lean_array_push(v___x_7786_, v___x_7784_);
return v___x_7787_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object* v_objs_7788_, lean_object* v_weakArgs_7789_, lean_object* v_traceArgs_7790_, lean_object* v_libFile_7791_, uint8_t v_linkDeps_7792_, lean_object* v_libs_7793_, lean_object* v___y_7794_, lean_object* v___y_7795_, lean_object* v___y_7796_, lean_object* v___y_7797_, lean_object* v___y_7798_, lean_object* v___y_7799_){
_start:
{
lean_object* v_toContext_7801_; lean_object* v_lakeEnv_7802_; lean_object* v_lean_7803_; lean_object* v_libs_7805_; lean_object* v___y_7806_; 
v_toContext_7801_ = lean_ctor_get(v___y_7798_, 1);
lean_inc(v_toContext_7801_);
lean_dec_ref(v___y_7798_);
v_lakeEnv_7802_ = lean_ctor_get(v_toContext_7801_, 1);
lean_inc_ref(v_lakeEnv_7802_);
lean_dec(v_toContext_7801_);
v_lean_7803_ = lean_ctor_get(v_lakeEnv_7802_, 1);
lean_inc_ref(v_lean_7803_);
lean_dec_ref(v_lakeEnv_7802_);
if (v_linkDeps_7792_ == 0)
{
lean_object* v___x_7851_; 
v___x_7851_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1));
v_libs_7805_ = v___x_7851_;
v___y_7806_ = v___y_7799_;
goto v___jp_7804_;
}
else
{
lean_object* v___x_7852_; 
v___x_7852_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7793_, v___y_7799_);
if (lean_obj_tag(v___x_7852_) == 0)
{
lean_object* v_a_7853_; lean_object* v_a_7854_; 
v_a_7853_ = lean_ctor_get(v___x_7852_, 0);
lean_inc(v_a_7853_);
v_a_7854_ = lean_ctor_get(v___x_7852_, 1);
lean_inc(v_a_7854_);
lean_dec_ref(v___x_7852_);
v_libs_7805_ = v_a_7853_;
v___y_7806_ = v_a_7854_;
goto v___jp_7804_;
}
else
{
lean_object* v_a_7855_; lean_object* v_a_7856_; lean_object* v___x_7858_; uint8_t v_isShared_7859_; uint8_t v_isSharedCheck_7863_; 
lean_dec_ref(v_lean_7803_);
lean_dec_ref(v_libFile_7791_);
v_a_7855_ = lean_ctor_get(v___x_7852_, 0);
v_a_7856_ = lean_ctor_get(v___x_7852_, 1);
v_isSharedCheck_7863_ = !lean_is_exclusive(v___x_7852_);
if (v_isSharedCheck_7863_ == 0)
{
v___x_7858_ = v___x_7852_;
v_isShared_7859_ = v_isSharedCheck_7863_;
goto v_resetjp_7857_;
}
else
{
lean_inc(v_a_7856_);
lean_inc(v_a_7855_);
lean_dec(v___x_7852_);
v___x_7858_ = lean_box(0);
v_isShared_7859_ = v_isSharedCheck_7863_;
goto v_resetjp_7857_;
}
v_resetjp_7857_:
{
lean_object* v___x_7861_; 
if (v_isShared_7859_ == 0)
{
v___x_7861_ = v___x_7858_;
goto v_reusejp_7860_;
}
else
{
lean_object* v_reuseFailAlloc_7862_; 
v_reuseFailAlloc_7862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7862_, 0, v_a_7855_);
lean_ctor_set(v_reuseFailAlloc_7862_, 1, v_a_7856_);
v___x_7861_ = v_reuseFailAlloc_7862_;
goto v_reusejp_7860_;
}
v_reusejp_7860_:
{
return v___x_7861_;
}
}
}
}
v___jp_7804_:
{
lean_object* v_leanLibDir_7807_; lean_object* v_cc_7808_; lean_object* v_ccLinkSharedFlags_7809_; lean_object* v_log_7810_; uint8_t v_action_7811_; uint8_t v_wantsRebuild_7812_; lean_object* v_trace_7813_; lean_object* v_buildTime_7814_; lean_object* v___x_7816_; uint8_t v_isShared_7817_; uint8_t v_isSharedCheck_7850_; 
v_leanLibDir_7807_ = lean_ctor_get(v_lean_7803_, 3);
lean_inc_ref(v_leanLibDir_7807_);
v_cc_7808_ = lean_ctor_get(v_lean_7803_, 13);
lean_inc_ref(v_cc_7808_);
v_ccLinkSharedFlags_7809_ = lean_ctor_get(v_lean_7803_, 19);
lean_inc_ref(v_ccLinkSharedFlags_7809_);
lean_dec_ref(v_lean_7803_);
v_log_7810_ = lean_ctor_get(v___y_7806_, 0);
v_action_7811_ = lean_ctor_get_uint8(v___y_7806_, sizeof(void*)*3);
v_wantsRebuild_7812_ = lean_ctor_get_uint8(v___y_7806_, sizeof(void*)*3 + 1);
v_trace_7813_ = lean_ctor_get(v___y_7806_, 1);
v_buildTime_7814_ = lean_ctor_get(v___y_7806_, 2);
v_isSharedCheck_7850_ = !lean_is_exclusive(v___y_7806_);
if (v_isSharedCheck_7850_ == 0)
{
v___x_7816_ = v___y_7806_;
v_isShared_7817_ = v_isSharedCheck_7850_;
goto v_resetjp_7815_;
}
else
{
lean_inc(v_buildTime_7814_);
lean_inc(v_trace_7813_);
lean_inc(v_log_7810_);
lean_dec(v___y_7806_);
v___x_7816_ = lean_box(0);
v_isShared_7817_ = v_isSharedCheck_7850_;
goto v_resetjp_7815_;
}
v_resetjp_7815_:
{
lean_object* v___x_7818_; lean_object* v___x_7819_; lean_object* v___x_7820_; lean_object* v___x_7821_; lean_object* v___x_7822_; lean_object* v___x_7823_; lean_object* v___x_7824_; lean_object* v___x_7825_; 
v___x_7818_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7788_, v_libs_7805_);
lean_dec_ref(v_libs_7805_);
v___x_7819_ = l_Array_append___redArg(v___x_7818_, v_weakArgs_7789_);
v___x_7820_ = l_Array_append___redArg(v___x_7819_, v_traceArgs_7790_);
v___x_7821_ = lean_obj_once(&l_Lake_buildLeanSharedLib___lam__0___closed__0, &l_Lake_buildLeanSharedLib___lam__0___closed__0_once, _init_l_Lake_buildLeanSharedLib___lam__0___closed__0);
v___x_7822_ = lean_array_push(v___x_7821_, v_leanLibDir_7807_);
v___x_7823_ = l_Array_append___redArg(v___x_7820_, v___x_7822_);
lean_dec_ref(v___x_7822_);
v___x_7824_ = l_Array_append___redArg(v___x_7823_, v_ccLinkSharedFlags_7809_);
lean_dec_ref(v_ccLinkSharedFlags_7809_);
v___x_7825_ = l_Lake_compileSharedLib(v_libFile_7791_, v___x_7824_, v_cc_7808_, v_log_7810_);
lean_dec_ref(v___x_7824_);
if (lean_obj_tag(v___x_7825_) == 0)
{
lean_object* v_a_7826_; lean_object* v_a_7827_; lean_object* v___x_7829_; uint8_t v_isShared_7830_; uint8_t v_isSharedCheck_7837_; 
v_a_7826_ = lean_ctor_get(v___x_7825_, 0);
v_a_7827_ = lean_ctor_get(v___x_7825_, 1);
v_isSharedCheck_7837_ = !lean_is_exclusive(v___x_7825_);
if (v_isSharedCheck_7837_ == 0)
{
v___x_7829_ = v___x_7825_;
v_isShared_7830_ = v_isSharedCheck_7837_;
goto v_resetjp_7828_;
}
else
{
lean_inc(v_a_7827_);
lean_inc(v_a_7826_);
lean_dec(v___x_7825_);
v___x_7829_ = lean_box(0);
v_isShared_7830_ = v_isSharedCheck_7837_;
goto v_resetjp_7828_;
}
v_resetjp_7828_:
{
lean_object* v___x_7832_; 
if (v_isShared_7817_ == 0)
{
lean_ctor_set(v___x_7816_, 0, v_a_7827_);
v___x_7832_ = v___x_7816_;
goto v_reusejp_7831_;
}
else
{
lean_object* v_reuseFailAlloc_7836_; 
v_reuseFailAlloc_7836_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7836_, 0, v_a_7827_);
lean_ctor_set(v_reuseFailAlloc_7836_, 1, v_trace_7813_);
lean_ctor_set(v_reuseFailAlloc_7836_, 2, v_buildTime_7814_);
lean_ctor_set_uint8(v_reuseFailAlloc_7836_, sizeof(void*)*3, v_action_7811_);
lean_ctor_set_uint8(v_reuseFailAlloc_7836_, sizeof(void*)*3 + 1, v_wantsRebuild_7812_);
v___x_7832_ = v_reuseFailAlloc_7836_;
goto v_reusejp_7831_;
}
v_reusejp_7831_:
{
lean_object* v___x_7834_; 
if (v_isShared_7830_ == 0)
{
lean_ctor_set(v___x_7829_, 1, v___x_7832_);
v___x_7834_ = v___x_7829_;
goto v_reusejp_7833_;
}
else
{
lean_object* v_reuseFailAlloc_7835_; 
v_reuseFailAlloc_7835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7835_, 0, v_a_7826_);
lean_ctor_set(v_reuseFailAlloc_7835_, 1, v___x_7832_);
v___x_7834_ = v_reuseFailAlloc_7835_;
goto v_reusejp_7833_;
}
v_reusejp_7833_:
{
return v___x_7834_;
}
}
}
}
else
{
lean_object* v_a_7838_; lean_object* v_a_7839_; lean_object* v___x_7841_; uint8_t v_isShared_7842_; uint8_t v_isSharedCheck_7849_; 
v_a_7838_ = lean_ctor_get(v___x_7825_, 0);
v_a_7839_ = lean_ctor_get(v___x_7825_, 1);
v_isSharedCheck_7849_ = !lean_is_exclusive(v___x_7825_);
if (v_isSharedCheck_7849_ == 0)
{
v___x_7841_ = v___x_7825_;
v_isShared_7842_ = v_isSharedCheck_7849_;
goto v_resetjp_7840_;
}
else
{
lean_inc(v_a_7839_);
lean_inc(v_a_7838_);
lean_dec(v___x_7825_);
v___x_7841_ = lean_box(0);
v_isShared_7842_ = v_isSharedCheck_7849_;
goto v_resetjp_7840_;
}
v_resetjp_7840_:
{
lean_object* v___x_7844_; 
if (v_isShared_7817_ == 0)
{
lean_ctor_set(v___x_7816_, 0, v_a_7839_);
v___x_7844_ = v___x_7816_;
goto v_reusejp_7843_;
}
else
{
lean_object* v_reuseFailAlloc_7848_; 
v_reuseFailAlloc_7848_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7848_, 0, v_a_7839_);
lean_ctor_set(v_reuseFailAlloc_7848_, 1, v_trace_7813_);
lean_ctor_set(v_reuseFailAlloc_7848_, 2, v_buildTime_7814_);
lean_ctor_set_uint8(v_reuseFailAlloc_7848_, sizeof(void*)*3, v_action_7811_);
lean_ctor_set_uint8(v_reuseFailAlloc_7848_, sizeof(void*)*3 + 1, v_wantsRebuild_7812_);
v___x_7844_ = v_reuseFailAlloc_7848_;
goto v_reusejp_7843_;
}
v_reusejp_7843_:
{
lean_object* v___x_7846_; 
if (v_isShared_7842_ == 0)
{
lean_ctor_set(v___x_7841_, 1, v___x_7844_);
v___x_7846_ = v___x_7841_;
goto v_reusejp_7845_;
}
else
{
lean_object* v_reuseFailAlloc_7847_; 
v_reuseFailAlloc_7847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7847_, 0, v_a_7838_);
lean_ctor_set(v_reuseFailAlloc_7847_, 1, v___x_7844_);
v___x_7846_ = v_reuseFailAlloc_7847_;
goto v_reusejp_7845_;
}
v_reusejp_7845_:
{
return v___x_7846_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object* v_objs_7864_, lean_object* v_weakArgs_7865_, lean_object* v_traceArgs_7866_, lean_object* v_libFile_7867_, lean_object* v_linkDeps_7868_, lean_object* v_libs_7869_, lean_object* v___y_7870_, lean_object* v___y_7871_, lean_object* v___y_7872_, lean_object* v___y_7873_, lean_object* v___y_7874_, lean_object* v___y_7875_, lean_object* v___y_7876_){
_start:
{
uint8_t v_linkDeps_boxed_7877_; lean_object* v_res_7878_; 
v_linkDeps_boxed_7877_ = lean_unbox(v_linkDeps_7868_);
v_res_7878_ = l_Lake_buildLeanSharedLib___lam__0(v_objs_7864_, v_weakArgs_7865_, v_traceArgs_7866_, v_libFile_7867_, v_linkDeps_boxed_7877_, v_libs_7869_, v___y_7870_, v___y_7871_, v___y_7872_, v___y_7873_, v___y_7874_, v___y_7875_);
lean_dec(v___y_7873_);
lean_dec(v___y_7872_);
lean_dec(v___y_7871_);
lean_dec_ref(v___y_7870_);
lean_dec_ref(v_libs_7869_);
lean_dec_ref(v_traceArgs_7866_);
lean_dec_ref(v_weakArgs_7865_);
lean_dec_ref(v_objs_7864_);
return v_res_7878_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object* v_objs_7879_, lean_object* v_weakArgs_7880_, lean_object* v_traceArgs_7881_, lean_object* v_libFile_7882_, uint8_t v_linkDeps_7883_, lean_object* v_libName_7884_, uint8_t v_plugin_7885_, lean_object* v_libs_7886_, lean_object* v___y_7887_, lean_object* v___y_7888_, lean_object* v___y_7889_, lean_object* v___y_7890_, lean_object* v___y_7891_, lean_object* v___y_7892_){
_start:
{
lean_object* v_log_7894_; uint8_t v_action_7895_; uint8_t v_wantsRebuild_7896_; lean_object* v_trace_7897_; lean_object* v_buildTime_7898_; lean_object* v___x_7900_; uint8_t v_isShared_7901_; uint8_t v_isSharedCheck_7958_; 
v_log_7894_ = lean_ctor_get(v___y_7892_, 0);
v_action_7895_ = lean_ctor_get_uint8(v___y_7892_, sizeof(void*)*3);
v_wantsRebuild_7896_ = lean_ctor_get_uint8(v___y_7892_, sizeof(void*)*3 + 1);
v_trace_7897_ = lean_ctor_get(v___y_7892_, 1);
v_buildTime_7898_ = lean_ctor_get(v___y_7892_, 2);
v_isSharedCheck_7958_ = !lean_is_exclusive(v___y_7892_);
if (v_isSharedCheck_7958_ == 0)
{
v___x_7900_ = v___y_7892_;
v_isShared_7901_ = v_isSharedCheck_7958_;
goto v_resetjp_7899_;
}
else
{
lean_inc(v_buildTime_7898_);
lean_inc(v_trace_7897_);
lean_inc(v_log_7894_);
lean_dec(v___y_7892_);
v___x_7900_ = lean_box(0);
v_isShared_7901_ = v_isSharedCheck_7958_;
goto v_resetjp_7899_;
}
v_resetjp_7899_:
{
lean_object* v_leanTrace_7902_; lean_object* v___x_7903_; lean_object* v___f_7904_; lean_object* v___x_7905_; uint64_t v___y_7907_; uint64_t v___x_7947_; lean_object* v___x_7948_; lean_object* v___x_7949_; uint8_t v___x_7950_; 
v_leanTrace_7902_ = lean_ctor_get(v___y_7891_, 2);
v___x_7903_ = lean_box(v_linkDeps_7883_);
lean_inc_ref(v_libs_7886_);
lean_inc_ref(v_libFile_7882_);
lean_inc_ref(v_traceArgs_7881_);
v___f_7904_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__0___boxed), 13, 6);
lean_closure_set(v___f_7904_, 0, v_objs_7879_);
lean_closure_set(v___f_7904_, 1, v_weakArgs_7880_);
lean_closure_set(v___f_7904_, 2, v_traceArgs_7881_);
lean_closure_set(v___f_7904_, 3, v_libFile_7882_);
lean_closure_set(v___f_7904_, 4, v___x_7903_);
lean_closure_set(v___f_7904_, 5, v_libs_7886_);
lean_inc_ref(v_leanTrace_7902_);
v___x_7905_ = l_Lake_BuildTrace_mix(v_trace_7897_, v_leanTrace_7902_);
v___x_7947_ = l_Lake_Hash_nil;
v___x_7948_ = lean_unsigned_to_nat(0u);
v___x_7949_ = lean_array_get_size(v_traceArgs_7881_);
v___x_7950_ = lean_nat_dec_lt(v___x_7948_, v___x_7949_);
if (v___x_7950_ == 0)
{
v___y_7907_ = v___x_7947_;
goto v___jp_7906_;
}
else
{
uint8_t v___x_7951_; 
v___x_7951_ = lean_nat_dec_le(v___x_7949_, v___x_7949_);
if (v___x_7951_ == 0)
{
if (v___x_7950_ == 0)
{
v___y_7907_ = v___x_7947_;
goto v___jp_7906_;
}
else
{
size_t v___x_7952_; size_t v___x_7953_; uint64_t v___x_7954_; 
v___x_7952_ = ((size_t)0ULL);
v___x_7953_ = lean_usize_of_nat(v___x_7949_);
v___x_7954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7881_, v___x_7952_, v___x_7953_, v___x_7947_);
v___y_7907_ = v___x_7954_;
goto v___jp_7906_;
}
}
else
{
size_t v___x_7955_; size_t v___x_7956_; uint64_t v___x_7957_; 
v___x_7955_ = ((size_t)0ULL);
v___x_7956_ = lean_usize_of_nat(v___x_7949_);
v___x_7957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7881_, v___x_7955_, v___x_7956_, v___x_7947_);
v___y_7907_ = v___x_7957_;
goto v___jp_7906_;
}
}
v___jp_7906_:
{
lean_object* v___x_7908_; lean_object* v___x_7909_; lean_object* v___x_7910_; lean_object* v___x_7911_; lean_object* v___x_7912_; lean_object* v___x_7913_; lean_object* v___x_7914_; lean_object* v___x_7915_; lean_object* v___x_7916_; lean_object* v___x_7917_; lean_object* v___x_7918_; lean_object* v___x_7919_; lean_object* v___x_7921_; 
v___x_7908_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_7909_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_7910_ = lean_array_to_list(v_traceArgs_7881_);
v___x_7911_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_7910_);
lean_dec(v___x_7910_);
v___x_7912_ = lean_string_append(v___x_7909_, v___x_7911_);
lean_dec_ref(v___x_7911_);
v___x_7913_ = lean_string_append(v___x_7908_, v___x_7912_);
lean_dec_ref(v___x_7912_);
v___x_7914_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_7915_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_7916_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_7916_, 0, v___x_7913_);
lean_ctor_set(v___x_7916_, 1, v___x_7914_);
lean_ctor_set(v___x_7916_, 2, v___x_7915_);
lean_ctor_set_uint64(v___x_7916_, sizeof(void*)*3, v___y_7907_);
v___x_7917_ = l_Lake_BuildTrace_mix(v___x_7905_, v___x_7916_);
v___x_7918_ = l_Lake_platformTrace;
v___x_7919_ = l_Lake_BuildTrace_mix(v___x_7917_, v___x_7918_);
if (v_isShared_7901_ == 0)
{
lean_ctor_set(v___x_7900_, 1, v___x_7919_);
v___x_7921_ = v___x_7900_;
goto v_reusejp_7920_;
}
else
{
lean_object* v_reuseFailAlloc_7946_; 
v_reuseFailAlloc_7946_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7946_, 0, v_log_7894_);
lean_ctor_set(v_reuseFailAlloc_7946_, 1, v___x_7919_);
lean_ctor_set(v_reuseFailAlloc_7946_, 2, v_buildTime_7898_);
lean_ctor_set_uint8(v_reuseFailAlloc_7946_, sizeof(void*)*3, v_action_7895_);
lean_ctor_set_uint8(v_reuseFailAlloc_7946_, sizeof(void*)*3 + 1, v_wantsRebuild_7896_);
v___x_7921_ = v_reuseFailAlloc_7946_;
goto v_reusejp_7920_;
}
v_reusejp_7920_:
{
uint8_t v___x_7922_; lean_object* v___x_7923_; uint8_t v___x_7924_; lean_object* v___x_7925_; 
v___x_7922_ = 0;
v___x_7923_ = l_Lake_sharedLibExt;
v___x_7924_ = 1;
v___x_7925_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_7882_, v___f_7904_, v___x_7922_, v___x_7923_, v___x_7924_, v___x_7922_, v___x_7922_, v___y_7887_, v___y_7888_, v___y_7889_, v___y_7890_, v___y_7891_, v___x_7921_);
if (lean_obj_tag(v___x_7925_) == 0)
{
lean_object* v_a_7926_; lean_object* v_a_7927_; lean_object* v___x_7929_; uint8_t v_isShared_7930_; uint8_t v_isSharedCheck_7936_; 
v_a_7926_ = lean_ctor_get(v___x_7925_, 0);
v_a_7927_ = lean_ctor_get(v___x_7925_, 1);
v_isSharedCheck_7936_ = !lean_is_exclusive(v___x_7925_);
if (v_isSharedCheck_7936_ == 0)
{
v___x_7929_ = v___x_7925_;
v_isShared_7930_ = v_isSharedCheck_7936_;
goto v_resetjp_7928_;
}
else
{
lean_inc(v_a_7927_);
lean_inc(v_a_7926_);
lean_dec(v___x_7925_);
v___x_7929_ = lean_box(0);
v_isShared_7930_ = v_isSharedCheck_7936_;
goto v_resetjp_7928_;
}
v_resetjp_7928_:
{
lean_object* v_path_7931_; lean_object* v___x_7932_; lean_object* v___x_7934_; 
v_path_7931_ = lean_ctor_get(v_a_7926_, 1);
lean_inc_ref(v_path_7931_);
lean_dec(v_a_7926_);
v___x_7932_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_7932_, 0, v_path_7931_);
lean_ctor_set(v___x_7932_, 1, v_libName_7884_);
lean_ctor_set(v___x_7932_, 2, v_libs_7886_);
lean_ctor_set_uint8(v___x_7932_, sizeof(void*)*3, v_plugin_7885_);
if (v_isShared_7930_ == 0)
{
lean_ctor_set(v___x_7929_, 0, v___x_7932_);
v___x_7934_ = v___x_7929_;
goto v_reusejp_7933_;
}
else
{
lean_object* v_reuseFailAlloc_7935_; 
v_reuseFailAlloc_7935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7935_, 0, v___x_7932_);
lean_ctor_set(v_reuseFailAlloc_7935_, 1, v_a_7927_);
v___x_7934_ = v_reuseFailAlloc_7935_;
goto v_reusejp_7933_;
}
v_reusejp_7933_:
{
return v___x_7934_;
}
}
}
else
{
lean_object* v_a_7937_; lean_object* v_a_7938_; lean_object* v___x_7940_; uint8_t v_isShared_7941_; uint8_t v_isSharedCheck_7945_; 
lean_dec_ref(v_libs_7886_);
lean_dec_ref(v_libName_7884_);
v_a_7937_ = lean_ctor_get(v___x_7925_, 0);
v_a_7938_ = lean_ctor_get(v___x_7925_, 1);
v_isSharedCheck_7945_ = !lean_is_exclusive(v___x_7925_);
if (v_isSharedCheck_7945_ == 0)
{
v___x_7940_ = v___x_7925_;
v_isShared_7941_ = v_isSharedCheck_7945_;
goto v_resetjp_7939_;
}
else
{
lean_inc(v_a_7938_);
lean_inc(v_a_7937_);
lean_dec(v___x_7925_);
v___x_7940_ = lean_box(0);
v_isShared_7941_ = v_isSharedCheck_7945_;
goto v_resetjp_7939_;
}
v_resetjp_7939_:
{
lean_object* v___x_7943_; 
if (v_isShared_7941_ == 0)
{
v___x_7943_ = v___x_7940_;
goto v_reusejp_7942_;
}
else
{
lean_object* v_reuseFailAlloc_7944_; 
v_reuseFailAlloc_7944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7944_, 0, v_a_7937_);
lean_ctor_set(v_reuseFailAlloc_7944_, 1, v_a_7938_);
v___x_7943_ = v_reuseFailAlloc_7944_;
goto v_reusejp_7942_;
}
v_reusejp_7942_:
{
return v___x_7943_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1___boxed(lean_object* v_objs_7959_, lean_object* v_weakArgs_7960_, lean_object* v_traceArgs_7961_, lean_object* v_libFile_7962_, lean_object* v_linkDeps_7963_, lean_object* v_libName_7964_, lean_object* v_plugin_7965_, lean_object* v_libs_7966_, lean_object* v___y_7967_, lean_object* v___y_7968_, lean_object* v___y_7969_, lean_object* v___y_7970_, lean_object* v___y_7971_, lean_object* v___y_7972_, lean_object* v___y_7973_){
_start:
{
uint8_t v_linkDeps_boxed_7974_; uint8_t v_plugin_boxed_7975_; lean_object* v_res_7976_; 
v_linkDeps_boxed_7974_ = lean_unbox(v_linkDeps_7963_);
v_plugin_boxed_7975_ = lean_unbox(v_plugin_7965_);
v_res_7976_ = l_Lake_buildLeanSharedLib___lam__1(v_objs_7959_, v_weakArgs_7960_, v_traceArgs_7961_, v_libFile_7962_, v_linkDeps_boxed_7974_, v_libName_7964_, v_plugin_boxed_7975_, v_libs_7966_, v___y_7967_, v___y_7968_, v___y_7969_, v___y_7970_, v___y_7971_, v___y_7972_);
return v_res_7976_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2(lean_object* v_weakArgs_7977_, lean_object* v_traceArgs_7978_, lean_object* v_libFile_7979_, uint8_t v_linkDeps_7980_, lean_object* v_libName_7981_, uint8_t v_plugin_7982_, lean_object* v_linkLibs_7983_, lean_object* v___x_7984_, lean_object* v_objs_7985_, lean_object* v___y_7986_, lean_object* v___y_7987_, lean_object* v___y_7988_, lean_object* v___y_7989_, lean_object* v___y_7990_, lean_object* v___y_7991_){
_start:
{
lean_object* v_trace_7993_; lean_object* v___x_7994_; lean_object* v___x_7995_; lean_object* v___f_7996_; lean_object* v___x_7997_; lean_object* v___x_7998_; lean_object* v___x_7999_; uint8_t v___x_8000_; lean_object* v___x_8001_; lean_object* v___x_8002_; 
v_trace_7993_ = lean_ctor_get(v___y_7991_, 1);
v___x_7994_ = lean_box(v_linkDeps_7980_);
v___x_7995_ = lean_box(v_plugin_7982_);
v___f_7996_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__1___boxed), 15, 7);
lean_closure_set(v___f_7996_, 0, v_objs_7985_);
lean_closure_set(v___f_7996_, 1, v_weakArgs_7977_);
lean_closure_set(v___f_7996_, 2, v_traceArgs_7978_);
lean_closure_set(v___f_7996_, 3, v_libFile_7979_);
lean_closure_set(v___f_7996_, 4, v___x_7994_);
lean_closure_set(v___f_7996_, 5, v_libName_7981_);
lean_closure_set(v___f_7996_, 6, v___x_7995_);
v___x_7997_ = ((lean_object*)(l_Lake_buildSharedLib___lam__3___closed__0));
v___x_7998_ = l_Lake_Job_collectArray___redArg(v_linkLibs_7983_, v___x_7997_);
v___x_7999_ = lean_unsigned_to_nat(0u);
v___x_8000_ = 0;
lean_inc_ref(v_trace_7993_);
v___x_8001_ = l_Lake_Job_mapM___redArg(v___x_7984_, v___x_7998_, v___f_7996_, v___x_7999_, v___x_8000_, v___y_7986_, v___y_7987_, v___y_7988_, v___y_7989_, v___y_7990_, v_trace_7993_);
v___x_8002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8002_, 0, v___x_8001_);
lean_ctor_set(v___x_8002_, 1, v___y_7991_);
return v___x_8002_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2___boxed(lean_object* v_weakArgs_8003_, lean_object* v_traceArgs_8004_, lean_object* v_libFile_8005_, lean_object* v_linkDeps_8006_, lean_object* v_libName_8007_, lean_object* v_plugin_8008_, lean_object* v_linkLibs_8009_, lean_object* v___x_8010_, lean_object* v_objs_8011_, lean_object* v___y_8012_, lean_object* v___y_8013_, lean_object* v___y_8014_, lean_object* v___y_8015_, lean_object* v___y_8016_, lean_object* v___y_8017_, lean_object* v___y_8018_){
_start:
{
uint8_t v_linkDeps_boxed_8019_; uint8_t v_plugin_boxed_8020_; lean_object* v_res_8021_; 
v_linkDeps_boxed_8019_ = lean_unbox(v_linkDeps_8006_);
v_plugin_boxed_8020_ = lean_unbox(v_plugin_8008_);
v_res_8021_ = l_Lake_buildLeanSharedLib___lam__2(v_weakArgs_8003_, v_traceArgs_8004_, v_libFile_8005_, v_linkDeps_boxed_8019_, v_libName_8007_, v_plugin_boxed_8020_, v_linkLibs_8009_, v___x_8010_, v_objs_8011_, v___y_8012_, v___y_8013_, v___y_8014_, v___y_8015_, v___y_8016_, v___y_8017_);
lean_dec_ref(v_linkLibs_8009_);
return v_res_8021_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object* v_libName_8022_, lean_object* v_libFile_8023_, lean_object* v_linkObjs_8024_, lean_object* v_linkLibs_8025_, lean_object* v_weakArgs_8026_, lean_object* v_traceArgs_8027_, uint8_t v_plugin_8028_, uint8_t v_linkDeps_8029_, lean_object* v_a_8030_, lean_object* v_a_8031_, lean_object* v_a_8032_, lean_object* v_a_8033_, lean_object* v_a_8034_, lean_object* v_a_8035_){
_start:
{
lean_object* v___x_8037_; lean_object* v___x_8038_; lean_object* v___x_8039_; lean_object* v___f_8040_; lean_object* v___x_8041_; lean_object* v___x_8042_; lean_object* v___x_8043_; uint8_t v___x_8044_; lean_object* v___x_8045_; 
v___x_8037_ = l_Lake_instDataKindDynlib;
v___x_8038_ = lean_box(v_linkDeps_8029_);
v___x_8039_ = lean_box(v_plugin_8028_);
v___f_8040_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__2___boxed), 16, 8);
lean_closure_set(v___f_8040_, 0, v_weakArgs_8026_);
lean_closure_set(v___f_8040_, 1, v_traceArgs_8027_);
lean_closure_set(v___f_8040_, 2, v_libFile_8023_);
lean_closure_set(v___f_8040_, 3, v___x_8038_);
lean_closure_set(v___f_8040_, 4, v_libName_8022_);
lean_closure_set(v___f_8040_, 5, v___x_8039_);
lean_closure_set(v___f_8040_, 6, v_linkLibs_8025_);
lean_closure_set(v___f_8040_, 7, v___x_8037_);
v___x_8041_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8042_ = l_Lake_Job_collectArray___redArg(v_linkObjs_8024_, v___x_8041_);
v___x_8043_ = lean_unsigned_to_nat(0u);
v___x_8044_ = 1;
v___x_8045_ = l_Lake_Job_bindM___redArg(v___x_8037_, v___x_8042_, v___f_8040_, v___x_8043_, v___x_8044_, v_a_8030_, v_a_8031_, v_a_8032_, v_a_8033_, v_a_8034_, v_a_8035_);
return v___x_8045_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object* v_libName_8046_, lean_object* v_libFile_8047_, lean_object* v_linkObjs_8048_, lean_object* v_linkLibs_8049_, lean_object* v_weakArgs_8050_, lean_object* v_traceArgs_8051_, lean_object* v_plugin_8052_, lean_object* v_linkDeps_8053_, lean_object* v_a_8054_, lean_object* v_a_8055_, lean_object* v_a_8056_, lean_object* v_a_8057_, lean_object* v_a_8058_, lean_object* v_a_8059_, lean_object* v_a_8060_){
_start:
{
uint8_t v_plugin_boxed_8061_; uint8_t v_linkDeps_boxed_8062_; lean_object* v_res_8063_; 
v_plugin_boxed_8061_ = lean_unbox(v_plugin_8052_);
v_linkDeps_boxed_8062_ = lean_unbox(v_linkDeps_8053_);
v_res_8063_ = l_Lake_buildLeanSharedLib(v_libName_8046_, v_libFile_8047_, v_linkObjs_8048_, v_linkLibs_8049_, v_weakArgs_8050_, v_traceArgs_8051_, v_plugin_boxed_8061_, v_linkDeps_boxed_8062_, v_a_8054_, v_a_8055_, v_a_8056_, v_a_8057_, v_a_8058_, v_a_8059_);
lean_dec_ref(v_linkObjs_8048_);
return v_res_8063_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0(lean_object* v_libs_8064_, lean_object* v_objs_8065_, lean_object* v_weakArgs_8066_, lean_object* v_traceArgs_8067_, uint8_t v_sharedLean_8068_, lean_object* v_exeFile_8069_, lean_object* v___y_8070_, lean_object* v___y_8071_, lean_object* v___y_8072_, lean_object* v___y_8073_, lean_object* v___y_8074_, lean_object* v___y_8075_){
_start:
{
lean_object* v___x_8077_; 
v___x_8077_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_8064_, v___y_8075_);
if (lean_obj_tag(v___x_8077_) == 0)
{
lean_object* v_toContext_8078_; lean_object* v_lakeEnv_8079_; lean_object* v_lean_8080_; lean_object* v_a_8081_; lean_object* v_a_8082_; lean_object* v_leanLibDir_8083_; lean_object* v_cc_8084_; lean_object* v_log_8085_; uint8_t v_action_8086_; uint8_t v_wantsRebuild_8087_; lean_object* v_trace_8088_; lean_object* v_buildTime_8089_; lean_object* v___x_8091_; uint8_t v_isShared_8092_; uint8_t v_isSharedCheck_8128_; 
v_toContext_8078_ = lean_ctor_get(v___y_8074_, 1);
lean_inc(v_toContext_8078_);
lean_dec_ref(v___y_8074_);
v_lakeEnv_8079_ = lean_ctor_get(v_toContext_8078_, 1);
lean_inc_ref(v_lakeEnv_8079_);
lean_dec(v_toContext_8078_);
v_lean_8080_ = lean_ctor_get(v_lakeEnv_8079_, 1);
lean_inc_ref(v_lean_8080_);
lean_dec_ref(v_lakeEnv_8079_);
v_a_8081_ = lean_ctor_get(v___x_8077_, 1);
lean_inc(v_a_8081_);
v_a_8082_ = lean_ctor_get(v___x_8077_, 0);
lean_inc(v_a_8082_);
lean_dec_ref(v___x_8077_);
v_leanLibDir_8083_ = lean_ctor_get(v_lean_8080_, 3);
v_cc_8084_ = lean_ctor_get(v_lean_8080_, 13);
lean_inc_ref(v_cc_8084_);
v_log_8085_ = lean_ctor_get(v_a_8081_, 0);
v_action_8086_ = lean_ctor_get_uint8(v_a_8081_, sizeof(void*)*3);
v_wantsRebuild_8087_ = lean_ctor_get_uint8(v_a_8081_, sizeof(void*)*3 + 1);
v_trace_8088_ = lean_ctor_get(v_a_8081_, 1);
v_buildTime_8089_ = lean_ctor_get(v_a_8081_, 2);
v_isSharedCheck_8128_ = !lean_is_exclusive(v_a_8081_);
if (v_isSharedCheck_8128_ == 0)
{
v___x_8091_ = v_a_8081_;
v_isShared_8092_ = v_isSharedCheck_8128_;
goto v_resetjp_8090_;
}
else
{
lean_inc(v_buildTime_8089_);
lean_inc(v_trace_8088_);
lean_inc(v_log_8085_);
lean_dec(v_a_8081_);
v___x_8091_ = lean_box(0);
v_isShared_8092_ = v_isSharedCheck_8128_;
goto v_resetjp_8090_;
}
v_resetjp_8090_:
{
lean_object* v___x_8093_; lean_object* v___x_8094_; lean_object* v___x_8095_; lean_object* v___x_8096_; lean_object* v___x_8097_; lean_object* v___x_8098_; lean_object* v___x_8099_; lean_object* v___x_8100_; lean_object* v___x_8101_; lean_object* v___x_8102_; lean_object* v___x_8103_; 
v___x_8093_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_8065_, v_a_8082_);
lean_dec(v_a_8082_);
v___x_8094_ = l_Array_append___redArg(v___x_8093_, v_weakArgs_8066_);
v___x_8095_ = l_Array_append___redArg(v___x_8094_, v_traceArgs_8067_);
v___x_8096_ = lean_unsigned_to_nat(2u);
v___x_8097_ = lean_mk_empty_array_with_capacity(v___x_8096_);
lean_dec_ref(v___x_8097_);
v___x_8098_ = lean_obj_once(&l_Lake_buildLeanSharedLib___lam__0___closed__0, &l_Lake_buildLeanSharedLib___lam__0___closed__0_once, _init_l_Lake_buildLeanSharedLib___lam__0___closed__0);
lean_inc_ref(v_leanLibDir_8083_);
v___x_8099_ = lean_array_push(v___x_8098_, v_leanLibDir_8083_);
v___x_8100_ = l_Array_append___redArg(v___x_8095_, v___x_8099_);
lean_dec_ref(v___x_8099_);
v___x_8101_ = l_Lake_LeanInstall_ccLinkFlags(v_sharedLean_8068_, v_lean_8080_);
lean_dec_ref(v_lean_8080_);
v___x_8102_ = l_Array_append___redArg(v___x_8100_, v___x_8101_);
lean_dec_ref(v___x_8101_);
v___x_8103_ = l_Lake_compileExe(v_exeFile_8069_, v___x_8102_, v_cc_8084_, v_log_8085_);
lean_dec_ref(v___x_8102_);
if (lean_obj_tag(v___x_8103_) == 0)
{
lean_object* v_a_8104_; lean_object* v_a_8105_; lean_object* v___x_8107_; uint8_t v_isShared_8108_; uint8_t v_isSharedCheck_8115_; 
v_a_8104_ = lean_ctor_get(v___x_8103_, 0);
v_a_8105_ = lean_ctor_get(v___x_8103_, 1);
v_isSharedCheck_8115_ = !lean_is_exclusive(v___x_8103_);
if (v_isSharedCheck_8115_ == 0)
{
v___x_8107_ = v___x_8103_;
v_isShared_8108_ = v_isSharedCheck_8115_;
goto v_resetjp_8106_;
}
else
{
lean_inc(v_a_8105_);
lean_inc(v_a_8104_);
lean_dec(v___x_8103_);
v___x_8107_ = lean_box(0);
v_isShared_8108_ = v_isSharedCheck_8115_;
goto v_resetjp_8106_;
}
v_resetjp_8106_:
{
lean_object* v___x_8110_; 
if (v_isShared_8092_ == 0)
{
lean_ctor_set(v___x_8091_, 0, v_a_8105_);
v___x_8110_ = v___x_8091_;
goto v_reusejp_8109_;
}
else
{
lean_object* v_reuseFailAlloc_8114_; 
v_reuseFailAlloc_8114_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8114_, 0, v_a_8105_);
lean_ctor_set(v_reuseFailAlloc_8114_, 1, v_trace_8088_);
lean_ctor_set(v_reuseFailAlloc_8114_, 2, v_buildTime_8089_);
lean_ctor_set_uint8(v_reuseFailAlloc_8114_, sizeof(void*)*3, v_action_8086_);
lean_ctor_set_uint8(v_reuseFailAlloc_8114_, sizeof(void*)*3 + 1, v_wantsRebuild_8087_);
v___x_8110_ = v_reuseFailAlloc_8114_;
goto v_reusejp_8109_;
}
v_reusejp_8109_:
{
lean_object* v___x_8112_; 
if (v_isShared_8108_ == 0)
{
lean_ctor_set(v___x_8107_, 1, v___x_8110_);
v___x_8112_ = v___x_8107_;
goto v_reusejp_8111_;
}
else
{
lean_object* v_reuseFailAlloc_8113_; 
v_reuseFailAlloc_8113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8113_, 0, v_a_8104_);
lean_ctor_set(v_reuseFailAlloc_8113_, 1, v___x_8110_);
v___x_8112_ = v_reuseFailAlloc_8113_;
goto v_reusejp_8111_;
}
v_reusejp_8111_:
{
return v___x_8112_;
}
}
}
}
else
{
lean_object* v_a_8116_; lean_object* v_a_8117_; lean_object* v___x_8119_; uint8_t v_isShared_8120_; uint8_t v_isSharedCheck_8127_; 
v_a_8116_ = lean_ctor_get(v___x_8103_, 0);
v_a_8117_ = lean_ctor_get(v___x_8103_, 1);
v_isSharedCheck_8127_ = !lean_is_exclusive(v___x_8103_);
if (v_isSharedCheck_8127_ == 0)
{
v___x_8119_ = v___x_8103_;
v_isShared_8120_ = v_isSharedCheck_8127_;
goto v_resetjp_8118_;
}
else
{
lean_inc(v_a_8117_);
lean_inc(v_a_8116_);
lean_dec(v___x_8103_);
v___x_8119_ = lean_box(0);
v_isShared_8120_ = v_isSharedCheck_8127_;
goto v_resetjp_8118_;
}
v_resetjp_8118_:
{
lean_object* v___x_8122_; 
if (v_isShared_8092_ == 0)
{
lean_ctor_set(v___x_8091_, 0, v_a_8117_);
v___x_8122_ = v___x_8091_;
goto v_reusejp_8121_;
}
else
{
lean_object* v_reuseFailAlloc_8126_; 
v_reuseFailAlloc_8126_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8126_, 0, v_a_8117_);
lean_ctor_set(v_reuseFailAlloc_8126_, 1, v_trace_8088_);
lean_ctor_set(v_reuseFailAlloc_8126_, 2, v_buildTime_8089_);
lean_ctor_set_uint8(v_reuseFailAlloc_8126_, sizeof(void*)*3, v_action_8086_);
lean_ctor_set_uint8(v_reuseFailAlloc_8126_, sizeof(void*)*3 + 1, v_wantsRebuild_8087_);
v___x_8122_ = v_reuseFailAlloc_8126_;
goto v_reusejp_8121_;
}
v_reusejp_8121_:
{
lean_object* v___x_8124_; 
if (v_isShared_8120_ == 0)
{
lean_ctor_set(v___x_8119_, 1, v___x_8122_);
v___x_8124_ = v___x_8119_;
goto v_reusejp_8123_;
}
else
{
lean_object* v_reuseFailAlloc_8125_; 
v_reuseFailAlloc_8125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8125_, 0, v_a_8116_);
lean_ctor_set(v_reuseFailAlloc_8125_, 1, v___x_8122_);
v___x_8124_ = v_reuseFailAlloc_8125_;
goto v_reusejp_8123_;
}
v_reusejp_8123_:
{
return v___x_8124_;
}
}
}
}
}
}
else
{
lean_object* v_a_8129_; lean_object* v_a_8130_; lean_object* v___x_8132_; uint8_t v_isShared_8133_; uint8_t v_isSharedCheck_8137_; 
lean_dec_ref(v___y_8074_);
lean_dec_ref(v_exeFile_8069_);
v_a_8129_ = lean_ctor_get(v___x_8077_, 0);
v_a_8130_ = lean_ctor_get(v___x_8077_, 1);
v_isSharedCheck_8137_ = !lean_is_exclusive(v___x_8077_);
if (v_isSharedCheck_8137_ == 0)
{
v___x_8132_ = v___x_8077_;
v_isShared_8133_ = v_isSharedCheck_8137_;
goto v_resetjp_8131_;
}
else
{
lean_inc(v_a_8130_);
lean_inc(v_a_8129_);
lean_dec(v___x_8077_);
v___x_8132_ = lean_box(0);
v_isShared_8133_ = v_isSharedCheck_8137_;
goto v_resetjp_8131_;
}
v_resetjp_8131_:
{
lean_object* v___x_8135_; 
if (v_isShared_8133_ == 0)
{
v___x_8135_ = v___x_8132_;
goto v_reusejp_8134_;
}
else
{
lean_object* v_reuseFailAlloc_8136_; 
v_reuseFailAlloc_8136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8136_, 0, v_a_8129_);
lean_ctor_set(v_reuseFailAlloc_8136_, 1, v_a_8130_);
v___x_8135_ = v_reuseFailAlloc_8136_;
goto v_reusejp_8134_;
}
v_reusejp_8134_:
{
return v___x_8135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object* v_libs_8138_, lean_object* v_objs_8139_, lean_object* v_weakArgs_8140_, lean_object* v_traceArgs_8141_, lean_object* v_sharedLean_8142_, lean_object* v_exeFile_8143_, lean_object* v___y_8144_, lean_object* v___y_8145_, lean_object* v___y_8146_, lean_object* v___y_8147_, lean_object* v___y_8148_, lean_object* v___y_8149_, lean_object* v___y_8150_){
_start:
{
uint8_t v_sharedLean_boxed_8151_; lean_object* v_res_8152_; 
v_sharedLean_boxed_8151_ = lean_unbox(v_sharedLean_8142_);
v_res_8152_ = l_Lake_buildLeanExe___lam__0(v_libs_8138_, v_objs_8139_, v_weakArgs_8140_, v_traceArgs_8141_, v_sharedLean_boxed_8151_, v_exeFile_8143_, v___y_8144_, v___y_8145_, v___y_8146_, v___y_8147_, v___y_8148_, v___y_8149_);
lean_dec(v___y_8147_);
lean_dec(v___y_8146_);
lean_dec(v___y_8145_);
lean_dec_ref(v___y_8144_);
lean_dec_ref(v_traceArgs_8141_);
lean_dec_ref(v_weakArgs_8140_);
lean_dec_ref(v_objs_8139_);
lean_dec_ref(v_libs_8138_);
return v_res_8152_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object* v_objs_8153_, lean_object* v_weakArgs_8154_, lean_object* v_traceArgs_8155_, uint8_t v_sharedLean_8156_, lean_object* v_exeFile_8157_, lean_object* v_libs_8158_, lean_object* v___y_8159_, lean_object* v___y_8160_, lean_object* v___y_8161_, lean_object* v___y_8162_, lean_object* v___y_8163_, lean_object* v___y_8164_){
_start:
{
lean_object* v_log_8166_; uint8_t v_action_8167_; uint8_t v_wantsRebuild_8168_; lean_object* v_trace_8169_; lean_object* v_buildTime_8170_; lean_object* v___x_8172_; uint8_t v_isShared_8173_; uint8_t v_isSharedCheck_8229_; 
v_log_8166_ = lean_ctor_get(v___y_8164_, 0);
v_action_8167_ = lean_ctor_get_uint8(v___y_8164_, sizeof(void*)*3);
v_wantsRebuild_8168_ = lean_ctor_get_uint8(v___y_8164_, sizeof(void*)*3 + 1);
v_trace_8169_ = lean_ctor_get(v___y_8164_, 1);
v_buildTime_8170_ = lean_ctor_get(v___y_8164_, 2);
v_isSharedCheck_8229_ = !lean_is_exclusive(v___y_8164_);
if (v_isSharedCheck_8229_ == 0)
{
v___x_8172_ = v___y_8164_;
v_isShared_8173_ = v_isSharedCheck_8229_;
goto v_resetjp_8171_;
}
else
{
lean_inc(v_buildTime_8170_);
lean_inc(v_trace_8169_);
lean_inc(v_log_8166_);
lean_dec(v___y_8164_);
v___x_8172_ = lean_box(0);
v_isShared_8173_ = v_isSharedCheck_8229_;
goto v_resetjp_8171_;
}
v_resetjp_8171_:
{
lean_object* v_leanTrace_8174_; lean_object* v___x_8175_; lean_object* v___f_8176_; lean_object* v___x_8177_; uint64_t v___y_8179_; uint64_t v___x_8218_; lean_object* v___x_8219_; lean_object* v___x_8220_; uint8_t v___x_8221_; 
v_leanTrace_8174_ = lean_ctor_get(v___y_8163_, 2);
v___x_8175_ = lean_box(v_sharedLean_8156_);
lean_inc_ref(v_exeFile_8157_);
lean_inc_ref(v_traceArgs_8155_);
v___f_8176_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__0___boxed), 13, 6);
lean_closure_set(v___f_8176_, 0, v_libs_8158_);
lean_closure_set(v___f_8176_, 1, v_objs_8153_);
lean_closure_set(v___f_8176_, 2, v_weakArgs_8154_);
lean_closure_set(v___f_8176_, 3, v_traceArgs_8155_);
lean_closure_set(v___f_8176_, 4, v___x_8175_);
lean_closure_set(v___f_8176_, 5, v_exeFile_8157_);
lean_inc_ref(v_leanTrace_8174_);
v___x_8177_ = l_Lake_BuildTrace_mix(v_trace_8169_, v_leanTrace_8174_);
v___x_8218_ = l_Lake_Hash_nil;
v___x_8219_ = lean_unsigned_to_nat(0u);
v___x_8220_ = lean_array_get_size(v_traceArgs_8155_);
v___x_8221_ = lean_nat_dec_lt(v___x_8219_, v___x_8220_);
if (v___x_8221_ == 0)
{
v___y_8179_ = v___x_8218_;
goto v___jp_8178_;
}
else
{
uint8_t v___x_8222_; 
v___x_8222_ = lean_nat_dec_le(v___x_8220_, v___x_8220_);
if (v___x_8222_ == 0)
{
if (v___x_8221_ == 0)
{
v___y_8179_ = v___x_8218_;
goto v___jp_8178_;
}
else
{
size_t v___x_8223_; size_t v___x_8224_; uint64_t v___x_8225_; 
v___x_8223_ = ((size_t)0ULL);
v___x_8224_ = lean_usize_of_nat(v___x_8220_);
v___x_8225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8155_, v___x_8223_, v___x_8224_, v___x_8218_);
v___y_8179_ = v___x_8225_;
goto v___jp_8178_;
}
}
else
{
size_t v___x_8226_; size_t v___x_8227_; uint64_t v___x_8228_; 
v___x_8226_ = ((size_t)0ULL);
v___x_8227_ = lean_usize_of_nat(v___x_8220_);
v___x_8228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8155_, v___x_8226_, v___x_8227_, v___x_8218_);
v___y_8179_ = v___x_8228_;
goto v___jp_8178_;
}
}
v___jp_8178_:
{
lean_object* v___x_8180_; lean_object* v___x_8181_; lean_object* v___x_8182_; lean_object* v___x_8183_; lean_object* v___x_8184_; lean_object* v___x_8185_; lean_object* v___x_8186_; lean_object* v___x_8187_; lean_object* v___x_8188_; lean_object* v___x_8189_; lean_object* v___x_8190_; lean_object* v___x_8191_; lean_object* v___x_8193_; 
v___x_8180_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_8181_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_8182_ = lean_array_to_list(v_traceArgs_8155_);
v___x_8183_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_8182_);
lean_dec(v___x_8182_);
v___x_8184_ = lean_string_append(v___x_8181_, v___x_8183_);
lean_dec_ref(v___x_8183_);
v___x_8185_ = lean_string_append(v___x_8180_, v___x_8184_);
lean_dec_ref(v___x_8184_);
v___x_8186_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_8187_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_8188_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_8188_, 0, v___x_8185_);
lean_ctor_set(v___x_8188_, 1, v___x_8186_);
lean_ctor_set(v___x_8188_, 2, v___x_8187_);
lean_ctor_set_uint64(v___x_8188_, sizeof(void*)*3, v___y_8179_);
v___x_8189_ = l_Lake_BuildTrace_mix(v___x_8177_, v___x_8188_);
v___x_8190_ = l_Lake_platformTrace;
v___x_8191_ = l_Lake_BuildTrace_mix(v___x_8189_, v___x_8190_);
if (v_isShared_8173_ == 0)
{
lean_ctor_set(v___x_8172_, 1, v___x_8191_);
v___x_8193_ = v___x_8172_;
goto v_reusejp_8192_;
}
else
{
lean_object* v_reuseFailAlloc_8217_; 
v_reuseFailAlloc_8217_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8217_, 0, v_log_8166_);
lean_ctor_set(v_reuseFailAlloc_8217_, 1, v___x_8191_);
lean_ctor_set(v_reuseFailAlloc_8217_, 2, v_buildTime_8170_);
lean_ctor_set_uint8(v_reuseFailAlloc_8217_, sizeof(void*)*3, v_action_8167_);
lean_ctor_set_uint8(v_reuseFailAlloc_8217_, sizeof(void*)*3 + 1, v_wantsRebuild_8168_);
v___x_8193_ = v_reuseFailAlloc_8217_;
goto v_reusejp_8192_;
}
v_reusejp_8192_:
{
uint8_t v___x_8194_; lean_object* v___x_8195_; uint8_t v___x_8196_; lean_object* v___x_8197_; 
v___x_8194_ = 0;
v___x_8195_ = l_System_FilePath_exeExtension;
v___x_8196_ = 1;
v___x_8197_ = l_Lake_buildArtifactUnlessUpToDate(v_exeFile_8157_, v___f_8176_, v___x_8194_, v___x_8195_, v___x_8196_, v___x_8196_, v___x_8194_, v___y_8159_, v___y_8160_, v___y_8161_, v___y_8162_, v___y_8163_, v___x_8193_);
if (lean_obj_tag(v___x_8197_) == 0)
{
lean_object* v_a_8198_; lean_object* v_a_8199_; lean_object* v___x_8201_; uint8_t v_isShared_8202_; uint8_t v_isSharedCheck_8207_; 
v_a_8198_ = lean_ctor_get(v___x_8197_, 0);
v_a_8199_ = lean_ctor_get(v___x_8197_, 1);
v_isSharedCheck_8207_ = !lean_is_exclusive(v___x_8197_);
if (v_isSharedCheck_8207_ == 0)
{
v___x_8201_ = v___x_8197_;
v_isShared_8202_ = v_isSharedCheck_8207_;
goto v_resetjp_8200_;
}
else
{
lean_inc(v_a_8199_);
lean_inc(v_a_8198_);
lean_dec(v___x_8197_);
v___x_8201_ = lean_box(0);
v_isShared_8202_ = v_isSharedCheck_8207_;
goto v_resetjp_8200_;
}
v_resetjp_8200_:
{
lean_object* v_path_8203_; lean_object* v___x_8205_; 
v_path_8203_ = lean_ctor_get(v_a_8198_, 1);
lean_inc_ref(v_path_8203_);
lean_dec(v_a_8198_);
if (v_isShared_8202_ == 0)
{
lean_ctor_set(v___x_8201_, 0, v_path_8203_);
v___x_8205_ = v___x_8201_;
goto v_reusejp_8204_;
}
else
{
lean_object* v_reuseFailAlloc_8206_; 
v_reuseFailAlloc_8206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8206_, 0, v_path_8203_);
lean_ctor_set(v_reuseFailAlloc_8206_, 1, v_a_8199_);
v___x_8205_ = v_reuseFailAlloc_8206_;
goto v_reusejp_8204_;
}
v_reusejp_8204_:
{
return v___x_8205_;
}
}
}
else
{
lean_object* v_a_8208_; lean_object* v_a_8209_; lean_object* v___x_8211_; uint8_t v_isShared_8212_; uint8_t v_isSharedCheck_8216_; 
v_a_8208_ = lean_ctor_get(v___x_8197_, 0);
v_a_8209_ = lean_ctor_get(v___x_8197_, 1);
v_isSharedCheck_8216_ = !lean_is_exclusive(v___x_8197_);
if (v_isSharedCheck_8216_ == 0)
{
v___x_8211_ = v___x_8197_;
v_isShared_8212_ = v_isSharedCheck_8216_;
goto v_resetjp_8210_;
}
else
{
lean_inc(v_a_8209_);
lean_inc(v_a_8208_);
lean_dec(v___x_8197_);
v___x_8211_ = lean_box(0);
v_isShared_8212_ = v_isSharedCheck_8216_;
goto v_resetjp_8210_;
}
v_resetjp_8210_:
{
lean_object* v___x_8214_; 
if (v_isShared_8212_ == 0)
{
v___x_8214_ = v___x_8211_;
goto v_reusejp_8213_;
}
else
{
lean_object* v_reuseFailAlloc_8215_; 
v_reuseFailAlloc_8215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8215_, 0, v_a_8208_);
lean_ctor_set(v_reuseFailAlloc_8215_, 1, v_a_8209_);
v___x_8214_ = v_reuseFailAlloc_8215_;
goto v_reusejp_8213_;
}
v_reusejp_8213_:
{
return v___x_8214_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object* v_objs_8230_, lean_object* v_weakArgs_8231_, lean_object* v_traceArgs_8232_, lean_object* v_sharedLean_8233_, lean_object* v_exeFile_8234_, lean_object* v_libs_8235_, lean_object* v___y_8236_, lean_object* v___y_8237_, lean_object* v___y_8238_, lean_object* v___y_8239_, lean_object* v___y_8240_, lean_object* v___y_8241_, lean_object* v___y_8242_){
_start:
{
uint8_t v_sharedLean_boxed_8243_; lean_object* v_res_8244_; 
v_sharedLean_boxed_8243_ = lean_unbox(v_sharedLean_8233_);
v_res_8244_ = l_Lake_buildLeanExe___lam__1(v_objs_8230_, v_weakArgs_8231_, v_traceArgs_8232_, v_sharedLean_boxed_8243_, v_exeFile_8234_, v_libs_8235_, v___y_8236_, v___y_8237_, v___y_8238_, v___y_8239_, v___y_8240_, v___y_8241_);
return v_res_8244_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2(lean_object* v_weakArgs_8245_, lean_object* v_traceArgs_8246_, uint8_t v_sharedLean_8247_, lean_object* v_exeFile_8248_, lean_object* v_linkLibs_8249_, lean_object* v___x_8250_, lean_object* v_objs_8251_, lean_object* v___y_8252_, lean_object* v___y_8253_, lean_object* v___y_8254_, lean_object* v___y_8255_, lean_object* v___y_8256_, lean_object* v___y_8257_){
_start:
{
lean_object* v_trace_8259_; lean_object* v___x_8260_; lean_object* v___f_8261_; lean_object* v___x_8262_; lean_object* v___x_8263_; lean_object* v___x_8264_; uint8_t v___x_8265_; lean_object* v___x_8266_; lean_object* v___x_8267_; 
v_trace_8259_ = lean_ctor_get(v___y_8257_, 1);
v___x_8260_ = lean_box(v_sharedLean_8247_);
v___f_8261_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__1___boxed), 13, 5);
lean_closure_set(v___f_8261_, 0, v_objs_8251_);
lean_closure_set(v___f_8261_, 1, v_weakArgs_8245_);
lean_closure_set(v___f_8261_, 2, v_traceArgs_8246_);
lean_closure_set(v___f_8261_, 3, v___x_8260_);
lean_closure_set(v___f_8261_, 4, v_exeFile_8248_);
v___x_8262_ = ((lean_object*)(l_Lake_buildSharedLib___lam__3___closed__0));
v___x_8263_ = l_Lake_Job_collectArray___redArg(v_linkLibs_8249_, v___x_8262_);
v___x_8264_ = lean_unsigned_to_nat(0u);
v___x_8265_ = 0;
lean_inc_ref(v_trace_8259_);
v___x_8266_ = l_Lake_Job_mapM___redArg(v___x_8250_, v___x_8263_, v___f_8261_, v___x_8264_, v___x_8265_, v___y_8252_, v___y_8253_, v___y_8254_, v___y_8255_, v___y_8256_, v_trace_8259_);
v___x_8267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8267_, 0, v___x_8266_);
lean_ctor_set(v___x_8267_, 1, v___y_8257_);
return v___x_8267_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2___boxed(lean_object* v_weakArgs_8268_, lean_object* v_traceArgs_8269_, lean_object* v_sharedLean_8270_, lean_object* v_exeFile_8271_, lean_object* v_linkLibs_8272_, lean_object* v___x_8273_, lean_object* v_objs_8274_, lean_object* v___y_8275_, lean_object* v___y_8276_, lean_object* v___y_8277_, lean_object* v___y_8278_, lean_object* v___y_8279_, lean_object* v___y_8280_, lean_object* v___y_8281_){
_start:
{
uint8_t v_sharedLean_boxed_8282_; lean_object* v_res_8283_; 
v_sharedLean_boxed_8282_ = lean_unbox(v_sharedLean_8270_);
v_res_8283_ = l_Lake_buildLeanExe___lam__2(v_weakArgs_8268_, v_traceArgs_8269_, v_sharedLean_boxed_8282_, v_exeFile_8271_, v_linkLibs_8272_, v___x_8273_, v_objs_8274_, v___y_8275_, v___y_8276_, v___y_8277_, v___y_8278_, v___y_8279_, v___y_8280_);
lean_dec_ref(v_linkLibs_8272_);
return v_res_8283_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object* v_exeFile_8284_, lean_object* v_linkObjs_8285_, lean_object* v_linkLibs_8286_, lean_object* v_weakArgs_8287_, lean_object* v_traceArgs_8288_, uint8_t v_sharedLean_8289_, lean_object* v_a_8290_, lean_object* v_a_8291_, lean_object* v_a_8292_, lean_object* v_a_8293_, lean_object* v_a_8294_, lean_object* v_a_8295_){
_start:
{
lean_object* v___x_8297_; lean_object* v___x_8298_; lean_object* v___f_8299_; lean_object* v___x_8300_; lean_object* v___x_8301_; lean_object* v___x_8302_; uint8_t v___x_8303_; lean_object* v___x_8304_; 
v___x_8297_ = l_Lake_instDataKindFilePath;
v___x_8298_ = lean_box(v_sharedLean_8289_);
v___f_8299_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__2___boxed), 14, 6);
lean_closure_set(v___f_8299_, 0, v_weakArgs_8287_);
lean_closure_set(v___f_8299_, 1, v_traceArgs_8288_);
lean_closure_set(v___f_8299_, 2, v___x_8298_);
lean_closure_set(v___f_8299_, 3, v_exeFile_8284_);
lean_closure_set(v___f_8299_, 4, v_linkLibs_8286_);
lean_closure_set(v___f_8299_, 5, v___x_8297_);
v___x_8300_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8301_ = l_Lake_Job_collectArray___redArg(v_linkObjs_8285_, v___x_8300_);
v___x_8302_ = lean_unsigned_to_nat(0u);
v___x_8303_ = 1;
v___x_8304_ = l_Lake_Job_bindM___redArg(v___x_8297_, v___x_8301_, v___f_8299_, v___x_8302_, v___x_8303_, v_a_8290_, v_a_8291_, v_a_8292_, v_a_8293_, v_a_8294_, v_a_8295_);
return v___x_8304_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object* v_exeFile_8305_, lean_object* v_linkObjs_8306_, lean_object* v_linkLibs_8307_, lean_object* v_weakArgs_8308_, lean_object* v_traceArgs_8309_, lean_object* v_sharedLean_8310_, lean_object* v_a_8311_, lean_object* v_a_8312_, lean_object* v_a_8313_, lean_object* v_a_8314_, lean_object* v_a_8315_, lean_object* v_a_8316_, lean_object* v_a_8317_){
_start:
{
uint8_t v_sharedLean_boxed_8318_; lean_object* v_res_8319_; 
v_sharedLean_boxed_8318_ = lean_unbox(v_sharedLean_8310_);
v_res_8319_ = l_Lake_buildLeanExe(v_exeFile_8305_, v_linkObjs_8306_, v_linkLibs_8307_, v_weakArgs_8308_, v_traceArgs_8309_, v_sharedLean_boxed_8318_, v_a_8311_, v_a_8312_, v_a_8313_, v_a_8314_, v_a_8315_, v_a_8316_);
lean_dec_ref(v_linkObjs_8306_);
return v_res_8319_;
}
}
lean_object* runtime_initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Actions(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Common(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Build_Job_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_JsonObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instMonadWorkspaceJobM = _init_l_Lake_instMonadWorkspaceJobM();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM);
l_Lake_platformTrace = _init_l_Lake_platformTrace();
lean_mark_persistent(l_Lake_platformTrace);
l_Lake_buildO___lam__2___boxed__const__1 = _init_l_Lake_buildO___lam__2___boxed__const__1();
lean_mark_persistent(l_Lake_buildO___lam__2___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Common(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* initialize_Lake_Util_IO(uint8_t builtin);
lean_object* initialize_Lake_Build_Actions(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Common(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Job_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_JsonObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Common(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Common(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Common(builtin);
}
#ifdef __cplusplus
}
#endif
