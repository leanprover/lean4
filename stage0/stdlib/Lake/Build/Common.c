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
lean_object* l_Lake_CacheMap_insertCore(uint64_t, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* l_Lake_ArtifactDescr_fromJson_x3f(lean_object*);
lean_object* l_Lean_Json_render(lean_object*);
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lake_CacheService_artifactUrl(uint64_t, lean_object*, lean_object*);
lean_object* l_Lake_downloadArtifactCore(uint64_t, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_setAccessRights(lean_object*, lean_object*);
lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_cacheScope(lean_object*);
lean_object* l_Lake_Cache_readOutputs_x3f(lean_object*, lean_object*, uint64_t, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* lean_io_hard_link(lean_object*, lean_object*);
lean_object* l_Lake_copyFile(lean_object*, lean_object*);
uint8_t l_Lake_JobAction_merge(uint8_t, uint8_t);
lean_object* l_Lake_removeFileIfExists(lean_object*);
lean_object* l_Lake_JsonObject_insertJson(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instToJsonLogEntry_toJson(lean_object*);
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
static const lean_string_object l_Lake_getArtifacts_x3f___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\n- "};
static const lean_object* l_Lake_getArtifacts_x3f___redArg___lam__0___closed__0 = (const lean_object*)&l_Lake_getArtifacts_x3f___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_getArtifacts_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "could not write outputs to cache: "};
static const lean_object* l_Lake_getArtifacts_x3f___redArg___closed__0 = (const lean_object*)&l_Lake_getArtifacts_x3f___redArg___closed__0_value;
static const lean_closure_object l_Lake_getArtifacts_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getArtifacts_x3f___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getArtifacts_x3f___redArg___closed__1 = (const lean_object*)&l_Lake_getArtifacts_x3f___redArg___closed__1_value;
static const lean_string_object l_Lake_getArtifacts_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "input '"};
static const lean_object* l_Lake_getArtifacts_x3f___redArg___closed__2 = (const lean_object*)&l_Lake_getArtifacts_x3f___redArg___closed__2_value;
static const lean_string_object l_Lake_getArtifacts_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "' found in package artifact cache, but some output(s) have issues:"};
static const lean_object* l_Lake_getArtifacts_x3f___redArg___closed__3 = (const lean_object*)&l_Lake_getArtifacts_x3f___redArg___closed__3_value;
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
static const lean_string_object l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "ill-formed artifact output:\n"};
static const lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg___closed__0_value;
static const lean_string_object l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(uint8_t, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(uint8_t, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___lam__0(lean_object* v_x1_3484_, lean_object* v_x2_3485_){
_start:
{
lean_object* v_message_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v_message_3486_ = lean_ctor_get(v_x2_3485_, 0);
v___x_3487_ = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___lam__0___closed__0));
v___x_3488_ = lean_string_append(v_x1_3484_, v___x_3487_);
v___x_3489_ = lean_string_append(v___x_3488_, v_message_3486_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___lam__0___boxed(lean_object* v_x1_3490_, lean_object* v_x2_3491_){
_start:
{
lean_object* v_res_3492_; 
v_res_3492_ = l_Lake_getArtifacts_x3f___redArg___lam__0(v_x1_3490_, v_x2_3491_);
lean_dec_ref(v_x2_3491_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___lam__1(lean_object* v_a_3493_, lean_object* v_____r_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_){
_start:
{
lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3502_, 0, v_a_3493_);
v___x_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3502_);
v___x_3504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3503_);
lean_ctor_set(v___x_3504_, 1, v___y_3500_);
return v___x_3504_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___lam__1___boxed(lean_object* v_a_3505_, lean_object* v_____r_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
lean_object* v_res_3514_; 
v_res_3514_ = l_Lake_getArtifacts_x3f___redArg___lam__1(v_a_3505_, v_____r_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v___y_3510_);
lean_dec(v___y_3509_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg(lean_object* v_inst_3519_, uint64_t v_inputHash_3520_, lean_object* v_savedTrace_3521_, lean_object* v_pkg_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_){
_start:
{
lean_object* v___y_3531_; lean_object* v_a_3535_; lean_object* v_a_3536_; lean_object* v___y_3551_; lean_object* v_toContext_3566_; lean_object* v_root_3567_; lean_object* v_lakeEnv_3568_; lean_object* v_lakeCache_3569_; uint8_t v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3622_; uint8_t v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; uint8_t v___y_3626_; lean_object* v___y_3627_; uint8_t v___y_3628_; lean_object* v___y_3629_; lean_object* v_config_3634_; lean_object* v_enableArtifactCache_x3f_3635_; lean_object* v___f_3636_; uint8_t v_a_3638_; lean_object* v_a_3639_; 
v_toContext_3566_ = lean_ctor_get(v_a_3527_, 1);
v_root_3567_ = lean_ctor_get(v_toContext_3566_, 0);
v_lakeEnv_3568_ = lean_ctor_get(v_toContext_3566_, 1);
v_lakeCache_3569_ = lean_ctor_get(v_toContext_3566_, 3);
lean_inc_ref(v_lakeCache_3569_);
v_config_3634_ = lean_ctor_get(v_pkg_3522_, 6);
v_enableArtifactCache_x3f_3635_ = lean_ctor_get(v_config_3634_, 25);
v___f_3636_ = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___closed__1));
if (lean_obj_tag(v_enableArtifactCache_x3f_3635_) == 0)
{
lean_object* v_enableArtifactCache_x3f_3727_; 
v_enableArtifactCache_x3f_3727_ = lean_ctor_get(v_lakeEnv_3568_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_3727_) == 0)
{
lean_object* v_config_3728_; lean_object* v_enableArtifactCache_x3f_3729_; 
v_config_3728_ = lean_ctor_get(v_root_3567_, 6);
v_enableArtifactCache_x3f_3729_ = lean_ctor_get(v_config_3728_, 25);
if (lean_obj_tag(v_enableArtifactCache_x3f_3729_) == 0)
{
uint8_t v___x_3730_; 
v___x_3730_ = 0;
v_a_3638_ = v___x_3730_;
v_a_3639_ = v_a_3528_;
goto v___jp_3637_;
}
else
{
lean_object* v_val_3731_; uint8_t v___x_3732_; 
v_val_3731_ = lean_ctor_get(v_enableArtifactCache_x3f_3729_, 0);
v___x_3732_ = lean_unbox(v_val_3731_);
v_a_3638_ = v___x_3732_;
v_a_3639_ = v_a_3528_;
goto v___jp_3637_;
}
}
else
{
lean_object* v_val_3733_; uint8_t v___x_3734_; 
v_val_3733_ = lean_ctor_get(v_enableArtifactCache_x3f_3727_, 0);
v___x_3734_ = lean_unbox(v_val_3733_);
v_a_3638_ = v___x_3734_;
v_a_3639_ = v_a_3528_;
goto v___jp_3637_;
}
}
else
{
lean_object* v_val_3735_; uint8_t v___x_3736_; 
v_val_3735_ = lean_ctor_get(v_enableArtifactCache_x3f_3635_, 0);
v___x_3736_ = lean_unbox(v_val_3735_);
v_a_3638_ = v___x_3736_;
v_a_3639_ = v_a_3528_;
goto v___jp_3637_;
}
v___jp_3530_:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3532_ = lean_box(0);
v___x_3533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3532_);
lean_ctor_set(v___x_3533_, 1, v___y_3531_);
return v___x_3533_;
}
v___jp_3534_:
{
lean_object* v_log_3537_; uint8_t v_action_3538_; uint8_t v_wantsRebuild_3539_; lean_object* v_trace_3540_; lean_object* v_buildTime_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3549_; 
v_log_3537_ = lean_ctor_get(v_a_3536_, 0);
v_action_3538_ = lean_ctor_get_uint8(v_a_3536_, sizeof(void*)*3);
v_wantsRebuild_3539_ = lean_ctor_get_uint8(v_a_3536_, sizeof(void*)*3 + 1);
v_trace_3540_ = lean_ctor_get(v_a_3536_, 1);
v_buildTime_3541_ = lean_ctor_get(v_a_3536_, 2);
v_isSharedCheck_3549_ = !lean_is_exclusive(v_a_3536_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3543_ = v_a_3536_;
v_isShared_3544_ = v_isSharedCheck_3549_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_buildTime_3541_);
lean_inc(v_trace_3540_);
lean_inc(v_log_3537_);
lean_dec(v_a_3536_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3549_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3545_; lean_object* v___x_3547_; 
v___x_3545_ = l_Array_shrink___redArg(v_log_3537_, v_a_3535_);
lean_dec(v_a_3535_);
if (v_isShared_3544_ == 0)
{
lean_ctor_set(v___x_3543_, 0, v___x_3545_);
v___x_3547_ = v___x_3543_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3545_);
lean_ctor_set(v_reuseFailAlloc_3548_, 1, v_trace_3540_);
lean_ctor_set(v_reuseFailAlloc_3548_, 2, v_buildTime_3541_);
lean_ctor_set_uint8(v_reuseFailAlloc_3548_, sizeof(void*)*3, v_action_3538_);
lean_ctor_set_uint8(v_reuseFailAlloc_3548_, sizeof(void*)*3 + 1, v_wantsRebuild_3539_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
v___y_3531_ = v___x_3547_;
goto v___jp_3530_;
}
}
}
v___jp_3550_:
{
if (lean_obj_tag(v___y_3551_) == 0)
{
lean_object* v_a_3552_; 
v_a_3552_ = lean_ctor_get(v___y_3551_, 0);
if (lean_obj_tag(v_a_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3561_; 
lean_inc_ref(v_a_3552_);
v_a_3553_ = lean_ctor_get(v___y_3551_, 1);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___y_3551_);
if (v_isSharedCheck_3561_ == 0)
{
lean_object* v_unused_3562_; 
v_unused_3562_ = lean_ctor_get(v___y_3551_, 0);
lean_dec(v_unused_3562_);
v___x_3555_ = v___y_3551_;
v_isShared_3556_ = v_isSharedCheck_3561_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___y_3551_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3561_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v_a_3557_; lean_object* v___x_3559_; 
v_a_3557_ = lean_ctor_get(v_a_3552_, 0);
lean_inc(v_a_3557_);
lean_dec_ref(v_a_3552_);
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 0, v_a_3557_);
v___x_3559_ = v___x_3555_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3557_);
lean_ctor_set(v_reuseFailAlloc_3560_, 1, v_a_3553_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
else
{
lean_object* v_a_3563_; 
v_a_3563_ = lean_ctor_get(v___y_3551_, 1);
lean_inc(v_a_3563_);
lean_dec_ref(v___y_3551_);
v___y_3531_ = v_a_3563_;
goto v___jp_3530_;
}
}
else
{
lean_object* v_a_3564_; lean_object* v_a_3565_; 
v_a_3564_ = lean_ctor_get(v___y_3551_, 0);
lean_inc(v_a_3564_);
v_a_3565_ = lean_ctor_get(v___y_3551_, 1);
lean_inc(v_a_3565_);
lean_dec_ref(v___y_3551_);
v_a_3535_ = v_a_3564_;
v_a_3536_ = v_a_3565_;
goto v___jp_3534_;
}
}
v___jp_3570_:
{
if (lean_obj_tag(v_savedTrace_3521_) == 2)
{
lean_object* v_data_3579_; uint64_t v_depHash_3580_; lean_object* v_outputs_x3f_3581_; uint8_t v___x_3582_; 
v_data_3579_ = lean_ctor_get(v_savedTrace_3521_, 0);
lean_inc_ref(v_data_3579_);
lean_dec_ref(v_savedTrace_3521_);
v_depHash_3580_ = lean_ctor_get_uint64(v_data_3579_, sizeof(void*)*3);
v_outputs_x3f_3581_ = lean_ctor_get(v_data_3579_, 1);
lean_inc(v_outputs_x3f_3581_);
lean_dec_ref(v_data_3579_);
v___x_3582_ = lean_uint64_dec_eq(v_depHash_3580_, v_inputHash_3520_);
if (v___x_3582_ == 0)
{
lean_dec(v_outputs_x3f_3581_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec_ref(v_lakeCache_3569_);
lean_dec_ref(v_inst_3519_);
v___y_3531_ = v___y_3578_;
goto v___jp_3530_;
}
else
{
if (lean_obj_tag(v_outputs_x3f_3581_) == 1)
{
lean_object* v_val_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v_val_3583_ = lean_ctor_get(v_outputs_x3f_3581_, 0);
lean_inc(v_val_3583_);
lean_dec_ref(v_outputs_x3f_3581_);
v___x_3584_ = lean_box(0);
lean_inc_ref(v___y_3577_);
lean_inc(v___y_3576_);
lean_inc(v___y_3575_);
lean_inc(v___y_3574_);
lean_inc_ref(v___y_3573_);
lean_inc(v_val_3583_);
v___x_3585_ = lean_apply_10(v_inst_3519_, v_val_3583_, v___x_3584_, v___x_3584_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, lean_box(0));
if (lean_obj_tag(v___x_3585_) == 0)
{
if (v___y_3571_ == 0)
{
lean_object* v_a_3586_; lean_object* v_a_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; 
lean_dec(v_val_3583_);
lean_dec_ref(v___y_3572_);
lean_dec_ref(v_lakeCache_3569_);
v_a_3586_ = lean_ctor_get(v___x_3585_, 0);
lean_inc(v_a_3586_);
v_a_3587_ = lean_ctor_get(v___x_3585_, 1);
lean_inc(v_a_3587_);
lean_dec_ref(v___x_3585_);
v___x_3588_ = lean_box(0);
v___x_3589_ = l_Lake_getArtifacts_x3f___redArg___lam__1(v_a_3586_, v___x_3588_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v_a_3587_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
v___y_3551_ = v___x_3589_;
goto v___jp_3550_;
}
else
{
lean_object* v_a_3590_; lean_object* v_a_3591_; lean_object* v_log_3592_; uint8_t v_action_3593_; uint8_t v_wantsRebuild_3594_; lean_object* v_trace_3595_; lean_object* v_buildTime_3596_; lean_object* v___x_3597_; 
v_a_3590_ = lean_ctor_get(v___x_3585_, 1);
lean_inc(v_a_3590_);
v_a_3591_ = lean_ctor_get(v___x_3585_, 0);
lean_inc(v_a_3591_);
lean_dec_ref(v___x_3585_);
v_log_3592_ = lean_ctor_get(v_a_3590_, 0);
v_action_3593_ = lean_ctor_get_uint8(v_a_3590_, sizeof(void*)*3);
v_wantsRebuild_3594_ = lean_ctor_get_uint8(v_a_3590_, sizeof(void*)*3 + 1);
v_trace_3595_ = lean_ctor_get(v_a_3590_, 1);
v_buildTime_3596_ = lean_ctor_get(v_a_3590_, 2);
v___x_3597_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_3569_, v___y_3572_, v_inputHash_3520_, v_val_3583_, v___x_3584_, v___x_3584_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
lean_dec_ref(v___x_3597_);
v___x_3598_ = lean_box(0);
v___x_3599_ = l_Lake_getArtifacts_x3f___redArg___lam__1(v_a_3591_, v___x_3598_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v_a_3590_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
v___y_3551_ = v___x_3599_;
goto v___jp_3550_;
}
else
{
lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3615_; 
lean_inc(v_buildTime_3596_);
lean_inc_ref(v_trace_3595_);
lean_inc_ref(v_log_3592_);
v_isSharedCheck_3615_ = !lean_is_exclusive(v_a_3590_);
if (v_isSharedCheck_3615_ == 0)
{
lean_object* v_unused_3616_; lean_object* v_unused_3617_; lean_object* v_unused_3618_; 
v_unused_3616_ = lean_ctor_get(v_a_3590_, 2);
lean_dec(v_unused_3616_);
v_unused_3617_ = lean_ctor_get(v_a_3590_, 1);
lean_dec(v_unused_3617_);
v_unused_3618_ = lean_ctor_get(v_a_3590_, 0);
lean_dec(v_unused_3618_);
v___x_3601_ = v_a_3590_;
v_isShared_3602_ = v_isSharedCheck_3615_;
goto v_resetjp_3600_;
}
else
{
lean_dec(v_a_3590_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3615_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v_a_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; uint8_t v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3612_; 
v_a_3603_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_a_3603_);
lean_dec_ref(v___x_3597_);
v___x_3604_ = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___closed__0));
v___x_3605_ = lean_io_error_to_string(v_a_3603_);
v___x_3606_ = lean_string_append(v___x_3604_, v___x_3605_);
lean_dec_ref(v___x_3605_);
v___x_3607_ = 2;
v___x_3608_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3608_, 0, v___x_3606_);
lean_ctor_set_uint8(v___x_3608_, sizeof(void*)*1, v___x_3607_);
v___x_3609_ = lean_box(0);
v___x_3610_ = lean_array_push(v_log_3592_, v___x_3608_);
if (v_isShared_3602_ == 0)
{
lean_ctor_set(v___x_3601_, 0, v___x_3610_);
v___x_3612_ = v___x_3601_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v___x_3610_);
lean_ctor_set(v_reuseFailAlloc_3614_, 1, v_trace_3595_);
lean_ctor_set(v_reuseFailAlloc_3614_, 2, v_buildTime_3596_);
lean_ctor_set_uint8(v_reuseFailAlloc_3614_, sizeof(void*)*3, v_action_3593_);
lean_ctor_set_uint8(v_reuseFailAlloc_3614_, sizeof(void*)*3 + 1, v_wantsRebuild_3594_);
v___x_3612_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
lean_object* v___x_3613_; 
v___x_3613_ = l_Lake_getArtifacts_x3f___redArg___lam__1(v_a_3591_, v___x_3609_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___x_3612_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
v___y_3551_ = v___x_3613_;
goto v___jp_3550_;
}
}
}
}
}
else
{
lean_object* v_a_3619_; lean_object* v_a_3620_; 
lean_dec(v_val_3583_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec_ref(v_lakeCache_3569_);
v_a_3619_ = lean_ctor_get(v___x_3585_, 0);
lean_inc(v_a_3619_);
v_a_3620_ = lean_ctor_get(v___x_3585_, 1);
lean_inc(v_a_3620_);
lean_dec_ref(v___x_3585_);
v_a_3535_ = v_a_3619_;
v_a_3536_ = v_a_3620_;
goto v___jp_3534_;
}
}
else
{
lean_dec(v_outputs_x3f_3581_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec_ref(v_lakeCache_3569_);
lean_dec_ref(v_inst_3519_);
v___y_3531_ = v___y_3578_;
goto v___jp_3530_;
}
}
}
else
{
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec_ref(v_lakeCache_3569_);
lean_dec(v_savedTrace_3521_);
lean_dec_ref(v_inst_3519_);
v___y_3531_ = v___y_3578_;
goto v___jp_3530_;
}
}
v___jp_3621_:
{
uint8_t v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3630_ = 2;
v___x_3631_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3631_, 0, v___y_3629_);
lean_ctor_set_uint8(v___x_3631_, sizeof(void*)*1, v___x_3630_);
v___x_3632_ = lean_array_push(v___y_3627_, v___x_3631_);
v___x_3633_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3633_, 0, v___x_3632_);
lean_ctor_set(v___x_3633_, 1, v___y_3622_);
lean_ctor_set(v___x_3633_, 2, v___y_3624_);
lean_ctor_set_uint8(v___x_3633_, sizeof(void*)*3, v___y_3628_);
lean_ctor_set_uint8(v___x_3633_, sizeof(void*)*3 + 1, v___y_3626_);
v___y_3571_ = v___y_3623_;
v___y_3572_ = v___y_3625_;
v___y_3573_ = v_a_3523_;
v___y_3574_ = v_a_3524_;
v___y_3575_ = v_a_3525_;
v___y_3576_ = v_a_3526_;
v___y_3577_ = v_a_3527_;
v___y_3578_ = v___x_3633_;
goto v___jp_3570_;
}
v___jp_3637_:
{
lean_object* v_log_3640_; uint8_t v_action_3641_; uint8_t v_wantsRebuild_3642_; lean_object* v_trace_3643_; lean_object* v_buildTime_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3726_; 
v_log_3640_ = lean_ctor_get(v_a_3639_, 0);
v_action_3641_ = lean_ctor_get_uint8(v_a_3639_, sizeof(void*)*3);
v_wantsRebuild_3642_ = lean_ctor_get_uint8(v_a_3639_, sizeof(void*)*3 + 1);
v_trace_3643_ = lean_ctor_get(v_a_3639_, 1);
v_buildTime_3644_ = lean_ctor_get(v_a_3639_, 2);
v_isSharedCheck_3726_ = !lean_is_exclusive(v_a_3639_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3646_ = v_a_3639_;
v_isShared_3647_ = v_isSharedCheck_3726_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_buildTime_3644_);
lean_inc(v_trace_3643_);
lean_inc(v_log_3640_);
lean_dec(v_a_3639_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3726_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3648_ = l_Lake_Package_cacheScope(v_pkg_3522_);
lean_inc_ref(v___x_3648_);
lean_inc_ref(v_lakeCache_3569_);
v___x_3649_ = l_Lake_Cache_readOutputs_x3f(v_lakeCache_3569_, v___x_3648_, v_inputHash_3520_, v_log_3640_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v_a_3651_; lean_object* v___x_3653_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
lean_inc(v_a_3650_);
v_a_3651_ = lean_ctor_get(v___x_3649_, 1);
lean_inc(v_a_3651_);
lean_dec_ref(v___x_3649_);
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 0, v_a_3651_);
v___x_3653_ = v___x_3646_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_a_3651_);
lean_ctor_set(v_reuseFailAlloc_3713_, 1, v_trace_3643_);
lean_ctor_set(v_reuseFailAlloc_3713_, 2, v_buildTime_3644_);
lean_ctor_set_uint8(v_reuseFailAlloc_3713_, sizeof(void*)*3, v_action_3641_);
lean_ctor_set_uint8(v_reuseFailAlloc_3713_, sizeof(void*)*3 + 1, v_wantsRebuild_3642_);
v___x_3653_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
if (lean_obj_tag(v_a_3650_) == 1)
{
lean_object* v_val_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3712_; 
v_val_3654_ = lean_ctor_get(v_a_3650_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v_a_3650_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3656_ = v_a_3650_;
v_isShared_3657_ = v_isSharedCheck_3712_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_val_3654_);
lean_dec(v_a_3650_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3712_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v_data_3658_; lean_object* v_service_x3f_3659_; lean_object* v_scope_x3f_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3711_; 
v_data_3658_ = lean_ctor_get(v_val_3654_, 0);
v_service_x3f_3659_ = lean_ctor_get(v_val_3654_, 1);
v_scope_x3f_3660_ = lean_ctor_get(v_val_3654_, 2);
v_isSharedCheck_3711_ = !lean_is_exclusive(v_val_3654_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3662_ = v_val_3654_;
v_isShared_3663_ = v_isSharedCheck_3711_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_scope_x3f_3660_);
lean_inc(v_service_x3f_3659_);
lean_inc(v_data_3658_);
lean_dec(v_val_3654_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3711_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3664_; 
lean_inc_ref(v_inst_3519_);
lean_inc_ref(v_a_3527_);
lean_inc(v_a_3526_);
lean_inc(v_a_3525_);
lean_inc(v_a_3524_);
lean_inc_ref(v_a_3523_);
v___x_3664_ = lean_apply_10(v_inst_3519_, v_data_3658_, v_service_x3f_3659_, v_scope_x3f_3660_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v___x_3653_, lean_box(0));
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v_a_3665_; lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3676_; 
lean_del_object(v___x_3662_);
lean_dec_ref(v___x_3648_);
lean_dec_ref(v_lakeCache_3569_);
lean_dec_ref(v_a_3527_);
lean_dec(v_a_3526_);
lean_dec(v_a_3525_);
lean_dec(v_a_3524_);
lean_dec_ref(v_a_3523_);
lean_dec(v_savedTrace_3521_);
lean_dec_ref(v_inst_3519_);
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
v_a_3666_ = lean_ctor_get(v___x_3664_, 1);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3668_ = v___x_3664_;
v_isShared_3669_ = v_isSharedCheck_3676_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_inc(v_a_3665_);
lean_dec(v___x_3664_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3676_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3671_; 
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 0, v_a_3665_);
v___x_3671_ = v___x_3656_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3665_);
v___x_3671_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
lean_object* v___x_3673_; 
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 0, v___x_3671_);
v___x_3673_ = v___x_3668_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3671_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v_a_3666_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
else
{
lean_object* v_a_3677_; lean_object* v_a_3678_; lean_object* v_log_3679_; uint8_t v_action_3680_; uint8_t v_wantsRebuild_3681_; lean_object* v_trace_3682_; lean_object* v_buildTime_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3693_; 
lean_del_object(v___x_3656_);
v_a_3677_ = lean_ctor_get(v___x_3664_, 1);
lean_inc(v_a_3677_);
v_a_3678_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_a_3678_);
lean_dec_ref(v___x_3664_);
v_log_3679_ = lean_ctor_get(v_a_3677_, 0);
lean_inc_ref(v_log_3679_);
v_action_3680_ = lean_ctor_get_uint8(v_a_3677_, sizeof(void*)*3);
v_wantsRebuild_3681_ = lean_ctor_get_uint8(v_a_3677_, sizeof(void*)*3 + 1);
v_trace_3682_ = lean_ctor_get(v_a_3677_, 1);
lean_inc_ref(v_trace_3682_);
v_buildTime_3683_ = lean_ctor_get(v_a_3677_, 2);
lean_inc(v_buildTime_3683_);
lean_dec(v_a_3677_);
v___x_3684_ = lean_array_get_size(v_log_3679_);
lean_inc(v_a_3678_);
v___x_3685_ = l_Array_extract___redArg(v_log_3679_, v_a_3678_, v___x_3684_);
v___x_3686_ = l_Array_shrink___redArg(v_log_3679_, v_a_3678_);
lean_dec(v_a_3678_);
v___x_3687_ = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___closed__2));
v___x_3688_ = l_Lake_Hash_hex(v_inputHash_3520_);
v___x_3689_ = lean_unsigned_to_nat(7u);
v___x_3690_ = lean_unsigned_to_nat(0u);
v___x_3691_ = lean_string_utf8_byte_size(v___x_3688_);
lean_inc_ref(v___x_3688_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 2, v___x_3691_);
lean_ctor_set(v___x_3662_, 1, v___x_3690_);
lean_ctor_set(v___x_3662_, 0, v___x_3688_);
v___x_3693_ = v___x_3662_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3688_);
lean_ctor_set(v_reuseFailAlloc_3710_, 1, v___x_3690_);
lean_ctor_set(v_reuseFailAlloc_3710_, 2, v___x_3691_);
v___x_3693_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; uint8_t v___x_3702_; 
v___x_3694_ = l_String_Slice_Pos_nextn(v___x_3693_, v___x_3690_, v___x_3689_);
lean_dec_ref(v___x_3693_);
v___x_3695_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3688_);
lean_ctor_set(v___x_3695_, 1, v___x_3690_);
lean_ctor_set(v___x_3695_, 2, v___x_3694_);
v___x_3696_ = l_String_Slice_toString(v___x_3695_);
lean_dec_ref(v___x_3695_);
v___x_3697_ = lean_string_append(v___x_3687_, v___x_3696_);
lean_dec_ref(v___x_3696_);
v___x_3698_ = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___closed__3));
v___x_3699_ = lean_string_append(v___x_3697_, v___x_3698_);
v___x_3700_ = lean_array_get_size(v___x_3685_);
v___x_3701_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__10));
v___x_3702_ = lean_nat_dec_lt(v___x_3690_, v___x_3700_);
if (v___x_3702_ == 0)
{
lean_dec_ref(v___x_3685_);
v___y_3622_ = v_trace_3682_;
v___y_3623_ = v_a_3638_;
v___y_3624_ = v_buildTime_3683_;
v___y_3625_ = v___x_3648_;
v___y_3626_ = v_wantsRebuild_3681_;
v___y_3627_ = v___x_3686_;
v___y_3628_ = v_action_3680_;
v___y_3629_ = v___x_3699_;
goto v___jp_3621_;
}
else
{
uint8_t v___x_3703_; 
v___x_3703_ = lean_nat_dec_le(v___x_3700_, v___x_3700_);
if (v___x_3703_ == 0)
{
if (v___x_3702_ == 0)
{
lean_dec_ref(v___x_3685_);
v___y_3622_ = v_trace_3682_;
v___y_3623_ = v_a_3638_;
v___y_3624_ = v_buildTime_3683_;
v___y_3625_ = v___x_3648_;
v___y_3626_ = v_wantsRebuild_3681_;
v___y_3627_ = v___x_3686_;
v___y_3628_ = v_action_3680_;
v___y_3629_ = v___x_3699_;
goto v___jp_3621_;
}
else
{
size_t v___x_3704_; size_t v___x_3705_; lean_object* v___x_3706_; 
v___x_3704_ = ((size_t)0ULL);
v___x_3705_ = lean_usize_of_nat(v___x_3700_);
v___x_3706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3701_, v___f_3636_, v___x_3685_, v___x_3704_, v___x_3705_, v___x_3699_);
v___y_3622_ = v_trace_3682_;
v___y_3623_ = v_a_3638_;
v___y_3624_ = v_buildTime_3683_;
v___y_3625_ = v___x_3648_;
v___y_3626_ = v_wantsRebuild_3681_;
v___y_3627_ = v___x_3686_;
v___y_3628_ = v_action_3680_;
v___y_3629_ = v___x_3706_;
goto v___jp_3621_;
}
}
else
{
size_t v___x_3707_; size_t v___x_3708_; lean_object* v___x_3709_; 
v___x_3707_ = ((size_t)0ULL);
v___x_3708_ = lean_usize_of_nat(v___x_3700_);
v___x_3709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3701_, v___f_3636_, v___x_3685_, v___x_3707_, v___x_3708_, v___x_3699_);
v___y_3622_ = v_trace_3682_;
v___y_3623_ = v_a_3638_;
v___y_3624_ = v_buildTime_3683_;
v___y_3625_ = v___x_3648_;
v___y_3626_ = v_wantsRebuild_3681_;
v___y_3627_ = v___x_3686_;
v___y_3628_ = v_action_3680_;
v___y_3629_ = v___x_3709_;
goto v___jp_3621_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3650_);
v___y_3571_ = v_a_3638_;
v___y_3572_ = v___x_3648_;
v___y_3573_ = v_a_3523_;
v___y_3574_ = v_a_3524_;
v___y_3575_ = v_a_3525_;
v___y_3576_ = v_a_3526_;
v___y_3577_ = v_a_3527_;
v___y_3578_ = v___x_3653_;
goto v___jp_3570_;
}
}
}
else
{
lean_object* v_a_3714_; lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3725_; 
lean_dec_ref(v___x_3648_);
lean_dec_ref(v_lakeCache_3569_);
lean_dec_ref(v_a_3527_);
lean_dec(v_a_3526_);
lean_dec(v_a_3525_);
lean_dec(v_a_3524_);
lean_dec_ref(v_a_3523_);
lean_dec(v_savedTrace_3521_);
lean_dec_ref(v_inst_3519_);
v_a_3714_ = lean_ctor_get(v___x_3649_, 0);
v_a_3715_ = lean_ctor_get(v___x_3649_, 1);
v_isSharedCheck_3725_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3717_ = v___x_3649_;
v_isShared_3718_ = v_isSharedCheck_3725_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_inc(v_a_3714_);
lean_dec(v___x_3649_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3725_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 0, v_a_3715_);
v___x_3720_ = v___x_3646_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_a_3715_);
lean_ctor_set(v_reuseFailAlloc_3724_, 1, v_trace_3643_);
lean_ctor_set(v_reuseFailAlloc_3724_, 2, v_buildTime_3644_);
lean_ctor_set_uint8(v_reuseFailAlloc_3724_, sizeof(void*)*3, v_action_3641_);
lean_ctor_set_uint8(v_reuseFailAlloc_3724_, sizeof(void*)*3 + 1, v_wantsRebuild_3642_);
v___x_3720_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
lean_object* v___x_3722_; 
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 1, v___x_3720_);
v___x_3722_ = v___x_3717_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3714_);
lean_ctor_set(v_reuseFailAlloc_3723_, 1, v___x_3720_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___boxed(lean_object* v_inst_3737_, lean_object* v_inputHash_3738_, lean_object* v_savedTrace_3739_, lean_object* v_pkg_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_){
_start:
{
uint64_t v_inputHash_boxed_3748_; lean_object* v_res_3749_; 
v_inputHash_boxed_3748_ = lean_unbox_uint64(v_inputHash_3738_);
lean_dec_ref(v_inputHash_3738_);
v_res_3749_ = l_Lake_getArtifacts_x3f___redArg(v_inst_3737_, v_inputHash_boxed_3748_, v_savedTrace_3739_, v_pkg_3740_, v_a_3741_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_);
return v_res_3749_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f(lean_object* v_00_u03b1_3750_, lean_object* v_inst_3751_, uint64_t v_inputHash_3752_, lean_object* v_savedTrace_3753_, lean_object* v_pkg_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_){
_start:
{
lean_object* v___x_3762_; 
v___x_3762_ = l_Lake_getArtifacts_x3f___redArg(v_inst_3751_, v_inputHash_3752_, v_savedTrace_3753_, v_pkg_3754_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___boxed(lean_object* v_00_u03b1_3763_, lean_object* v_inst_3764_, lean_object* v_inputHash_3765_, lean_object* v_savedTrace_3766_, lean_object* v_pkg_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_){
_start:
{
uint64_t v_inputHash_boxed_3775_; lean_object* v_res_3776_; 
v_inputHash_boxed_3775_ = lean_unbox_uint64(v_inputHash_3765_);
lean_dec_ref(v_inputHash_3765_);
v_res_3776_ = l_Lake_getArtifacts_x3f(v_00_u03b1_3763_, v_inst_3764_, v_inputHash_boxed_3775_, v_savedTrace_3766_, v_pkg_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___redArg(lean_object* v_descr_3789_, lean_object* v_service_x3f_3790_, lean_object* v_scope_x3f_3791_, uint8_t v_exe_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_){
_start:
{
lean_object* v___y_3797_; lean_object* v_mtime_3798_; lean_object* v___y_3799_; lean_object* v___y_3803_; lean_object* v_log_3804_; uint8_t v_action_3805_; uint8_t v_wantsRebuild_3806_; lean_object* v_trace_3807_; lean_object* v_buildTime_3808_; lean_object* v_toContext_3823_; lean_object* v_log_3824_; uint8_t v_action_3825_; uint8_t v_wantsRebuild_3826_; lean_object* v_trace_3827_; lean_object* v_buildTime_3828_; lean_object* v_lakeConfig_3829_; lean_object* v_lakeCache_3830_; uint64_t v_hash_3831_; lean_object* v_ext_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___y_3836_; lean_object* v___x_3933_; lean_object* v___x_3934_; uint8_t v___x_3935_; 
v_toContext_3823_ = lean_ctor_get(v_a_3793_, 1);
lean_inc(v_toContext_3823_);
lean_dec_ref(v_a_3793_);
v_log_3824_ = lean_ctor_get(v_a_3794_, 0);
v_action_3825_ = lean_ctor_get_uint8(v_a_3794_, sizeof(void*)*3);
v_wantsRebuild_3826_ = lean_ctor_get_uint8(v_a_3794_, sizeof(void*)*3 + 1);
v_trace_3827_ = lean_ctor_get(v_a_3794_, 1);
v_buildTime_3828_ = lean_ctor_get(v_a_3794_, 2);
v_lakeConfig_3829_ = lean_ctor_get(v_toContext_3823_, 2);
lean_inc_ref(v_lakeConfig_3829_);
v_lakeCache_3830_ = lean_ctor_get(v_toContext_3823_, 3);
lean_inc_ref(v_lakeCache_3830_);
lean_dec(v_toContext_3823_);
v_hash_3831_ = lean_ctor_get_uint64(v_descr_3789_, sizeof(void*)*1);
v_ext_3832_ = lean_ctor_get(v_descr_3789_, 0);
v___x_3833_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
v___x_3834_ = l_System_FilePath_join(v_lakeCache_3830_, v___x_3833_);
v___x_3933_ = lean_string_utf8_byte_size(v_ext_3832_);
v___x_3934_ = lean_unsigned_to_nat(0u);
v___x_3935_ = lean_nat_dec_eq(v___x_3933_, v___x_3934_);
if (v___x_3935_ == 0)
{
lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3936_ = l_Lake_Hash_hex(v_hash_3831_);
v___x_3937_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_3938_ = lean_string_append(v___x_3936_, v___x_3937_);
v___x_3939_ = lean_string_append(v___x_3938_, v_ext_3832_);
v___y_3836_ = v___x_3939_;
goto v___jp_3835_;
}
else
{
lean_object* v___x_3940_; 
v___x_3940_ = l_Lake_Hash_hex(v_hash_3831_);
v___y_3836_ = v___x_3940_;
goto v___jp_3835_;
}
v___jp_3796_:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; 
lean_inc_ref(v___y_3797_);
v___x_3800_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3800_, 0, v_descr_3789_);
lean_ctor_set(v___x_3800_, 1, v___y_3797_);
lean_ctor_set(v___x_3800_, 2, v___y_3797_);
lean_ctor_set(v___x_3800_, 3, v_mtime_3798_);
v___x_3801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3800_);
lean_ctor_set(v___x_3801_, 1, v___y_3799_);
return v___x_3801_;
}
v___jp_3802_:
{
lean_object* v___x_3809_; 
v___x_3809_ = lean_io_metadata(v___y_3803_);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_object* v_a_3810_; lean_object* v_modified_3811_; lean_object* v___x_3812_; 
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_a_3810_);
lean_dec_ref(v___x_3809_);
v_modified_3811_ = lean_ctor_get(v_a_3810_, 1);
lean_inc_ref(v_modified_3811_);
lean_dec(v_a_3810_);
v___x_3812_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3812_, 0, v_log_3804_);
lean_ctor_set(v___x_3812_, 1, v_trace_3807_);
lean_ctor_set(v___x_3812_, 2, v_buildTime_3808_);
lean_ctor_set_uint8(v___x_3812_, sizeof(void*)*3, v_action_3805_);
lean_ctor_set_uint8(v___x_3812_, sizeof(void*)*3 + 1, v_wantsRebuild_3806_);
v___y_3797_ = v___y_3803_;
v_mtime_3798_ = v_modified_3811_;
v___y_3799_ = v___x_3812_;
goto v___jp_3796_;
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; uint8_t v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
lean_dec_ref(v___y_3803_);
lean_dec_ref(v_descr_3789_);
v_a_3813_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_a_3813_);
lean_dec_ref(v___x_3809_);
v___x_3814_ = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__0));
v___x_3815_ = lean_io_error_to_string(v_a_3813_);
v___x_3816_ = lean_string_append(v___x_3814_, v___x_3815_);
lean_dec_ref(v___x_3815_);
v___x_3817_ = 3;
v___x_3818_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3818_, 0, v___x_3816_);
lean_ctor_set_uint8(v___x_3818_, sizeof(void*)*1, v___x_3817_);
v___x_3819_ = lean_array_get_size(v_log_3804_);
v___x_3820_ = lean_array_push(v_log_3804_, v___x_3818_);
v___x_3821_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3821_, 0, v___x_3820_);
lean_ctor_set(v___x_3821_, 1, v_trace_3807_);
lean_ctor_set(v___x_3821_, 2, v_buildTime_3808_);
lean_ctor_set_uint8(v___x_3821_, sizeof(void*)*3, v_action_3805_);
lean_ctor_set_uint8(v___x_3821_, sizeof(void*)*3 + 1, v_wantsRebuild_3806_);
v___x_3822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3819_);
lean_ctor_set(v___x_3822_, 1, v___x_3821_);
return v___x_3822_;
}
}
v___jp_3835_:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3837_ = l_Lake_joinRelative(v___x_3834_, v___y_3836_);
v___x_3838_ = lean_io_metadata(v___x_3837_);
if (lean_obj_tag(v___x_3838_) == 0)
{
lean_object* v_a_3839_; lean_object* v_modified_3840_; 
lean_dec_ref(v_lakeConfig_3829_);
lean_dec(v_scope_x3f_3791_);
lean_dec(v_service_x3f_3790_);
v_a_3839_ = lean_ctor_get(v___x_3838_, 0);
lean_inc(v_a_3839_);
lean_dec_ref(v___x_3838_);
v_modified_3840_ = lean_ctor_get(v_a_3839_, 1);
lean_inc_ref(v_modified_3840_);
lean_dec(v_a_3839_);
v___y_3797_ = v___x_3837_;
v_mtime_3798_ = v_modified_3840_;
v___y_3799_ = v_a_3794_;
goto v___jp_3796_;
}
else
{
lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3929_; 
lean_inc(v_buildTime_3828_);
lean_inc_ref(v_trace_3827_);
lean_inc_ref(v_log_3824_);
v_isSharedCheck_3929_ = !lean_is_exclusive(v_a_3794_);
if (v_isSharedCheck_3929_ == 0)
{
lean_object* v_unused_3930_; lean_object* v_unused_3931_; lean_object* v_unused_3932_; 
v_unused_3930_ = lean_ctor_get(v_a_3794_, 2);
lean_dec(v_unused_3930_);
v_unused_3931_ = lean_ctor_get(v_a_3794_, 1);
lean_dec(v_unused_3931_);
v_unused_3932_ = lean_ctor_get(v_a_3794_, 0);
lean_dec(v_unused_3932_);
v___x_3842_ = v_a_3794_;
v_isShared_3843_ = v_isSharedCheck_3929_;
goto v_resetjp_3841_;
}
else
{
lean_dec(v_a_3794_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3929_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v_a_3844_; 
v_a_3844_ = lean_ctor_get(v___x_3838_, 0);
lean_inc(v_a_3844_);
lean_dec_ref(v___x_3838_);
if (lean_obj_tag(v_a_3844_) == 11)
{
lean_dec_ref(v_a_3844_);
if (lean_obj_tag(v_service_x3f_3790_) == 1)
{
lean_object* v_val_3845_; lean_object* v_cacheServices_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v_val_3845_ = lean_ctor_get(v_service_x3f_3790_, 0);
lean_inc(v_val_3845_);
lean_dec_ref(v_service_x3f_3790_);
v_cacheServices_3846_ = lean_ctor_get(v_lakeConfig_3829_, 3);
lean_inc(v_cacheServices_3846_);
lean_dec_ref(v_lakeConfig_3829_);
v___x_3847_ = lean_box(0);
lean_inc(v_val_3845_);
v___x_3848_ = l_Lean_Name_str___override(v___x_3847_, v_val_3845_);
v___x_3849_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_cacheServices_3846_, v___x_3848_);
lean_dec(v___x_3848_);
lean_dec(v_cacheServices_3846_);
if (lean_obj_tag(v___x_3849_) == 1)
{
lean_dec(v_val_3845_);
if (lean_obj_tag(v_scope_x3f_3791_) == 1)
{
lean_object* v_val_3850_; lean_object* v_val_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; uint8_t v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
v_val_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_val_3850_);
lean_dec_ref(v___x_3849_);
v_val_3851_ = lean_ctor_get(v_scope_x3f_3791_, 0);
lean_inc(v_val_3851_);
lean_dec_ref(v_scope_x3f_3791_);
v___x_3852_ = l_Lake_CacheService_artifactUrl(v_hash_3831_, v_val_3850_, v_val_3851_);
v___x_3853_ = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__1));
v___x_3854_ = l_Lake_Hash_hex(v_hash_3831_);
v___x_3855_ = lean_string_append(v___x_3853_, v___x_3854_);
lean_dec_ref(v___x_3854_);
v___x_3856_ = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__2));
v___x_3857_ = lean_string_append(v___x_3855_, v___x_3856_);
v___x_3858_ = lean_string_append(v___x_3857_, v___x_3837_);
v___x_3859_ = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__3));
v___x_3860_ = lean_string_append(v___x_3858_, v___x_3859_);
v___x_3861_ = lean_string_append(v___x_3860_, v___x_3852_);
v___x_3862_ = 0;
v___x_3863_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3863_, 0, v___x_3861_);
lean_ctor_set_uint8(v___x_3863_, sizeof(void*)*1, v___x_3862_);
v___x_3864_ = lean_array_push(v_log_3824_, v___x_3863_);
lean_inc_ref(v___x_3837_);
v___x_3865_ = l_Lake_downloadArtifactCore(v_hash_3831_, v___x_3852_, v___x_3837_, v___x_3864_);
if (lean_obj_tag(v___x_3865_) == 0)
{
lean_object* v_a_3866_; uint8_t v___x_3867_; uint8_t v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
lean_del_object(v___x_3842_);
v_a_3866_ = lean_ctor_get(v___x_3865_, 1);
lean_inc(v_a_3866_);
lean_dec_ref(v___x_3865_);
v___x_3867_ = 1;
v___x_3868_ = 0;
v___x_3869_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_3869_, 0, v___x_3867_);
lean_ctor_set_uint8(v___x_3869_, 1, v___x_3868_);
lean_ctor_set_uint8(v___x_3869_, 2, v_exe_3792_);
lean_inc_ref_n(v___x_3869_, 2);
v___x_3870_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3869_);
lean_ctor_set(v___x_3870_, 1, v___x_3869_);
lean_ctor_set(v___x_3870_, 2, v___x_3869_);
v___x_3871_ = l_IO_setAccessRights(v___x_3837_, v___x_3870_);
lean_dec_ref(v___x_3870_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_dec_ref(v___x_3871_);
v___y_3803_ = v___x_3837_;
v_log_3804_ = v_a_3866_;
v_action_3805_ = v_action_3825_;
v_wantsRebuild_3806_ = v_wantsRebuild_3826_;
v_trace_3807_ = v_trace_3827_;
v_buildTime_3808_ = v_buildTime_3828_;
goto v___jp_3802_;
}
else
{
lean_object* v_a_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; uint8_t v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_a_3872_);
lean_dec_ref(v___x_3871_);
v___x_3873_ = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__4));
v___x_3874_ = lean_io_error_to_string(v_a_3872_);
v___x_3875_ = lean_string_append(v___x_3873_, v___x_3874_);
lean_dec_ref(v___x_3874_);
v___x_3876_ = 2;
v___x_3877_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3877_, 0, v___x_3875_);
lean_ctor_set_uint8(v___x_3877_, sizeof(void*)*1, v___x_3876_);
v___x_3878_ = lean_array_push(v_a_3866_, v___x_3877_);
v___y_3803_ = v___x_3837_;
v_log_3804_ = v___x_3878_;
v_action_3805_ = v_action_3825_;
v_wantsRebuild_3806_ = v_wantsRebuild_3826_;
v_trace_3807_ = v_trace_3827_;
v_buildTime_3808_ = v_buildTime_3828_;
goto v___jp_3802_;
}
}
else
{
lean_object* v_a_3879_; lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3890_; 
lean_dec_ref(v___x_3837_);
lean_dec_ref(v_descr_3789_);
v_a_3879_ = lean_ctor_get(v___x_3865_, 0);
v_a_3880_ = lean_ctor_get(v___x_3865_, 1);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3865_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3882_ = v___x_3865_;
v_isShared_3883_ = v_isSharedCheck_3890_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_inc(v_a_3879_);
lean_dec(v___x_3865_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3890_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3843_ == 0)
{
lean_ctor_set(v___x_3842_, 0, v_a_3880_);
v___x_3885_ = v___x_3842_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_a_3880_);
lean_ctor_set(v_reuseFailAlloc_3889_, 1, v_trace_3827_);
lean_ctor_set(v_reuseFailAlloc_3889_, 2, v_buildTime_3828_);
lean_ctor_set_uint8(v_reuseFailAlloc_3889_, sizeof(void*)*3, v_action_3825_);
lean_ctor_set_uint8(v_reuseFailAlloc_3889_, sizeof(void*)*3 + 1, v_wantsRebuild_3826_);
v___x_3885_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
lean_object* v___x_3887_; 
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 1, v___x_3885_);
v___x_3887_ = v___x_3882_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_a_3879_);
lean_ctor_set(v_reuseFailAlloc_3888_, 1, v___x_3885_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
}
}
}
else
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3895_; 
lean_dec_ref(v___x_3849_);
lean_dec_ref(v___x_3837_);
lean_dec(v_scope_x3f_3791_);
lean_dec_ref(v_descr_3789_);
v___x_3891_ = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__6));
v___x_3892_ = lean_array_get_size(v_log_3824_);
v___x_3893_ = lean_array_push(v_log_3824_, v___x_3891_);
if (v_isShared_3843_ == 0)
{
lean_ctor_set(v___x_3842_, 0, v___x_3893_);
v___x_3895_ = v___x_3842_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3893_);
lean_ctor_set(v_reuseFailAlloc_3897_, 1, v_trace_3827_);
lean_ctor_set(v_reuseFailAlloc_3897_, 2, v_buildTime_3828_);
lean_ctor_set_uint8(v_reuseFailAlloc_3897_, sizeof(void*)*3, v_action_3825_);
lean_ctor_set_uint8(v_reuseFailAlloc_3897_, sizeof(void*)*3 + 1, v_wantsRebuild_3826_);
v___x_3895_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
lean_object* v___x_3896_; 
v___x_3896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3892_);
lean_ctor_set(v___x_3896_, 1, v___x_3895_);
return v___x_3896_;
}
}
}
else
{
lean_object* v___x_3898_; lean_object* v___x_3899_; uint8_t v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3905_; 
lean_dec(v___x_3849_);
lean_dec_ref(v___x_3837_);
lean_dec(v_scope_x3f_3791_);
lean_dec_ref(v_descr_3789_);
v___x_3898_ = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__7));
v___x_3899_ = lean_string_append(v___x_3898_, v_val_3845_);
lean_dec(v_val_3845_);
v___x_3900_ = 3;
v___x_3901_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3901_, 0, v___x_3899_);
lean_ctor_set_uint8(v___x_3901_, sizeof(void*)*1, v___x_3900_);
v___x_3902_ = lean_array_get_size(v_log_3824_);
v___x_3903_ = lean_array_push(v_log_3824_, v___x_3901_);
if (v_isShared_3843_ == 0)
{
lean_ctor_set(v___x_3842_, 0, v___x_3903_);
v___x_3905_ = v___x_3842_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v___x_3903_);
lean_ctor_set(v_reuseFailAlloc_3907_, 1, v_trace_3827_);
lean_ctor_set(v_reuseFailAlloc_3907_, 2, v_buildTime_3828_);
lean_ctor_set_uint8(v_reuseFailAlloc_3907_, sizeof(void*)*3, v_action_3825_);
lean_ctor_set_uint8(v_reuseFailAlloc_3907_, sizeof(void*)*3 + 1, v_wantsRebuild_3826_);
v___x_3905_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
lean_object* v___x_3906_; 
v___x_3906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3902_);
lean_ctor_set(v___x_3906_, 1, v___x_3905_);
return v___x_3906_;
}
}
}
else
{
lean_object* v___x_3908_; lean_object* v___x_3909_; uint8_t v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3915_; 
lean_dec_ref(v_lakeConfig_3829_);
lean_dec(v_scope_x3f_3791_);
lean_dec(v_service_x3f_3790_);
lean_dec_ref(v_descr_3789_);
v___x_3908_ = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__8));
v___x_3909_ = lean_string_append(v___x_3908_, v___x_3837_);
lean_dec_ref(v___x_3837_);
v___x_3910_ = 3;
v___x_3911_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3911_, 0, v___x_3909_);
lean_ctor_set_uint8(v___x_3911_, sizeof(void*)*1, v___x_3910_);
v___x_3912_ = lean_array_get_size(v_log_3824_);
v___x_3913_ = lean_array_push(v_log_3824_, v___x_3911_);
if (v_isShared_3843_ == 0)
{
lean_ctor_set(v___x_3842_, 0, v___x_3913_);
v___x_3915_ = v___x_3842_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3913_);
lean_ctor_set(v_reuseFailAlloc_3917_, 1, v_trace_3827_);
lean_ctor_set(v_reuseFailAlloc_3917_, 2, v_buildTime_3828_);
lean_ctor_set_uint8(v_reuseFailAlloc_3917_, sizeof(void*)*3, v_action_3825_);
lean_ctor_set_uint8(v_reuseFailAlloc_3917_, sizeof(void*)*3 + 1, v_wantsRebuild_3826_);
v___x_3915_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
lean_object* v___x_3916_; 
v___x_3916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3912_);
lean_ctor_set(v___x_3916_, 1, v___x_3915_);
return v___x_3916_;
}
}
}
else
{
lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; uint8_t v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3926_; 
lean_dec_ref(v___x_3837_);
lean_dec_ref(v_lakeConfig_3829_);
lean_dec(v_scope_x3f_3791_);
lean_dec(v_service_x3f_3790_);
lean_dec_ref(v_descr_3789_);
v___x_3918_ = ((lean_object*)(l_Lake_resolveArtifact___redArg___closed__9));
v___x_3919_ = lean_io_error_to_string(v_a_3844_);
v___x_3920_ = lean_string_append(v___x_3918_, v___x_3919_);
lean_dec_ref(v___x_3919_);
v___x_3921_ = 3;
v___x_3922_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3922_, 0, v___x_3920_);
lean_ctor_set_uint8(v___x_3922_, sizeof(void*)*1, v___x_3921_);
v___x_3923_ = lean_array_get_size(v_log_3824_);
v___x_3924_ = lean_array_push(v_log_3824_, v___x_3922_);
if (v_isShared_3843_ == 0)
{
lean_ctor_set(v___x_3842_, 0, v___x_3924_);
v___x_3926_ = v___x_3842_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3924_);
lean_ctor_set(v_reuseFailAlloc_3928_, 1, v_trace_3827_);
lean_ctor_set(v_reuseFailAlloc_3928_, 2, v_buildTime_3828_);
lean_ctor_set_uint8(v_reuseFailAlloc_3928_, sizeof(void*)*3, v_action_3825_);
lean_ctor_set_uint8(v_reuseFailAlloc_3928_, sizeof(void*)*3 + 1, v_wantsRebuild_3826_);
v___x_3926_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
lean_object* v___x_3927_; 
v___x_3927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3923_);
lean_ctor_set(v___x_3927_, 1, v___x_3926_);
return v___x_3927_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___redArg___boxed(lean_object* v_descr_3941_, lean_object* v_service_x3f_3942_, lean_object* v_scope_x3f_3943_, lean_object* v_exe_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_){
_start:
{
uint8_t v_exe_boxed_3948_; lean_object* v_res_3949_; 
v_exe_boxed_3948_ = lean_unbox(v_exe_3944_);
v_res_3949_ = l_Lake_resolveArtifact___redArg(v_descr_3941_, v_service_x3f_3942_, v_scope_x3f_3943_, v_exe_boxed_3948_, v_a_3945_, v_a_3946_);
return v_res_3949_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact(lean_object* v_descr_3950_, lean_object* v_service_x3f_3951_, lean_object* v_scope_x3f_3952_, uint8_t v_exe_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_){
_start:
{
lean_object* v___x_3961_; 
v___x_3961_ = l_Lake_resolveArtifact___redArg(v_descr_3950_, v_service_x3f_3951_, v_scope_x3f_3952_, v_exe_3953_, v_a_3958_, v_a_3959_);
return v___x_3961_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___boxed(lean_object* v_descr_3962_, lean_object* v_service_x3f_3963_, lean_object* v_scope_x3f_3964_, lean_object* v_exe_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_){
_start:
{
uint8_t v_exe_boxed_3973_; lean_object* v_res_3974_; 
v_exe_boxed_3973_ = lean_unbox(v_exe_3965_);
v_res_3974_ = l_Lake_resolveArtifact(v_descr_3962_, v_service_x3f_3963_, v_scope_x3f_3964_, v_exe_boxed_3973_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_);
lean_dec(v_a_3969_);
lean_dec(v_a_3968_);
lean_dec(v_a_3967_);
lean_dec_ref(v_a_3966_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg(lean_object* v_out_3977_, lean_object* v_service_x3f_3978_, lean_object* v_scope_x3f_3979_, uint8_t v_exe_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_){
_start:
{
lean_object* v___x_3984_; 
lean_inc(v_out_3977_);
v___x_3984_ = l_Lake_ArtifactDescr_fromJson_x3f(v_out_3977_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v_a_3985_; lean_object* v_log_3986_; uint8_t v_action_3987_; uint8_t v_wantsRebuild_3988_; lean_object* v_trace_3989_; lean_object* v_buildTime_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_4012_; 
lean_dec_ref(v_a_3981_);
lean_dec(v_scope_x3f_3979_);
lean_dec(v_service_x3f_3978_);
v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_a_3985_);
lean_dec_ref(v___x_3984_);
v_log_3986_ = lean_ctor_get(v_a_3982_, 0);
v_action_3987_ = lean_ctor_get_uint8(v_a_3982_, sizeof(void*)*3);
v_wantsRebuild_3988_ = lean_ctor_get_uint8(v_a_3982_, sizeof(void*)*3 + 1);
v_trace_3989_ = lean_ctor_get(v_a_3982_, 1);
v_buildTime_3990_ = lean_ctor_get(v_a_3982_, 2);
v_isSharedCheck_4012_ = !lean_is_exclusive(v_a_3982_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_3992_ = v_a_3982_;
v_isShared_3993_ = v_isSharedCheck_4012_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_buildTime_3990_);
lean_inc(v_trace_3989_);
lean_inc(v_log_3986_);
lean_dec(v_a_3982_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_4012_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; uint8_t v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4009_; 
v___x_3994_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg___closed__0));
v___x_3995_ = l_Lean_Json_render(v_out_3977_);
v___x_3996_ = lean_unsigned_to_nat(80u);
v___x_3997_ = lean_unsigned_to_nat(2u);
v___x_3998_ = lean_unsigned_to_nat(0u);
v___x_3999_ = l_Std_Format_pretty(v___x_3995_, v___x_3996_, v___x_3997_, v___x_3998_);
v___x_4000_ = lean_string_append(v___x_3994_, v___x_3999_);
lean_dec_ref(v___x_3999_);
v___x_4001_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg___closed__1));
v___x_4002_ = lean_string_append(v___x_4000_, v___x_4001_);
v___x_4003_ = lean_string_append(v___x_4002_, v_a_3985_);
lean_dec(v_a_3985_);
v___x_4004_ = 3;
v___x_4005_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4005_, 0, v___x_4003_);
lean_ctor_set_uint8(v___x_4005_, sizeof(void*)*1, v___x_4004_);
v___x_4006_ = lean_array_get_size(v_log_3986_);
v___x_4007_ = lean_array_push(v_log_3986_, v___x_4005_);
if (v_isShared_3993_ == 0)
{
lean_ctor_set(v___x_3992_, 0, v___x_4007_);
v___x_4009_ = v___x_3992_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_4007_);
lean_ctor_set(v_reuseFailAlloc_4011_, 1, v_trace_3989_);
lean_ctor_set(v_reuseFailAlloc_4011_, 2, v_buildTime_3990_);
lean_ctor_set_uint8(v_reuseFailAlloc_4011_, sizeof(void*)*3, v_action_3987_);
lean_ctor_set_uint8(v_reuseFailAlloc_4011_, sizeof(void*)*3 + 1, v_wantsRebuild_3988_);
v___x_4009_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
lean_object* v___x_4010_; 
v___x_4010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4006_);
lean_ctor_set(v___x_4010_, 1, v___x_4009_);
return v___x_4010_;
}
}
}
else
{
lean_object* v_a_4013_; lean_object* v___x_4014_; 
lean_dec(v_out_3977_);
v_a_4013_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_a_4013_);
lean_dec_ref(v___x_3984_);
v___x_4014_ = l_Lake_resolveArtifact___redArg(v_a_4013_, v_service_x3f_3978_, v_scope_x3f_3979_, v_exe_3980_, v_a_3981_, v_a_3982_);
return v___x_4014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg___boxed(lean_object* v_out_4015_, lean_object* v_service_x3f_4016_, lean_object* v_scope_x3f_4017_, lean_object* v_exe_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_){
_start:
{
uint8_t v_exe_boxed_4022_; lean_object* v_res_4023_; 
v_exe_boxed_4022_ = lean_unbox(v_exe_4018_);
v_res_4023_ = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg(v_out_4015_, v_service_x3f_4016_, v_scope_x3f_4017_, v_exe_boxed_4022_, v_a_4019_, v_a_4020_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput(lean_object* v_out_4024_, lean_object* v_service_x3f_4025_, lean_object* v_scope_x3f_4026_, uint8_t v_exe_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_){
_start:
{
lean_object* v___x_4035_; 
v___x_4035_ = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg(v_out_4024_, v_service_x3f_4025_, v_scope_x3f_4026_, v_exe_4027_, v_a_4032_, v_a_4033_);
return v___x_4035_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___boxed(lean_object* v_out_4036_, lean_object* v_service_x3f_4037_, lean_object* v_scope_x3f_4038_, lean_object* v_exe_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_){
_start:
{
uint8_t v_exe_boxed_4047_; lean_object* v_res_4048_; 
v_exe_boxed_4047_ = lean_unbox(v_exe_4039_);
v_res_4048_ = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput(v_out_4036_, v_service_x3f_4037_, v_scope_x3f_4038_, v_exe_boxed_4047_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_);
lean_dec(v_a_4043_);
lean_dec(v_a_4042_);
lean_dec(v_a_4041_);
lean_dec_ref(v_a_4040_);
return v_res_4048_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(uint8_t v_exe_4049_, lean_object* v_out_4050_, lean_object* v_service_x3f_4051_, lean_object* v_scope_x3f_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_){
_start:
{
lean_object* v___x_4060_; 
v___x_4060_ = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg(v_out_4050_, v_service_x3f_4051_, v_scope_x3f_4052_, v_exe_4049_, v___y_4057_, v___y_4058_);
return v___x_4060_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed(lean_object* v_exe_4061_, lean_object* v_out_4062_, lean_object* v_service_x3f_4063_, lean_object* v_scope_x3f_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_){
_start:
{
uint8_t v_exe_boxed_4072_; lean_object* v_res_4073_; 
v_exe_boxed_4072_ = lean_unbox(v_exe_4061_);
v_res_4073_ = l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(v_exe_boxed_4072_, v_out_4062_, v_service_x3f_4063_, v_scope_x3f_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
lean_dec(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
return v_res_4073_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(uint8_t v_exe_4074_){
_start:
{
lean_object* v___x_4075_; lean_object* v___f_4076_; 
v___x_4075_ = lean_box(v_exe_4074_);
v___f_4076_ = lean_alloc_closure((void*)(l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed), 11, 1);
lean_closure_set(v___f_4076_, 0, v___x_4075_);
return v___f_4076_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___boxed(lean_object* v_exe_4077_){
_start:
{
uint8_t v_exe_boxed_4078_; lean_object* v_res_4079_; 
v_exe_boxed_4078_ = lean_unbox(v_exe_4077_);
v_res_4079_ = l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(v_exe_boxed_4078_);
return v_res_4079_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg(lean_object* v_path_4080_, lean_object* v_ext_4081_, uint8_t v_text_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_){
_start:
{
lean_object* v___x_4086_; 
lean_inc_ref(v_path_4080_);
v___x_4086_ = l_Lake_fetchFileHash___redArg(v_path_4080_, v_text_4082_, v_a_4083_, v_a_4084_);
if (lean_obj_tag(v___x_4086_) == 0)
{
lean_object* v_a_4087_; lean_object* v_a_4088_; lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4105_; 
v_a_4087_ = lean_ctor_get(v___x_4086_, 0);
v_a_4088_ = lean_ctor_get(v___x_4086_, 1);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4090_ = v___x_4086_;
v_isShared_4091_ = v_isSharedCheck_4105_;
goto v_resetjp_4089_;
}
else
{
lean_inc(v_a_4088_);
lean_inc(v_a_4087_);
lean_dec(v___x_4086_);
v___x_4090_ = lean_box(0);
v_isShared_4091_ = v_isSharedCheck_4105_;
goto v_resetjp_4089_;
}
v_resetjp_4089_:
{
lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___x_4101_; 
v___x_4101_ = lean_io_metadata(v_path_4080_);
if (lean_obj_tag(v___x_4101_) == 0)
{
lean_object* v_a_4102_; lean_object* v_modified_4103_; 
v_a_4102_ = lean_ctor_get(v___x_4101_, 0);
lean_inc(v_a_4102_);
lean_dec_ref(v___x_4101_);
v_modified_4103_ = lean_ctor_get(v_a_4102_, 1);
lean_inc_ref(v_modified_4103_);
lean_dec(v_a_4102_);
v___y_4093_ = v_a_4088_;
v___y_4094_ = v_modified_4103_;
goto v___jp_4092_;
}
else
{
lean_object* v___x_4104_; 
lean_dec_ref(v___x_4101_);
v___x_4104_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___y_4093_ = v_a_4088_;
v___y_4094_ = v___x_4104_;
goto v___jp_4092_;
}
v___jp_4092_:
{
lean_object* v___x_4095_; uint64_t v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4099_; 
v___x_4095_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4095_, 0, v_ext_4081_);
v___x_4096_ = lean_unbox_uint64(v_a_4087_);
lean_dec(v_a_4087_);
lean_ctor_set_uint64(v___x_4095_, sizeof(void*)*1, v___x_4096_);
lean_inc_ref(v_path_4080_);
v___x_4097_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4095_);
lean_ctor_set(v___x_4097_, 1, v_path_4080_);
lean_ctor_set(v___x_4097_, 2, v_path_4080_);
lean_ctor_set(v___x_4097_, 3, v___y_4094_);
if (v_isShared_4091_ == 0)
{
lean_ctor_set(v___x_4090_, 1, v___y_4093_);
lean_ctor_set(v___x_4090_, 0, v___x_4097_);
v___x_4099_ = v___x_4090_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v___x_4097_);
lean_ctor_set(v_reuseFailAlloc_4100_, 1, v___y_4093_);
v___x_4099_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
return v___x_4099_;
}
}
}
}
else
{
lean_object* v_a_4106_; lean_object* v_a_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4114_; 
lean_dec_ref(v_ext_4081_);
lean_dec_ref(v_path_4080_);
v_a_4106_ = lean_ctor_get(v___x_4086_, 0);
v_a_4107_ = lean_ctor_get(v___x_4086_, 1);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4109_ = v___x_4086_;
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_inc(v_a_4106_);
lean_dec(v___x_4086_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4112_; 
if (v_isShared_4110_ == 0)
{
v___x_4112_ = v___x_4109_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_a_4106_);
lean_ctor_set(v_reuseFailAlloc_4113_, 1, v_a_4107_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
return v___x_4112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg___boxed(lean_object* v_path_4115_, lean_object* v_ext_4116_, lean_object* v_text_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_){
_start:
{
uint8_t v_text_boxed_4121_; lean_object* v_res_4122_; 
v_text_boxed_4121_ = lean_unbox(v_text_4117_);
v_res_4122_ = l_Lake_computeArtifact___redArg(v_path_4115_, v_ext_4116_, v_text_boxed_4121_, v_a_4118_, v_a_4119_);
lean_dec_ref(v_a_4118_);
return v_res_4122_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact(lean_object* v_path_4123_, lean_object* v_ext_4124_, uint8_t v_text_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_){
_start:
{
lean_object* v___x_4133_; 
v___x_4133_ = l_Lake_computeArtifact___redArg(v_path_4123_, v_ext_4124_, v_text_4125_, v_a_4130_, v_a_4131_);
return v___x_4133_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___boxed(lean_object* v_path_4134_, lean_object* v_ext_4135_, lean_object* v_text_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_){
_start:
{
uint8_t v_text_boxed_4144_; lean_object* v_res_4145_; 
v_text_boxed_4144_ = lean_unbox(v_text_4136_);
v_res_4145_ = l_Lake_computeArtifact(v_path_4134_, v_ext_4135_, v_text_boxed_4144_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_, v_a_4142_);
lean_dec_ref(v_a_4141_);
lean_dec(v_a_4140_);
lean_dec(v_a_4139_);
lean_dec(v_a_4138_);
lean_dec_ref(v_a_4137_);
return v_res_4145_;
}
}
LEAN_EXPORT lean_object* l_Lake_restoreArtifact(lean_object* v_file_4149_, lean_object* v_art_4150_, uint8_t v_exe_4151_, lean_object* v_a_4152_){
_start:
{
lean_object* v___y_4155_; uint8_t v___x_4168_; 
v___x_4168_ = l_System_FilePath_pathExists(v_file_4149_);
if (v___x_4168_ == 0)
{
lean_object* v_descr_4169_; lean_object* v_path_4170_; lean_object* v___y_4172_; lean_object* v___x_4187_; lean_object* v___x_4188_; uint8_t v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
v_descr_4169_ = lean_ctor_get(v_art_4150_, 0);
v_path_4170_ = lean_ctor_get(v_art_4150_, 1);
v___x_4187_ = ((lean_object*)(l_Lake_restoreArtifact___closed__1));
v___x_4188_ = lean_string_append(v___x_4187_, v_path_4170_);
v___x_4189_ = 0;
v___x_4190_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4190_, 0, v___x_4188_);
lean_ctor_set_uint8(v___x_4190_, sizeof(void*)*1, v___x_4189_);
v___x_4191_ = lean_array_push(v_a_4152_, v___x_4190_);
lean_inc_ref(v_file_4149_);
v___x_4192_ = l_Lake_createParentDirs(v_file_4149_);
if (lean_obj_tag(v___x_4192_) == 0)
{
lean_object* v___x_4193_; 
lean_dec_ref(v___x_4192_);
v___x_4193_ = lean_io_hard_link(v_path_4170_, v_file_4149_);
if (lean_obj_tag(v___x_4193_) == 0)
{
lean_dec_ref(v___x_4193_);
v___y_4172_ = v___x_4191_;
goto v___jp_4171_;
}
else
{
lean_object* v_a_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
v_a_4194_ = lean_ctor_get(v___x_4193_, 0);
lean_inc(v_a_4194_);
lean_dec_ref(v___x_4193_);
v___x_4195_ = ((lean_object*)(l_Lake_restoreArtifact___closed__2));
v___x_4196_ = lean_io_error_to_string(v_a_4194_);
v___x_4197_ = lean_string_append(v___x_4195_, v___x_4196_);
lean_dec_ref(v___x_4196_);
v___x_4198_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4198_, 0, v___x_4197_);
lean_ctor_set_uint8(v___x_4198_, sizeof(void*)*1, v___x_4189_);
v___x_4199_ = lean_array_push(v___x_4191_, v___x_4198_);
v___x_4200_ = l_Lake_copyFile(v_path_4170_, v_file_4149_);
if (lean_obj_tag(v___x_4200_) == 0)
{
uint8_t v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
lean_dec_ref(v___x_4200_);
v___x_4201_ = 1;
v___x_4202_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4202_, 0, v___x_4201_);
lean_ctor_set_uint8(v___x_4202_, 1, v___x_4168_);
lean_ctor_set_uint8(v___x_4202_, 2, v_exe_4151_);
lean_inc_ref_n(v___x_4202_, 2);
v___x_4203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4202_);
lean_ctor_set(v___x_4203_, 1, v___x_4202_);
lean_ctor_set(v___x_4203_, 2, v___x_4202_);
v___x_4204_ = l_IO_setAccessRights(v_file_4149_, v___x_4203_);
lean_dec_ref(v___x_4203_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_dec_ref(v___x_4204_);
v___y_4172_ = v___x_4199_;
goto v___jp_4171_;
}
else
{
lean_object* v_a_4205_; lean_object* v___x_4206_; uint8_t v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
lean_dec_ref(v_art_4150_);
lean_dec_ref(v_file_4149_);
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
lean_inc(v_a_4205_);
lean_dec_ref(v___x_4204_);
v___x_4206_ = lean_io_error_to_string(v_a_4205_);
v___x_4207_ = 3;
v___x_4208_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4208_, 0, v___x_4206_);
lean_ctor_set_uint8(v___x_4208_, sizeof(void*)*1, v___x_4207_);
v___x_4209_ = lean_array_get_size(v___x_4199_);
v___x_4210_ = lean_array_push(v___x_4199_, v___x_4208_);
v___x_4211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4211_, 0, v___x_4209_);
lean_ctor_set(v___x_4211_, 1, v___x_4210_);
return v___x_4211_;
}
}
else
{
lean_object* v_a_4212_; lean_object* v___x_4213_; uint8_t v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; 
lean_dec_ref(v_art_4150_);
lean_dec_ref(v_file_4149_);
v_a_4212_ = lean_ctor_get(v___x_4200_, 0);
lean_inc(v_a_4212_);
lean_dec_ref(v___x_4200_);
v___x_4213_ = lean_io_error_to_string(v_a_4212_);
v___x_4214_ = 3;
v___x_4215_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4215_, 0, v___x_4213_);
lean_ctor_set_uint8(v___x_4215_, sizeof(void*)*1, v___x_4214_);
v___x_4216_ = lean_array_get_size(v___x_4199_);
v___x_4217_ = lean_array_push(v___x_4199_, v___x_4215_);
v___x_4218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4218_, 0, v___x_4216_);
lean_ctor_set(v___x_4218_, 1, v___x_4217_);
return v___x_4218_;
}
}
}
else
{
lean_object* v_a_4219_; lean_object* v___x_4220_; uint8_t v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
lean_dec_ref(v_art_4150_);
lean_dec_ref(v_file_4149_);
v_a_4219_ = lean_ctor_get(v___x_4192_, 0);
lean_inc(v_a_4219_);
lean_dec_ref(v___x_4192_);
v___x_4220_ = lean_io_error_to_string(v_a_4219_);
v___x_4221_ = 3;
v___x_4222_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4222_, 0, v___x_4220_);
lean_ctor_set_uint8(v___x_4222_, sizeof(void*)*1, v___x_4221_);
v___x_4223_ = lean_array_get_size(v___x_4191_);
v___x_4224_ = lean_array_push(v___x_4191_, v___x_4222_);
v___x_4225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4225_, 0, v___x_4223_);
lean_ctor_set(v___x_4225_, 1, v___x_4224_);
return v___x_4225_;
}
v___jp_4171_:
{
uint64_t v_hash_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; uint8_t v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
v_hash_4173_ = lean_ctor_get_uint64(v_descr_4169_, sizeof(void*)*1);
v___x_4174_ = ((lean_object*)(l_Lake_restoreArtifact___closed__0));
v___x_4175_ = lean_string_append(v___x_4174_, v_file_4149_);
v___x_4176_ = 0;
v___x_4177_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4177_, 0, v___x_4175_);
lean_ctor_set_uint8(v___x_4177_, sizeof(void*)*1, v___x_4176_);
v___x_4178_ = lean_array_push(v___y_4172_, v___x_4177_);
lean_inc_ref(v_file_4149_);
v___x_4179_ = l_Lake_writeFileHash(v_file_4149_, v_hash_4173_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_dec_ref(v___x_4179_);
v___y_4155_ = v___x_4178_;
goto v___jp_4154_;
}
else
{
lean_object* v_a_4180_; lean_object* v___x_4181_; uint8_t v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
lean_dec_ref(v_art_4150_);
lean_dec_ref(v_file_4149_);
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
lean_inc(v_a_4180_);
lean_dec_ref(v___x_4179_);
v___x_4181_ = lean_io_error_to_string(v_a_4180_);
v___x_4182_ = 3;
v___x_4183_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4183_, 0, v___x_4181_);
lean_ctor_set_uint8(v___x_4183_, sizeof(void*)*1, v___x_4182_);
v___x_4184_ = lean_array_get_size(v___x_4178_);
v___x_4185_ = lean_array_push(v___x_4178_, v___x_4183_);
v___x_4186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4186_, 0, v___x_4184_);
lean_ctor_set(v___x_4186_, 1, v___x_4185_);
return v___x_4186_;
}
}
}
else
{
v___y_4155_ = v_a_4152_;
goto v___jp_4154_;
}
v___jp_4154_:
{
lean_object* v_descr_4156_; lean_object* v_mtime_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4165_; 
v_descr_4156_ = lean_ctor_get(v_art_4150_, 0);
v_mtime_4157_ = lean_ctor_get(v_art_4150_, 3);
v_isSharedCheck_4165_ = !lean_is_exclusive(v_art_4150_);
if (v_isSharedCheck_4165_ == 0)
{
lean_object* v_unused_4166_; lean_object* v_unused_4167_; 
v_unused_4166_ = lean_ctor_get(v_art_4150_, 2);
lean_dec(v_unused_4166_);
v_unused_4167_ = lean_ctor_get(v_art_4150_, 1);
lean_dec(v_unused_4167_);
v___x_4159_ = v_art_4150_;
v_isShared_4160_ = v_isSharedCheck_4165_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_mtime_4157_);
lean_inc(v_descr_4156_);
lean_dec(v_art_4150_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4165_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4162_; 
lean_inc_ref(v_file_4149_);
if (v_isShared_4160_ == 0)
{
lean_ctor_set(v___x_4159_, 2, v_file_4149_);
lean_ctor_set(v___x_4159_, 1, v_file_4149_);
v___x_4162_ = v___x_4159_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_descr_4156_);
lean_ctor_set(v_reuseFailAlloc_4164_, 1, v_file_4149_);
lean_ctor_set(v_reuseFailAlloc_4164_, 2, v_file_4149_);
lean_ctor_set(v_reuseFailAlloc_4164_, 3, v_mtime_4157_);
v___x_4162_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
lean_object* v___x_4163_; 
v___x_4163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4163_, 0, v___x_4162_);
lean_ctor_set(v___x_4163_, 1, v___y_4155_);
return v___x_4163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_restoreArtifact___boxed(lean_object* v_file_4226_, lean_object* v_art_4227_, lean_object* v_exe_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_){
_start:
{
uint8_t v_exe_boxed_4231_; lean_object* v_res_4232_; 
v_exe_boxed_4231_ = lean_unbox(v_exe_4228_);
v_res_4232_ = l_Lake_restoreArtifact(v_file_4226_, v_art_4227_, v_exe_boxed_4231_, v_a_4229_);
return v_res_4232_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(lean_object* v_val_4233_, lean_object* v_a_x3f_4234_, lean_object* v___y_4235_){
_start:
{
lean_object* v___x_4237_; lean_object* v_log_4238_; uint8_t v_action_4239_; uint8_t v_wantsRebuild_4240_; lean_object* v_trace_4241_; lean_object* v_buildTime_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4253_; 
v___x_4237_ = lean_io_mono_ms_now();
v_log_4238_ = lean_ctor_get(v___y_4235_, 0);
v_action_4239_ = lean_ctor_get_uint8(v___y_4235_, sizeof(void*)*3);
v_wantsRebuild_4240_ = lean_ctor_get_uint8(v___y_4235_, sizeof(void*)*3 + 1);
v_trace_4241_ = lean_ctor_get(v___y_4235_, 1);
v_buildTime_4242_ = lean_ctor_get(v___y_4235_, 2);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___y_4235_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4244_ = v___y_4235_;
v_isShared_4245_ = v_isSharedCheck_4253_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_buildTime_4242_);
lean_inc(v_trace_4241_);
lean_inc(v_log_4238_);
lean_dec(v___y_4235_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4253_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4250_; 
v___x_4246_ = lean_nat_sub(v___x_4237_, v_val_4233_);
lean_dec(v___x_4237_);
v___x_4247_ = lean_box(0);
v___x_4248_ = lean_nat_add(v_buildTime_4242_, v___x_4246_);
lean_dec(v___x_4246_);
lean_dec(v_buildTime_4242_);
if (v_isShared_4245_ == 0)
{
lean_ctor_set(v___x_4244_, 2, v___x_4248_);
v___x_4250_ = v___x_4244_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_log_4238_);
lean_ctor_set(v_reuseFailAlloc_4252_, 1, v_trace_4241_);
lean_ctor_set(v_reuseFailAlloc_4252_, 2, v___x_4248_);
lean_ctor_set_uint8(v_reuseFailAlloc_4252_, sizeof(void*)*3, v_action_4239_);
lean_ctor_set_uint8(v_reuseFailAlloc_4252_, sizeof(void*)*3 + 1, v_wantsRebuild_4240_);
v___x_4250_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
lean_object* v___x_4251_; 
v___x_4251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4247_);
lean_ctor_set(v___x_4251_, 1, v___x_4250_);
return v___x_4251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0___boxed(lean_object* v_val_4254_, lean_object* v_a_x3f_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_){
_start:
{
lean_object* v_res_4258_; 
v_res_4258_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v_val_4254_, v_a_x3f_4255_, v___y_4256_);
lean_dec(v_a_x3f_4255_);
lean_dec(v_val_4254_);
return v_res_4258_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(lean_object* v_file_4259_, lean_object* v_build_4260_, lean_object* v_traceFile_4261_, lean_object* v_ext_4262_, uint8_t v_text_4263_, lean_object* v_a_4264_, lean_object* v_depTrace_4265_, lean_object* v_traceFile_4266_, uint8_t v_action_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_){
_start:
{
lean_object* v_a_4275_; lean_object* v_a_4276_; lean_object* v_log_4279_; uint8_t v_action_4280_; uint8_t v_wantsRebuild_4281_; lean_object* v_trace_4282_; lean_object* v_buildTime_4283_; lean_object* v_toBuildConfig_4289_; lean_object* v_log_4290_; uint8_t v_action_4291_; uint8_t v_wantsRebuild_4292_; lean_object* v_trace_4293_; lean_object* v_buildTime_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4473_; 
v_toBuildConfig_4289_ = lean_ctor_get(v_a_4271_, 0);
v_log_4290_ = lean_ctor_get(v_a_4272_, 0);
v_action_4291_ = lean_ctor_get_uint8(v_a_4272_, sizeof(void*)*3);
v_wantsRebuild_4292_ = lean_ctor_get_uint8(v_a_4272_, sizeof(void*)*3 + 1);
v_trace_4293_ = lean_ctor_get(v_a_4272_, 1);
v_buildTime_4294_ = lean_ctor_get(v_a_4272_, 2);
v_isSharedCheck_4473_ = !lean_is_exclusive(v_a_4272_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4296_ = v_a_4272_;
v_isShared_4297_ = v_isSharedCheck_4473_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_buildTime_4294_);
lean_inc(v_trace_4293_);
lean_inc(v_log_4290_);
lean_dec(v_a_4272_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4473_;
goto v_resetjp_4295_;
}
v___jp_4274_:
{
lean_object* v___x_4277_; 
v___x_4277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4277_, 0, v_a_4275_);
lean_ctor_set(v___x_4277_, 1, v_a_4276_);
return v___x_4277_;
}
v___jp_4278_:
{
lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; 
v___x_4284_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_4285_ = lean_array_get_size(v_log_4279_);
v___x_4286_ = lean_array_push(v_log_4279_, v___x_4284_);
v___x_4287_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4287_, 0, v___x_4286_);
lean_ctor_set(v___x_4287_, 1, v_trace_4282_);
lean_ctor_set(v___x_4287_, 2, v_buildTime_4283_);
lean_ctor_set_uint8(v___x_4287_, sizeof(void*)*3, v_action_4280_);
lean_ctor_set_uint8(v___x_4287_, sizeof(void*)*3 + 1, v_wantsRebuild_4281_);
v___x_4288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4288_, 0, v___x_4285_);
lean_ctor_set(v___x_4288_, 1, v___x_4287_);
return v___x_4288_;
}
v_resetjp_4295_:
{
uint8_t v_noBuild_4298_; uint8_t v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v_noBuild_4298_ = lean_ctor_get_uint8(v_toBuildConfig_4289_, sizeof(void*)*2 + 2);
v___x_4299_ = l_Lake_JobAction_merge(v_action_4291_, v_action_4267_);
v___x_4300_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_4266_);
v___x_4301_ = l_System_FilePath_addExtension(v_traceFile_4266_, v___x_4300_);
if (v_noBuild_4298_ == 0)
{
lean_object* v___x_4302_; lean_object* v_a_4304_; lean_object* v_a_4305_; lean_object* v___x_4309_; 
v___x_4302_ = lean_io_mono_ms_now();
v___x_4309_ = l_Lake_removeFileIfExists(v_file_4259_);
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_object* v___x_4311_; 
lean_dec_ref(v___x_4309_);
lean_inc_ref(v_log_4290_);
if (v_isShared_4297_ == 0)
{
v___x_4311_ = v___x_4296_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_log_4290_);
lean_ctor_set(v_reuseFailAlloc_4448_, 1, v_trace_4293_);
lean_ctor_set(v_reuseFailAlloc_4448_, 2, v_buildTime_4294_);
lean_ctor_set_uint8(v_reuseFailAlloc_4448_, sizeof(void*)*3 + 1, v_wantsRebuild_4292_);
v___x_4311_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
lean_object* v___x_4312_; 
lean_ctor_set_uint8(v___x_4311_, sizeof(void*)*3, v___x_4299_);
lean_inc_ref(v_a_4271_);
v___x_4312_ = lean_apply_7(v_build_4260_, v_a_4264_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v___x_4311_, lean_box(0));
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_object* v_a_4313_; lean_object* v_log_4314_; uint8_t v_action_4315_; uint8_t v_wantsRebuild_4316_; lean_object* v_trace_4317_; lean_object* v_buildTime_4318_; lean_object* v___x_4319_; 
v_a_4313_ = lean_ctor_get(v___x_4312_, 1);
lean_inc(v_a_4313_);
lean_dec_ref(v___x_4312_);
v_log_4314_ = lean_ctor_get(v_a_4313_, 0);
v_action_4315_ = lean_ctor_get_uint8(v_a_4313_, sizeof(void*)*3);
v_wantsRebuild_4316_ = lean_ctor_get_uint8(v_a_4313_, sizeof(void*)*3 + 1);
v_trace_4317_ = lean_ctor_get(v_a_4313_, 1);
v_buildTime_4318_ = lean_ctor_get(v_a_4313_, 2);
lean_inc_ref(v_file_4259_);
v___x_4319_ = l_Lake_clearFileHash(v_file_4259_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v___x_4320_; 
lean_dec_ref(v___x_4319_);
v___x_4320_ = l_Lake_removeFileIfExists(v_traceFile_4261_);
if (lean_obj_tag(v___x_4320_) == 0)
{
lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4412_; 
v_isSharedCheck_4412_ = !lean_is_exclusive(v___x_4320_);
if (v_isSharedCheck_4412_ == 0)
{
lean_object* v_unused_4413_; 
v_unused_4413_ = lean_ctor_get(v___x_4320_, 0);
lean_dec(v_unused_4413_);
v___x_4322_ = v___x_4320_;
v_isShared_4323_ = v_isSharedCheck_4412_;
goto v_resetjp_4321_;
}
else
{
lean_dec(v___x_4320_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4412_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4324_; 
v___x_4324_ = l_Lake_computeArtifact___redArg(v_file_4259_, v_ext_4262_, v_text_4263_, v_a_4271_, v_a_4313_);
lean_dec_ref(v_a_4271_);
if (lean_obj_tag(v___x_4324_) == 0)
{
lean_object* v_a_4325_; lean_object* v_a_4326_; lean_object* v_descr_4327_; lean_object* v_log_4328_; uint8_t v_action_4329_; uint8_t v_wantsRebuild_4330_; lean_object* v_trace_4331_; lean_object* v_buildTime_4332_; uint64_t v_hash_4333_; lean_object* v_ext_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___y_4339_; lean_object* v___x_4402_; lean_object* v___x_4403_; uint8_t v___x_4404_; 
v_a_4325_ = lean_ctor_get(v___x_4324_, 1);
lean_inc(v_a_4325_);
v_a_4326_ = lean_ctor_get(v___x_4324_, 0);
lean_inc(v_a_4326_);
lean_dec_ref(v___x_4324_);
v_descr_4327_ = lean_ctor_get(v_a_4326_, 0);
v_log_4328_ = lean_ctor_get(v_a_4325_, 0);
v_action_4329_ = lean_ctor_get_uint8(v_a_4325_, sizeof(void*)*3);
v_wantsRebuild_4330_ = lean_ctor_get_uint8(v_a_4325_, sizeof(void*)*3 + 1);
v_trace_4331_ = lean_ctor_get(v_a_4325_, 1);
v_buildTime_4332_ = lean_ctor_get(v_a_4325_, 2);
v_hash_4333_ = lean_ctor_get_uint64(v_descr_4327_, sizeof(void*)*1);
v_ext_4334_ = lean_ctor_get(v_descr_4327_, 0);
v___x_4335_ = lean_array_get_size(v_log_4290_);
lean_dec_ref(v_log_4290_);
v___x_4336_ = lean_array_get_size(v_log_4328_);
v___x_4337_ = l_Array_extract___redArg(v_log_4328_, v___x_4335_, v___x_4336_);
v___x_4402_ = lean_string_utf8_byte_size(v_ext_4334_);
v___x_4403_ = lean_unsigned_to_nat(0u);
v___x_4404_ = lean_nat_dec_eq(v___x_4402_, v___x_4403_);
if (v___x_4404_ == 0)
{
lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; 
v___x_4405_ = l_Lake_Hash_hex(v_hash_4333_);
v___x_4406_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_4407_ = lean_string_append(v___x_4405_, v___x_4406_);
v___x_4408_ = lean_string_append(v___x_4407_, v_ext_4334_);
v___y_4339_ = v___x_4408_;
goto v___jp_4338_;
}
else
{
lean_object* v___x_4409_; 
v___x_4409_ = l_Lake_Hash_hex(v_hash_4333_);
v___y_4339_ = v___x_4409_;
goto v___jp_4338_;
}
v___jp_4338_:
{
lean_object* v___x_4341_; 
if (v_isShared_4323_ == 0)
{
lean_ctor_set_tag(v___x_4322_, 3);
lean_ctor_set(v___x_4322_, 0, v___y_4339_);
v___x_4341_ = v___x_4322_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v___y_4339_);
v___x_4341_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4342_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_4265_, v___x_4341_, v___x_4337_);
v___x_4343_ = l_Lake_BuildMetadata_writeFile(v_traceFile_4266_, v___x_4342_);
if (lean_obj_tag(v___x_4343_) == 0)
{
lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4384_; 
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4343_);
if (v_isSharedCheck_4384_ == 0)
{
lean_object* v_unused_4385_; 
v_unused_4385_ = lean_ctor_get(v___x_4343_, 0);
lean_dec(v_unused_4385_);
v___x_4345_ = v___x_4343_;
v_isShared_4346_ = v_isSharedCheck_4384_;
goto v_resetjp_4344_;
}
else
{
lean_dec(v___x_4343_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4384_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___x_4347_; 
v___x_4347_ = l_Lake_removeFileIfExists(v___x_4301_);
lean_dec_ref(v___x_4301_);
if (lean_obj_tag(v___x_4347_) == 0)
{
lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4367_; 
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4347_);
if (v_isSharedCheck_4367_ == 0)
{
lean_object* v_unused_4368_; 
v_unused_4368_ = lean_ctor_get(v___x_4347_, 0);
lean_dec(v_unused_4368_);
v___x_4349_ = v___x_4347_;
v_isShared_4350_ = v_isSharedCheck_4367_;
goto v_resetjp_4348_;
}
else
{
lean_dec(v___x_4347_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4367_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4352_; 
lean_inc(v_a_4326_);
if (v_isShared_4350_ == 0)
{
lean_ctor_set(v___x_4349_, 0, v_a_4326_);
v___x_4352_ = v___x_4349_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4326_);
v___x_4352_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
lean_object* v___x_4354_; 
if (v_isShared_4346_ == 0)
{
lean_ctor_set_tag(v___x_4345_, 1);
lean_ctor_set(v___x_4345_, 0, v___x_4352_);
v___x_4354_ = v___x_4345_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v___x_4352_);
v___x_4354_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
lean_object* v___x_4355_; lean_object* v_a_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4363_; 
v___x_4355_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v___x_4302_, v___x_4354_, v_a_4325_);
lean_dec_ref(v___x_4354_);
lean_dec(v___x_4302_);
v_a_4356_ = lean_ctor_get(v___x_4355_, 1);
v_isSharedCheck_4363_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4363_ == 0)
{
lean_object* v_unused_4364_; 
v_unused_4364_ = lean_ctor_get(v___x_4355_, 0);
lean_dec(v_unused_4364_);
v___x_4358_ = v___x_4355_;
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_a_4356_);
lean_dec(v___x_4355_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v___x_4361_; 
if (v_isShared_4359_ == 0)
{
lean_ctor_set(v___x_4358_, 0, v_a_4326_);
v___x_4361_ = v___x_4358_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_a_4326_);
lean_ctor_set(v_reuseFailAlloc_4362_, 1, v_a_4356_);
v___x_4361_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
return v___x_4361_;
}
}
}
}
}
}
else
{
lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4380_; 
lean_inc(v_buildTime_4332_);
lean_inc_ref(v_trace_4331_);
lean_inc_ref(v_log_4328_);
lean_del_object(v___x_4345_);
lean_dec(v_a_4326_);
v_isSharedCheck_4380_ = !lean_is_exclusive(v_a_4325_);
if (v_isSharedCheck_4380_ == 0)
{
lean_object* v_unused_4381_; lean_object* v_unused_4382_; lean_object* v_unused_4383_; 
v_unused_4381_ = lean_ctor_get(v_a_4325_, 2);
lean_dec(v_unused_4381_);
v_unused_4382_ = lean_ctor_get(v_a_4325_, 1);
lean_dec(v_unused_4382_);
v_unused_4383_ = lean_ctor_get(v_a_4325_, 0);
lean_dec(v_unused_4383_);
v___x_4370_ = v_a_4325_;
v_isShared_4371_ = v_isSharedCheck_4380_;
goto v_resetjp_4369_;
}
else
{
lean_dec(v_a_4325_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4380_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v_a_4372_; lean_object* v___x_4373_; uint8_t v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4378_; 
v_a_4372_ = lean_ctor_get(v___x_4347_, 0);
lean_inc(v_a_4372_);
lean_dec_ref(v___x_4347_);
v___x_4373_ = lean_io_error_to_string(v_a_4372_);
v___x_4374_ = 3;
v___x_4375_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4375_, 0, v___x_4373_);
lean_ctor_set_uint8(v___x_4375_, sizeof(void*)*1, v___x_4374_);
v___x_4376_ = lean_array_push(v_log_4328_, v___x_4375_);
if (v_isShared_4371_ == 0)
{
lean_ctor_set(v___x_4370_, 0, v___x_4376_);
v___x_4378_ = v___x_4370_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v___x_4376_);
lean_ctor_set(v_reuseFailAlloc_4379_, 1, v_trace_4331_);
lean_ctor_set(v_reuseFailAlloc_4379_, 2, v_buildTime_4332_);
lean_ctor_set_uint8(v_reuseFailAlloc_4379_, sizeof(void*)*3, v_action_4329_);
lean_ctor_set_uint8(v_reuseFailAlloc_4379_, sizeof(void*)*3 + 1, v_wantsRebuild_4330_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
v_a_4304_ = v___x_4336_;
v_a_4305_ = v___x_4378_;
goto v___jp_4303_;
}
}
}
}
}
else
{
lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4397_; 
lean_inc(v_buildTime_4332_);
lean_inc_ref(v_trace_4331_);
lean_inc_ref(v_log_4328_);
lean_dec(v_a_4326_);
lean_dec_ref(v___x_4301_);
v_isSharedCheck_4397_ = !lean_is_exclusive(v_a_4325_);
if (v_isSharedCheck_4397_ == 0)
{
lean_object* v_unused_4398_; lean_object* v_unused_4399_; lean_object* v_unused_4400_; 
v_unused_4398_ = lean_ctor_get(v_a_4325_, 2);
lean_dec(v_unused_4398_);
v_unused_4399_ = lean_ctor_get(v_a_4325_, 1);
lean_dec(v_unused_4399_);
v_unused_4400_ = lean_ctor_get(v_a_4325_, 0);
lean_dec(v_unused_4400_);
v___x_4387_ = v_a_4325_;
v_isShared_4388_ = v_isSharedCheck_4397_;
goto v_resetjp_4386_;
}
else
{
lean_dec(v_a_4325_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4397_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
lean_object* v_a_4389_; lean_object* v___x_4390_; uint8_t v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4395_; 
v_a_4389_ = lean_ctor_get(v___x_4343_, 0);
lean_inc(v_a_4389_);
lean_dec_ref(v___x_4343_);
v___x_4390_ = lean_io_error_to_string(v_a_4389_);
v___x_4391_ = 3;
v___x_4392_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4392_, 0, v___x_4390_);
lean_ctor_set_uint8(v___x_4392_, sizeof(void*)*1, v___x_4391_);
v___x_4393_ = lean_array_push(v_log_4328_, v___x_4392_);
if (v_isShared_4388_ == 0)
{
lean_ctor_set(v___x_4387_, 0, v___x_4393_);
v___x_4395_ = v___x_4387_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4393_);
lean_ctor_set(v_reuseFailAlloc_4396_, 1, v_trace_4331_);
lean_ctor_set(v_reuseFailAlloc_4396_, 2, v_buildTime_4332_);
lean_ctor_set_uint8(v_reuseFailAlloc_4396_, sizeof(void*)*3, v_action_4329_);
lean_ctor_set_uint8(v_reuseFailAlloc_4396_, sizeof(void*)*3 + 1, v_wantsRebuild_4330_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
v_a_4304_ = v___x_4336_;
v_a_4305_ = v___x_4395_;
goto v___jp_4303_;
}
}
}
}
}
}
else
{
lean_object* v_a_4410_; lean_object* v_a_4411_; 
lean_del_object(v___x_4322_);
lean_dec_ref(v___x_4301_);
lean_dec_ref(v_log_4290_);
lean_dec_ref(v_traceFile_4266_);
v_a_4410_ = lean_ctor_get(v___x_4324_, 0);
lean_inc(v_a_4410_);
v_a_4411_ = lean_ctor_get(v___x_4324_, 1);
lean_inc(v_a_4411_);
lean_dec_ref(v___x_4324_);
v_a_4304_ = v_a_4410_;
v_a_4305_ = v_a_4411_;
goto v___jp_4303_;
}
}
}
else
{
lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4426_; 
lean_inc(v_buildTime_4318_);
lean_inc_ref(v_trace_4317_);
lean_inc_ref(v_log_4314_);
lean_dec_ref(v___x_4301_);
lean_dec_ref(v_log_4290_);
lean_dec_ref(v_a_4271_);
lean_dec_ref(v_traceFile_4266_);
lean_dec_ref(v_ext_4262_);
lean_dec_ref(v_file_4259_);
v_isSharedCheck_4426_ = !lean_is_exclusive(v_a_4313_);
if (v_isSharedCheck_4426_ == 0)
{
lean_object* v_unused_4427_; lean_object* v_unused_4428_; lean_object* v_unused_4429_; 
v_unused_4427_ = lean_ctor_get(v_a_4313_, 2);
lean_dec(v_unused_4427_);
v_unused_4428_ = lean_ctor_get(v_a_4313_, 1);
lean_dec(v_unused_4428_);
v_unused_4429_ = lean_ctor_get(v_a_4313_, 0);
lean_dec(v_unused_4429_);
v___x_4415_ = v_a_4313_;
v_isShared_4416_ = v_isSharedCheck_4426_;
goto v_resetjp_4414_;
}
else
{
lean_dec(v_a_4313_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4426_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
lean_object* v_a_4417_; lean_object* v___x_4418_; uint8_t v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4424_; 
v_a_4417_ = lean_ctor_get(v___x_4320_, 0);
lean_inc(v_a_4417_);
lean_dec_ref(v___x_4320_);
v___x_4418_ = lean_io_error_to_string(v_a_4417_);
v___x_4419_ = 3;
v___x_4420_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4420_, 0, v___x_4418_);
lean_ctor_set_uint8(v___x_4420_, sizeof(void*)*1, v___x_4419_);
v___x_4421_ = lean_array_get_size(v_log_4314_);
v___x_4422_ = lean_array_push(v_log_4314_, v___x_4420_);
if (v_isShared_4416_ == 0)
{
lean_ctor_set(v___x_4415_, 0, v___x_4422_);
v___x_4424_ = v___x_4415_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4422_);
lean_ctor_set(v_reuseFailAlloc_4425_, 1, v_trace_4317_);
lean_ctor_set(v_reuseFailAlloc_4425_, 2, v_buildTime_4318_);
lean_ctor_set_uint8(v_reuseFailAlloc_4425_, sizeof(void*)*3, v_action_4315_);
lean_ctor_set_uint8(v_reuseFailAlloc_4425_, sizeof(void*)*3 + 1, v_wantsRebuild_4316_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
v_a_4304_ = v___x_4421_;
v_a_4305_ = v___x_4424_;
goto v___jp_4303_;
}
}
}
}
else
{
lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4442_; 
lean_inc(v_buildTime_4318_);
lean_inc_ref(v_trace_4317_);
lean_inc_ref(v_log_4314_);
lean_dec_ref(v___x_4301_);
lean_dec_ref(v_log_4290_);
lean_dec_ref(v_a_4271_);
lean_dec_ref(v_traceFile_4266_);
lean_dec_ref(v_ext_4262_);
lean_dec_ref(v_file_4259_);
v_isSharedCheck_4442_ = !lean_is_exclusive(v_a_4313_);
if (v_isSharedCheck_4442_ == 0)
{
lean_object* v_unused_4443_; lean_object* v_unused_4444_; lean_object* v_unused_4445_; 
v_unused_4443_ = lean_ctor_get(v_a_4313_, 2);
lean_dec(v_unused_4443_);
v_unused_4444_ = lean_ctor_get(v_a_4313_, 1);
lean_dec(v_unused_4444_);
v_unused_4445_ = lean_ctor_get(v_a_4313_, 0);
lean_dec(v_unused_4445_);
v___x_4431_ = v_a_4313_;
v_isShared_4432_ = v_isSharedCheck_4442_;
goto v_resetjp_4430_;
}
else
{
lean_dec(v_a_4313_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4442_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v_a_4433_; lean_object* v___x_4434_; uint8_t v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4440_; 
v_a_4433_ = lean_ctor_get(v___x_4319_, 0);
lean_inc(v_a_4433_);
lean_dec_ref(v___x_4319_);
v___x_4434_ = lean_io_error_to_string(v_a_4433_);
v___x_4435_ = 3;
v___x_4436_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4436_, 0, v___x_4434_);
lean_ctor_set_uint8(v___x_4436_, sizeof(void*)*1, v___x_4435_);
v___x_4437_ = lean_array_get_size(v_log_4314_);
v___x_4438_ = lean_array_push(v_log_4314_, v___x_4436_);
if (v_isShared_4432_ == 0)
{
lean_ctor_set(v___x_4431_, 0, v___x_4438_);
v___x_4440_ = v___x_4431_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v___x_4438_);
lean_ctor_set(v_reuseFailAlloc_4441_, 1, v_trace_4317_);
lean_ctor_set(v_reuseFailAlloc_4441_, 2, v_buildTime_4318_);
lean_ctor_set_uint8(v_reuseFailAlloc_4441_, sizeof(void*)*3, v_action_4315_);
lean_ctor_set_uint8(v_reuseFailAlloc_4441_, sizeof(void*)*3 + 1, v_wantsRebuild_4316_);
v___x_4440_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
v_a_4304_ = v___x_4437_;
v_a_4305_ = v___x_4440_;
goto v___jp_4303_;
}
}
}
}
else
{
lean_object* v_a_4446_; lean_object* v_a_4447_; 
lean_dec_ref(v___x_4301_);
lean_dec_ref(v_log_4290_);
lean_dec_ref(v_a_4271_);
lean_dec_ref(v_traceFile_4266_);
lean_dec_ref(v_ext_4262_);
lean_dec_ref(v_file_4259_);
v_a_4446_ = lean_ctor_get(v___x_4312_, 0);
lean_inc(v_a_4446_);
v_a_4447_ = lean_ctor_get(v___x_4312_, 1);
lean_inc(v_a_4447_);
lean_dec_ref(v___x_4312_);
v_a_4304_ = v_a_4446_;
v_a_4305_ = v_a_4447_;
goto v___jp_4303_;
}
}
}
else
{
lean_object* v_a_4449_; lean_object* v___x_4450_; uint8_t v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4456_; 
lean_dec_ref(v___x_4301_);
lean_dec_ref(v_a_4271_);
lean_dec(v_a_4270_);
lean_dec(v_a_4269_);
lean_dec(v_a_4268_);
lean_dec_ref(v_traceFile_4266_);
lean_dec_ref(v_a_4264_);
lean_dec_ref(v_ext_4262_);
lean_dec_ref(v_build_4260_);
lean_dec_ref(v_file_4259_);
v_a_4449_ = lean_ctor_get(v___x_4309_, 0);
lean_inc(v_a_4449_);
lean_dec_ref(v___x_4309_);
v___x_4450_ = lean_io_error_to_string(v_a_4449_);
v___x_4451_ = 3;
v___x_4452_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4452_, 0, v___x_4450_);
lean_ctor_set_uint8(v___x_4452_, sizeof(void*)*1, v___x_4451_);
v___x_4453_ = lean_array_get_size(v_log_4290_);
v___x_4454_ = lean_array_push(v_log_4290_, v___x_4452_);
if (v_isShared_4297_ == 0)
{
lean_ctor_set(v___x_4296_, 0, v___x_4454_);
v___x_4456_ = v___x_4296_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v___x_4454_);
lean_ctor_set(v_reuseFailAlloc_4457_, 1, v_trace_4293_);
lean_ctor_set(v_reuseFailAlloc_4457_, 2, v_buildTime_4294_);
lean_ctor_set_uint8(v_reuseFailAlloc_4457_, sizeof(void*)*3 + 1, v_wantsRebuild_4292_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
lean_ctor_set_uint8(v___x_4456_, sizeof(void*)*3, v___x_4299_);
v_a_4304_ = v___x_4453_;
v_a_4305_ = v___x_4456_;
goto v___jp_4303_;
}
}
v___jp_4303_:
{
lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v_a_4308_; 
v___x_4306_ = lean_box(0);
v___x_4307_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v___x_4302_, v___x_4306_, v_a_4305_);
lean_dec(v___x_4302_);
v_a_4308_ = lean_ctor_get(v___x_4307_, 1);
lean_inc(v_a_4308_);
lean_dec_ref(v___x_4307_);
v_a_4275_ = v_a_4304_;
v_a_4276_ = v_a_4308_;
goto v___jp_4274_;
}
}
else
{
uint8_t v___x_4458_; 
lean_dec_ref(v_a_4271_);
lean_dec(v_a_4270_);
lean_dec(v_a_4269_);
lean_dec(v_a_4268_);
lean_dec_ref(v_a_4264_);
lean_dec_ref(v_ext_4262_);
lean_dec_ref(v_build_4260_);
lean_dec_ref(v_file_4259_);
v___x_4458_ = l_System_FilePath_pathExists(v_traceFile_4266_);
lean_dec_ref(v_traceFile_4266_);
if (v___x_4458_ == 0)
{
lean_dec_ref(v___x_4301_);
lean_del_object(v___x_4296_);
v_log_4279_ = v_log_4290_;
v_action_4280_ = v___x_4299_;
v_wantsRebuild_4281_ = v_noBuild_4298_;
v_trace_4282_ = v_trace_4293_;
v_buildTime_4283_ = v_buildTime_4294_;
goto v___jp_4278_;
}
else
{
lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; 
v___x_4459_ = lean_box(0);
v___x_4460_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_4461_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_4265_, v___x_4459_, v___x_4460_);
v___x_4462_ = l_Lake_BuildMetadata_writeFile(v___x_4301_, v___x_4461_);
if (lean_obj_tag(v___x_4462_) == 0)
{
lean_dec_ref(v___x_4462_);
lean_del_object(v___x_4296_);
v_log_4279_ = v_log_4290_;
v_action_4280_ = v___x_4299_;
v_wantsRebuild_4281_ = v_noBuild_4298_;
v_trace_4282_ = v_trace_4293_;
v_buildTime_4283_ = v_buildTime_4294_;
goto v___jp_4278_;
}
else
{
lean_object* v_a_4463_; lean_object* v___x_4464_; uint8_t v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4470_; 
v_a_4463_ = lean_ctor_get(v___x_4462_, 0);
lean_inc(v_a_4463_);
lean_dec_ref(v___x_4462_);
v___x_4464_ = lean_io_error_to_string(v_a_4463_);
v___x_4465_ = 3;
v___x_4466_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4466_, 0, v___x_4464_);
lean_ctor_set_uint8(v___x_4466_, sizeof(void*)*1, v___x_4465_);
v___x_4467_ = lean_array_get_size(v_log_4290_);
v___x_4468_ = lean_array_push(v_log_4290_, v___x_4466_);
if (v_isShared_4297_ == 0)
{
lean_ctor_set(v___x_4296_, 0, v___x_4468_);
v___x_4470_ = v___x_4296_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v___x_4468_);
lean_ctor_set(v_reuseFailAlloc_4472_, 1, v_trace_4293_);
lean_ctor_set(v_reuseFailAlloc_4472_, 2, v_buildTime_4294_);
v___x_4470_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
lean_object* v___x_4471_; 
lean_ctor_set_uint8(v___x_4470_, sizeof(void*)*3, v___x_4299_);
lean_ctor_set_uint8(v___x_4470_, sizeof(void*)*3 + 1, v_noBuild_4298_);
v___x_4471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4467_);
lean_ctor_set(v___x_4471_, 1, v___x_4470_);
return v___x_4471_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___boxed(lean_object* v_file_4474_, lean_object* v_build_4475_, lean_object* v_traceFile_4476_, lean_object* v_ext_4477_, lean_object* v_text_4478_, lean_object* v_a_4479_, lean_object* v_depTrace_4480_, lean_object* v_traceFile_4481_, lean_object* v_action_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_){
_start:
{
uint8_t v_text_boxed_4489_; uint8_t v_action_boxed_4490_; lean_object* v_res_4491_; 
v_text_boxed_4489_ = lean_unbox(v_text_4478_);
v_action_boxed_4490_ = lean_unbox(v_action_4482_);
v_res_4491_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(v_file_4474_, v_build_4475_, v_traceFile_4476_, v_ext_4477_, v_text_boxed_4489_, v_a_4479_, v_depTrace_4480_, v_traceFile_4481_, v_action_boxed_4490_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_);
lean_dec_ref(v_depTrace_4480_);
lean_dec_ref(v_traceFile_4476_);
return v_res_4491_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(lean_object* v_file_4492_, lean_object* v_build_4493_, uint8_t v_text_4494_, lean_object* v_ext_4495_, lean_object* v_depTrace_4496_, lean_object* v_traceFile_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_){
_start:
{
uint8_t v___x_4505_; lean_object* v___x_4506_; 
v___x_4505_ = 3;
lean_inc_ref(v_traceFile_4497_);
v___x_4506_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(v_file_4492_, v_build_4493_, v_traceFile_4497_, v_ext_4495_, v_text_4494_, v_a_4498_, v_depTrace_4496_, v_traceFile_4497_, v___x_4505_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_);
lean_dec_ref(v_traceFile_4497_);
return v___x_4506_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild___boxed(lean_object* v_file_4507_, lean_object* v_build_4508_, lean_object* v_text_4509_, lean_object* v_ext_4510_, lean_object* v_depTrace_4511_, lean_object* v_traceFile_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_){
_start:
{
uint8_t v_text_boxed_4520_; lean_object* v_res_4521_; 
v_text_boxed_4520_ = lean_unbox(v_text_4509_);
v_res_4521_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_4507_, v_build_4508_, v_text_boxed_4520_, v_ext_4510_, v_depTrace_4511_, v_traceFile_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_);
lean_dec_ref(v_depTrace_4511_);
return v_res_4521_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(lean_object* v_art_4523_, lean_object* v_traceFile_4524_, lean_object* v_a_4525_){
_start:
{
lean_object* v_log_4527_; uint8_t v_action_4528_; uint8_t v_wantsRebuild_4529_; lean_object* v_trace_4530_; lean_object* v_buildTime_4531_; lean_object* v___x_4532_; 
v_log_4527_ = lean_ctor_get(v_a_4525_, 0);
v_action_4528_ = lean_ctor_get_uint8(v_a_4525_, sizeof(void*)*3);
v_wantsRebuild_4529_ = lean_ctor_get_uint8(v_a_4525_, sizeof(void*)*3 + 1);
v_trace_4530_ = lean_ctor_get(v_a_4525_, 1);
v_buildTime_4531_ = lean_ctor_get(v_a_4525_, 2);
v___x_4532_ = lean_io_metadata(v_traceFile_4524_);
if (lean_obj_tag(v___x_4532_) == 0)
{
lean_object* v_a_4533_; lean_object* v_modified_4534_; lean_object* v_descr_4535_; lean_object* v_path_4536_; lean_object* v_name_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4545_; 
v_a_4533_ = lean_ctor_get(v___x_4532_, 0);
lean_inc(v_a_4533_);
lean_dec_ref(v___x_4532_);
v_modified_4534_ = lean_ctor_get(v_a_4533_, 1);
lean_inc_ref(v_modified_4534_);
lean_dec(v_a_4533_);
v_descr_4535_ = lean_ctor_get(v_art_4523_, 0);
v_path_4536_ = lean_ctor_get(v_art_4523_, 1);
v_name_4537_ = lean_ctor_get(v_art_4523_, 2);
v_isSharedCheck_4545_ = !lean_is_exclusive(v_art_4523_);
if (v_isSharedCheck_4545_ == 0)
{
lean_object* v_unused_4546_; 
v_unused_4546_ = lean_ctor_get(v_art_4523_, 3);
lean_dec(v_unused_4546_);
v___x_4539_ = v_art_4523_;
v_isShared_4540_ = v_isSharedCheck_4545_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_name_4537_);
lean_inc(v_path_4536_);
lean_inc(v_descr_4535_);
lean_dec(v_art_4523_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4545_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v___x_4542_; 
if (v_isShared_4540_ == 0)
{
lean_ctor_set(v___x_4539_, 3, v_modified_4534_);
v___x_4542_ = v___x_4539_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_descr_4535_);
lean_ctor_set(v_reuseFailAlloc_4544_, 1, v_path_4536_);
lean_ctor_set(v_reuseFailAlloc_4544_, 2, v_name_4537_);
lean_ctor_set(v_reuseFailAlloc_4544_, 3, v_modified_4534_);
v___x_4542_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
lean_object* v___x_4543_; 
v___x_4543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4542_);
lean_ctor_set(v___x_4543_, 1, v_a_4525_);
return v___x_4543_;
}
}
}
else
{
lean_object* v_a_4547_; 
v_a_4547_ = lean_ctor_get(v___x_4532_, 0);
lean_inc(v_a_4547_);
lean_dec_ref(v___x_4532_);
if (lean_obj_tag(v_a_4547_) == 11)
{
lean_object* v___x_4548_; 
lean_dec_ref(v_a_4547_);
v___x_4548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4548_, 0, v_art_4523_);
lean_ctor_set(v___x_4548_, 1, v_a_4525_);
return v___x_4548_;
}
else
{
lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4563_; 
lean_inc(v_buildTime_4531_);
lean_inc_ref(v_trace_4530_);
lean_inc_ref(v_log_4527_);
lean_dec_ref(v_art_4523_);
v_isSharedCheck_4563_ = !lean_is_exclusive(v_a_4525_);
if (v_isSharedCheck_4563_ == 0)
{
lean_object* v_unused_4564_; lean_object* v_unused_4565_; lean_object* v_unused_4566_; 
v_unused_4564_ = lean_ctor_get(v_a_4525_, 2);
lean_dec(v_unused_4564_);
v_unused_4565_ = lean_ctor_get(v_a_4525_, 1);
lean_dec(v_unused_4565_);
v_unused_4566_ = lean_ctor_get(v_a_4525_, 0);
lean_dec(v_unused_4566_);
v___x_4550_ = v_a_4525_;
v_isShared_4551_ = v_isSharedCheck_4563_;
goto v_resetjp_4549_;
}
else
{
lean_dec(v_a_4525_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4563_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; uint8_t v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4560_; 
v___x_4552_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___closed__0));
v___x_4553_ = lean_io_error_to_string(v_a_4547_);
v___x_4554_ = lean_string_append(v___x_4552_, v___x_4553_);
lean_dec_ref(v___x_4553_);
v___x_4555_ = 3;
v___x_4556_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4556_, 0, v___x_4554_);
lean_ctor_set_uint8(v___x_4556_, sizeof(void*)*1, v___x_4555_);
v___x_4557_ = lean_array_get_size(v_log_4527_);
v___x_4558_ = lean_array_push(v_log_4527_, v___x_4556_);
if (v_isShared_4551_ == 0)
{
lean_ctor_set(v___x_4550_, 0, v___x_4558_);
v___x_4560_ = v___x_4550_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v___x_4558_);
lean_ctor_set(v_reuseFailAlloc_4562_, 1, v_trace_4530_);
lean_ctor_set(v_reuseFailAlloc_4562_, 2, v_buildTime_4531_);
lean_ctor_set_uint8(v_reuseFailAlloc_4562_, sizeof(void*)*3, v_action_4528_);
lean_ctor_set_uint8(v_reuseFailAlloc_4562_, sizeof(void*)*3 + 1, v_wantsRebuild_4529_);
v___x_4560_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
lean_object* v___x_4561_; 
v___x_4561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4557_);
lean_ctor_set(v___x_4561_, 1, v___x_4560_);
return v___x_4561_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___boxed(lean_object* v_art_4567_, lean_object* v_traceFile_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_){
_start:
{
lean_object* v_res_4571_; 
v_res_4571_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_4567_, v_traceFile_4568_, v_a_4569_);
lean_dec_ref(v_traceFile_4568_);
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(lean_object* v_art_4572_, lean_object* v_traceFile_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_){
_start:
{
lean_object* v___x_4581_; 
v___x_4581_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_4572_, v_traceFile_4573_, v_a_4579_);
return v___x_4581_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___boxed(lean_object* v_art_4582_, lean_object* v_traceFile_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_){
_start:
{
lean_object* v_res_4591_; 
v_res_4591_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(v_art_4582_, v_traceFile_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
lean_dec_ref(v_a_4588_);
lean_dec(v_a_4587_);
lean_dec(v_a_4586_);
lean_dec(v_a_4585_);
lean_dec_ref(v_a_4584_);
lean_dec_ref(v_traceFile_4583_);
return v_res_4591_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(lean_object* v_a_4592_, lean_object* v_____r_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_){
_start:
{
lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; 
v___x_4601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4601_, 0, v_a_4592_);
v___x_4602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4602_, 0, v___x_4601_);
v___x_4603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4603_, 0, v___x_4602_);
lean_ctor_set(v___x_4603_, 1, v___y_4599_);
return v___x_4603_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0___boxed(lean_object* v_a_4604_, lean_object* v_____r_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_){
_start:
{
lean_object* v_res_4613_; 
v_res_4613_ = l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4604_, v_____r_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_);
lean_dec_ref(v___y_4610_);
lean_dec(v___y_4609_);
lean_dec(v___y_4608_);
lean_dec(v___y_4607_);
lean_dec_ref(v___y_4606_);
return v_res_4613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(lean_object* v_as_4614_, size_t v_i_4615_, size_t v_stop_4616_, lean_object* v_b_4617_){
_start:
{
uint8_t v___x_4618_; 
v___x_4618_ = lean_usize_dec_eq(v_i_4615_, v_stop_4616_);
if (v___x_4618_ == 0)
{
lean_object* v___x_4619_; lean_object* v_message_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; size_t v___x_4624_; size_t v___x_4625_; 
v___x_4619_ = lean_array_uget_borrowed(v_as_4614_, v_i_4615_);
v_message_4620_ = lean_ctor_get(v___x_4619_, 0);
v___x_4621_ = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___lam__0___closed__0));
v___x_4622_ = lean_string_append(v_b_4617_, v___x_4621_);
v___x_4623_ = lean_string_append(v___x_4622_, v_message_4620_);
v___x_4624_ = ((size_t)1ULL);
v___x_4625_ = lean_usize_add(v_i_4615_, v___x_4624_);
v_i_4615_ = v___x_4625_;
v_b_4617_ = v___x_4623_;
goto _start;
}
else
{
return v_b_4617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0___boxed(lean_object* v_as_4627_, lean_object* v_i_4628_, lean_object* v_stop_4629_, lean_object* v_b_4630_){
_start:
{
size_t v_i_boxed_4631_; size_t v_stop_boxed_4632_; lean_object* v_res_4633_; 
v_i_boxed_4631_ = lean_unbox_usize(v_i_4628_);
lean_dec(v_i_4628_);
v_stop_boxed_4632_ = lean_unbox_usize(v_stop_4629_);
lean_dec(v_stop_4629_);
v_res_4633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(v_as_4627_, v_i_boxed_4631_, v_stop_boxed_4632_, v_b_4630_);
lean_dec_ref(v_as_4627_);
return v_res_4633_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(uint8_t v_exe_4634_, lean_object* v___y_4635_, uint64_t v_inputHash_4636_, lean_object* v_savedTrace_4637_, lean_object* v_pkg_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_){
_start:
{
lean_object* v___y_4646_; lean_object* v_a_4650_; lean_object* v_a_4651_; lean_object* v___y_4666_; lean_object* v_toContext_4681_; lean_object* v_root_4682_; lean_object* v_lakeEnv_4683_; lean_object* v_lakeCache_4684_; uint8_t v___y_4686_; lean_object* v___y_4687_; lean_object* v___y_4688_; lean_object* v___y_4689_; lean_object* v___y_4690_; lean_object* v___y_4691_; lean_object* v___y_4692_; lean_object* v___y_4693_; uint8_t v___y_4737_; lean_object* v___y_4738_; lean_object* v___y_4739_; lean_object* v___y_4740_; uint8_t v___y_4741_; lean_object* v___y_4742_; uint8_t v___y_4743_; lean_object* v___y_4744_; uint8_t v_a_4750_; lean_object* v_a_4751_; lean_object* v_config_4838_; lean_object* v_enableArtifactCache_x3f_4839_; 
v_toContext_4681_ = lean_ctor_get(v_a_4642_, 1);
v_root_4682_ = lean_ctor_get(v_toContext_4681_, 0);
v_lakeEnv_4683_ = lean_ctor_get(v_toContext_4681_, 1);
v_lakeCache_4684_ = lean_ctor_get(v_toContext_4681_, 3);
lean_inc_ref(v_lakeCache_4684_);
v_config_4838_ = lean_ctor_get(v_pkg_4638_, 6);
v_enableArtifactCache_x3f_4839_ = lean_ctor_get(v_config_4838_, 25);
if (lean_obj_tag(v_enableArtifactCache_x3f_4839_) == 0)
{
lean_object* v_enableArtifactCache_x3f_4840_; 
v_enableArtifactCache_x3f_4840_ = lean_ctor_get(v_lakeEnv_4683_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_4840_) == 0)
{
lean_object* v_config_4841_; lean_object* v_enableArtifactCache_x3f_4842_; 
v_config_4841_ = lean_ctor_get(v_root_4682_, 6);
v_enableArtifactCache_x3f_4842_ = lean_ctor_get(v_config_4841_, 25);
if (lean_obj_tag(v_enableArtifactCache_x3f_4842_) == 0)
{
uint8_t v___x_4843_; 
v___x_4843_ = 0;
v_a_4750_ = v___x_4843_;
v_a_4751_ = v_a_4643_;
goto v___jp_4749_;
}
else
{
lean_object* v_val_4844_; uint8_t v___x_4845_; 
v_val_4844_ = lean_ctor_get(v_enableArtifactCache_x3f_4842_, 0);
v___x_4845_ = lean_unbox(v_val_4844_);
v_a_4750_ = v___x_4845_;
v_a_4751_ = v_a_4643_;
goto v___jp_4749_;
}
}
else
{
lean_object* v_val_4846_; uint8_t v___x_4847_; 
v_val_4846_ = lean_ctor_get(v_enableArtifactCache_x3f_4840_, 0);
v___x_4847_ = lean_unbox(v_val_4846_);
v_a_4750_ = v___x_4847_;
v_a_4751_ = v_a_4643_;
goto v___jp_4749_;
}
}
else
{
lean_object* v_val_4848_; uint8_t v___x_4849_; 
v_val_4848_ = lean_ctor_get(v_enableArtifactCache_x3f_4839_, 0);
v___x_4849_ = lean_unbox(v_val_4848_);
v_a_4750_ = v___x_4849_;
v_a_4751_ = v_a_4643_;
goto v___jp_4749_;
}
v___jp_4645_:
{
lean_object* v___x_4647_; lean_object* v___x_4648_; 
v___x_4647_ = lean_box(0);
v___x_4648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4648_, 0, v___x_4647_);
lean_ctor_set(v___x_4648_, 1, v___y_4646_);
return v___x_4648_;
}
v___jp_4649_:
{
lean_object* v_log_4652_; uint8_t v_action_4653_; uint8_t v_wantsRebuild_4654_; lean_object* v_trace_4655_; lean_object* v_buildTime_4656_; lean_object* v___x_4658_; uint8_t v_isShared_4659_; uint8_t v_isSharedCheck_4664_; 
v_log_4652_ = lean_ctor_get(v_a_4651_, 0);
v_action_4653_ = lean_ctor_get_uint8(v_a_4651_, sizeof(void*)*3);
v_wantsRebuild_4654_ = lean_ctor_get_uint8(v_a_4651_, sizeof(void*)*3 + 1);
v_trace_4655_ = lean_ctor_get(v_a_4651_, 1);
v_buildTime_4656_ = lean_ctor_get(v_a_4651_, 2);
v_isSharedCheck_4664_ = !lean_is_exclusive(v_a_4651_);
if (v_isSharedCheck_4664_ == 0)
{
v___x_4658_ = v_a_4651_;
v_isShared_4659_ = v_isSharedCheck_4664_;
goto v_resetjp_4657_;
}
else
{
lean_inc(v_buildTime_4656_);
lean_inc(v_trace_4655_);
lean_inc(v_log_4652_);
lean_dec(v_a_4651_);
v___x_4658_ = lean_box(0);
v_isShared_4659_ = v_isSharedCheck_4664_;
goto v_resetjp_4657_;
}
v_resetjp_4657_:
{
lean_object* v___x_4660_; lean_object* v___x_4662_; 
v___x_4660_ = l_Array_shrink___redArg(v_log_4652_, v_a_4650_);
lean_dec(v_a_4650_);
if (v_isShared_4659_ == 0)
{
lean_ctor_set(v___x_4658_, 0, v___x_4660_);
v___x_4662_ = v___x_4658_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v___x_4660_);
lean_ctor_set(v_reuseFailAlloc_4663_, 1, v_trace_4655_);
lean_ctor_set(v_reuseFailAlloc_4663_, 2, v_buildTime_4656_);
lean_ctor_set_uint8(v_reuseFailAlloc_4663_, sizeof(void*)*3, v_action_4653_);
lean_ctor_set_uint8(v_reuseFailAlloc_4663_, sizeof(void*)*3 + 1, v_wantsRebuild_4654_);
v___x_4662_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
v___y_4646_ = v___x_4662_;
goto v___jp_4645_;
}
}
}
v___jp_4665_:
{
if (lean_obj_tag(v___y_4666_) == 0)
{
lean_object* v_a_4667_; 
v_a_4667_ = lean_ctor_get(v___y_4666_, 0);
if (lean_obj_tag(v_a_4667_) == 0)
{
lean_object* v_a_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4676_; 
lean_inc_ref(v_a_4667_);
v_a_4668_ = lean_ctor_get(v___y_4666_, 1);
v_isSharedCheck_4676_ = !lean_is_exclusive(v___y_4666_);
if (v_isSharedCheck_4676_ == 0)
{
lean_object* v_unused_4677_; 
v_unused_4677_ = lean_ctor_get(v___y_4666_, 0);
lean_dec(v_unused_4677_);
v___x_4670_ = v___y_4666_;
v_isShared_4671_ = v_isSharedCheck_4676_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_a_4668_);
lean_dec(v___y_4666_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4676_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v_a_4672_; lean_object* v___x_4674_; 
v_a_4672_ = lean_ctor_get(v_a_4667_, 0);
lean_inc(v_a_4672_);
lean_dec_ref(v_a_4667_);
if (v_isShared_4671_ == 0)
{
lean_ctor_set(v___x_4670_, 0, v_a_4672_);
v___x_4674_ = v___x_4670_;
goto v_reusejp_4673_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v_a_4672_);
lean_ctor_set(v_reuseFailAlloc_4675_, 1, v_a_4668_);
v___x_4674_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4673_;
}
v_reusejp_4673_:
{
return v___x_4674_;
}
}
}
else
{
lean_object* v_a_4678_; 
v_a_4678_ = lean_ctor_get(v___y_4666_, 1);
lean_inc(v_a_4678_);
lean_dec_ref(v___y_4666_);
v___y_4646_ = v_a_4678_;
goto v___jp_4645_;
}
}
else
{
lean_object* v_a_4679_; lean_object* v_a_4680_; 
v_a_4679_ = lean_ctor_get(v___y_4666_, 0);
lean_inc(v_a_4679_);
v_a_4680_ = lean_ctor_get(v___y_4666_, 1);
lean_inc(v_a_4680_);
lean_dec_ref(v___y_4666_);
v_a_4650_ = v_a_4679_;
v_a_4651_ = v_a_4680_;
goto v___jp_4649_;
}
}
v___jp_4685_:
{
if (lean_obj_tag(v_savedTrace_4637_) == 2)
{
lean_object* v_data_4694_; uint64_t v_depHash_4695_; lean_object* v_outputs_x3f_4696_; uint8_t v___x_4697_; 
v_data_4694_ = lean_ctor_get(v_savedTrace_4637_, 0);
lean_inc_ref(v_data_4694_);
lean_dec_ref(v_savedTrace_4637_);
v_depHash_4695_ = lean_ctor_get_uint64(v_data_4694_, sizeof(void*)*3);
v_outputs_x3f_4696_ = lean_ctor_get(v_data_4694_, 1);
lean_inc(v_outputs_x3f_4696_);
lean_dec_ref(v_data_4694_);
v___x_4697_ = lean_uint64_dec_eq(v_depHash_4695_, v_inputHash_4636_);
if (v___x_4697_ == 0)
{
lean_dec(v_outputs_x3f_4696_);
lean_dec_ref(v___y_4692_);
lean_dec_ref(v___y_4687_);
lean_dec_ref(v_lakeCache_4684_);
v___y_4646_ = v___y_4693_;
goto v___jp_4645_;
}
else
{
if (lean_obj_tag(v_outputs_x3f_4696_) == 1)
{
lean_object* v_val_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; 
v_val_4698_ = lean_ctor_get(v_outputs_x3f_4696_, 0);
lean_inc(v_val_4698_);
lean_dec_ref(v_outputs_x3f_4696_);
v___x_4699_ = lean_box(0);
lean_inc_ref(v___y_4692_);
lean_inc(v_val_4698_);
v___x_4700_ = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg(v_val_4698_, v___x_4699_, v___x_4699_, v_exe_4634_, v___y_4692_, v___y_4693_);
if (lean_obj_tag(v___x_4700_) == 0)
{
if (v___y_4686_ == 0)
{
lean_object* v_a_4701_; lean_object* v_a_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; 
lean_dec(v_val_4698_);
lean_dec_ref(v___y_4687_);
lean_dec_ref(v_lakeCache_4684_);
v_a_4701_ = lean_ctor_get(v___x_4700_, 0);
lean_inc(v_a_4701_);
v_a_4702_ = lean_ctor_get(v___x_4700_, 1);
lean_inc(v_a_4702_);
lean_dec_ref(v___x_4700_);
v___x_4703_ = lean_box(0);
v___x_4704_ = l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4701_, v___x_4703_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v_a_4702_);
lean_dec_ref(v___y_4692_);
v___y_4666_ = v___x_4704_;
goto v___jp_4665_;
}
else
{
lean_object* v_a_4705_; lean_object* v_a_4706_; lean_object* v_log_4707_; uint8_t v_action_4708_; uint8_t v_wantsRebuild_4709_; lean_object* v_trace_4710_; lean_object* v_buildTime_4711_; lean_object* v___x_4712_; 
v_a_4705_ = lean_ctor_get(v___x_4700_, 1);
lean_inc(v_a_4705_);
v_a_4706_ = lean_ctor_get(v___x_4700_, 0);
lean_inc(v_a_4706_);
lean_dec_ref(v___x_4700_);
v_log_4707_ = lean_ctor_get(v_a_4705_, 0);
v_action_4708_ = lean_ctor_get_uint8(v_a_4705_, sizeof(void*)*3);
v_wantsRebuild_4709_ = lean_ctor_get_uint8(v_a_4705_, sizeof(void*)*3 + 1);
v_trace_4710_ = lean_ctor_get(v_a_4705_, 1);
v_buildTime_4711_ = lean_ctor_get(v_a_4705_, 2);
v___x_4712_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_4684_, v___y_4687_, v_inputHash_4636_, v_val_4698_, v___x_4699_, v___x_4699_);
if (lean_obj_tag(v___x_4712_) == 0)
{
lean_object* v___x_4713_; lean_object* v___x_4714_; 
lean_dec_ref(v___x_4712_);
v___x_4713_ = lean_box(0);
v___x_4714_ = l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4706_, v___x_4713_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v_a_4705_);
lean_dec_ref(v___y_4692_);
v___y_4666_ = v___x_4714_;
goto v___jp_4665_;
}
else
{
lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4730_; 
lean_inc(v_buildTime_4711_);
lean_inc_ref(v_trace_4710_);
lean_inc_ref(v_log_4707_);
v_isSharedCheck_4730_ = !lean_is_exclusive(v_a_4705_);
if (v_isSharedCheck_4730_ == 0)
{
lean_object* v_unused_4731_; lean_object* v_unused_4732_; lean_object* v_unused_4733_; 
v_unused_4731_ = lean_ctor_get(v_a_4705_, 2);
lean_dec(v_unused_4731_);
v_unused_4732_ = lean_ctor_get(v_a_4705_, 1);
lean_dec(v_unused_4732_);
v_unused_4733_ = lean_ctor_get(v_a_4705_, 0);
lean_dec(v_unused_4733_);
v___x_4716_ = v_a_4705_;
v_isShared_4717_ = v_isSharedCheck_4730_;
goto v_resetjp_4715_;
}
else
{
lean_dec(v_a_4705_);
v___x_4716_ = lean_box(0);
v_isShared_4717_ = v_isSharedCheck_4730_;
goto v_resetjp_4715_;
}
v_resetjp_4715_:
{
lean_object* v_a_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; uint8_t v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4727_; 
v_a_4718_ = lean_ctor_get(v___x_4712_, 0);
lean_inc(v_a_4718_);
lean_dec_ref(v___x_4712_);
v___x_4719_ = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___closed__0));
v___x_4720_ = lean_io_error_to_string(v_a_4718_);
v___x_4721_ = lean_string_append(v___x_4719_, v___x_4720_);
lean_dec_ref(v___x_4720_);
v___x_4722_ = 2;
v___x_4723_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4723_, 0, v___x_4721_);
lean_ctor_set_uint8(v___x_4723_, sizeof(void*)*1, v___x_4722_);
v___x_4724_ = lean_box(0);
v___x_4725_ = lean_array_push(v_log_4707_, v___x_4723_);
if (v_isShared_4717_ == 0)
{
lean_ctor_set(v___x_4716_, 0, v___x_4725_);
v___x_4727_ = v___x_4716_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4729_; 
v_reuseFailAlloc_4729_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4729_, 0, v___x_4725_);
lean_ctor_set(v_reuseFailAlloc_4729_, 1, v_trace_4710_);
lean_ctor_set(v_reuseFailAlloc_4729_, 2, v_buildTime_4711_);
lean_ctor_set_uint8(v_reuseFailAlloc_4729_, sizeof(void*)*3, v_action_4708_);
lean_ctor_set_uint8(v_reuseFailAlloc_4729_, sizeof(void*)*3 + 1, v_wantsRebuild_4709_);
v___x_4727_ = v_reuseFailAlloc_4729_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
lean_object* v___x_4728_; 
v___x_4728_ = l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4706_, v___x_4724_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___x_4727_);
lean_dec_ref(v___y_4692_);
v___y_4666_ = v___x_4728_;
goto v___jp_4665_;
}
}
}
}
}
else
{
lean_object* v_a_4734_; lean_object* v_a_4735_; 
lean_dec(v_val_4698_);
lean_dec_ref(v___y_4692_);
lean_dec_ref(v___y_4687_);
lean_dec_ref(v_lakeCache_4684_);
v_a_4734_ = lean_ctor_get(v___x_4700_, 0);
lean_inc(v_a_4734_);
v_a_4735_ = lean_ctor_get(v___x_4700_, 1);
lean_inc(v_a_4735_);
lean_dec_ref(v___x_4700_);
v_a_4650_ = v_a_4734_;
v_a_4651_ = v_a_4735_;
goto v___jp_4649_;
}
}
else
{
lean_dec(v_outputs_x3f_4696_);
lean_dec_ref(v___y_4692_);
lean_dec_ref(v___y_4687_);
lean_dec_ref(v_lakeCache_4684_);
v___y_4646_ = v___y_4693_;
goto v___jp_4645_;
}
}
}
else
{
lean_dec_ref(v___y_4692_);
lean_dec_ref(v___y_4687_);
lean_dec_ref(v_lakeCache_4684_);
lean_dec(v_savedTrace_4637_);
v___y_4646_ = v___y_4693_;
goto v___jp_4645_;
}
}
v___jp_4736_:
{
uint8_t v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; 
v___x_4745_ = 2;
v___x_4746_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4746_, 0, v___y_4744_);
lean_ctor_set_uint8(v___x_4746_, sizeof(void*)*1, v___x_4745_);
v___x_4747_ = lean_array_push(v___y_4739_, v___x_4746_);
v___x_4748_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4748_, 0, v___x_4747_);
lean_ctor_set(v___x_4748_, 1, v___y_4740_);
lean_ctor_set(v___x_4748_, 2, v___y_4742_);
lean_ctor_set_uint8(v___x_4748_, sizeof(void*)*3, v___y_4741_);
lean_ctor_set_uint8(v___x_4748_, sizeof(void*)*3 + 1, v___y_4743_);
v___y_4686_ = v___y_4737_;
v___y_4687_ = v___y_4738_;
v___y_4688_ = v___y_4635_;
v___y_4689_ = v_a_4639_;
v___y_4690_ = v_a_4640_;
v___y_4691_ = v_a_4641_;
v___y_4692_ = v_a_4642_;
v___y_4693_ = v___x_4748_;
goto v___jp_4685_;
}
v___jp_4749_:
{
lean_object* v_log_4752_; uint8_t v_action_4753_; uint8_t v_wantsRebuild_4754_; lean_object* v_trace_4755_; lean_object* v_buildTime_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4837_; 
v_log_4752_ = lean_ctor_get(v_a_4751_, 0);
v_action_4753_ = lean_ctor_get_uint8(v_a_4751_, sizeof(void*)*3);
v_wantsRebuild_4754_ = lean_ctor_get_uint8(v_a_4751_, sizeof(void*)*3 + 1);
v_trace_4755_ = lean_ctor_get(v_a_4751_, 1);
v_buildTime_4756_ = lean_ctor_get(v_a_4751_, 2);
v_isSharedCheck_4837_ = !lean_is_exclusive(v_a_4751_);
if (v_isSharedCheck_4837_ == 0)
{
v___x_4758_ = v_a_4751_;
v_isShared_4759_ = v_isSharedCheck_4837_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_buildTime_4756_);
lean_inc(v_trace_4755_);
lean_inc(v_log_4752_);
lean_dec(v_a_4751_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4837_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
lean_object* v___x_4760_; lean_object* v___x_4761_; 
v___x_4760_ = l_Lake_Package_cacheScope(v_pkg_4638_);
lean_inc_ref(v___x_4760_);
lean_inc_ref(v_lakeCache_4684_);
v___x_4761_ = l_Lake_Cache_readOutputs_x3f(v_lakeCache_4684_, v___x_4760_, v_inputHash_4636_, v_log_4752_);
if (lean_obj_tag(v___x_4761_) == 0)
{
lean_object* v_a_4762_; lean_object* v_a_4763_; lean_object* v___x_4765_; 
v_a_4762_ = lean_ctor_get(v___x_4761_, 0);
lean_inc(v_a_4762_);
v_a_4763_ = lean_ctor_get(v___x_4761_, 1);
lean_inc(v_a_4763_);
lean_dec_ref(v___x_4761_);
if (v_isShared_4759_ == 0)
{
lean_ctor_set(v___x_4758_, 0, v_a_4763_);
v___x_4765_ = v___x_4758_;
goto v_reusejp_4764_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v_a_4763_);
lean_ctor_set(v_reuseFailAlloc_4824_, 1, v_trace_4755_);
lean_ctor_set(v_reuseFailAlloc_4824_, 2, v_buildTime_4756_);
lean_ctor_set_uint8(v_reuseFailAlloc_4824_, sizeof(void*)*3, v_action_4753_);
lean_ctor_set_uint8(v_reuseFailAlloc_4824_, sizeof(void*)*3 + 1, v_wantsRebuild_4754_);
v___x_4765_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4764_;
}
v_reusejp_4764_:
{
if (lean_obj_tag(v_a_4762_) == 1)
{
lean_object* v_val_4766_; lean_object* v___x_4768_; uint8_t v_isShared_4769_; uint8_t v_isSharedCheck_4823_; 
v_val_4766_ = lean_ctor_get(v_a_4762_, 0);
v_isSharedCheck_4823_ = !lean_is_exclusive(v_a_4762_);
if (v_isSharedCheck_4823_ == 0)
{
v___x_4768_ = v_a_4762_;
v_isShared_4769_ = v_isSharedCheck_4823_;
goto v_resetjp_4767_;
}
else
{
lean_inc(v_val_4766_);
lean_dec(v_a_4762_);
v___x_4768_ = lean_box(0);
v_isShared_4769_ = v_isSharedCheck_4823_;
goto v_resetjp_4767_;
}
v_resetjp_4767_:
{
lean_object* v_data_4770_; lean_object* v_service_x3f_4771_; lean_object* v_scope_x3f_4772_; lean_object* v___x_4774_; uint8_t v_isShared_4775_; uint8_t v_isSharedCheck_4822_; 
v_data_4770_ = lean_ctor_get(v_val_4766_, 0);
v_service_x3f_4771_ = lean_ctor_get(v_val_4766_, 1);
v_scope_x3f_4772_ = lean_ctor_get(v_val_4766_, 2);
v_isSharedCheck_4822_ = !lean_is_exclusive(v_val_4766_);
if (v_isSharedCheck_4822_ == 0)
{
v___x_4774_ = v_val_4766_;
v_isShared_4775_ = v_isSharedCheck_4822_;
goto v_resetjp_4773_;
}
else
{
lean_inc(v_scope_x3f_4772_);
lean_inc(v_service_x3f_4771_);
lean_inc(v_data_4770_);
lean_dec(v_val_4766_);
v___x_4774_ = lean_box(0);
v_isShared_4775_ = v_isSharedCheck_4822_;
goto v_resetjp_4773_;
}
v_resetjp_4773_:
{
lean_object* v___x_4776_; 
lean_inc_ref(v_a_4642_);
v___x_4776_ = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg(v_data_4770_, v_service_x3f_4771_, v_scope_x3f_4772_, v_exe_4634_, v_a_4642_, v___x_4765_);
if (lean_obj_tag(v___x_4776_) == 0)
{
lean_object* v_a_4777_; lean_object* v_a_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4788_; 
lean_del_object(v___x_4774_);
lean_dec_ref(v___x_4760_);
lean_dec_ref(v_lakeCache_4684_);
lean_dec_ref(v_a_4642_);
lean_dec(v_savedTrace_4637_);
v_a_4777_ = lean_ctor_get(v___x_4776_, 0);
v_a_4778_ = lean_ctor_get(v___x_4776_, 1);
v_isSharedCheck_4788_ = !lean_is_exclusive(v___x_4776_);
if (v_isSharedCheck_4788_ == 0)
{
v___x_4780_ = v___x_4776_;
v_isShared_4781_ = v_isSharedCheck_4788_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_a_4778_);
lean_inc(v_a_4777_);
lean_dec(v___x_4776_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4788_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v___x_4783_; 
if (v_isShared_4769_ == 0)
{
lean_ctor_set(v___x_4768_, 0, v_a_4777_);
v___x_4783_ = v___x_4768_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v_a_4777_);
v___x_4783_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
lean_object* v___x_4785_; 
if (v_isShared_4781_ == 0)
{
lean_ctor_set(v___x_4780_, 0, v___x_4783_);
v___x_4785_ = v___x_4780_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v___x_4783_);
lean_ctor_set(v_reuseFailAlloc_4786_, 1, v_a_4778_);
v___x_4785_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
return v___x_4785_;
}
}
}
}
else
{
lean_object* v_a_4789_; lean_object* v_a_4790_; lean_object* v_log_4791_; uint8_t v_action_4792_; uint8_t v_wantsRebuild_4793_; lean_object* v_trace_4794_; lean_object* v_buildTime_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4805_; 
lean_del_object(v___x_4768_);
v_a_4789_ = lean_ctor_get(v___x_4776_, 1);
lean_inc(v_a_4789_);
v_a_4790_ = lean_ctor_get(v___x_4776_, 0);
lean_inc(v_a_4790_);
lean_dec_ref(v___x_4776_);
v_log_4791_ = lean_ctor_get(v_a_4789_, 0);
lean_inc_ref(v_log_4791_);
v_action_4792_ = lean_ctor_get_uint8(v_a_4789_, sizeof(void*)*3);
v_wantsRebuild_4793_ = lean_ctor_get_uint8(v_a_4789_, sizeof(void*)*3 + 1);
v_trace_4794_ = lean_ctor_get(v_a_4789_, 1);
lean_inc_ref(v_trace_4794_);
v_buildTime_4795_ = lean_ctor_get(v_a_4789_, 2);
lean_inc(v_buildTime_4795_);
lean_dec(v_a_4789_);
v___x_4796_ = lean_array_get_size(v_log_4791_);
lean_inc(v_a_4790_);
v___x_4797_ = l_Array_extract___redArg(v_log_4791_, v_a_4790_, v___x_4796_);
v___x_4798_ = l_Array_shrink___redArg(v_log_4791_, v_a_4790_);
lean_dec(v_a_4790_);
v___x_4799_ = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___closed__2));
v___x_4800_ = l_Lake_Hash_hex(v_inputHash_4636_);
v___x_4801_ = lean_unsigned_to_nat(7u);
v___x_4802_ = lean_unsigned_to_nat(0u);
v___x_4803_ = lean_string_utf8_byte_size(v___x_4800_);
lean_inc_ref(v___x_4800_);
if (v_isShared_4775_ == 0)
{
lean_ctor_set(v___x_4774_, 2, v___x_4803_);
lean_ctor_set(v___x_4774_, 1, v___x_4802_);
lean_ctor_set(v___x_4774_, 0, v___x_4800_);
v___x_4805_ = v___x_4774_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4821_; 
v_reuseFailAlloc_4821_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4821_, 0, v___x_4800_);
lean_ctor_set(v_reuseFailAlloc_4821_, 1, v___x_4802_);
lean_ctor_set(v_reuseFailAlloc_4821_, 2, v___x_4803_);
v___x_4805_ = v_reuseFailAlloc_4821_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; uint8_t v___x_4813_; 
v___x_4806_ = l_String_Slice_Pos_nextn(v___x_4805_, v___x_4802_, v___x_4801_);
lean_dec_ref(v___x_4805_);
v___x_4807_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4807_, 0, v___x_4800_);
lean_ctor_set(v___x_4807_, 1, v___x_4802_);
lean_ctor_set(v___x_4807_, 2, v___x_4806_);
v___x_4808_ = l_String_Slice_toString(v___x_4807_);
lean_dec_ref(v___x_4807_);
v___x_4809_ = lean_string_append(v___x_4799_, v___x_4808_);
lean_dec_ref(v___x_4808_);
v___x_4810_ = ((lean_object*)(l_Lake_getArtifacts_x3f___redArg___closed__3));
v___x_4811_ = lean_string_append(v___x_4809_, v___x_4810_);
v___x_4812_ = lean_array_get_size(v___x_4797_);
v___x_4813_ = lean_nat_dec_lt(v___x_4802_, v___x_4812_);
if (v___x_4813_ == 0)
{
lean_dec_ref(v___x_4797_);
v___y_4737_ = v_a_4750_;
v___y_4738_ = v___x_4760_;
v___y_4739_ = v___x_4798_;
v___y_4740_ = v_trace_4794_;
v___y_4741_ = v_action_4792_;
v___y_4742_ = v_buildTime_4795_;
v___y_4743_ = v_wantsRebuild_4793_;
v___y_4744_ = v___x_4811_;
goto v___jp_4736_;
}
else
{
uint8_t v___x_4814_; 
v___x_4814_ = lean_nat_dec_le(v___x_4812_, v___x_4812_);
if (v___x_4814_ == 0)
{
if (v___x_4813_ == 0)
{
lean_dec_ref(v___x_4797_);
v___y_4737_ = v_a_4750_;
v___y_4738_ = v___x_4760_;
v___y_4739_ = v___x_4798_;
v___y_4740_ = v_trace_4794_;
v___y_4741_ = v_action_4792_;
v___y_4742_ = v_buildTime_4795_;
v___y_4743_ = v_wantsRebuild_4793_;
v___y_4744_ = v___x_4811_;
goto v___jp_4736_;
}
else
{
size_t v___x_4815_; size_t v___x_4816_; lean_object* v___x_4817_; 
v___x_4815_ = ((size_t)0ULL);
v___x_4816_ = lean_usize_of_nat(v___x_4812_);
v___x_4817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(v___x_4797_, v___x_4815_, v___x_4816_, v___x_4811_);
lean_dec_ref(v___x_4797_);
v___y_4737_ = v_a_4750_;
v___y_4738_ = v___x_4760_;
v___y_4739_ = v___x_4798_;
v___y_4740_ = v_trace_4794_;
v___y_4741_ = v_action_4792_;
v___y_4742_ = v_buildTime_4795_;
v___y_4743_ = v_wantsRebuild_4793_;
v___y_4744_ = v___x_4817_;
goto v___jp_4736_;
}
}
else
{
size_t v___x_4818_; size_t v___x_4819_; lean_object* v___x_4820_; 
v___x_4818_ = ((size_t)0ULL);
v___x_4819_ = lean_usize_of_nat(v___x_4812_);
v___x_4820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(v___x_4797_, v___x_4818_, v___x_4819_, v___x_4811_);
lean_dec_ref(v___x_4797_);
v___y_4737_ = v_a_4750_;
v___y_4738_ = v___x_4760_;
v___y_4739_ = v___x_4798_;
v___y_4740_ = v_trace_4794_;
v___y_4741_ = v_action_4792_;
v___y_4742_ = v_buildTime_4795_;
v___y_4743_ = v_wantsRebuild_4793_;
v___y_4744_ = v___x_4820_;
goto v___jp_4736_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_4762_);
v___y_4686_ = v_a_4750_;
v___y_4687_ = v___x_4760_;
v___y_4688_ = v___y_4635_;
v___y_4689_ = v_a_4639_;
v___y_4690_ = v_a_4640_;
v___y_4691_ = v_a_4641_;
v___y_4692_ = v_a_4642_;
v___y_4693_ = v___x_4765_;
goto v___jp_4685_;
}
}
}
else
{
lean_object* v_a_4825_; lean_object* v_a_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4836_; 
lean_dec_ref(v___x_4760_);
lean_dec_ref(v_lakeCache_4684_);
lean_dec_ref(v_a_4642_);
lean_dec(v_savedTrace_4637_);
v_a_4825_ = lean_ctor_get(v___x_4761_, 0);
v_a_4826_ = lean_ctor_get(v___x_4761_, 1);
v_isSharedCheck_4836_ = !lean_is_exclusive(v___x_4761_);
if (v_isSharedCheck_4836_ == 0)
{
v___x_4828_ = v___x_4761_;
v_isShared_4829_ = v_isSharedCheck_4836_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_a_4826_);
lean_inc(v_a_4825_);
lean_dec(v___x_4761_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4836_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
lean_object* v___x_4831_; 
if (v_isShared_4759_ == 0)
{
lean_ctor_set(v___x_4758_, 0, v_a_4826_);
v___x_4831_ = v___x_4758_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_a_4826_);
lean_ctor_set(v_reuseFailAlloc_4835_, 1, v_trace_4755_);
lean_ctor_set(v_reuseFailAlloc_4835_, 2, v_buildTime_4756_);
lean_ctor_set_uint8(v_reuseFailAlloc_4835_, sizeof(void*)*3, v_action_4753_);
lean_ctor_set_uint8(v_reuseFailAlloc_4835_, sizeof(void*)*3 + 1, v_wantsRebuild_4754_);
v___x_4831_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
lean_object* v___x_4833_; 
if (v_isShared_4829_ == 0)
{
lean_ctor_set(v___x_4828_, 1, v___x_4831_);
v___x_4833_ = v___x_4828_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v_a_4825_);
lean_ctor_set(v_reuseFailAlloc_4834_, 1, v___x_4831_);
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
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object* v_exe_4850_, lean_object* v___y_4851_, lean_object* v_inputHash_4852_, lean_object* v_savedTrace_4853_, lean_object* v_pkg_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_){
_start:
{
uint8_t v_exe_boxed_4861_; uint64_t v_inputHash_boxed_4862_; lean_object* v_res_4863_; 
v_exe_boxed_4861_ = lean_unbox(v_exe_4850_);
v_inputHash_boxed_4862_ = lean_unbox_uint64(v_inputHash_4852_);
lean_dec_ref(v_inputHash_4852_);
v_res_4863_ = l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(v_exe_boxed_4861_, v___y_4851_, v_inputHash_boxed_4862_, v_savedTrace_4853_, v_pkg_4854_, v_a_4855_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_);
lean_dec(v_a_4857_);
lean_dec(v_a_4856_);
lean_dec(v_a_4855_);
lean_dec_ref(v___y_4851_);
return v_res_4863_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(uint8_t v_exe_4864_, uint64_t v_hash_4865_, lean_object* v_a_4866_, lean_object* v_val_4867_, lean_object* v_file_4868_, lean_object* v___x_4869_, uint8_t v_restore_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_){
_start:
{
lean_object* v___x_4878_; 
lean_inc(v_a_4866_);
v___x_4878_ = l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(v_exe_4864_, v___y_4871_, v_hash_4865_, v_a_4866_, v_val_4867_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_);
if (lean_obj_tag(v___x_4878_) == 0)
{
lean_object* v_a_4879_; 
v_a_4879_ = lean_ctor_get(v___x_4878_, 0);
lean_inc(v_a_4879_);
if (lean_obj_tag(v_a_4879_) == 1)
{
lean_object* v_a_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_5018_; 
v_a_4880_ = lean_ctor_get(v___x_4878_, 1);
v_isSharedCheck_5018_ = !lean_is_exclusive(v___x_4878_);
if (v_isSharedCheck_5018_ == 0)
{
lean_object* v_unused_5019_; 
v_unused_5019_ = lean_ctor_get(v___x_4878_, 0);
lean_dec(v_unused_5019_);
v___x_4882_ = v___x_4878_;
v_isShared_4883_ = v_isSharedCheck_5018_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_a_4880_);
lean_dec(v___x_4878_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_5018_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
lean_object* v_val_4884_; lean_object* v___y_4886_; lean_object* v___x_4932_; 
v_val_4884_ = lean_ctor_get(v_a_4879_, 0);
v___x_4932_ = l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(v_hash_4865_, v_a_4866_, v_a_4880_);
lean_dec(v_a_4866_);
if (lean_obj_tag(v___x_4932_) == 0)
{
lean_object* v_a_4933_; uint8_t v___x_4934_; 
v_a_4933_ = lean_ctor_get(v___x_4932_, 0);
lean_inc(v_a_4933_);
v___x_4934_ = lean_unbox(v_a_4933_);
lean_dec(v_a_4933_);
if (v___x_4934_ == 0)
{
lean_object* v_a_4935_; lean_object* v___x_4937_; uint8_t v_isShared_4938_; uint8_t v_isSharedCheck_5006_; 
v_a_4935_ = lean_ctor_get(v___x_4932_, 1);
v_isSharedCheck_5006_ = !lean_is_exclusive(v___x_4932_);
if (v_isSharedCheck_5006_ == 0)
{
lean_object* v_unused_5007_; 
v_unused_5007_ = lean_ctor_get(v___x_4932_, 0);
lean_dec(v_unused_5007_);
v___x_4937_ = v___x_4932_;
v_isShared_4938_ = v_isSharedCheck_5006_;
goto v_resetjp_4936_;
}
else
{
lean_inc(v_a_4935_);
lean_dec(v___x_4932_);
v___x_4937_ = lean_box(0);
v_isShared_4938_ = v_isSharedCheck_5006_;
goto v_resetjp_4936_;
}
v_resetjp_4936_:
{
lean_object* v_log_4939_; uint8_t v_action_4940_; uint8_t v_wantsRebuild_4941_; lean_object* v_trace_4942_; lean_object* v_buildTime_4943_; lean_object* v___x_4944_; 
v_log_4939_ = lean_ctor_get(v_a_4935_, 0);
v_action_4940_ = lean_ctor_get_uint8(v_a_4935_, sizeof(void*)*3);
v_wantsRebuild_4941_ = lean_ctor_get_uint8(v_a_4935_, sizeof(void*)*3 + 1);
v_trace_4942_ = lean_ctor_get(v_a_4935_, 1);
v_buildTime_4943_ = lean_ctor_get(v_a_4935_, 2);
v___x_4944_ = l_Lake_removeFileIfExists(v_file_4868_);
if (lean_obj_tag(v___x_4944_) == 0)
{
lean_object* v___x_4946_; uint8_t v_isShared_4947_; uint8_t v_isSharedCheck_4985_; 
v_isSharedCheck_4985_ = !lean_is_exclusive(v___x_4944_);
if (v_isSharedCheck_4985_ == 0)
{
lean_object* v_unused_4986_; 
v_unused_4986_ = lean_ctor_get(v___x_4944_, 0);
lean_dec(v_unused_4986_);
v___x_4946_ = v___x_4944_;
v_isShared_4947_ = v_isSharedCheck_4985_;
goto v_resetjp_4945_;
}
else
{
lean_dec(v___x_4944_);
v___x_4946_ = lean_box(0);
v_isShared_4947_ = v_isSharedCheck_4985_;
goto v_resetjp_4945_;
}
v_resetjp_4945_:
{
lean_object* v___y_4949_; lean_object* v_descr_4974_; uint64_t v_hash_4975_; lean_object* v_ext_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; uint8_t v___x_4979_; 
v_descr_4974_ = lean_ctor_get(v_val_4884_, 0);
v_hash_4975_ = lean_ctor_get_uint64(v_descr_4974_, sizeof(void*)*1);
v_ext_4976_ = lean_ctor_get(v_descr_4974_, 0);
v___x_4977_ = lean_string_utf8_byte_size(v_ext_4976_);
v___x_4978_ = lean_unsigned_to_nat(0u);
v___x_4979_ = lean_nat_dec_eq(v___x_4977_, v___x_4978_);
if (v___x_4979_ == 0)
{
lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; 
v___x_4980_ = l_Lake_Hash_hex(v_hash_4975_);
v___x_4981_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_4982_ = lean_string_append(v___x_4980_, v___x_4981_);
v___x_4983_ = lean_string_append(v___x_4982_, v_ext_4976_);
v___y_4949_ = v___x_4983_;
goto v___jp_4948_;
}
else
{
lean_object* v___x_4984_; 
v___x_4984_ = l_Lake_Hash_hex(v_hash_4975_);
v___y_4949_ = v___x_4984_;
goto v___jp_4948_;
}
v___jp_4948_:
{
lean_object* v___x_4951_; 
if (v_isShared_4947_ == 0)
{
lean_ctor_set_tag(v___x_4946_, 3);
lean_ctor_set(v___x_4946_, 0, v___y_4949_);
v___x_4951_ = v___x_4946_;
goto v_reusejp_4950_;
}
else
{
lean_object* v_reuseFailAlloc_4973_; 
v_reuseFailAlloc_4973_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4973_, 0, v___y_4949_);
v___x_4951_ = v_reuseFailAlloc_4973_;
goto v_reusejp_4950_;
}
v_reusejp_4950_:
{
lean_object* v___x_4952_; lean_object* v___x_4953_; 
v___x_4952_ = l_Lake_BuildMetadata_ofFetch(v_hash_4865_, v___x_4951_);
v___x_4953_ = l_Lake_BuildMetadata_writeFile(v___x_4869_, v___x_4952_);
if (lean_obj_tag(v___x_4953_) == 0)
{
lean_dec_ref(v___x_4953_);
lean_del_object(v___x_4937_);
v___y_4886_ = v_a_4935_;
goto v___jp_4885_;
}
else
{
lean_object* v___x_4955_; uint8_t v_isShared_4956_; uint8_t v_isSharedCheck_4969_; 
lean_inc(v_buildTime_4943_);
lean_inc_ref(v_trace_4942_);
lean_inc_ref(v_log_4939_);
lean_del_object(v___x_4882_);
lean_dec_ref(v_a_4879_);
lean_dec_ref(v_file_4868_);
v_isSharedCheck_4969_ = !lean_is_exclusive(v_a_4935_);
if (v_isSharedCheck_4969_ == 0)
{
lean_object* v_unused_4970_; lean_object* v_unused_4971_; lean_object* v_unused_4972_; 
v_unused_4970_ = lean_ctor_get(v_a_4935_, 2);
lean_dec(v_unused_4970_);
v_unused_4971_ = lean_ctor_get(v_a_4935_, 1);
lean_dec(v_unused_4971_);
v_unused_4972_ = lean_ctor_get(v_a_4935_, 0);
lean_dec(v_unused_4972_);
v___x_4955_ = v_a_4935_;
v_isShared_4956_ = v_isSharedCheck_4969_;
goto v_resetjp_4954_;
}
else
{
lean_dec(v_a_4935_);
v___x_4955_ = lean_box(0);
v_isShared_4956_ = v_isSharedCheck_4969_;
goto v_resetjp_4954_;
}
v_resetjp_4954_:
{
lean_object* v_a_4957_; lean_object* v___x_4958_; uint8_t v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4964_; 
v_a_4957_ = lean_ctor_get(v___x_4953_, 0);
lean_inc(v_a_4957_);
lean_dec_ref(v___x_4953_);
v___x_4958_ = lean_io_error_to_string(v_a_4957_);
v___x_4959_ = 3;
v___x_4960_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4960_, 0, v___x_4958_);
lean_ctor_set_uint8(v___x_4960_, sizeof(void*)*1, v___x_4959_);
v___x_4961_ = lean_array_get_size(v_log_4939_);
v___x_4962_ = lean_array_push(v_log_4939_, v___x_4960_);
if (v_isShared_4956_ == 0)
{
lean_ctor_set(v___x_4955_, 0, v___x_4962_);
v___x_4964_ = v___x_4955_;
goto v_reusejp_4963_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v___x_4962_);
lean_ctor_set(v_reuseFailAlloc_4968_, 1, v_trace_4942_);
lean_ctor_set(v_reuseFailAlloc_4968_, 2, v_buildTime_4943_);
lean_ctor_set_uint8(v_reuseFailAlloc_4968_, sizeof(void*)*3, v_action_4940_);
lean_ctor_set_uint8(v_reuseFailAlloc_4968_, sizeof(void*)*3 + 1, v_wantsRebuild_4941_);
v___x_4964_ = v_reuseFailAlloc_4968_;
goto v_reusejp_4963_;
}
v_reusejp_4963_:
{
lean_object* v___x_4966_; 
if (v_isShared_4938_ == 0)
{
lean_ctor_set_tag(v___x_4937_, 1);
lean_ctor_set(v___x_4937_, 1, v___x_4964_);
lean_ctor_set(v___x_4937_, 0, v___x_4961_);
v___x_4966_ = v___x_4937_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v___x_4961_);
lean_ctor_set(v_reuseFailAlloc_4967_, 1, v___x_4964_);
v___x_4966_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
return v___x_4966_;
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
lean_object* v___x_4988_; uint8_t v_isShared_4989_; uint8_t v_isSharedCheck_5002_; 
lean_inc(v_buildTime_4943_);
lean_inc_ref(v_trace_4942_);
lean_inc_ref(v_log_4939_);
lean_del_object(v___x_4882_);
lean_dec_ref(v_a_4879_);
lean_dec_ref(v___x_4869_);
lean_dec_ref(v_file_4868_);
v_isSharedCheck_5002_ = !lean_is_exclusive(v_a_4935_);
if (v_isSharedCheck_5002_ == 0)
{
lean_object* v_unused_5003_; lean_object* v_unused_5004_; lean_object* v_unused_5005_; 
v_unused_5003_ = lean_ctor_get(v_a_4935_, 2);
lean_dec(v_unused_5003_);
v_unused_5004_ = lean_ctor_get(v_a_4935_, 1);
lean_dec(v_unused_5004_);
v_unused_5005_ = lean_ctor_get(v_a_4935_, 0);
lean_dec(v_unused_5005_);
v___x_4988_ = v_a_4935_;
v_isShared_4989_ = v_isSharedCheck_5002_;
goto v_resetjp_4987_;
}
else
{
lean_dec(v_a_4935_);
v___x_4988_ = lean_box(0);
v_isShared_4989_ = v_isSharedCheck_5002_;
goto v_resetjp_4987_;
}
v_resetjp_4987_:
{
lean_object* v_a_4990_; lean_object* v___x_4991_; uint8_t v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4997_; 
v_a_4990_ = lean_ctor_get(v___x_4944_, 0);
lean_inc(v_a_4990_);
lean_dec_ref(v___x_4944_);
v___x_4991_ = lean_io_error_to_string(v_a_4990_);
v___x_4992_ = 3;
v___x_4993_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4993_, 0, v___x_4991_);
lean_ctor_set_uint8(v___x_4993_, sizeof(void*)*1, v___x_4992_);
v___x_4994_ = lean_array_get_size(v_log_4939_);
v___x_4995_ = lean_array_push(v_log_4939_, v___x_4993_);
if (v_isShared_4989_ == 0)
{
lean_ctor_set(v___x_4988_, 0, v___x_4995_);
v___x_4997_ = v___x_4988_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v___x_4995_);
lean_ctor_set(v_reuseFailAlloc_5001_, 1, v_trace_4942_);
lean_ctor_set(v_reuseFailAlloc_5001_, 2, v_buildTime_4943_);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, sizeof(void*)*3, v_action_4940_);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, sizeof(void*)*3 + 1, v_wantsRebuild_4941_);
v___x_4997_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
lean_object* v___x_4999_; 
if (v_isShared_4938_ == 0)
{
lean_ctor_set_tag(v___x_4937_, 1);
lean_ctor_set(v___x_4937_, 1, v___x_4997_);
lean_ctor_set(v___x_4937_, 0, v___x_4994_);
v___x_4999_ = v___x_4937_;
goto v_reusejp_4998_;
}
else
{
lean_object* v_reuseFailAlloc_5000_; 
v_reuseFailAlloc_5000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5000_, 0, v___x_4994_);
lean_ctor_set(v_reuseFailAlloc_5000_, 1, v___x_4997_);
v___x_4999_ = v_reuseFailAlloc_5000_;
goto v_reusejp_4998_;
}
v_reusejp_4998_:
{
return v___x_4999_;
}
}
}
}
}
}
else
{
lean_object* v_a_5008_; 
lean_dec_ref(v___x_4869_);
v_a_5008_ = lean_ctor_get(v___x_4932_, 1);
lean_inc(v_a_5008_);
lean_dec_ref(v___x_4932_);
v___y_4886_ = v_a_5008_;
goto v___jp_4885_;
}
}
else
{
lean_object* v_a_5009_; lean_object* v_a_5010_; lean_object* v___x_5012_; uint8_t v_isShared_5013_; uint8_t v_isSharedCheck_5017_; 
lean_del_object(v___x_4882_);
lean_dec_ref(v_a_4879_);
lean_dec_ref(v___x_4869_);
lean_dec_ref(v_file_4868_);
v_a_5009_ = lean_ctor_get(v___x_4932_, 0);
v_a_5010_ = lean_ctor_get(v___x_4932_, 1);
v_isSharedCheck_5017_ = !lean_is_exclusive(v___x_4932_);
if (v_isSharedCheck_5017_ == 0)
{
v___x_5012_ = v___x_4932_;
v_isShared_5013_ = v_isSharedCheck_5017_;
goto v_resetjp_5011_;
}
else
{
lean_inc(v_a_5010_);
lean_inc(v_a_5009_);
lean_dec(v___x_4932_);
v___x_5012_ = lean_box(0);
v_isShared_5013_ = v_isSharedCheck_5017_;
goto v_resetjp_5011_;
}
v_resetjp_5011_:
{
lean_object* v___x_5015_; 
if (v_isShared_5013_ == 0)
{
v___x_5015_ = v___x_5012_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v_a_5009_);
lean_ctor_set(v_reuseFailAlloc_5016_, 1, v_a_5010_);
v___x_5015_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
return v___x_5015_;
}
}
}
v___jp_4885_:
{
if (v_restore_4870_ == 0)
{
lean_object* v___x_4888_; 
lean_dec_ref(v_file_4868_);
if (v_isShared_4883_ == 0)
{
lean_ctor_set(v___x_4882_, 1, v___y_4886_);
v___x_4888_ = v___x_4882_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v_a_4879_);
lean_ctor_set(v_reuseFailAlloc_4889_, 1, v___y_4886_);
v___x_4888_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
return v___x_4888_;
}
}
else
{
lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4930_; 
lean_inc(v_val_4884_);
lean_del_object(v___x_4882_);
v_isSharedCheck_4930_ = !lean_is_exclusive(v_a_4879_);
if (v_isSharedCheck_4930_ == 0)
{
lean_object* v_unused_4931_; 
v_unused_4931_ = lean_ctor_get(v_a_4879_, 0);
lean_dec(v_unused_4931_);
v___x_4891_ = v_a_4879_;
v_isShared_4892_ = v_isSharedCheck_4930_;
goto v_resetjp_4890_;
}
else
{
lean_dec(v_a_4879_);
v___x_4891_ = lean_box(0);
v_isShared_4892_ = v_isSharedCheck_4930_;
goto v_resetjp_4890_;
}
v_resetjp_4890_:
{
lean_object* v_log_4893_; uint8_t v_action_4894_; uint8_t v_wantsRebuild_4895_; lean_object* v_trace_4896_; lean_object* v_buildTime_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4929_; 
v_log_4893_ = lean_ctor_get(v___y_4886_, 0);
v_action_4894_ = lean_ctor_get_uint8(v___y_4886_, sizeof(void*)*3);
v_wantsRebuild_4895_ = lean_ctor_get_uint8(v___y_4886_, sizeof(void*)*3 + 1);
v_trace_4896_ = lean_ctor_get(v___y_4886_, 1);
v_buildTime_4897_ = lean_ctor_get(v___y_4886_, 2);
v_isSharedCheck_4929_ = !lean_is_exclusive(v___y_4886_);
if (v_isSharedCheck_4929_ == 0)
{
v___x_4899_ = v___y_4886_;
v_isShared_4900_ = v_isSharedCheck_4929_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_buildTime_4897_);
lean_inc(v_trace_4896_);
lean_inc(v_log_4893_);
lean_dec(v___y_4886_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4929_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v___x_4901_; 
v___x_4901_ = l_Lake_restoreArtifact(v_file_4868_, v_val_4884_, v_exe_4864_, v_log_4893_);
if (lean_obj_tag(v___x_4901_) == 0)
{
lean_object* v_a_4902_; lean_object* v_a_4903_; lean_object* v___x_4905_; uint8_t v_isShared_4906_; uint8_t v_isSharedCheck_4916_; 
v_a_4902_ = lean_ctor_get(v___x_4901_, 0);
v_a_4903_ = lean_ctor_get(v___x_4901_, 1);
v_isSharedCheck_4916_ = !lean_is_exclusive(v___x_4901_);
if (v_isSharedCheck_4916_ == 0)
{
v___x_4905_ = v___x_4901_;
v_isShared_4906_ = v_isSharedCheck_4916_;
goto v_resetjp_4904_;
}
else
{
lean_inc(v_a_4903_);
lean_inc(v_a_4902_);
lean_dec(v___x_4901_);
v___x_4905_ = lean_box(0);
v_isShared_4906_ = v_isSharedCheck_4916_;
goto v_resetjp_4904_;
}
v_resetjp_4904_:
{
lean_object* v___x_4908_; 
if (v_isShared_4900_ == 0)
{
lean_ctor_set(v___x_4899_, 0, v_a_4903_);
v___x_4908_ = v___x_4899_;
goto v_reusejp_4907_;
}
else
{
lean_object* v_reuseFailAlloc_4915_; 
v_reuseFailAlloc_4915_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4915_, 0, v_a_4903_);
lean_ctor_set(v_reuseFailAlloc_4915_, 1, v_trace_4896_);
lean_ctor_set(v_reuseFailAlloc_4915_, 2, v_buildTime_4897_);
lean_ctor_set_uint8(v_reuseFailAlloc_4915_, sizeof(void*)*3, v_action_4894_);
lean_ctor_set_uint8(v_reuseFailAlloc_4915_, sizeof(void*)*3 + 1, v_wantsRebuild_4895_);
v___x_4908_ = v_reuseFailAlloc_4915_;
goto v_reusejp_4907_;
}
v_reusejp_4907_:
{
lean_object* v___x_4910_; 
if (v_isShared_4892_ == 0)
{
lean_ctor_set(v___x_4891_, 0, v_a_4902_);
v___x_4910_ = v___x_4891_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4914_; 
v_reuseFailAlloc_4914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4914_, 0, v_a_4902_);
v___x_4910_ = v_reuseFailAlloc_4914_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
lean_object* v___x_4912_; 
if (v_isShared_4906_ == 0)
{
lean_ctor_set(v___x_4905_, 1, v___x_4908_);
lean_ctor_set(v___x_4905_, 0, v___x_4910_);
v___x_4912_ = v___x_4905_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v___x_4910_);
lean_ctor_set(v_reuseFailAlloc_4913_, 1, v___x_4908_);
v___x_4912_ = v_reuseFailAlloc_4913_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
return v___x_4912_;
}
}
}
}
}
else
{
lean_object* v_a_4917_; lean_object* v_a_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4928_; 
lean_del_object(v___x_4891_);
v_a_4917_ = lean_ctor_get(v___x_4901_, 0);
v_a_4918_ = lean_ctor_get(v___x_4901_, 1);
v_isSharedCheck_4928_ = !lean_is_exclusive(v___x_4901_);
if (v_isSharedCheck_4928_ == 0)
{
v___x_4920_ = v___x_4901_;
v_isShared_4921_ = v_isSharedCheck_4928_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_a_4918_);
lean_inc(v_a_4917_);
lean_dec(v___x_4901_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4928_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v___x_4923_; 
if (v_isShared_4900_ == 0)
{
lean_ctor_set(v___x_4899_, 0, v_a_4918_);
v___x_4923_ = v___x_4899_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v_a_4918_);
lean_ctor_set(v_reuseFailAlloc_4927_, 1, v_trace_4896_);
lean_ctor_set(v_reuseFailAlloc_4927_, 2, v_buildTime_4897_);
lean_ctor_set_uint8(v_reuseFailAlloc_4927_, sizeof(void*)*3, v_action_4894_);
lean_ctor_set_uint8(v_reuseFailAlloc_4927_, sizeof(void*)*3 + 1, v_wantsRebuild_4895_);
v___x_4923_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
lean_object* v___x_4925_; 
if (v_isShared_4921_ == 0)
{
lean_ctor_set(v___x_4920_, 1, v___x_4923_);
v___x_4925_ = v___x_4920_;
goto v_reusejp_4924_;
}
else
{
lean_object* v_reuseFailAlloc_4926_; 
v_reuseFailAlloc_4926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4926_, 0, v_a_4917_);
lean_ctor_set(v_reuseFailAlloc_4926_, 1, v___x_4923_);
v___x_4925_ = v_reuseFailAlloc_4926_;
goto v_reusejp_4924_;
}
v_reusejp_4924_:
{
return v___x_4925_;
}
}
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
lean_object* v_a_5020_; lean_object* v___x_5022_; uint8_t v_isShared_5023_; uint8_t v_isSharedCheck_5028_; 
lean_dec(v_a_4879_);
lean_dec_ref(v___x_4869_);
lean_dec_ref(v_file_4868_);
lean_dec(v_a_4866_);
v_a_5020_ = lean_ctor_get(v___x_4878_, 1);
v_isSharedCheck_5028_ = !lean_is_exclusive(v___x_4878_);
if (v_isSharedCheck_5028_ == 0)
{
lean_object* v_unused_5029_; 
v_unused_5029_ = lean_ctor_get(v___x_4878_, 0);
lean_dec(v_unused_5029_);
v___x_5022_ = v___x_4878_;
v_isShared_5023_ = v_isSharedCheck_5028_;
goto v_resetjp_5021_;
}
else
{
lean_inc(v_a_5020_);
lean_dec(v___x_4878_);
v___x_5022_ = lean_box(0);
v_isShared_5023_ = v_isSharedCheck_5028_;
goto v_resetjp_5021_;
}
v_resetjp_5021_:
{
lean_object* v___x_5024_; lean_object* v___x_5026_; 
v___x_5024_ = lean_box(0);
if (v_isShared_5023_ == 0)
{
lean_ctor_set(v___x_5022_, 0, v___x_5024_);
v___x_5026_ = v___x_5022_;
goto v_reusejp_5025_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v___x_5024_);
lean_ctor_set(v_reuseFailAlloc_5027_, 1, v_a_5020_);
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
lean_dec_ref(v___x_4869_);
lean_dec_ref(v_file_4868_);
lean_dec(v_a_4866_);
return v___x_4878_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object* v_exe_5030_, lean_object* v_hash_5031_, lean_object* v_a_5032_, lean_object* v_val_5033_, lean_object* v_file_5034_, lean_object* v___x_5035_, lean_object* v_restore_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_){
_start:
{
uint8_t v_exe_boxed_5044_; uint64_t v_hash_boxed_5045_; uint8_t v_restore_boxed_5046_; lean_object* v_res_5047_; 
v_exe_boxed_5044_ = lean_unbox(v_exe_5030_);
v_hash_boxed_5045_ = lean_unbox_uint64(v_hash_5031_);
lean_dec_ref(v_hash_5031_);
v_restore_boxed_5046_ = lean_unbox(v_restore_5036_);
v_res_5047_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_boxed_5044_, v_hash_boxed_5045_, v_a_5032_, v_val_5033_, v_file_5034_, v___x_5035_, v_restore_boxed_5046_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_);
lean_dec(v___y_5040_);
lean_dec(v___y_5039_);
lean_dec(v___y_5038_);
lean_dec_ref(v___y_5037_);
return v_res_5047_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1(uint8_t v_a_5048_, lean_object* v_file_5049_, lean_object* v_ext_5050_, uint8_t v_text_5051_, uint8_t v_exe_5052_, uint8_t v___y_5053_, lean_object* v_val_5054_, uint64_t v_hash_5055_, lean_object* v_____r_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_){
_start:
{
uint8_t v___x_5064_; uint8_t v___x_5065_; 
v___x_5064_ = 1;
v___x_5065_ = l_Lake_instDecidableEqOutputStatus(v_a_5048_, v___x_5064_);
if (v___x_5065_ == 0)
{
lean_object* v_toContext_5066_; lean_object* v_log_5067_; uint8_t v_action_5068_; uint8_t v_wantsRebuild_5069_; lean_object* v_trace_5070_; lean_object* v_buildTime_5071_; lean_object* v_lakeCache_5072_; lean_object* v___x_5073_; 
v_toContext_5066_ = lean_ctor_get(v___y_5061_, 1);
lean_inc(v_toContext_5066_);
lean_dec_ref(v___y_5061_);
v_log_5067_ = lean_ctor_get(v___y_5062_, 0);
v_action_5068_ = lean_ctor_get_uint8(v___y_5062_, sizeof(void*)*3);
v_wantsRebuild_5069_ = lean_ctor_get_uint8(v___y_5062_, sizeof(void*)*3 + 1);
v_trace_5070_ = lean_ctor_get(v___y_5062_, 1);
v_buildTime_5071_ = lean_ctor_get(v___y_5062_, 2);
v_lakeCache_5072_ = lean_ctor_get(v_toContext_5066_, 3);
lean_inc_ref(v_lakeCache_5072_);
lean_dec(v_toContext_5066_);
lean_inc_ref(v_lakeCache_5072_);
v___x_5073_ = l_Lake_Cache_saveArtifact(v_lakeCache_5072_, v_file_5049_, v_ext_5050_, v_text_5051_, v_exe_5052_, v___y_5053_);
if (lean_obj_tag(v___x_5073_) == 0)
{
lean_object* v_a_5074_; lean_object* v___x_5076_; uint8_t v_isShared_5077_; uint8_t v_isSharedCheck_5115_; 
v_a_5074_ = lean_ctor_get(v___x_5073_, 0);
v_isSharedCheck_5115_ = !lean_is_exclusive(v___x_5073_);
if (v_isSharedCheck_5115_ == 0)
{
v___x_5076_ = v___x_5073_;
v_isShared_5077_ = v_isSharedCheck_5115_;
goto v_resetjp_5075_;
}
else
{
lean_inc(v_a_5074_);
lean_dec(v___x_5073_);
v___x_5076_ = lean_box(0);
v_isShared_5077_ = v_isSharedCheck_5115_;
goto v_resetjp_5075_;
}
v_resetjp_5075_:
{
lean_object* v_descr_5078_; uint64_t v_hash_5079_; lean_object* v_ext_5080_; lean_object* v___x_5081_; lean_object* v___y_5083_; lean_object* v___x_5107_; lean_object* v___x_5108_; uint8_t v___x_5109_; 
v_descr_5078_ = lean_ctor_get(v_a_5074_, 0);
v_hash_5079_ = lean_ctor_get_uint64(v_descr_5078_, sizeof(void*)*1);
v_ext_5080_ = lean_ctor_get(v_descr_5078_, 0);
v___x_5081_ = l_Lake_Package_cacheScope(v_val_5054_);
v___x_5107_ = lean_string_utf8_byte_size(v_ext_5080_);
v___x_5108_ = lean_unsigned_to_nat(0u);
v___x_5109_ = lean_nat_dec_eq(v___x_5107_, v___x_5108_);
if (v___x_5109_ == 0)
{
lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; 
v___x_5110_ = l_Lake_Hash_hex(v_hash_5079_);
v___x_5111_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5112_ = lean_string_append(v___x_5110_, v___x_5111_);
v___x_5113_ = lean_string_append(v___x_5112_, v_ext_5080_);
v___y_5083_ = v___x_5113_;
goto v___jp_5082_;
}
else
{
lean_object* v___x_5114_; 
v___x_5114_ = l_Lake_Hash_hex(v_hash_5079_);
v___y_5083_ = v___x_5114_;
goto v___jp_5082_;
}
v___jp_5082_:
{
lean_object* v___x_5085_; 
if (v_isShared_5077_ == 0)
{
lean_ctor_set_tag(v___x_5076_, 3);
lean_ctor_set(v___x_5076_, 0, v___y_5083_);
v___x_5085_ = v___x_5076_;
goto v_reusejp_5084_;
}
else
{
lean_object* v_reuseFailAlloc_5106_; 
v_reuseFailAlloc_5106_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5106_, 0, v___y_5083_);
v___x_5085_ = v_reuseFailAlloc_5106_;
goto v_reusejp_5084_;
}
v_reusejp_5084_:
{
lean_object* v___x_5086_; lean_object* v___x_5087_; 
v___x_5086_ = lean_box(0);
v___x_5087_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_5072_, v___x_5081_, v_hash_5055_, v___x_5085_, v___x_5086_, v___x_5086_);
if (lean_obj_tag(v___x_5087_) == 0)
{
lean_object* v___x_5088_; 
lean_dec_ref(v___x_5087_);
v___x_5088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5088_, 0, v_a_5074_);
lean_ctor_set(v___x_5088_, 1, v___y_5062_);
return v___x_5088_;
}
else
{
lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5102_; 
lean_inc(v_buildTime_5071_);
lean_inc_ref(v_trace_5070_);
lean_inc_ref(v_log_5067_);
lean_dec(v_a_5074_);
v_isSharedCheck_5102_ = !lean_is_exclusive(v___y_5062_);
if (v_isSharedCheck_5102_ == 0)
{
lean_object* v_unused_5103_; lean_object* v_unused_5104_; lean_object* v_unused_5105_; 
v_unused_5103_ = lean_ctor_get(v___y_5062_, 2);
lean_dec(v_unused_5103_);
v_unused_5104_ = lean_ctor_get(v___y_5062_, 1);
lean_dec(v_unused_5104_);
v_unused_5105_ = lean_ctor_get(v___y_5062_, 0);
lean_dec(v_unused_5105_);
v___x_5090_ = v___y_5062_;
v_isShared_5091_ = v_isSharedCheck_5102_;
goto v_resetjp_5089_;
}
else
{
lean_dec(v___y_5062_);
v___x_5090_ = lean_box(0);
v_isShared_5091_ = v_isSharedCheck_5102_;
goto v_resetjp_5089_;
}
v_resetjp_5089_:
{
lean_object* v_a_5092_; lean_object* v___x_5093_; uint8_t v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5099_; 
v_a_5092_ = lean_ctor_get(v___x_5087_, 0);
lean_inc(v_a_5092_);
lean_dec_ref(v___x_5087_);
v___x_5093_ = lean_io_error_to_string(v_a_5092_);
v___x_5094_ = 3;
v___x_5095_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5095_, 0, v___x_5093_);
lean_ctor_set_uint8(v___x_5095_, sizeof(void*)*1, v___x_5094_);
v___x_5096_ = lean_array_get_size(v_log_5067_);
v___x_5097_ = lean_array_push(v_log_5067_, v___x_5095_);
if (v_isShared_5091_ == 0)
{
lean_ctor_set(v___x_5090_, 0, v___x_5097_);
v___x_5099_ = v___x_5090_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v___x_5097_);
lean_ctor_set(v_reuseFailAlloc_5101_, 1, v_trace_5070_);
lean_ctor_set(v_reuseFailAlloc_5101_, 2, v_buildTime_5071_);
lean_ctor_set_uint8(v_reuseFailAlloc_5101_, sizeof(void*)*3, v_action_5068_);
lean_ctor_set_uint8(v_reuseFailAlloc_5101_, sizeof(void*)*3 + 1, v_wantsRebuild_5069_);
v___x_5099_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
lean_object* v___x_5100_; 
v___x_5100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5100_, 0, v___x_5096_);
lean_ctor_set(v___x_5100_, 1, v___x_5099_);
return v___x_5100_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5117_; uint8_t v_isShared_5118_; uint8_t v_isSharedCheck_5129_; 
lean_inc(v_buildTime_5071_);
lean_inc_ref(v_trace_5070_);
lean_inc_ref(v_log_5067_);
lean_dec_ref(v_lakeCache_5072_);
lean_dec_ref(v_val_5054_);
v_isSharedCheck_5129_ = !lean_is_exclusive(v___y_5062_);
if (v_isSharedCheck_5129_ == 0)
{
lean_object* v_unused_5130_; lean_object* v_unused_5131_; lean_object* v_unused_5132_; 
v_unused_5130_ = lean_ctor_get(v___y_5062_, 2);
lean_dec(v_unused_5130_);
v_unused_5131_ = lean_ctor_get(v___y_5062_, 1);
lean_dec(v_unused_5131_);
v_unused_5132_ = lean_ctor_get(v___y_5062_, 0);
lean_dec(v_unused_5132_);
v___x_5117_ = v___y_5062_;
v_isShared_5118_ = v_isSharedCheck_5129_;
goto v_resetjp_5116_;
}
else
{
lean_dec(v___y_5062_);
v___x_5117_ = lean_box(0);
v_isShared_5118_ = v_isSharedCheck_5129_;
goto v_resetjp_5116_;
}
v_resetjp_5116_:
{
lean_object* v_a_5119_; lean_object* v___x_5120_; uint8_t v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5126_; 
v_a_5119_ = lean_ctor_get(v___x_5073_, 0);
lean_inc(v_a_5119_);
lean_dec_ref(v___x_5073_);
v___x_5120_ = lean_io_error_to_string(v_a_5119_);
v___x_5121_ = 3;
v___x_5122_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5122_, 0, v___x_5120_);
lean_ctor_set_uint8(v___x_5122_, sizeof(void*)*1, v___x_5121_);
v___x_5123_ = lean_array_get_size(v_log_5067_);
v___x_5124_ = lean_array_push(v_log_5067_, v___x_5122_);
if (v_isShared_5118_ == 0)
{
lean_ctor_set(v___x_5117_, 0, v___x_5124_);
v___x_5126_ = v___x_5117_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5128_; 
v_reuseFailAlloc_5128_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5128_, 0, v___x_5124_);
lean_ctor_set(v_reuseFailAlloc_5128_, 1, v_trace_5070_);
lean_ctor_set(v_reuseFailAlloc_5128_, 2, v_buildTime_5071_);
lean_ctor_set_uint8(v_reuseFailAlloc_5128_, sizeof(void*)*3, v_action_5068_);
lean_ctor_set_uint8(v_reuseFailAlloc_5128_, sizeof(void*)*3 + 1, v_wantsRebuild_5069_);
v___x_5126_ = v_reuseFailAlloc_5128_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
lean_object* v___x_5127_; 
v___x_5127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5127_, 0, v___x_5123_);
lean_ctor_set(v___x_5127_, 1, v___x_5126_);
return v___x_5127_;
}
}
}
}
else
{
lean_object* v___x_5133_; 
lean_dec_ref(v_val_5054_);
v___x_5133_ = l_Lake_computeArtifact___redArg(v_file_5049_, v_ext_5050_, v_text_5051_, v___y_5061_, v___y_5062_);
lean_dec_ref(v___y_5061_);
return v___x_5133_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___boxed(lean_object* v_a_5134_, lean_object* v_file_5135_, lean_object* v_ext_5136_, lean_object* v_text_5137_, lean_object* v_exe_5138_, lean_object* v___y_5139_, lean_object* v_val_5140_, lean_object* v_hash_5141_, lean_object* v_____r_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_){
_start:
{
uint8_t v_a_312305__boxed_5150_; uint8_t v_text_boxed_5151_; uint8_t v_exe_boxed_5152_; uint8_t v___y_312306__boxed_5153_; uint64_t v_hash_boxed_5154_; lean_object* v_res_5155_; 
v_a_312305__boxed_5150_ = lean_unbox(v_a_5134_);
v_text_boxed_5151_ = lean_unbox(v_text_5137_);
v_exe_boxed_5152_ = lean_unbox(v_exe_5138_);
v___y_312306__boxed_5153_ = lean_unbox(v___y_5139_);
v_hash_boxed_5154_ = lean_unbox_uint64(v_hash_5141_);
lean_dec_ref(v_hash_5141_);
v_res_5155_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v_a_312305__boxed_5150_, v_file_5135_, v_ext_5136_, v_text_boxed_5151_, v_exe_boxed_5152_, v___y_312306__boxed_5153_, v_val_5140_, v_hash_boxed_5154_, v_____r_5142_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_);
lean_dec(v___y_5146_);
lean_dec(v___y_5145_);
lean_dec(v___y_5144_);
lean_dec_ref(v___y_5143_);
return v_res_5155_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object* v_file_5156_, lean_object* v_build_5157_, uint8_t v_text_5158_, lean_object* v_ext_5159_, uint8_t v_restore_5160_, uint8_t v_exe_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_){
_start:
{
lean_object* v_log_5169_; uint8_t v_action_5170_; uint8_t v_wantsRebuild_5171_; lean_object* v_trace_5172_; lean_object* v_buildTime_5173_; lean_object* v___x_5175_; uint8_t v_isShared_5176_; uint8_t v_isSharedCheck_5416_; 
v_log_5169_ = lean_ctor_get(v_a_5167_, 0);
v_action_5170_ = lean_ctor_get_uint8(v_a_5167_, sizeof(void*)*3);
v_wantsRebuild_5171_ = lean_ctor_get_uint8(v_a_5167_, sizeof(void*)*3 + 1);
v_trace_5172_ = lean_ctor_get(v_a_5167_, 1);
v_buildTime_5173_ = lean_ctor_get(v_a_5167_, 2);
v_isSharedCheck_5416_ = !lean_is_exclusive(v_a_5167_);
if (v_isSharedCheck_5416_ == 0)
{
v___x_5175_ = v_a_5167_;
v_isShared_5176_ = v_isSharedCheck_5416_;
goto v_resetjp_5174_;
}
else
{
lean_inc(v_buildTime_5173_);
lean_inc(v_trace_5172_);
lean_inc(v_log_5169_);
lean_dec(v_a_5167_);
v___x_5175_ = lean_box(0);
v_isShared_5176_ = v_isSharedCheck_5416_;
goto v_resetjp_5174_;
}
v_resetjp_5174_:
{
lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v_art_5180_; lean_object* v___y_5181_; lean_object* v___y_5197_; lean_object* v_log_5198_; uint8_t v_action_5199_; uint8_t v_wantsRebuild_5200_; lean_object* v_buildTime_5201_; lean_object* v___x_5207_; 
v___x_5177_ = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(v_file_5156_);
v___x_5178_ = lean_string_append(v_file_5156_, v___x_5177_);
lean_inc_ref(v___x_5178_);
v___x_5207_ = l_Lake_readTraceFile(v___x_5178_, v_log_5169_);
if (lean_obj_tag(v___x_5207_) == 0)
{
if (lean_obj_tag(v_a_5163_) == 1)
{
lean_object* v_a_5208_; lean_object* v_a_5209_; lean_object* v_val_5210_; uint64_t v_hash_5211_; lean_object* v_mtime_5212_; uint8_t v___y_5214_; lean_object* v___y_5215_; uint8_t v___y_5216_; lean_object* v___y_5217_; lean_object* v___y_5218_; lean_object* v___y_5219_; lean_object* v___y_5220_; lean_object* v___y_5221_; lean_object* v___y_5222_; lean_object* v_config_5226_; lean_object* v_outputsRef_x3f_5227_; lean_object* v_a_5229_; lean_object* v_a_5230_; lean_object* v___y_5254_; lean_object* v_enableArtifactCache_x3f_5257_; lean_object* v_restoreAllArtifacts_x3f_5258_; uint8_t v___y_5260_; lean_object* v_a_5261_; uint8_t v___y_5278_; uint8_t v_a_5279_; lean_object* v_a_5280_; lean_object* v_a_5283_; lean_object* v___y_5313_; uint8_t v___y_5314_; uint8_t v___y_5353_; uint8_t v_a_5354_; lean_object* v_a_5355_; uint8_t v_a_5357_; lean_object* v_a_5358_; lean_object* v___x_5368_; 
v_a_5208_ = lean_ctor_get(v___x_5207_, 0);
lean_inc(v_a_5208_);
v_a_5209_ = lean_ctor_get(v___x_5207_, 1);
lean_inc(v_a_5209_);
lean_dec_ref(v___x_5207_);
v_val_5210_ = lean_ctor_get(v_a_5163_, 0);
v_hash_5211_ = lean_ctor_get_uint64(v_trace_5172_, sizeof(void*)*3);
v_mtime_5212_ = lean_ctor_get(v_trace_5172_, 2);
v_config_5226_ = lean_ctor_get(v_val_5210_, 6);
v_outputsRef_x3f_5227_ = lean_ctor_get(v_val_5210_, 23);
lean_inc(v_outputsRef_x3f_5227_);
v_enableArtifactCache_x3f_5257_ = lean_ctor_get(v_config_5226_, 25);
v_restoreAllArtifacts_x3f_5258_ = lean_ctor_get(v_config_5226_, 26);
lean_inc_ref(v_trace_5172_);
v___x_5368_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5368_, 0, v_a_5209_);
lean_ctor_set(v___x_5368_, 1, v_trace_5172_);
lean_ctor_set(v___x_5368_, 2, v_buildTime_5173_);
lean_ctor_set_uint8(v___x_5368_, sizeof(void*)*3, v_action_5170_);
lean_ctor_set_uint8(v___x_5368_, sizeof(void*)*3 + 1, v_wantsRebuild_5171_);
if (lean_obj_tag(v_enableArtifactCache_x3f_5257_) == 0)
{
lean_object* v_toContext_5369_; lean_object* v_lakeEnv_5370_; lean_object* v_enableArtifactCache_x3f_5371_; 
v_toContext_5369_ = lean_ctor_get(v_a_5166_, 1);
v_lakeEnv_5370_ = lean_ctor_get(v_toContext_5369_, 1);
v_enableArtifactCache_x3f_5371_ = lean_ctor_get(v_lakeEnv_5370_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_5371_) == 0)
{
lean_object* v_root_5372_; lean_object* v_config_5373_; lean_object* v_enableArtifactCache_x3f_5374_; 
v_root_5372_ = lean_ctor_get(v_toContext_5369_, 0);
v_config_5373_ = lean_ctor_get(v_root_5372_, 6);
v_enableArtifactCache_x3f_5374_ = lean_ctor_get(v_config_5373_, 25);
if (lean_obj_tag(v_enableArtifactCache_x3f_5374_) == 0)
{
v_a_5283_ = v___x_5368_;
goto v___jp_5282_;
}
else
{
lean_object* v_val_5375_; uint8_t v___x_5376_; 
v_val_5375_ = lean_ctor_get(v_enableArtifactCache_x3f_5374_, 0);
v___x_5376_ = lean_unbox(v_val_5375_);
v_a_5357_ = v___x_5376_;
v_a_5358_ = v___x_5368_;
goto v___jp_5356_;
}
}
else
{
lean_object* v_val_5377_; uint8_t v___x_5378_; 
v_val_5377_ = lean_ctor_get(v_enableArtifactCache_x3f_5371_, 0);
v___x_5378_ = lean_unbox(v_val_5377_);
v_a_5357_ = v___x_5378_;
v_a_5358_ = v___x_5368_;
goto v___jp_5356_;
}
}
else
{
lean_object* v_val_5379_; uint8_t v___x_5380_; 
v_val_5379_ = lean_ctor_get(v_enableArtifactCache_x3f_5257_, 0);
v___x_5380_ = lean_unbox(v_val_5379_);
v_a_5357_ = v___x_5380_;
v_a_5358_ = v___x_5368_;
goto v___jp_5356_;
}
v___jp_5213_:
{
lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; 
lean_dec_ref(v___y_5219_);
v___x_5223_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5223_, 0, v___y_5222_);
v___x_5224_ = l_Lake_CacheMap_insertCore(v_hash_5211_, v___x_5223_, v___y_5217_);
v___x_5225_ = lean_st_ref_set(v___y_5220_, v___x_5224_);
lean_dec(v___y_5220_);
v___y_5197_ = v___y_5218_;
v_log_5198_ = v___y_5215_;
v_action_5199_ = v___y_5214_;
v_wantsRebuild_5200_ = v___y_5216_;
v_buildTime_5201_ = v___y_5221_;
goto v___jp_5196_;
}
v___jp_5228_:
{
if (lean_obj_tag(v_outputsRef_x3f_5227_) == 1)
{
lean_object* v_val_5231_; lean_object* v___x_5232_; lean_object* v_descr_5233_; lean_object* v_log_5234_; uint8_t v_action_5235_; uint8_t v_wantsRebuild_5236_; lean_object* v_trace_5237_; lean_object* v_buildTime_5238_; uint64_t v_hash_5239_; lean_object* v_ext_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; uint8_t v___x_5243_; 
v_val_5231_ = lean_ctor_get(v_outputsRef_x3f_5227_, 0);
lean_inc(v_val_5231_);
lean_dec_ref(v_outputsRef_x3f_5227_);
v___x_5232_ = lean_st_ref_take(v_val_5231_);
v_descr_5233_ = lean_ctor_get(v_a_5229_, 0);
v_log_5234_ = lean_ctor_get(v_a_5230_, 0);
lean_inc_ref(v_log_5234_);
v_action_5235_ = lean_ctor_get_uint8(v_a_5230_, sizeof(void*)*3);
v_wantsRebuild_5236_ = lean_ctor_get_uint8(v_a_5230_, sizeof(void*)*3 + 1);
v_trace_5237_ = lean_ctor_get(v_a_5230_, 1);
lean_inc_ref(v_trace_5237_);
v_buildTime_5238_ = lean_ctor_get(v_a_5230_, 2);
lean_inc(v_buildTime_5238_);
lean_dec_ref(v_a_5230_);
v_hash_5239_ = lean_ctor_get_uint64(v_descr_5233_, sizeof(void*)*1);
v_ext_5240_ = lean_ctor_get(v_descr_5233_, 0);
v___x_5241_ = lean_string_utf8_byte_size(v_ext_5240_);
v___x_5242_ = lean_unsigned_to_nat(0u);
v___x_5243_ = lean_nat_dec_eq(v___x_5241_, v___x_5242_);
if (v___x_5243_ == 0)
{
lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; 
v___x_5244_ = l_Lake_Hash_hex(v_hash_5239_);
v___x_5245_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5246_ = lean_string_append(v___x_5244_, v___x_5245_);
v___x_5247_ = lean_string_append(v___x_5246_, v_ext_5240_);
v___y_5214_ = v_action_5235_;
v___y_5215_ = v_log_5234_;
v___y_5216_ = v_wantsRebuild_5236_;
v___y_5217_ = v___x_5232_;
v___y_5218_ = v_a_5229_;
v___y_5219_ = v_trace_5237_;
v___y_5220_ = v_val_5231_;
v___y_5221_ = v_buildTime_5238_;
v___y_5222_ = v___x_5247_;
goto v___jp_5213_;
}
else
{
lean_object* v___x_5248_; 
v___x_5248_ = l_Lake_Hash_hex(v_hash_5239_);
v___y_5214_ = v_action_5235_;
v___y_5215_ = v_log_5234_;
v___y_5216_ = v_wantsRebuild_5236_;
v___y_5217_ = v___x_5232_;
v___y_5218_ = v_a_5229_;
v___y_5219_ = v_trace_5237_;
v___y_5220_ = v_val_5231_;
v___y_5221_ = v_buildTime_5238_;
v___y_5222_ = v___x_5248_;
goto v___jp_5213_;
}
}
else
{
lean_object* v_log_5249_; uint8_t v_action_5250_; uint8_t v_wantsRebuild_5251_; lean_object* v_buildTime_5252_; 
lean_dec(v_outputsRef_x3f_5227_);
v_log_5249_ = lean_ctor_get(v_a_5230_, 0);
lean_inc_ref(v_log_5249_);
v_action_5250_ = lean_ctor_get_uint8(v_a_5230_, sizeof(void*)*3);
v_wantsRebuild_5251_ = lean_ctor_get_uint8(v_a_5230_, sizeof(void*)*3 + 1);
v_buildTime_5252_ = lean_ctor_get(v_a_5230_, 2);
lean_inc(v_buildTime_5252_);
lean_dec_ref(v_a_5230_);
v___y_5197_ = v_a_5229_;
v_log_5198_ = v_log_5249_;
v_action_5199_ = v_action_5250_;
v_wantsRebuild_5200_ = v_wantsRebuild_5251_;
v_buildTime_5201_ = v_buildTime_5252_;
goto v___jp_5196_;
}
}
v___jp_5253_:
{
if (lean_obj_tag(v___y_5254_) == 0)
{
lean_object* v_a_5255_; lean_object* v_a_5256_; 
v_a_5255_ = lean_ctor_get(v___y_5254_, 0);
lean_inc(v_a_5255_);
v_a_5256_ = lean_ctor_get(v___y_5254_, 1);
lean_inc(v_a_5256_);
lean_dec_ref(v___y_5254_);
v_a_5229_ = v_a_5255_;
v_a_5230_ = v_a_5256_;
goto v___jp_5228_;
}
else
{
lean_dec(v_outputsRef_x3f_5227_);
lean_dec_ref(v___x_5178_);
lean_del_object(v___x_5175_);
return v___y_5254_;
}
}
v___jp_5259_:
{
lean_object* v___x_5262_; 
lean_inc_ref(v_a_5166_);
lean_inc_ref(v___x_5178_);
lean_inc_ref(v_file_5156_);
lean_inc(v_val_5210_);
v___x_5262_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_5161_, v_hash_5211_, v_a_5208_, v_val_5210_, v_file_5156_, v___x_5178_, v___y_5260_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5261_);
if (lean_obj_tag(v___x_5262_) == 0)
{
lean_object* v_a_5263_; 
v_a_5263_ = lean_ctor_get(v___x_5262_, 0);
lean_inc(v_a_5263_);
if (lean_obj_tag(v_a_5263_) == 1)
{
lean_object* v_a_5264_; lean_object* v_val_5265_; 
lean_dec_ref(v_a_5163_);
lean_dec_ref(v_trace_5172_);
lean_dec_ref(v_a_5166_);
lean_dec(v_a_5165_);
lean_dec(v_a_5164_);
lean_dec_ref(v_a_5162_);
lean_dec_ref(v_ext_5159_);
lean_dec_ref(v_build_5157_);
lean_dec_ref(v_file_5156_);
v_a_5264_ = lean_ctor_get(v___x_5262_, 1);
lean_inc(v_a_5264_);
lean_dec_ref(v___x_5262_);
v_val_5265_ = lean_ctor_get(v_a_5263_, 0);
lean_inc(v_val_5265_);
lean_dec_ref(v_a_5263_);
v_a_5229_ = v_val_5265_;
v_a_5230_ = v_a_5264_;
goto v___jp_5228_;
}
else
{
lean_object* v_a_5266_; lean_object* v___x_5267_; 
lean_dec(v_a_5263_);
v_a_5266_ = lean_ctor_get(v___x_5262_, 1);
lean_inc(v_a_5266_);
lean_dec_ref(v___x_5262_);
lean_inc_ref(v___x_5178_);
v___x_5267_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5156_, v_build_5157_, v_text_5158_, v_ext_5159_, v_trace_5172_, v___x_5178_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5266_);
lean_dec_ref(v_trace_5172_);
v___y_5254_ = v___x_5267_;
goto v___jp_5253_;
}
}
else
{
lean_object* v_a_5268_; lean_object* v_a_5269_; lean_object* v___x_5271_; uint8_t v_isShared_5272_; uint8_t v_isSharedCheck_5276_; 
lean_dec(v_outputsRef_x3f_5227_);
lean_dec_ref(v_a_5163_);
lean_dec_ref(v___x_5178_);
lean_del_object(v___x_5175_);
lean_dec_ref(v_trace_5172_);
lean_dec_ref(v_a_5166_);
lean_dec(v_a_5165_);
lean_dec(v_a_5164_);
lean_dec_ref(v_a_5162_);
lean_dec_ref(v_ext_5159_);
lean_dec_ref(v_build_5157_);
lean_dec_ref(v_file_5156_);
v_a_5268_ = lean_ctor_get(v___x_5262_, 0);
v_a_5269_ = lean_ctor_get(v___x_5262_, 1);
v_isSharedCheck_5276_ = !lean_is_exclusive(v___x_5262_);
if (v_isSharedCheck_5276_ == 0)
{
v___x_5271_ = v___x_5262_;
v_isShared_5272_ = v_isSharedCheck_5276_;
goto v_resetjp_5270_;
}
else
{
lean_inc(v_a_5269_);
lean_inc(v_a_5268_);
lean_dec(v___x_5262_);
v___x_5271_ = lean_box(0);
v_isShared_5272_ = v_isSharedCheck_5276_;
goto v_resetjp_5270_;
}
v_resetjp_5270_:
{
lean_object* v___x_5274_; 
if (v_isShared_5272_ == 0)
{
v___x_5274_ = v___x_5271_;
goto v_reusejp_5273_;
}
else
{
lean_object* v_reuseFailAlloc_5275_; 
v_reuseFailAlloc_5275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5275_, 0, v_a_5268_);
lean_ctor_set(v_reuseFailAlloc_5275_, 1, v_a_5269_);
v___x_5274_ = v_reuseFailAlloc_5275_;
goto v_reusejp_5273_;
}
v_reusejp_5273_:
{
return v___x_5274_;
}
}
}
}
v___jp_5277_:
{
if (v_a_5279_ == 0)
{
lean_object* v___x_5281_; 
lean_dec(v_a_5208_);
lean_inc_ref(v___x_5178_);
v___x_5281_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5156_, v_build_5157_, v_text_5158_, v_ext_5159_, v_trace_5172_, v___x_5178_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5280_);
lean_dec_ref(v_trace_5172_);
v___y_5254_ = v___x_5281_;
goto v___jp_5253_;
}
else
{
v___y_5260_ = v___y_5278_;
v_a_5261_ = v_a_5280_;
goto v___jp_5259_;
}
}
v___jp_5282_:
{
lean_object* v___x_5284_; 
lean_inc(v_a_5208_);
v___x_5284_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5162_, v_file_5156_, v_trace_5172_, v_a_5208_, v_mtime_5212_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5283_);
if (lean_obj_tag(v___x_5284_) == 0)
{
lean_object* v_a_5285_; lean_object* v_a_5286_; uint8_t v___x_5287_; uint8_t v___x_5288_; uint8_t v___x_5289_; 
v_a_5285_ = lean_ctor_get(v___x_5284_, 0);
lean_inc(v_a_5285_);
v_a_5286_ = lean_ctor_get(v___x_5284_, 1);
lean_inc(v_a_5286_);
lean_dec_ref(v___x_5284_);
v___x_5287_ = 0;
v___x_5288_ = lean_unbox(v_a_5285_);
lean_dec(v_a_5285_);
v___x_5289_ = l_Lake_instDecidableEqOutputStatus(v___x_5288_, v___x_5287_);
if (v___x_5289_ == 0)
{
lean_object* v___x_5290_; 
lean_dec(v_a_5208_);
lean_dec_ref(v_a_5163_);
lean_dec_ref(v_trace_5172_);
lean_dec(v_a_5165_);
lean_dec(v_a_5164_);
lean_dec_ref(v_a_5162_);
lean_dec_ref(v_build_5157_);
v___x_5290_ = l_Lake_computeArtifact___redArg(v_file_5156_, v_ext_5159_, v_text_5158_, v_a_5166_, v_a_5286_);
lean_dec_ref(v_a_5166_);
v___y_5254_ = v___x_5290_;
goto v___jp_5253_;
}
else
{
if (lean_obj_tag(v_enableArtifactCache_x3f_5257_) == 0)
{
lean_object* v_toContext_5291_; lean_object* v_lakeEnv_5292_; lean_object* v_enableArtifactCache_x3f_5293_; 
v_toContext_5291_ = lean_ctor_get(v_a_5166_, 1);
v_lakeEnv_5292_ = lean_ctor_get(v_toContext_5291_, 1);
v_enableArtifactCache_x3f_5293_ = lean_ctor_get(v_lakeEnv_5292_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_5293_) == 0)
{
lean_object* v_root_5294_; lean_object* v_config_5295_; lean_object* v_enableArtifactCache_x3f_5296_; 
v_root_5294_ = lean_ctor_get(v_toContext_5291_, 0);
v_config_5295_ = lean_ctor_get(v_root_5294_, 6);
v_enableArtifactCache_x3f_5296_ = lean_ctor_get(v_config_5295_, 25);
if (lean_obj_tag(v_enableArtifactCache_x3f_5296_) == 0)
{
v___y_5260_ = v___x_5289_;
v_a_5261_ = v_a_5286_;
goto v___jp_5259_;
}
else
{
lean_object* v_val_5297_; uint8_t v___x_5298_; 
v_val_5297_ = lean_ctor_get(v_enableArtifactCache_x3f_5296_, 0);
v___x_5298_ = lean_unbox(v_val_5297_);
v___y_5278_ = v___x_5289_;
v_a_5279_ = v___x_5298_;
v_a_5280_ = v_a_5286_;
goto v___jp_5277_;
}
}
else
{
lean_object* v_val_5299_; uint8_t v___x_5300_; 
v_val_5299_ = lean_ctor_get(v_enableArtifactCache_x3f_5293_, 0);
v___x_5300_ = lean_unbox(v_val_5299_);
v___y_5278_ = v___x_5289_;
v_a_5279_ = v___x_5300_;
v_a_5280_ = v_a_5286_;
goto v___jp_5277_;
}
}
else
{
lean_object* v_val_5301_; uint8_t v___x_5302_; 
v_val_5301_ = lean_ctor_get(v_enableArtifactCache_x3f_5257_, 0);
v___x_5302_ = lean_unbox(v_val_5301_);
v___y_5278_ = v___x_5289_;
v_a_5279_ = v___x_5302_;
v_a_5280_ = v_a_5286_;
goto v___jp_5277_;
}
}
}
else
{
lean_object* v_a_5303_; lean_object* v_a_5304_; lean_object* v___x_5306_; uint8_t v_isShared_5307_; uint8_t v_isSharedCheck_5311_; 
lean_dec(v_outputsRef_x3f_5227_);
lean_dec(v_a_5208_);
lean_dec_ref(v_a_5163_);
lean_dec_ref(v___x_5178_);
lean_del_object(v___x_5175_);
lean_dec_ref(v_trace_5172_);
lean_dec_ref(v_a_5166_);
lean_dec(v_a_5165_);
lean_dec(v_a_5164_);
lean_dec_ref(v_a_5162_);
lean_dec_ref(v_ext_5159_);
lean_dec_ref(v_build_5157_);
lean_dec_ref(v_file_5156_);
v_a_5303_ = lean_ctor_get(v___x_5284_, 0);
v_a_5304_ = lean_ctor_get(v___x_5284_, 1);
v_isSharedCheck_5311_ = !lean_is_exclusive(v___x_5284_);
if (v_isSharedCheck_5311_ == 0)
{
v___x_5306_ = v___x_5284_;
v_isShared_5307_ = v_isSharedCheck_5311_;
goto v_resetjp_5305_;
}
else
{
lean_inc(v_a_5304_);
lean_inc(v_a_5303_);
lean_dec(v___x_5284_);
v___x_5306_ = lean_box(0);
v_isShared_5307_ = v_isSharedCheck_5311_;
goto v_resetjp_5305_;
}
v_resetjp_5305_:
{
lean_object* v___x_5309_; 
if (v_isShared_5307_ == 0)
{
v___x_5309_ = v___x_5306_;
goto v_reusejp_5308_;
}
else
{
lean_object* v_reuseFailAlloc_5310_; 
v_reuseFailAlloc_5310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5310_, 0, v_a_5303_);
lean_ctor_set(v_reuseFailAlloc_5310_, 1, v_a_5304_);
v___x_5309_ = v_reuseFailAlloc_5310_;
goto v_reusejp_5308_;
}
v_reusejp_5308_:
{
return v___x_5309_;
}
}
}
}
v___jp_5312_:
{
lean_object* v___x_5315_; 
lean_inc_ref(v_a_5166_);
lean_inc_ref(v___x_5178_);
lean_inc_ref(v_file_5156_);
lean_inc(v_val_5210_);
lean_inc(v_a_5208_);
v___x_5315_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_5161_, v_hash_5211_, v_a_5208_, v_val_5210_, v_file_5156_, v___x_5178_, v___y_5314_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v___y_5313_);
if (lean_obj_tag(v___x_5315_) == 0)
{
lean_object* v_a_5316_; 
v_a_5316_ = lean_ctor_get(v___x_5315_, 0);
lean_inc(v_a_5316_);
if (lean_obj_tag(v_a_5316_) == 1)
{
lean_object* v_a_5317_; lean_object* v_val_5318_; 
lean_dec(v_val_5210_);
lean_dec_ref(v_a_5163_);
lean_dec(v_a_5208_);
lean_dec_ref(v_trace_5172_);
lean_dec_ref(v_a_5166_);
lean_dec(v_a_5165_);
lean_dec(v_a_5164_);
lean_dec_ref(v_a_5162_);
lean_dec_ref(v_ext_5159_);
lean_dec_ref(v_build_5157_);
lean_dec_ref(v_file_5156_);
v_a_5317_ = lean_ctor_get(v___x_5315_, 1);
lean_inc(v_a_5317_);
lean_dec_ref(v___x_5315_);
v_val_5318_ = lean_ctor_get(v_a_5316_, 0);
lean_inc(v_val_5318_);
lean_dec_ref(v_a_5316_);
v_a_5229_ = v_val_5318_;
v_a_5230_ = v_a_5317_;
goto v___jp_5228_;
}
else
{
lean_object* v_a_5319_; lean_object* v___x_5320_; 
lean_dec(v_a_5316_);
v_a_5319_ = lean_ctor_get(v___x_5315_, 1);
lean_inc(v_a_5319_);
lean_dec_ref(v___x_5315_);
v___x_5320_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5162_, v_file_5156_, v_trace_5172_, v_a_5208_, v_mtime_5212_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5319_);
if (lean_obj_tag(v___x_5320_) == 0)
{
lean_object* v_a_5321_; lean_object* v_a_5322_; uint8_t v___x_5323_; uint8_t v___x_5324_; uint8_t v___x_5325_; 
v_a_5321_ = lean_ctor_get(v___x_5320_, 0);
lean_inc(v_a_5321_);
v_a_5322_ = lean_ctor_get(v___x_5320_, 1);
lean_inc(v_a_5322_);
lean_dec_ref(v___x_5320_);
v___x_5323_ = 0;
v___x_5324_ = lean_unbox(v_a_5321_);
v___x_5325_ = l_Lake_instDecidableEqOutputStatus(v___x_5324_, v___x_5323_);
if (v___x_5325_ == 0)
{
lean_object* v___x_5326_; uint8_t v___x_5327_; lean_object* v___x_5328_; 
lean_dec_ref(v_trace_5172_);
lean_dec_ref(v_build_5157_);
v___x_5326_ = lean_box(0);
v___x_5327_ = lean_unbox(v_a_5321_);
lean_dec(v_a_5321_);
v___x_5328_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v___x_5327_, v_file_5156_, v_ext_5159_, v_text_5158_, v_exe_5161_, v___y_5314_, v_val_5210_, v_hash_5211_, v___x_5326_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5322_);
lean_dec(v_a_5165_);
lean_dec(v_a_5164_);
lean_dec_ref(v_a_5163_);
lean_dec_ref(v_a_5162_);
v___y_5254_ = v___x_5328_;
goto v___jp_5253_;
}
else
{
lean_object* v___x_5329_; 
lean_inc_ref(v_a_5166_);
lean_inc(v_a_5165_);
lean_inc(v_a_5164_);
lean_inc_ref(v_a_5163_);
lean_inc_ref(v_a_5162_);
lean_inc_ref(v___x_5178_);
lean_inc_ref(v_ext_5159_);
lean_inc_ref(v_file_5156_);
v___x_5329_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5156_, v_build_5157_, v_text_5158_, v_ext_5159_, v_trace_5172_, v___x_5178_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5322_);
lean_dec_ref(v_trace_5172_);
if (lean_obj_tag(v___x_5329_) == 0)
{
lean_object* v_a_5330_; lean_object* v___x_5331_; uint8_t v___x_5332_; lean_object* v___x_5333_; 
v_a_5330_ = lean_ctor_get(v___x_5329_, 1);
lean_inc(v_a_5330_);
lean_dec_ref(v___x_5329_);
v___x_5331_ = lean_box(0);
v___x_5332_ = lean_unbox(v_a_5321_);
lean_dec(v_a_5321_);
v___x_5333_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v___x_5332_, v_file_5156_, v_ext_5159_, v_text_5158_, v_exe_5161_, v___y_5314_, v_val_5210_, v_hash_5211_, v___x_5331_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5330_);
lean_dec(v_a_5165_);
lean_dec(v_a_5164_);
lean_dec_ref(v_a_5163_);
lean_dec_ref(v_a_5162_);
v___y_5254_ = v___x_5333_;
goto v___jp_5253_;
}
else
{
lean_dec(v_a_5321_);
lean_dec(v_outputsRef_x3f_5227_);
lean_dec(v_val_5210_);
lean_dec_ref(v_a_5163_);
lean_dec_ref(v___x_5178_);
lean_del_object(v___x_5175_);
lean_dec_ref(v_a_5166_);
lean_dec(v_a_5165_);
lean_dec(v_a_5164_);
lean_dec_ref(v_a_5162_);
lean_dec_ref(v_ext_5159_);
lean_dec_ref(v_file_5156_);
return v___x_5329_;
}
}
}
else
{
lean_object* v_a_5334_; lean_object* v_a_5335_; lean_object* v___x_5337_; uint8_t v_isShared_5338_; uint8_t v_isSharedCheck_5342_; 
lean_dec(v_outputsRef_x3f_5227_);
lean_dec(v_val_5210_);
lean_dec_ref(v_a_5163_);
lean_dec_ref(v___x_5178_);
lean_del_object(v___x_5175_);
lean_dec_ref(v_trace_5172_);
lean_dec_ref(v_a_5166_);
lean_dec(v_a_5165_);
lean_dec(v_a_5164_);
lean_dec_ref(v_a_5162_);
lean_dec_ref(v_ext_5159_);
lean_dec_ref(v_build_5157_);
lean_dec_ref(v_file_5156_);
v_a_5334_ = lean_ctor_get(v___x_5320_, 0);
v_a_5335_ = lean_ctor_get(v___x_5320_, 1);
v_isSharedCheck_5342_ = !lean_is_exclusive(v___x_5320_);
if (v_isSharedCheck_5342_ == 0)
{
v___x_5337_ = v___x_5320_;
v_isShared_5338_ = v_isSharedCheck_5342_;
goto v_resetjp_5336_;
}
else
{
lean_inc(v_a_5335_);
lean_inc(v_a_5334_);
lean_dec(v___x_5320_);
v___x_5337_ = lean_box(0);
v_isShared_5338_ = v_isSharedCheck_5342_;
goto v_resetjp_5336_;
}
v_resetjp_5336_:
{
lean_object* v___x_5340_; 
if (v_isShared_5338_ == 0)
{
v___x_5340_ = v___x_5337_;
goto v_reusejp_5339_;
}
else
{
lean_object* v_reuseFailAlloc_5341_; 
v_reuseFailAlloc_5341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5341_, 0, v_a_5334_);
lean_ctor_set(v_reuseFailAlloc_5341_, 1, v_a_5335_);
v___x_5340_ = v_reuseFailAlloc_5341_;
goto v_reusejp_5339_;
}
v_reusejp_5339_:
{
return v___x_5340_;
}
}
}
}
}
else
{
lean_object* v_a_5343_; lean_object* v_a_5344_; lean_object* v___x_5346_; uint8_t v_isShared_5347_; uint8_t v_isSharedCheck_5351_; 
lean_dec(v_outputsRef_x3f_5227_);
lean_dec(v_val_5210_);
lean_dec_ref(v_a_5163_);
lean_dec(v_a_5208_);
lean_dec_ref(v___x_5178_);
lean_del_object(v___x_5175_);
lean_dec_ref(v_trace_5172_);
lean_dec_ref(v_a_5166_);
lean_dec(v_a_5165_);
lean_dec(v_a_5164_);
lean_dec_ref(v_a_5162_);
lean_dec_ref(v_ext_5159_);
lean_dec_ref(v_build_5157_);
lean_dec_ref(v_file_5156_);
v_a_5343_ = lean_ctor_get(v___x_5315_, 0);
v_a_5344_ = lean_ctor_get(v___x_5315_, 1);
v_isSharedCheck_5351_ = !lean_is_exclusive(v___x_5315_);
if (v_isSharedCheck_5351_ == 0)
{
v___x_5346_ = v___x_5315_;
v_isShared_5347_ = v_isSharedCheck_5351_;
goto v_resetjp_5345_;
}
else
{
lean_inc(v_a_5344_);
lean_inc(v_a_5343_);
lean_dec(v___x_5315_);
v___x_5346_ = lean_box(0);
v_isShared_5347_ = v_isSharedCheck_5351_;
goto v_resetjp_5345_;
}
v_resetjp_5345_:
{
lean_object* v___x_5349_; 
if (v_isShared_5347_ == 0)
{
v___x_5349_ = v___x_5346_;
goto v_reusejp_5348_;
}
else
{
lean_object* v_reuseFailAlloc_5350_; 
v_reuseFailAlloc_5350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5350_, 0, v_a_5343_);
lean_ctor_set(v_reuseFailAlloc_5350_, 1, v_a_5344_);
v___x_5349_ = v_reuseFailAlloc_5350_;
goto v_reusejp_5348_;
}
v_reusejp_5348_:
{
return v___x_5349_;
}
}
}
}
v___jp_5352_:
{
if (v_restore_5160_ == 0)
{
v___y_5313_ = v_a_5355_;
v___y_5314_ = v_a_5354_;
goto v___jp_5312_;
}
else
{
v___y_5313_ = v_a_5355_;
v___y_5314_ = v___y_5353_;
goto v___jp_5312_;
}
}
v___jp_5356_:
{
if (v_a_5357_ == 0)
{
v_a_5283_ = v_a_5358_;
goto v___jp_5282_;
}
else
{
lean_inc(v_val_5210_);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5258_) == 0)
{
lean_object* v_toContext_5359_; lean_object* v_root_5360_; lean_object* v_config_5361_; lean_object* v_restoreAllArtifacts_x3f_5362_; 
v_toContext_5359_ = lean_ctor_get(v_a_5166_, 1);
v_root_5360_ = lean_ctor_get(v_toContext_5359_, 0);
v_config_5361_ = lean_ctor_get(v_root_5360_, 6);
v_restoreAllArtifacts_x3f_5362_ = lean_ctor_get(v_config_5361_, 26);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5362_) == 0)
{
uint8_t v___x_5363_; 
v___x_5363_ = 0;
v___y_5353_ = v_a_5357_;
v_a_5354_ = v___x_5363_;
v_a_5355_ = v_a_5358_;
goto v___jp_5352_;
}
else
{
lean_object* v_val_5364_; uint8_t v___x_5365_; 
v_val_5364_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5362_, 0);
v___x_5365_ = lean_unbox(v_val_5364_);
v___y_5353_ = v_a_5357_;
v_a_5354_ = v___x_5365_;
v_a_5355_ = v_a_5358_;
goto v___jp_5352_;
}
}
else
{
lean_object* v_val_5366_; uint8_t v___x_5367_; 
v_val_5366_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5258_, 0);
v___x_5367_ = lean_unbox(v_val_5366_);
v___y_5353_ = v_a_5357_;
v_a_5354_ = v___x_5367_;
v_a_5355_ = v_a_5358_;
goto v___jp_5352_;
}
}
}
}
else
{
lean_object* v_a_5381_; lean_object* v_a_5382_; lean_object* v_mtime_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; 
lean_del_object(v___x_5175_);
v_a_5381_ = lean_ctor_get(v___x_5207_, 0);
lean_inc(v_a_5381_);
v_a_5382_ = lean_ctor_get(v___x_5207_, 1);
lean_inc(v_a_5382_);
lean_dec_ref(v___x_5207_);
v_mtime_5383_ = lean_ctor_get(v_trace_5172_, 2);
lean_inc_ref(v_trace_5172_);
v___x_5384_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5384_, 0, v_a_5382_);
lean_ctor_set(v___x_5384_, 1, v_trace_5172_);
lean_ctor_set(v___x_5384_, 2, v_buildTime_5173_);
lean_ctor_set_uint8(v___x_5384_, sizeof(void*)*3, v_action_5170_);
lean_ctor_set_uint8(v___x_5384_, sizeof(void*)*3 + 1, v_wantsRebuild_5171_);
v___x_5385_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5162_, v_file_5156_, v_trace_5172_, v_a_5381_, v_mtime_5383_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v___x_5384_);
if (lean_obj_tag(v___x_5385_) == 0)
{
lean_object* v_a_5386_; lean_object* v_a_5387_; uint8_t v___x_5388_; uint8_t v___x_5389_; uint8_t v___x_5390_; 
v_a_5386_ = lean_ctor_get(v___x_5385_, 0);
lean_inc(v_a_5386_);
v_a_5387_ = lean_ctor_get(v___x_5385_, 1);
lean_inc(v_a_5387_);
lean_dec_ref(v___x_5385_);
v___x_5388_ = 0;
v___x_5389_ = lean_unbox(v_a_5386_);
lean_dec(v_a_5386_);
v___x_5390_ = l_Lake_instDecidableEqOutputStatus(v___x_5389_, v___x_5388_);
if (v___x_5390_ == 0)
{
lean_object* v___x_5391_; 
lean_dec_ref(v_trace_5172_);
lean_dec(v_a_5165_);
lean_dec(v_a_5164_);
lean_dec(v_a_5163_);
lean_dec_ref(v_a_5162_);
lean_dec_ref(v_build_5157_);
v___x_5391_ = l_Lake_computeArtifact___redArg(v_file_5156_, v_ext_5159_, v_text_5158_, v_a_5166_, v_a_5387_);
lean_dec_ref(v_a_5166_);
if (lean_obj_tag(v___x_5391_) == 0)
{
lean_object* v_a_5392_; lean_object* v_a_5393_; 
v_a_5392_ = lean_ctor_get(v___x_5391_, 0);
lean_inc(v_a_5392_);
v_a_5393_ = lean_ctor_get(v___x_5391_, 1);
lean_inc(v_a_5393_);
lean_dec_ref(v___x_5391_);
v_art_5180_ = v_a_5392_;
v___y_5181_ = v_a_5393_;
goto v___jp_5179_;
}
else
{
lean_dec_ref(v___x_5178_);
return v___x_5391_;
}
}
else
{
lean_object* v___x_5394_; 
lean_inc_ref(v___x_5178_);
v___x_5394_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5156_, v_build_5157_, v_text_5158_, v_ext_5159_, v_trace_5172_, v___x_5178_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5387_);
lean_dec_ref(v_trace_5172_);
if (lean_obj_tag(v___x_5394_) == 0)
{
lean_object* v_a_5395_; lean_object* v_a_5396_; 
v_a_5395_ = lean_ctor_get(v___x_5394_, 0);
lean_inc(v_a_5395_);
v_a_5396_ = lean_ctor_get(v___x_5394_, 1);
lean_inc(v_a_5396_);
lean_dec_ref(v___x_5394_);
v_art_5180_ = v_a_5395_;
v___y_5181_ = v_a_5396_;
goto v___jp_5179_;
}
else
{
lean_dec_ref(v___x_5178_);
return v___x_5394_;
}
}
}
else
{
lean_object* v_a_5397_; lean_object* v_a_5398_; lean_object* v___x_5400_; uint8_t v_isShared_5401_; uint8_t v_isSharedCheck_5405_; 
lean_dec_ref(v___x_5178_);
lean_dec_ref(v_trace_5172_);
lean_dec_ref(v_a_5166_);
lean_dec(v_a_5165_);
lean_dec(v_a_5164_);
lean_dec(v_a_5163_);
lean_dec_ref(v_a_5162_);
lean_dec_ref(v_ext_5159_);
lean_dec_ref(v_build_5157_);
lean_dec_ref(v_file_5156_);
v_a_5397_ = lean_ctor_get(v___x_5385_, 0);
v_a_5398_ = lean_ctor_get(v___x_5385_, 1);
v_isSharedCheck_5405_ = !lean_is_exclusive(v___x_5385_);
if (v_isSharedCheck_5405_ == 0)
{
v___x_5400_ = v___x_5385_;
v_isShared_5401_ = v_isSharedCheck_5405_;
goto v_resetjp_5399_;
}
else
{
lean_inc(v_a_5398_);
lean_inc(v_a_5397_);
lean_dec(v___x_5385_);
v___x_5400_ = lean_box(0);
v_isShared_5401_ = v_isSharedCheck_5405_;
goto v_resetjp_5399_;
}
v_resetjp_5399_:
{
lean_object* v___x_5403_; 
if (v_isShared_5401_ == 0)
{
v___x_5403_ = v___x_5400_;
goto v_reusejp_5402_;
}
else
{
lean_object* v_reuseFailAlloc_5404_; 
v_reuseFailAlloc_5404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5404_, 0, v_a_5397_);
lean_ctor_set(v_reuseFailAlloc_5404_, 1, v_a_5398_);
v___x_5403_ = v_reuseFailAlloc_5404_;
goto v_reusejp_5402_;
}
v_reusejp_5402_:
{
return v___x_5403_;
}
}
}
}
}
else
{
lean_object* v_a_5406_; lean_object* v_a_5407_; lean_object* v___x_5409_; uint8_t v_isShared_5410_; uint8_t v_isSharedCheck_5415_; 
lean_dec_ref(v___x_5178_);
lean_del_object(v___x_5175_);
lean_dec_ref(v_a_5166_);
lean_dec(v_a_5165_);
lean_dec(v_a_5164_);
lean_dec(v_a_5163_);
lean_dec_ref(v_a_5162_);
lean_dec_ref(v_ext_5159_);
lean_dec_ref(v_build_5157_);
lean_dec_ref(v_file_5156_);
v_a_5406_ = lean_ctor_get(v___x_5207_, 0);
v_a_5407_ = lean_ctor_get(v___x_5207_, 1);
v_isSharedCheck_5415_ = !lean_is_exclusive(v___x_5207_);
if (v_isSharedCheck_5415_ == 0)
{
v___x_5409_ = v___x_5207_;
v_isShared_5410_ = v_isSharedCheck_5415_;
goto v_resetjp_5408_;
}
else
{
lean_inc(v_a_5407_);
lean_inc(v_a_5406_);
lean_dec(v___x_5207_);
v___x_5409_ = lean_box(0);
v_isShared_5410_ = v_isSharedCheck_5415_;
goto v_resetjp_5408_;
}
v_resetjp_5408_:
{
lean_object* v___x_5411_; lean_object* v___x_5413_; 
v___x_5411_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5411_, 0, v_a_5407_);
lean_ctor_set(v___x_5411_, 1, v_trace_5172_);
lean_ctor_set(v___x_5411_, 2, v_buildTime_5173_);
lean_ctor_set_uint8(v___x_5411_, sizeof(void*)*3, v_action_5170_);
lean_ctor_set_uint8(v___x_5411_, sizeof(void*)*3 + 1, v_wantsRebuild_5171_);
if (v_isShared_5410_ == 0)
{
lean_ctor_set(v___x_5409_, 1, v___x_5411_);
v___x_5413_ = v___x_5409_;
goto v_reusejp_5412_;
}
else
{
lean_object* v_reuseFailAlloc_5414_; 
v_reuseFailAlloc_5414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5414_, 0, v_a_5406_);
lean_ctor_set(v_reuseFailAlloc_5414_, 1, v___x_5411_);
v___x_5413_ = v_reuseFailAlloc_5414_;
goto v_reusejp_5412_;
}
v_reusejp_5412_:
{
return v___x_5413_;
}
}
}
v___jp_5179_:
{
lean_object* v_log_5182_; uint8_t v_action_5183_; uint8_t v_wantsRebuild_5184_; lean_object* v_buildTime_5185_; lean_object* v___x_5187_; uint8_t v_isShared_5188_; uint8_t v_isSharedCheck_5194_; 
v_log_5182_ = lean_ctor_get(v___y_5181_, 0);
v_action_5183_ = lean_ctor_get_uint8(v___y_5181_, sizeof(void*)*3);
v_wantsRebuild_5184_ = lean_ctor_get_uint8(v___y_5181_, sizeof(void*)*3 + 1);
v_buildTime_5185_ = lean_ctor_get(v___y_5181_, 2);
v_isSharedCheck_5194_ = !lean_is_exclusive(v___y_5181_);
if (v_isSharedCheck_5194_ == 0)
{
lean_object* v_unused_5195_; 
v_unused_5195_ = lean_ctor_get(v___y_5181_, 1);
lean_dec(v_unused_5195_);
v___x_5187_ = v___y_5181_;
v_isShared_5188_ = v_isSharedCheck_5194_;
goto v_resetjp_5186_;
}
else
{
lean_inc(v_buildTime_5185_);
lean_inc(v_log_5182_);
lean_dec(v___y_5181_);
v___x_5187_ = lean_box(0);
v_isShared_5188_ = v_isSharedCheck_5194_;
goto v_resetjp_5186_;
}
v_resetjp_5186_:
{
lean_object* v___x_5189_; lean_object* v___x_5191_; 
v___x_5189_ = l_Lake_Artifact_trace(v_art_5180_);
if (v_isShared_5188_ == 0)
{
lean_ctor_set(v___x_5187_, 1, v___x_5189_);
v___x_5191_ = v___x_5187_;
goto v_reusejp_5190_;
}
else
{
lean_object* v_reuseFailAlloc_5193_; 
v_reuseFailAlloc_5193_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5193_, 0, v_log_5182_);
lean_ctor_set(v_reuseFailAlloc_5193_, 1, v___x_5189_);
lean_ctor_set(v_reuseFailAlloc_5193_, 2, v_buildTime_5185_);
lean_ctor_set_uint8(v_reuseFailAlloc_5193_, sizeof(void*)*3, v_action_5183_);
lean_ctor_set_uint8(v_reuseFailAlloc_5193_, sizeof(void*)*3 + 1, v_wantsRebuild_5184_);
v___x_5191_ = v_reuseFailAlloc_5193_;
goto v_reusejp_5190_;
}
v_reusejp_5190_:
{
lean_object* v___x_5192_; 
v___x_5192_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_5180_, v___x_5178_, v___x_5191_);
lean_dec_ref(v___x_5178_);
return v___x_5192_;
}
}
}
v___jp_5196_:
{
lean_object* v___x_5202_; lean_object* v___x_5204_; 
v___x_5202_ = l_Lake_Artifact_trace(v___y_5197_);
if (v_isShared_5176_ == 0)
{
lean_ctor_set(v___x_5175_, 2, v_buildTime_5201_);
lean_ctor_set(v___x_5175_, 1, v___x_5202_);
lean_ctor_set(v___x_5175_, 0, v_log_5198_);
v___x_5204_ = v___x_5175_;
goto v_reusejp_5203_;
}
else
{
lean_object* v_reuseFailAlloc_5206_; 
v_reuseFailAlloc_5206_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5206_, 0, v_log_5198_);
lean_ctor_set(v_reuseFailAlloc_5206_, 1, v___x_5202_);
lean_ctor_set(v_reuseFailAlloc_5206_, 2, v_buildTime_5201_);
v___x_5204_ = v_reuseFailAlloc_5206_;
goto v_reusejp_5203_;
}
v_reusejp_5203_:
{
lean_object* v___x_5205_; 
lean_ctor_set_uint8(v___x_5204_, sizeof(void*)*3, v_action_5199_);
lean_ctor_set_uint8(v___x_5204_, sizeof(void*)*3 + 1, v_wantsRebuild_5200_);
v___x_5205_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v___y_5197_, v___x_5178_, v___x_5204_);
lean_dec_ref(v___x_5178_);
return v___x_5205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___boxed(lean_object* v_file_5417_, lean_object* v_build_5418_, lean_object* v_text_5419_, lean_object* v_ext_5420_, lean_object* v_restore_5421_, lean_object* v_exe_5422_, lean_object* v_a_5423_, lean_object* v_a_5424_, lean_object* v_a_5425_, lean_object* v_a_5426_, lean_object* v_a_5427_, lean_object* v_a_5428_, lean_object* v_a_5429_){
_start:
{
uint8_t v_text_boxed_5430_; uint8_t v_restore_boxed_5431_; uint8_t v_exe_boxed_5432_; lean_object* v_res_5433_; 
v_text_boxed_5430_ = lean_unbox(v_text_5419_);
v_restore_boxed_5431_ = lean_unbox(v_restore_5421_);
v_exe_boxed_5432_ = lean_unbox(v_exe_5422_);
v_res_5433_ = l_Lake_buildArtifactUnlessUpToDate(v_file_5417_, v_build_5418_, v_text_boxed_5430_, v_ext_5420_, v_restore_boxed_5431_, v_exe_boxed_5432_, v_a_5423_, v_a_5424_, v_a_5425_, v_a_5426_, v_a_5427_, v_a_5428_);
return v_res_5433_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0(lean_object* v_extraDepTrace_5435_, lean_object* v_build_5436_, lean_object* v_file_5437_, uint8_t v_text_5438_, lean_object* v_depInfo_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_){
_start:
{
lean_object* v___x_5447_; 
lean_inc_ref(v___y_5444_);
lean_inc(v___y_5443_);
lean_inc(v___y_5442_);
lean_inc(v___y_5441_);
lean_inc_ref(v___y_5440_);
v___x_5447_ = lean_apply_7(v_extraDepTrace_5435_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_, v___y_5444_, v___y_5445_, lean_box(0));
if (lean_obj_tag(v___x_5447_) == 0)
{
lean_object* v_a_5448_; lean_object* v_a_5449_; lean_object* v_log_5450_; uint8_t v_action_5451_; uint8_t v_wantsRebuild_5452_; lean_object* v_trace_5453_; lean_object* v_buildTime_5454_; lean_object* v___x_5456_; uint8_t v_isShared_5457_; uint8_t v_isSharedCheck_5485_; 
v_a_5448_ = lean_ctor_get(v___x_5447_, 1);
lean_inc(v_a_5448_);
v_a_5449_ = lean_ctor_get(v___x_5447_, 0);
lean_inc(v_a_5449_);
lean_dec_ref(v___x_5447_);
v_log_5450_ = lean_ctor_get(v_a_5448_, 0);
v_action_5451_ = lean_ctor_get_uint8(v_a_5448_, sizeof(void*)*3);
v_wantsRebuild_5452_ = lean_ctor_get_uint8(v_a_5448_, sizeof(void*)*3 + 1);
v_trace_5453_ = lean_ctor_get(v_a_5448_, 1);
v_buildTime_5454_ = lean_ctor_get(v_a_5448_, 2);
v_isSharedCheck_5485_ = !lean_is_exclusive(v_a_5448_);
if (v_isSharedCheck_5485_ == 0)
{
v___x_5456_ = v_a_5448_;
v_isShared_5457_ = v_isSharedCheck_5485_;
goto v_resetjp_5455_;
}
else
{
lean_inc(v_buildTime_5454_);
lean_inc(v_trace_5453_);
lean_inc(v_log_5450_);
lean_dec(v_a_5448_);
v___x_5456_ = lean_box(0);
v_isShared_5457_ = v_isSharedCheck_5485_;
goto v_resetjp_5455_;
}
v_resetjp_5455_:
{
lean_object* v___x_5458_; lean_object* v___x_5460_; 
v___x_5458_ = l_Lake_BuildTrace_mix(v_trace_5453_, v_a_5449_);
if (v_isShared_5457_ == 0)
{
lean_ctor_set(v___x_5456_, 1, v___x_5458_);
v___x_5460_ = v___x_5456_;
goto v_reusejp_5459_;
}
else
{
lean_object* v_reuseFailAlloc_5484_; 
v_reuseFailAlloc_5484_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5484_, 0, v_log_5450_);
lean_ctor_set(v_reuseFailAlloc_5484_, 1, v___x_5458_);
lean_ctor_set(v_reuseFailAlloc_5484_, 2, v_buildTime_5454_);
lean_ctor_set_uint8(v_reuseFailAlloc_5484_, sizeof(void*)*3, v_action_5451_);
lean_ctor_set_uint8(v_reuseFailAlloc_5484_, sizeof(void*)*3 + 1, v_wantsRebuild_5452_);
v___x_5460_ = v_reuseFailAlloc_5484_;
goto v_reusejp_5459_;
}
v_reusejp_5459_:
{
lean_object* v___x_5461_; lean_object* v___x_5462_; uint8_t v___x_5463_; lean_object* v___x_5464_; 
v___x_5461_ = lean_apply_1(v_build_5436_, v_depInfo_5439_);
v___x_5462_ = ((lean_object*)(l_Lake_buildFileAfterDep___redArg___lam__0___closed__0));
v___x_5463_ = 0;
v___x_5464_ = l_Lake_buildArtifactUnlessUpToDate(v_file_5437_, v___x_5461_, v_text_5438_, v___x_5462_, v___x_5463_, v___x_5463_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_, v___y_5444_, v___x_5460_);
if (lean_obj_tag(v___x_5464_) == 0)
{
lean_object* v_a_5465_; lean_object* v_a_5466_; lean_object* v___x_5468_; uint8_t v_isShared_5469_; uint8_t v_isSharedCheck_5474_; 
v_a_5465_ = lean_ctor_get(v___x_5464_, 0);
v_a_5466_ = lean_ctor_get(v___x_5464_, 1);
v_isSharedCheck_5474_ = !lean_is_exclusive(v___x_5464_);
if (v_isSharedCheck_5474_ == 0)
{
v___x_5468_ = v___x_5464_;
v_isShared_5469_ = v_isSharedCheck_5474_;
goto v_resetjp_5467_;
}
else
{
lean_inc(v_a_5466_);
lean_inc(v_a_5465_);
lean_dec(v___x_5464_);
v___x_5468_ = lean_box(0);
v_isShared_5469_ = v_isSharedCheck_5474_;
goto v_resetjp_5467_;
}
v_resetjp_5467_:
{
lean_object* v_path_5470_; lean_object* v___x_5472_; 
v_path_5470_ = lean_ctor_get(v_a_5465_, 1);
lean_inc_ref(v_path_5470_);
lean_dec(v_a_5465_);
if (v_isShared_5469_ == 0)
{
lean_ctor_set(v___x_5468_, 0, v_path_5470_);
v___x_5472_ = v___x_5468_;
goto v_reusejp_5471_;
}
else
{
lean_object* v_reuseFailAlloc_5473_; 
v_reuseFailAlloc_5473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5473_, 0, v_path_5470_);
lean_ctor_set(v_reuseFailAlloc_5473_, 1, v_a_5466_);
v___x_5472_ = v_reuseFailAlloc_5473_;
goto v_reusejp_5471_;
}
v_reusejp_5471_:
{
return v___x_5472_;
}
}
}
else
{
lean_object* v_a_5475_; lean_object* v_a_5476_; lean_object* v___x_5478_; uint8_t v_isShared_5479_; uint8_t v_isSharedCheck_5483_; 
v_a_5475_ = lean_ctor_get(v___x_5464_, 0);
v_a_5476_ = lean_ctor_get(v___x_5464_, 1);
v_isSharedCheck_5483_ = !lean_is_exclusive(v___x_5464_);
if (v_isSharedCheck_5483_ == 0)
{
v___x_5478_ = v___x_5464_;
v_isShared_5479_ = v_isSharedCheck_5483_;
goto v_resetjp_5477_;
}
else
{
lean_inc(v_a_5476_);
lean_inc(v_a_5475_);
lean_dec(v___x_5464_);
v___x_5478_ = lean_box(0);
v_isShared_5479_ = v_isSharedCheck_5483_;
goto v_resetjp_5477_;
}
v_resetjp_5477_:
{
lean_object* v___x_5481_; 
if (v_isShared_5479_ == 0)
{
v___x_5481_ = v___x_5478_;
goto v_reusejp_5480_;
}
else
{
lean_object* v_reuseFailAlloc_5482_; 
v_reuseFailAlloc_5482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5482_, 0, v_a_5475_);
lean_ctor_set(v_reuseFailAlloc_5482_, 1, v_a_5476_);
v___x_5481_ = v_reuseFailAlloc_5482_;
goto v_reusejp_5480_;
}
v_reusejp_5480_:
{
return v___x_5481_;
}
}
}
}
}
}
else
{
lean_object* v_a_5486_; lean_object* v_a_5487_; lean_object* v___x_5489_; uint8_t v_isShared_5490_; uint8_t v_isSharedCheck_5494_; 
lean_dec_ref(v___y_5444_);
lean_dec(v___y_5443_);
lean_dec(v___y_5442_);
lean_dec(v___y_5441_);
lean_dec_ref(v___y_5440_);
lean_dec(v_depInfo_5439_);
lean_dec_ref(v_file_5437_);
lean_dec_ref(v_build_5436_);
v_a_5486_ = lean_ctor_get(v___x_5447_, 0);
v_a_5487_ = lean_ctor_get(v___x_5447_, 1);
v_isSharedCheck_5494_ = !lean_is_exclusive(v___x_5447_);
if (v_isSharedCheck_5494_ == 0)
{
v___x_5489_ = v___x_5447_;
v_isShared_5490_ = v_isSharedCheck_5494_;
goto v_resetjp_5488_;
}
else
{
lean_inc(v_a_5487_);
lean_inc(v_a_5486_);
lean_dec(v___x_5447_);
v___x_5489_ = lean_box(0);
v_isShared_5490_ = v_isSharedCheck_5494_;
goto v_resetjp_5488_;
}
v_resetjp_5488_:
{
lean_object* v___x_5492_; 
if (v_isShared_5490_ == 0)
{
v___x_5492_ = v___x_5489_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v_a_5486_);
lean_ctor_set(v_reuseFailAlloc_5493_, 1, v_a_5487_);
v___x_5492_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
return v___x_5492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___boxed(lean_object* v_extraDepTrace_5495_, lean_object* v_build_5496_, lean_object* v_file_5497_, lean_object* v_text_5498_, lean_object* v_depInfo_5499_, lean_object* v___y_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_, lean_object* v___y_5503_, lean_object* v___y_5504_, lean_object* v___y_5505_, lean_object* v___y_5506_){
_start:
{
uint8_t v_text_boxed_5507_; lean_object* v_res_5508_; 
v_text_boxed_5507_ = lean_unbox(v_text_5498_);
v_res_5508_ = l_Lake_buildFileAfterDep___redArg___lam__0(v_extraDepTrace_5495_, v_build_5496_, v_file_5497_, v_text_boxed_5507_, v_depInfo_5499_, v___y_5500_, v___y_5501_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_);
return v_res_5508_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg(lean_object* v_file_5509_, lean_object* v_dep_5510_, lean_object* v_build_5511_, lean_object* v_extraDepTrace_5512_, uint8_t v_text_5513_, lean_object* v_a_5514_, lean_object* v_a_5515_, lean_object* v_a_5516_, lean_object* v_a_5517_, lean_object* v_a_5518_, lean_object* v_a_5519_){
_start:
{
lean_object* v___x_5521_; lean_object* v___f_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; uint8_t v___x_5525_; lean_object* v___x_5526_; 
v___x_5521_ = lean_box(v_text_5513_);
v___f_5522_ = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_5522_, 0, v_extraDepTrace_5512_);
lean_closure_set(v___f_5522_, 1, v_build_5511_);
lean_closure_set(v___f_5522_, 2, v_file_5509_);
lean_closure_set(v___f_5522_, 3, v___x_5521_);
v___x_5523_ = l_Lake_instDataKindFilePath;
v___x_5524_ = lean_unsigned_to_nat(0u);
v___x_5525_ = 0;
v___x_5526_ = l_Lake_Job_mapM___redArg(v___x_5523_, v_dep_5510_, v___f_5522_, v___x_5524_, v___x_5525_, v_a_5514_, v_a_5515_, v_a_5516_, v_a_5517_, v_a_5518_, v_a_5519_);
return v___x_5526_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___boxed(lean_object* v_file_5527_, lean_object* v_dep_5528_, lean_object* v_build_5529_, lean_object* v_extraDepTrace_5530_, lean_object* v_text_5531_, lean_object* v_a_5532_, lean_object* v_a_5533_, lean_object* v_a_5534_, lean_object* v_a_5535_, lean_object* v_a_5536_, lean_object* v_a_5537_, lean_object* v_a_5538_){
_start:
{
uint8_t v_text_boxed_5539_; lean_object* v_res_5540_; 
v_text_boxed_5539_ = lean_unbox(v_text_5531_);
v_res_5540_ = l_Lake_buildFileAfterDep___redArg(v_file_5527_, v_dep_5528_, v_build_5529_, v_extraDepTrace_5530_, v_text_boxed_5539_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_, v_a_5536_, v_a_5537_);
return v_res_5540_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object* v_00_u03b1_5541_, lean_object* v_file_5542_, lean_object* v_dep_5543_, lean_object* v_build_5544_, lean_object* v_extraDepTrace_5545_, uint8_t v_text_5546_, lean_object* v_a_5547_, lean_object* v_a_5548_, lean_object* v_a_5549_, lean_object* v_a_5550_, lean_object* v_a_5551_, lean_object* v_a_5552_){
_start:
{
lean_object* v___x_5554_; lean_object* v___f_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; uint8_t v___x_5558_; lean_object* v___x_5559_; 
v___x_5554_ = lean_box(v_text_5546_);
v___f_5555_ = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_5555_, 0, v_extraDepTrace_5545_);
lean_closure_set(v___f_5555_, 1, v_build_5544_);
lean_closure_set(v___f_5555_, 2, v_file_5542_);
lean_closure_set(v___f_5555_, 3, v___x_5554_);
v___x_5556_ = l_Lake_instDataKindFilePath;
v___x_5557_ = lean_unsigned_to_nat(0u);
v___x_5558_ = 0;
v___x_5559_ = l_Lake_Job_mapM___redArg(v___x_5556_, v_dep_5543_, v___f_5555_, v___x_5557_, v___x_5558_, v_a_5547_, v_a_5548_, v_a_5549_, v_a_5550_, v_a_5551_, v_a_5552_);
return v___x_5559_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___boxed(lean_object* v_00_u03b1_5560_, lean_object* v_file_5561_, lean_object* v_dep_5562_, lean_object* v_build_5563_, lean_object* v_extraDepTrace_5564_, lean_object* v_text_5565_, lean_object* v_a_5566_, lean_object* v_a_5567_, lean_object* v_a_5568_, lean_object* v_a_5569_, lean_object* v_a_5570_, lean_object* v_a_5571_, lean_object* v_a_5572_){
_start:
{
uint8_t v_text_boxed_5573_; lean_object* v_res_5574_; 
v_text_boxed_5573_ = lean_unbox(v_text_5565_);
v_res_5574_ = l_Lake_buildFileAfterDep(v_00_u03b1_5560_, v_file_5561_, v_dep_5562_, v_build_5563_, v_extraDepTrace_5564_, v_text_boxed_5573_, v_a_5566_, v_a_5567_, v_a_5568_, v_a_5569_, v_a_5570_, v_a_5571_);
return v_res_5574_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(lean_object* v_info_5575_){
_start:
{
lean_object* v___x_5577_; 
v___x_5577_ = l_Lake_computeBinFileHash(v_info_5575_);
if (lean_obj_tag(v___x_5577_) == 0)
{
lean_object* v_a_5578_; lean_object* v___x_5579_; 
v_a_5578_ = lean_ctor_get(v___x_5577_, 0);
lean_inc(v_a_5578_);
lean_dec_ref(v___x_5577_);
v___x_5579_ = lean_io_metadata(v_info_5575_);
if (lean_obj_tag(v___x_5579_) == 0)
{
lean_object* v_a_5580_; lean_object* v___x_5582_; uint8_t v_isShared_5583_; uint8_t v_isSharedCheck_5591_; 
v_a_5580_ = lean_ctor_get(v___x_5579_, 0);
v_isSharedCheck_5591_ = !lean_is_exclusive(v___x_5579_);
if (v_isSharedCheck_5591_ == 0)
{
v___x_5582_ = v___x_5579_;
v_isShared_5583_ = v_isSharedCheck_5591_;
goto v_resetjp_5581_;
}
else
{
lean_inc(v_a_5580_);
lean_dec(v___x_5579_);
v___x_5582_ = lean_box(0);
v_isShared_5583_ = v_isSharedCheck_5591_;
goto v_resetjp_5581_;
}
v_resetjp_5581_:
{
lean_object* v_modified_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; uint64_t v___x_5587_; lean_object* v___x_5589_; 
v_modified_5584_ = lean_ctor_get(v_a_5580_, 1);
lean_inc_ref(v_modified_5584_);
lean_dec(v_a_5580_);
v___x_5585_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_5586_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_5586_, 0, v_info_5575_);
lean_ctor_set(v___x_5586_, 1, v___x_5585_);
lean_ctor_set(v___x_5586_, 2, v_modified_5584_);
v___x_5587_ = lean_unbox_uint64(v_a_5578_);
lean_dec(v_a_5578_);
lean_ctor_set_uint64(v___x_5586_, sizeof(void*)*3, v___x_5587_);
if (v_isShared_5583_ == 0)
{
lean_ctor_set(v___x_5582_, 0, v___x_5586_);
v___x_5589_ = v___x_5582_;
goto v_reusejp_5588_;
}
else
{
lean_object* v_reuseFailAlloc_5590_; 
v_reuseFailAlloc_5590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5590_, 0, v___x_5586_);
v___x_5589_ = v_reuseFailAlloc_5590_;
goto v_reusejp_5588_;
}
v_reusejp_5588_:
{
return v___x_5589_;
}
}
}
else
{
lean_object* v_a_5592_; lean_object* v___x_5594_; uint8_t v_isShared_5595_; uint8_t v_isSharedCheck_5599_; 
lean_dec(v_a_5578_);
lean_dec_ref(v_info_5575_);
v_a_5592_ = lean_ctor_get(v___x_5579_, 0);
v_isSharedCheck_5599_ = !lean_is_exclusive(v___x_5579_);
if (v_isSharedCheck_5599_ == 0)
{
v___x_5594_ = v___x_5579_;
v_isShared_5595_ = v_isSharedCheck_5599_;
goto v_resetjp_5593_;
}
else
{
lean_inc(v_a_5592_);
lean_dec(v___x_5579_);
v___x_5594_ = lean_box(0);
v_isShared_5595_ = v_isSharedCheck_5599_;
goto v_resetjp_5593_;
}
v_resetjp_5593_:
{
lean_object* v___x_5597_; 
if (v_isShared_5595_ == 0)
{
v___x_5597_ = v___x_5594_;
goto v_reusejp_5596_;
}
else
{
lean_object* v_reuseFailAlloc_5598_; 
v_reuseFailAlloc_5598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5598_, 0, v_a_5592_);
v___x_5597_ = v_reuseFailAlloc_5598_;
goto v_reusejp_5596_;
}
v_reusejp_5596_:
{
return v___x_5597_;
}
}
}
}
else
{
lean_object* v_a_5600_; lean_object* v___x_5602_; uint8_t v_isShared_5603_; uint8_t v_isSharedCheck_5607_; 
lean_dec_ref(v_info_5575_);
v_a_5600_ = lean_ctor_get(v___x_5577_, 0);
v_isSharedCheck_5607_ = !lean_is_exclusive(v___x_5577_);
if (v_isSharedCheck_5607_ == 0)
{
v___x_5602_ = v___x_5577_;
v_isShared_5603_ = v_isSharedCheck_5607_;
goto v_resetjp_5601_;
}
else
{
lean_inc(v_a_5600_);
lean_dec(v___x_5577_);
v___x_5602_ = lean_box(0);
v_isShared_5603_ = v_isSharedCheck_5607_;
goto v_resetjp_5601_;
}
v_resetjp_5601_:
{
lean_object* v___x_5605_; 
if (v_isShared_5603_ == 0)
{
v___x_5605_ = v___x_5602_;
goto v_reusejp_5604_;
}
else
{
lean_object* v_reuseFailAlloc_5606_; 
v_reuseFailAlloc_5606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5606_, 0, v_a_5600_);
v___x_5605_ = v_reuseFailAlloc_5606_;
goto v_reusejp_5604_;
}
v_reusejp_5604_:
{
return v___x_5605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0___boxed(lean_object* v_info_5608_, lean_object* v_a_5609_){
_start:
{
lean_object* v_res_5610_; 
v_res_5610_ = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(v_info_5608_);
return v_res_5610_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0(lean_object* v_path_5611_, lean_object* v___y_5612_, lean_object* v___y_5613_, lean_object* v___y_5614_, lean_object* v___y_5615_, lean_object* v___y_5616_, lean_object* v___y_5617_){
_start:
{
lean_object* v_log_5619_; uint8_t v_action_5620_; uint8_t v_wantsRebuild_5621_; lean_object* v_trace_5622_; lean_object* v_buildTime_5623_; lean_object* v___x_5625_; uint8_t v_isShared_5626_; uint8_t v_isSharedCheck_5643_; 
v_log_5619_ = lean_ctor_get(v___y_5617_, 0);
v_action_5620_ = lean_ctor_get_uint8(v___y_5617_, sizeof(void*)*3);
v_wantsRebuild_5621_ = lean_ctor_get_uint8(v___y_5617_, sizeof(void*)*3 + 1);
v_trace_5622_ = lean_ctor_get(v___y_5617_, 1);
v_buildTime_5623_ = lean_ctor_get(v___y_5617_, 2);
v_isSharedCheck_5643_ = !lean_is_exclusive(v___y_5617_);
if (v_isSharedCheck_5643_ == 0)
{
v___x_5625_ = v___y_5617_;
v_isShared_5626_ = v_isSharedCheck_5643_;
goto v_resetjp_5624_;
}
else
{
lean_inc(v_buildTime_5623_);
lean_inc(v_trace_5622_);
lean_inc(v_log_5619_);
lean_dec(v___y_5617_);
v___x_5625_ = lean_box(0);
v_isShared_5626_ = v_isSharedCheck_5643_;
goto v_resetjp_5624_;
}
v_resetjp_5624_:
{
lean_object* v___x_5627_; 
lean_inc_ref(v_path_5611_);
v___x_5627_ = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(v_path_5611_);
if (lean_obj_tag(v___x_5627_) == 0)
{
lean_object* v_a_5628_; lean_object* v___x_5630_; 
lean_dec_ref(v_trace_5622_);
v_a_5628_ = lean_ctor_get(v___x_5627_, 0);
lean_inc(v_a_5628_);
lean_dec_ref(v___x_5627_);
if (v_isShared_5626_ == 0)
{
lean_ctor_set(v___x_5625_, 1, v_a_5628_);
v___x_5630_ = v___x_5625_;
goto v_reusejp_5629_;
}
else
{
lean_object* v_reuseFailAlloc_5632_; 
v_reuseFailAlloc_5632_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5632_, 0, v_log_5619_);
lean_ctor_set(v_reuseFailAlloc_5632_, 1, v_a_5628_);
lean_ctor_set(v_reuseFailAlloc_5632_, 2, v_buildTime_5623_);
lean_ctor_set_uint8(v_reuseFailAlloc_5632_, sizeof(void*)*3, v_action_5620_);
lean_ctor_set_uint8(v_reuseFailAlloc_5632_, sizeof(void*)*3 + 1, v_wantsRebuild_5621_);
v___x_5630_ = v_reuseFailAlloc_5632_;
goto v_reusejp_5629_;
}
v_reusejp_5629_:
{
lean_object* v___x_5631_; 
v___x_5631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5631_, 0, v_path_5611_);
lean_ctor_set(v___x_5631_, 1, v___x_5630_);
return v___x_5631_;
}
}
else
{
lean_object* v_a_5633_; lean_object* v___x_5634_; uint8_t v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5640_; 
lean_dec_ref(v_path_5611_);
v_a_5633_ = lean_ctor_get(v___x_5627_, 0);
lean_inc(v_a_5633_);
lean_dec_ref(v___x_5627_);
v___x_5634_ = lean_io_error_to_string(v_a_5633_);
v___x_5635_ = 3;
v___x_5636_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5636_, 0, v___x_5634_);
lean_ctor_set_uint8(v___x_5636_, sizeof(void*)*1, v___x_5635_);
v___x_5637_ = lean_array_get_size(v_log_5619_);
v___x_5638_ = lean_array_push(v_log_5619_, v___x_5636_);
if (v_isShared_5626_ == 0)
{
lean_ctor_set(v___x_5625_, 0, v___x_5638_);
v___x_5640_ = v___x_5625_;
goto v_reusejp_5639_;
}
else
{
lean_object* v_reuseFailAlloc_5642_; 
v_reuseFailAlloc_5642_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5642_, 0, v___x_5638_);
lean_ctor_set(v_reuseFailAlloc_5642_, 1, v_trace_5622_);
lean_ctor_set(v_reuseFailAlloc_5642_, 2, v_buildTime_5623_);
lean_ctor_set_uint8(v_reuseFailAlloc_5642_, sizeof(void*)*3, v_action_5620_);
lean_ctor_set_uint8(v_reuseFailAlloc_5642_, sizeof(void*)*3 + 1, v_wantsRebuild_5621_);
v___x_5640_ = v_reuseFailAlloc_5642_;
goto v_reusejp_5639_;
}
v_reusejp_5639_:
{
lean_object* v___x_5641_; 
v___x_5641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5641_, 0, v___x_5637_);
lean_ctor_set(v___x_5641_, 1, v___x_5640_);
return v___x_5641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0___boxed(lean_object* v_path_5644_, lean_object* v___y_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_, lean_object* v___y_5648_, lean_object* v___y_5649_, lean_object* v___y_5650_, lean_object* v___y_5651_){
_start:
{
lean_object* v_res_5652_; 
v_res_5652_ = l_Lake_inputBinFile___redArg___lam__0(v_path_5644_, v___y_5645_, v___y_5646_, v___y_5647_, v___y_5648_, v___y_5649_, v___y_5650_);
lean_dec_ref(v___y_5649_);
lean_dec(v___y_5648_);
lean_dec(v___y_5647_);
lean_dec(v___y_5646_);
lean_dec_ref(v___y_5645_);
return v_res_5652_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg(lean_object* v_path_5654_, lean_object* v_a_5655_, lean_object* v_a_5656_, lean_object* v_a_5657_, lean_object* v_a_5658_, lean_object* v_a_5659_){
_start:
{
lean_object* v___f_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; 
v___f_5661_ = lean_alloc_closure((void*)(l_Lake_inputBinFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5661_, 0, v_path_5654_);
v___x_5662_ = l_Lake_instDataKindFilePath;
v___x_5663_ = lean_unsigned_to_nat(0u);
v___x_5664_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
v___x_5665_ = l_Lake_Job_async___redArg(v___x_5662_, v___f_5661_, v___x_5663_, v___x_5664_, v_a_5655_, v_a_5656_, v_a_5657_, v_a_5658_, v_a_5659_);
return v___x_5665_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___boxed(lean_object* v_path_5666_, lean_object* v_a_5667_, lean_object* v_a_5668_, lean_object* v_a_5669_, lean_object* v_a_5670_, lean_object* v_a_5671_, lean_object* v_a_5672_){
_start:
{
lean_object* v_res_5673_; 
v_res_5673_ = l_Lake_inputBinFile___redArg(v_path_5666_, v_a_5667_, v_a_5668_, v_a_5669_, v_a_5670_, v_a_5671_);
return v_res_5673_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object* v_path_5674_, lean_object* v_a_5675_, lean_object* v_a_5676_, lean_object* v_a_5677_, lean_object* v_a_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_){
_start:
{
lean_object* v___x_5682_; 
v___x_5682_ = l_Lake_inputBinFile___redArg(v_path_5674_, v_a_5675_, v_a_5676_, v_a_5677_, v_a_5678_, v_a_5679_);
return v___x_5682_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___boxed(lean_object* v_path_5683_, lean_object* v_a_5684_, lean_object* v_a_5685_, lean_object* v_a_5686_, lean_object* v_a_5687_, lean_object* v_a_5688_, lean_object* v_a_5689_, lean_object* v_a_5690_){
_start:
{
lean_object* v_res_5691_; 
v_res_5691_ = l_Lake_inputBinFile(v_path_5683_, v_a_5684_, v_a_5685_, v_a_5686_, v_a_5687_, v_a_5688_, v_a_5689_);
lean_dec_ref(v_a_5689_);
return v_res_5691_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(lean_object* v_info_5692_){
_start:
{
lean_object* v___x_5694_; 
v___x_5694_ = l_Lake_computeTextFileHash(v_info_5692_);
if (lean_obj_tag(v___x_5694_) == 0)
{
lean_object* v_a_5695_; lean_object* v___x_5696_; 
v_a_5695_ = lean_ctor_get(v___x_5694_, 0);
lean_inc(v_a_5695_);
lean_dec_ref(v___x_5694_);
v___x_5696_ = lean_io_metadata(v_info_5692_);
if (lean_obj_tag(v___x_5696_) == 0)
{
lean_object* v_a_5697_; lean_object* v___x_5699_; uint8_t v_isShared_5700_; uint8_t v_isSharedCheck_5708_; 
v_a_5697_ = lean_ctor_get(v___x_5696_, 0);
v_isSharedCheck_5708_ = !lean_is_exclusive(v___x_5696_);
if (v_isSharedCheck_5708_ == 0)
{
v___x_5699_ = v___x_5696_;
v_isShared_5700_ = v_isSharedCheck_5708_;
goto v_resetjp_5698_;
}
else
{
lean_inc(v_a_5697_);
lean_dec(v___x_5696_);
v___x_5699_ = lean_box(0);
v_isShared_5700_ = v_isSharedCheck_5708_;
goto v_resetjp_5698_;
}
v_resetjp_5698_:
{
lean_object* v_modified_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; uint64_t v___x_5704_; lean_object* v___x_5706_; 
v_modified_5701_ = lean_ctor_get(v_a_5697_, 1);
lean_inc_ref(v_modified_5701_);
lean_dec(v_a_5697_);
v___x_5702_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_5703_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_5703_, 0, v_info_5692_);
lean_ctor_set(v___x_5703_, 1, v___x_5702_);
lean_ctor_set(v___x_5703_, 2, v_modified_5701_);
v___x_5704_ = lean_unbox_uint64(v_a_5695_);
lean_dec(v_a_5695_);
lean_ctor_set_uint64(v___x_5703_, sizeof(void*)*3, v___x_5704_);
if (v_isShared_5700_ == 0)
{
lean_ctor_set(v___x_5699_, 0, v___x_5703_);
v___x_5706_ = v___x_5699_;
goto v_reusejp_5705_;
}
else
{
lean_object* v_reuseFailAlloc_5707_; 
v_reuseFailAlloc_5707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5707_, 0, v___x_5703_);
v___x_5706_ = v_reuseFailAlloc_5707_;
goto v_reusejp_5705_;
}
v_reusejp_5705_:
{
return v___x_5706_;
}
}
}
else
{
lean_object* v_a_5709_; lean_object* v___x_5711_; uint8_t v_isShared_5712_; uint8_t v_isSharedCheck_5716_; 
lean_dec(v_a_5695_);
lean_dec_ref(v_info_5692_);
v_a_5709_ = lean_ctor_get(v___x_5696_, 0);
v_isSharedCheck_5716_ = !lean_is_exclusive(v___x_5696_);
if (v_isSharedCheck_5716_ == 0)
{
v___x_5711_ = v___x_5696_;
v_isShared_5712_ = v_isSharedCheck_5716_;
goto v_resetjp_5710_;
}
else
{
lean_inc(v_a_5709_);
lean_dec(v___x_5696_);
v___x_5711_ = lean_box(0);
v_isShared_5712_ = v_isSharedCheck_5716_;
goto v_resetjp_5710_;
}
v_resetjp_5710_:
{
lean_object* v___x_5714_; 
if (v_isShared_5712_ == 0)
{
v___x_5714_ = v___x_5711_;
goto v_reusejp_5713_;
}
else
{
lean_object* v_reuseFailAlloc_5715_; 
v_reuseFailAlloc_5715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5715_, 0, v_a_5709_);
v___x_5714_ = v_reuseFailAlloc_5715_;
goto v_reusejp_5713_;
}
v_reusejp_5713_:
{
return v___x_5714_;
}
}
}
}
else
{
lean_object* v_a_5717_; lean_object* v___x_5719_; uint8_t v_isShared_5720_; uint8_t v_isSharedCheck_5724_; 
lean_dec_ref(v_info_5692_);
v_a_5717_ = lean_ctor_get(v___x_5694_, 0);
v_isSharedCheck_5724_ = !lean_is_exclusive(v___x_5694_);
if (v_isSharedCheck_5724_ == 0)
{
v___x_5719_ = v___x_5694_;
v_isShared_5720_ = v_isSharedCheck_5724_;
goto v_resetjp_5718_;
}
else
{
lean_inc(v_a_5717_);
lean_dec(v___x_5694_);
v___x_5719_ = lean_box(0);
v_isShared_5720_ = v_isSharedCheck_5724_;
goto v_resetjp_5718_;
}
v_resetjp_5718_:
{
lean_object* v___x_5722_; 
if (v_isShared_5720_ == 0)
{
v___x_5722_ = v___x_5719_;
goto v_reusejp_5721_;
}
else
{
lean_object* v_reuseFailAlloc_5723_; 
v_reuseFailAlloc_5723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5723_, 0, v_a_5717_);
v___x_5722_ = v_reuseFailAlloc_5723_;
goto v_reusejp_5721_;
}
v_reusejp_5721_:
{
return v___x_5722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0___boxed(lean_object* v_info_5725_, lean_object* v_a_5726_){
_start:
{
lean_object* v_res_5727_; 
v_res_5727_ = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(v_info_5725_);
return v_res_5727_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0(lean_object* v_path_5728_, lean_object* v___y_5729_, lean_object* v___y_5730_, lean_object* v___y_5731_, lean_object* v___y_5732_, lean_object* v___y_5733_, lean_object* v___y_5734_){
_start:
{
lean_object* v_log_5736_; uint8_t v_action_5737_; uint8_t v_wantsRebuild_5738_; lean_object* v_trace_5739_; lean_object* v_buildTime_5740_; lean_object* v___x_5742_; uint8_t v_isShared_5743_; uint8_t v_isSharedCheck_5760_; 
v_log_5736_ = lean_ctor_get(v___y_5734_, 0);
v_action_5737_ = lean_ctor_get_uint8(v___y_5734_, sizeof(void*)*3);
v_wantsRebuild_5738_ = lean_ctor_get_uint8(v___y_5734_, sizeof(void*)*3 + 1);
v_trace_5739_ = lean_ctor_get(v___y_5734_, 1);
v_buildTime_5740_ = lean_ctor_get(v___y_5734_, 2);
v_isSharedCheck_5760_ = !lean_is_exclusive(v___y_5734_);
if (v_isSharedCheck_5760_ == 0)
{
v___x_5742_ = v___y_5734_;
v_isShared_5743_ = v_isSharedCheck_5760_;
goto v_resetjp_5741_;
}
else
{
lean_inc(v_buildTime_5740_);
lean_inc(v_trace_5739_);
lean_inc(v_log_5736_);
lean_dec(v___y_5734_);
v___x_5742_ = lean_box(0);
v_isShared_5743_ = v_isSharedCheck_5760_;
goto v_resetjp_5741_;
}
v_resetjp_5741_:
{
lean_object* v___x_5744_; 
lean_inc_ref(v_path_5728_);
v___x_5744_ = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(v_path_5728_);
if (lean_obj_tag(v___x_5744_) == 0)
{
lean_object* v_a_5745_; lean_object* v___x_5747_; 
lean_dec_ref(v_trace_5739_);
v_a_5745_ = lean_ctor_get(v___x_5744_, 0);
lean_inc(v_a_5745_);
lean_dec_ref(v___x_5744_);
if (v_isShared_5743_ == 0)
{
lean_ctor_set(v___x_5742_, 1, v_a_5745_);
v___x_5747_ = v___x_5742_;
goto v_reusejp_5746_;
}
else
{
lean_object* v_reuseFailAlloc_5749_; 
v_reuseFailAlloc_5749_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5749_, 0, v_log_5736_);
lean_ctor_set(v_reuseFailAlloc_5749_, 1, v_a_5745_);
lean_ctor_set(v_reuseFailAlloc_5749_, 2, v_buildTime_5740_);
lean_ctor_set_uint8(v_reuseFailAlloc_5749_, sizeof(void*)*3, v_action_5737_);
lean_ctor_set_uint8(v_reuseFailAlloc_5749_, sizeof(void*)*3 + 1, v_wantsRebuild_5738_);
v___x_5747_ = v_reuseFailAlloc_5749_;
goto v_reusejp_5746_;
}
v_reusejp_5746_:
{
lean_object* v___x_5748_; 
v___x_5748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5748_, 0, v_path_5728_);
lean_ctor_set(v___x_5748_, 1, v___x_5747_);
return v___x_5748_;
}
}
else
{
lean_object* v_a_5750_; lean_object* v___x_5751_; uint8_t v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5757_; 
lean_dec_ref(v_path_5728_);
v_a_5750_ = lean_ctor_get(v___x_5744_, 0);
lean_inc(v_a_5750_);
lean_dec_ref(v___x_5744_);
v___x_5751_ = lean_io_error_to_string(v_a_5750_);
v___x_5752_ = 3;
v___x_5753_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5753_, 0, v___x_5751_);
lean_ctor_set_uint8(v___x_5753_, sizeof(void*)*1, v___x_5752_);
v___x_5754_ = lean_array_get_size(v_log_5736_);
v___x_5755_ = lean_array_push(v_log_5736_, v___x_5753_);
if (v_isShared_5743_ == 0)
{
lean_ctor_set(v___x_5742_, 0, v___x_5755_);
v___x_5757_ = v___x_5742_;
goto v_reusejp_5756_;
}
else
{
lean_object* v_reuseFailAlloc_5759_; 
v_reuseFailAlloc_5759_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5759_, 0, v___x_5755_);
lean_ctor_set(v_reuseFailAlloc_5759_, 1, v_trace_5739_);
lean_ctor_set(v_reuseFailAlloc_5759_, 2, v_buildTime_5740_);
lean_ctor_set_uint8(v_reuseFailAlloc_5759_, sizeof(void*)*3, v_action_5737_);
lean_ctor_set_uint8(v_reuseFailAlloc_5759_, sizeof(void*)*3 + 1, v_wantsRebuild_5738_);
v___x_5757_ = v_reuseFailAlloc_5759_;
goto v_reusejp_5756_;
}
v_reusejp_5756_:
{
lean_object* v___x_5758_; 
v___x_5758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5758_, 0, v___x_5754_);
lean_ctor_set(v___x_5758_, 1, v___x_5757_);
return v___x_5758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0___boxed(lean_object* v_path_5761_, lean_object* v___y_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_, lean_object* v___y_5765_, lean_object* v___y_5766_, lean_object* v___y_5767_, lean_object* v___y_5768_){
_start:
{
lean_object* v_res_5769_; 
v_res_5769_ = l_Lake_inputTextFile___redArg___lam__0(v_path_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_);
lean_dec_ref(v___y_5766_);
lean_dec(v___y_5765_);
lean_dec(v___y_5764_);
lean_dec(v___y_5763_);
lean_dec_ref(v___y_5762_);
return v_res_5769_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg(lean_object* v_path_5770_, lean_object* v_a_5771_, lean_object* v_a_5772_, lean_object* v_a_5773_, lean_object* v_a_5774_, lean_object* v_a_5775_){
_start:
{
lean_object* v___f_5777_; lean_object* v___x_5778_; lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; 
v___f_5777_ = lean_alloc_closure((void*)(l_Lake_inputTextFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5777_, 0, v_path_5770_);
v___x_5778_ = l_Lake_instDataKindFilePath;
v___x_5779_ = lean_unsigned_to_nat(0u);
v___x_5780_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
v___x_5781_ = l_Lake_Job_async___redArg(v___x_5778_, v___f_5777_, v___x_5779_, v___x_5780_, v_a_5771_, v_a_5772_, v_a_5773_, v_a_5774_, v_a_5775_);
return v___x_5781_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___boxed(lean_object* v_path_5782_, lean_object* v_a_5783_, lean_object* v_a_5784_, lean_object* v_a_5785_, lean_object* v_a_5786_, lean_object* v_a_5787_, lean_object* v_a_5788_){
_start:
{
lean_object* v_res_5789_; 
v_res_5789_ = l_Lake_inputTextFile___redArg(v_path_5782_, v_a_5783_, v_a_5784_, v_a_5785_, v_a_5786_, v_a_5787_);
return v_res_5789_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object* v_path_5790_, lean_object* v_a_5791_, lean_object* v_a_5792_, lean_object* v_a_5793_, lean_object* v_a_5794_, lean_object* v_a_5795_, lean_object* v_a_5796_){
_start:
{
lean_object* v___x_5798_; 
v___x_5798_ = l_Lake_inputTextFile___redArg(v_path_5790_, v_a_5791_, v_a_5792_, v_a_5793_, v_a_5794_, v_a_5795_);
return v___x_5798_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___boxed(lean_object* v_path_5799_, lean_object* v_a_5800_, lean_object* v_a_5801_, lean_object* v_a_5802_, lean_object* v_a_5803_, lean_object* v_a_5804_, lean_object* v_a_5805_, lean_object* v_a_5806_){
_start:
{
lean_object* v_res_5807_; 
v_res_5807_ = l_Lake_inputTextFile(v_path_5799_, v_a_5800_, v_a_5801_, v_a_5802_, v_a_5803_, v_a_5804_, v_a_5805_);
lean_dec_ref(v_a_5805_);
return v_res_5807_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg(lean_object* v_path_5808_, uint8_t v_text_5809_, lean_object* v_a_5810_, lean_object* v_a_5811_, lean_object* v_a_5812_, lean_object* v_a_5813_, lean_object* v_a_5814_){
_start:
{
if (v_text_5809_ == 0)
{
lean_object* v___x_5816_; 
v___x_5816_ = l_Lake_inputBinFile___redArg(v_path_5808_, v_a_5810_, v_a_5811_, v_a_5812_, v_a_5813_, v_a_5814_);
return v___x_5816_;
}
else
{
lean_object* v___x_5817_; 
v___x_5817_ = l_Lake_inputTextFile___redArg(v_path_5808_, v_a_5810_, v_a_5811_, v_a_5812_, v_a_5813_, v_a_5814_);
return v___x_5817_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg___boxed(lean_object* v_path_5818_, lean_object* v_text_5819_, lean_object* v_a_5820_, lean_object* v_a_5821_, lean_object* v_a_5822_, lean_object* v_a_5823_, lean_object* v_a_5824_, lean_object* v_a_5825_){
_start:
{
uint8_t v_text_boxed_5826_; lean_object* v_res_5827_; 
v_text_boxed_5826_ = lean_unbox(v_text_5819_);
v_res_5827_ = l_Lake_inputFile___redArg(v_path_5818_, v_text_boxed_5826_, v_a_5820_, v_a_5821_, v_a_5822_, v_a_5823_, v_a_5824_);
return v_res_5827_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object* v_path_5828_, uint8_t v_text_5829_, lean_object* v_a_5830_, lean_object* v_a_5831_, lean_object* v_a_5832_, lean_object* v_a_5833_, lean_object* v_a_5834_, lean_object* v_a_5835_){
_start:
{
if (v_text_5829_ == 0)
{
lean_object* v___x_5837_; 
v___x_5837_ = l_Lake_inputBinFile___redArg(v_path_5828_, v_a_5830_, v_a_5831_, v_a_5832_, v_a_5833_, v_a_5834_);
return v___x_5837_;
}
else
{
lean_object* v___x_5838_; 
v___x_5838_ = l_Lake_inputTextFile___redArg(v_path_5828_, v_a_5830_, v_a_5831_, v_a_5832_, v_a_5833_, v_a_5834_);
return v___x_5838_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object* v_path_5839_, lean_object* v_text_5840_, lean_object* v_a_5841_, lean_object* v_a_5842_, lean_object* v_a_5843_, lean_object* v_a_5844_, lean_object* v_a_5845_, lean_object* v_a_5846_, lean_object* v_a_5847_){
_start:
{
uint8_t v_text_boxed_5848_; lean_object* v_res_5849_; 
v_text_boxed_5848_ = lean_unbox(v_text_5840_);
v_res_5849_ = l_Lake_inputFile(v_path_5839_, v_text_boxed_5848_, v_a_5841_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_, v_a_5846_);
lean_dec_ref(v_a_5846_);
return v_res_5849_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0(lean_object* v_x_5850_){
_start:
{
uint8_t v___x_5852_; lean_object* v___x_5853_; lean_object* v___x_5854_; 
v___x_5852_ = 1;
v___x_5853_ = lean_box(v___x_5852_);
v___x_5854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5854_, 0, v___x_5853_);
return v___x_5854_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0___boxed(lean_object* v_x_5855_, lean_object* v___y_5856_){
_start:
{
lean_object* v_res_5857_; 
v_res_5857_ = l_Lake_inputDir___lam__0(v_x_5855_);
lean_dec_ref(v_x_5855_);
return v_res_5857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(lean_object* v_filter_5858_, lean_object* v_as_5859_, size_t v_i_5860_, size_t v_stop_5861_, lean_object* v_b_5862_, lean_object* v___y_5863_){
_start:
{
lean_object* v_a_5866_; lean_object* v_a_5867_; uint8_t v___x_5871_; 
v___x_5871_ = lean_usize_dec_eq(v_i_5860_, v_stop_5861_);
if (v___x_5871_ == 0)
{
lean_object* v___x_5872_; uint8_t v___x_5873_; 
v___x_5872_ = lean_array_uget_borrowed(v_as_5859_, v_i_5860_);
v___x_5873_ = l_System_FilePath_isDir(v___x_5872_);
if (v___x_5873_ == 0)
{
lean_object* v___x_5874_; uint8_t v___x_5875_; 
lean_inc_ref(v_filter_5858_);
lean_inc(v___x_5872_);
v___x_5874_ = lean_apply_1(v_filter_5858_, v___x_5872_);
v___x_5875_ = lean_unbox(v___x_5874_);
if (v___x_5875_ == 0)
{
v_a_5866_ = v_b_5862_;
v_a_5867_ = v___y_5863_;
goto v___jp_5865_;
}
else
{
lean_object* v___x_5876_; 
lean_inc(v___x_5872_);
v___x_5876_ = lean_array_push(v_b_5862_, v___x_5872_);
v_a_5866_ = v___x_5876_;
v_a_5867_ = v___y_5863_;
goto v___jp_5865_;
}
}
else
{
v_a_5866_ = v_b_5862_;
v_a_5867_ = v___y_5863_;
goto v___jp_5865_;
}
}
else
{
lean_object* v___x_5877_; 
lean_dec_ref(v_filter_5858_);
v___x_5877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5877_, 0, v_b_5862_);
lean_ctor_set(v___x_5877_, 1, v___y_5863_);
return v___x_5877_;
}
v___jp_5865_:
{
size_t v___x_5868_; size_t v___x_5869_; 
v___x_5868_ = ((size_t)1ULL);
v___x_5869_ = lean_usize_add(v_i_5860_, v___x_5868_);
v_i_5860_ = v___x_5869_;
v_b_5862_ = v_a_5866_;
v___y_5863_ = v_a_5867_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg___boxed(lean_object* v_filter_5878_, lean_object* v_as_5879_, lean_object* v_i_5880_, lean_object* v_stop_5881_, lean_object* v_b_5882_, lean_object* v___y_5883_, lean_object* v___y_5884_){
_start:
{
size_t v_i_boxed_5885_; size_t v_stop_boxed_5886_; lean_object* v_res_5887_; 
v_i_boxed_5885_ = lean_unbox_usize(v_i_5880_);
lean_dec(v_i_5880_);
v_stop_boxed_5886_ = lean_unbox_usize(v_stop_5881_);
lean_dec(v_stop_5881_);
v_res_5887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_5878_, v_as_5879_, v_i_boxed_5885_, v_stop_boxed_5886_, v_b_5882_, v___y_5883_);
lean_dec_ref(v_as_5879_);
return v_res_5887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(lean_object* v_as_5889_, lean_object* v_lo_5890_, lean_object* v_hi_5891_){
_start:
{
uint8_t v___x_5892_; 
v___x_5892_ = lean_nat_dec_lt(v_lo_5890_, v_hi_5891_);
if (v___x_5892_ == 0)
{
lean_dec(v_lo_5890_);
return v_as_5889_;
}
else
{
lean_object* v___f_5893_; lean_object* v___x_5894_; lean_object* v_fst_5895_; lean_object* v_snd_5896_; uint8_t v___x_5897_; 
v___f_5893_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___closed__0));
lean_inc(v_lo_5890_);
v___x_5894_ = l_Array_qpartition___redArg(v_as_5889_, v___f_5893_, v_lo_5890_, v_hi_5891_);
v_fst_5895_ = lean_ctor_get(v___x_5894_, 0);
lean_inc(v_fst_5895_);
v_snd_5896_ = lean_ctor_get(v___x_5894_, 1);
lean_inc(v_snd_5896_);
lean_dec_ref(v___x_5894_);
v___x_5897_ = lean_nat_dec_le(v_hi_5891_, v_fst_5895_);
if (v___x_5897_ == 0)
{
lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; 
v___x_5898_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_snd_5896_, v_lo_5890_, v_fst_5895_);
v___x_5899_ = lean_unsigned_to_nat(1u);
v___x_5900_ = lean_nat_add(v_fst_5895_, v___x_5899_);
lean_dec(v_fst_5895_);
v_as_5889_ = v___x_5898_;
v_lo_5890_ = v___x_5900_;
goto _start;
}
else
{
lean_dec(v_fst_5895_);
lean_dec(v_lo_5890_);
return v_snd_5896_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___boxed(lean_object* v_as_5902_, lean_object* v_lo_5903_, lean_object* v_hi_5904_){
_start:
{
lean_object* v_res_5905_; 
v_res_5905_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_as_5902_, v_lo_5903_, v_hi_5904_);
lean_dec(v_hi_5904_);
return v_res_5905_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1(lean_object* v_path_5908_, lean_object* v___f_5909_, lean_object* v_filter_5910_, lean_object* v___y_5911_, lean_object* v___y_5912_, lean_object* v___y_5913_, lean_object* v___y_5914_, lean_object* v___y_5915_, lean_object* v___y_5916_){
_start:
{
lean_object* v___y_5919_; lean_object* v___y_5920_; lean_object* v___y_5923_; lean_object* v___y_5924_; lean_object* v___y_5925_; lean_object* v___y_5926_; lean_object* v___y_5927_; lean_object* v___y_5930_; lean_object* v___y_5931_; lean_object* v___y_5932_; lean_object* v___y_5933_; lean_object* v___y_5934_; lean_object* v_log_5936_; uint8_t v_action_5937_; uint8_t v_wantsRebuild_5938_; lean_object* v_trace_5939_; lean_object* v_buildTime_5940_; lean_object* v___x_5941_; 
v_log_5936_ = lean_ctor_get(v___y_5916_, 0);
v_action_5937_ = lean_ctor_get_uint8(v___y_5916_, sizeof(void*)*3);
v_wantsRebuild_5938_ = lean_ctor_get_uint8(v___y_5916_, sizeof(void*)*3 + 1);
v_trace_5939_ = lean_ctor_get(v___y_5916_, 1);
v_buildTime_5940_ = lean_ctor_get(v___y_5916_, 2);
v___x_5941_ = l_System_FilePath_walkDir(v_path_5908_, v___f_5909_);
if (lean_obj_tag(v___x_5941_) == 0)
{
lean_object* v_a_5942_; lean_object* v___x_5943_; lean_object* v_a_5945_; lean_object* v_a_5946_; lean_object* v___y_5953_; lean_object* v___x_5956_; lean_object* v___x_5957_; uint8_t v___x_5958_; 
v_a_5942_ = lean_ctor_get(v___x_5941_, 0);
lean_inc(v_a_5942_);
lean_dec_ref(v___x_5941_);
v___x_5943_ = lean_unsigned_to_nat(0u);
v___x_5956_ = lean_array_get_size(v_a_5942_);
v___x_5957_ = ((lean_object*)(l_Lake_inputDir___lam__1___closed__0));
v___x_5958_ = lean_nat_dec_lt(v___x_5943_, v___x_5956_);
if (v___x_5958_ == 0)
{
lean_dec(v_a_5942_);
lean_dec_ref(v_filter_5910_);
v_a_5945_ = v___x_5957_;
v_a_5946_ = v___y_5916_;
goto v___jp_5944_;
}
else
{
uint8_t v___x_5959_; 
v___x_5959_ = lean_nat_dec_le(v___x_5956_, v___x_5956_);
if (v___x_5959_ == 0)
{
if (v___x_5958_ == 0)
{
lean_dec(v_a_5942_);
lean_dec_ref(v_filter_5910_);
v_a_5945_ = v___x_5957_;
v_a_5946_ = v___y_5916_;
goto v___jp_5944_;
}
else
{
size_t v___x_5960_; size_t v___x_5961_; lean_object* v___x_5962_; 
v___x_5960_ = ((size_t)0ULL);
v___x_5961_ = lean_usize_of_nat(v___x_5956_);
v___x_5962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_5910_, v_a_5942_, v___x_5960_, v___x_5961_, v___x_5957_, v___y_5916_);
lean_dec(v_a_5942_);
v___y_5953_ = v___x_5962_;
goto v___jp_5952_;
}
}
else
{
size_t v___x_5963_; size_t v___x_5964_; lean_object* v___x_5965_; 
v___x_5963_ = ((size_t)0ULL);
v___x_5964_ = lean_usize_of_nat(v___x_5956_);
v___x_5965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_5910_, v_a_5942_, v___x_5963_, v___x_5964_, v___x_5957_, v___y_5916_);
lean_dec(v_a_5942_);
v___y_5953_ = v___x_5965_;
goto v___jp_5952_;
}
}
v___jp_5944_:
{
lean_object* v___x_5947_; uint8_t v___x_5948_; 
v___x_5947_ = lean_array_get_size(v_a_5945_);
v___x_5948_ = lean_nat_dec_eq(v___x_5947_, v___x_5943_);
if (v___x_5948_ == 0)
{
lean_object* v___x_5949_; lean_object* v___x_5950_; uint8_t v___x_5951_; 
v___x_5949_ = lean_unsigned_to_nat(1u);
v___x_5950_ = lean_nat_sub(v___x_5947_, v___x_5949_);
v___x_5951_ = lean_nat_dec_le(v___x_5943_, v___x_5950_);
if (v___x_5951_ == 0)
{
lean_inc(v___x_5950_);
v___y_5930_ = v___x_5947_;
v___y_5931_ = v___x_5950_;
v___y_5932_ = v_a_5945_;
v___y_5933_ = v_a_5946_;
v___y_5934_ = v___x_5950_;
goto v___jp_5929_;
}
else
{
v___y_5930_ = v___x_5947_;
v___y_5931_ = v___x_5950_;
v___y_5932_ = v_a_5945_;
v___y_5933_ = v_a_5946_;
v___y_5934_ = v___x_5943_;
goto v___jp_5929_;
}
}
else
{
v___y_5919_ = v_a_5946_;
v___y_5920_ = v_a_5945_;
goto v___jp_5918_;
}
}
v___jp_5952_:
{
if (lean_obj_tag(v___y_5953_) == 0)
{
lean_object* v_a_5954_; lean_object* v_a_5955_; 
v_a_5954_ = lean_ctor_get(v___y_5953_, 0);
lean_inc(v_a_5954_);
v_a_5955_ = lean_ctor_get(v___y_5953_, 1);
lean_inc(v_a_5955_);
lean_dec_ref(v___y_5953_);
v_a_5945_ = v_a_5954_;
v_a_5946_ = v_a_5955_;
goto v___jp_5944_;
}
else
{
return v___y_5953_;
}
}
}
else
{
lean_object* v___x_5967_; uint8_t v_isShared_5968_; uint8_t v_isSharedCheck_5979_; 
lean_inc(v_buildTime_5940_);
lean_inc_ref(v_trace_5939_);
lean_inc_ref(v_log_5936_);
lean_dec_ref(v_filter_5910_);
v_isSharedCheck_5979_ = !lean_is_exclusive(v___y_5916_);
if (v_isSharedCheck_5979_ == 0)
{
lean_object* v_unused_5980_; lean_object* v_unused_5981_; lean_object* v_unused_5982_; 
v_unused_5980_ = lean_ctor_get(v___y_5916_, 2);
lean_dec(v_unused_5980_);
v_unused_5981_ = lean_ctor_get(v___y_5916_, 1);
lean_dec(v_unused_5981_);
v_unused_5982_ = lean_ctor_get(v___y_5916_, 0);
lean_dec(v_unused_5982_);
v___x_5967_ = v___y_5916_;
v_isShared_5968_ = v_isSharedCheck_5979_;
goto v_resetjp_5966_;
}
else
{
lean_dec(v___y_5916_);
v___x_5967_ = lean_box(0);
v_isShared_5968_ = v_isSharedCheck_5979_;
goto v_resetjp_5966_;
}
v_resetjp_5966_:
{
lean_object* v_a_5969_; lean_object* v___x_5970_; uint8_t v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5976_; 
v_a_5969_ = lean_ctor_get(v___x_5941_, 0);
lean_inc(v_a_5969_);
lean_dec_ref(v___x_5941_);
v___x_5970_ = lean_io_error_to_string(v_a_5969_);
v___x_5971_ = 3;
v___x_5972_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5972_, 0, v___x_5970_);
lean_ctor_set_uint8(v___x_5972_, sizeof(void*)*1, v___x_5971_);
v___x_5973_ = lean_array_get_size(v_log_5936_);
v___x_5974_ = lean_array_push(v_log_5936_, v___x_5972_);
if (v_isShared_5968_ == 0)
{
lean_ctor_set(v___x_5967_, 0, v___x_5974_);
v___x_5976_ = v___x_5967_;
goto v_reusejp_5975_;
}
else
{
lean_object* v_reuseFailAlloc_5978_; 
v_reuseFailAlloc_5978_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5978_, 0, v___x_5974_);
lean_ctor_set(v_reuseFailAlloc_5978_, 1, v_trace_5939_);
lean_ctor_set(v_reuseFailAlloc_5978_, 2, v_buildTime_5940_);
lean_ctor_set_uint8(v_reuseFailAlloc_5978_, sizeof(void*)*3, v_action_5937_);
lean_ctor_set_uint8(v_reuseFailAlloc_5978_, sizeof(void*)*3 + 1, v_wantsRebuild_5938_);
v___x_5976_ = v_reuseFailAlloc_5978_;
goto v_reusejp_5975_;
}
v_reusejp_5975_:
{
lean_object* v___x_5977_; 
v___x_5977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5977_, 0, v___x_5973_);
lean_ctor_set(v___x_5977_, 1, v___x_5976_);
return v___x_5977_;
}
}
}
v___jp_5918_:
{
lean_object* v___x_5921_; 
v___x_5921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5921_, 0, v___y_5920_);
lean_ctor_set(v___x_5921_, 1, v___y_5919_);
return v___x_5921_;
}
v___jp_5922_:
{
lean_object* v___x_5928_; 
lean_dec(v___y_5923_);
v___x_5928_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v___y_5926_, v___y_5924_, v___y_5927_);
lean_dec(v___y_5927_);
v___y_5919_ = v___y_5925_;
v___y_5920_ = v___x_5928_;
goto v___jp_5918_;
}
v___jp_5929_:
{
uint8_t v___x_5935_; 
v___x_5935_ = lean_nat_dec_le(v___y_5934_, v___y_5931_);
if (v___x_5935_ == 0)
{
lean_dec(v___y_5931_);
lean_inc(v___y_5934_);
v___y_5923_ = v___y_5930_;
v___y_5924_ = v___y_5934_;
v___y_5925_ = v___y_5933_;
v___y_5926_ = v___y_5932_;
v___y_5927_ = v___y_5934_;
goto v___jp_5922_;
}
else
{
v___y_5923_ = v___y_5930_;
v___y_5924_ = v___y_5934_;
v___y_5925_ = v___y_5933_;
v___y_5926_ = v___y_5932_;
v___y_5927_ = v___y_5931_;
goto v___jp_5922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1___boxed(lean_object* v_path_5983_, lean_object* v___f_5984_, lean_object* v_filter_5985_, lean_object* v___y_5986_, lean_object* v___y_5987_, lean_object* v___y_5988_, lean_object* v___y_5989_, lean_object* v___y_5990_, lean_object* v___y_5991_, lean_object* v___y_5992_){
_start:
{
lean_object* v_res_5993_; 
v_res_5993_ = l_Lake_inputDir___lam__1(v_path_5983_, v___f_5984_, v_filter_5985_, v___y_5986_, v___y_5987_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_);
lean_dec_ref(v___y_5990_);
lean_dec(v___y_5989_);
lean_dec(v___y_5988_);
lean_dec(v___y_5987_);
lean_dec_ref(v___y_5986_);
return v_res_5993_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(uint8_t v_text_5994_, size_t v_sz_5995_, size_t v_i_5996_, lean_object* v_bs_5997_, lean_object* v___y_5998_, lean_object* v___y_5999_, lean_object* v___y_6000_, lean_object* v___y_6001_, lean_object* v___y_6002_, lean_object* v___y_6003_){
_start:
{
uint8_t v___x_6005_; 
v___x_6005_ = lean_usize_dec_lt(v_i_5996_, v_sz_5995_);
if (v___x_6005_ == 0)
{
lean_object* v___x_6006_; 
lean_dec_ref(v___y_6002_);
lean_dec(v___y_6001_);
lean_dec(v___y_6000_);
lean_dec(v___y_5999_);
lean_dec_ref(v___y_5998_);
v___x_6006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6006_, 0, v_bs_5997_);
lean_ctor_set(v___x_6006_, 1, v___y_6003_);
return v___x_6006_;
}
else
{
lean_object* v_v_6007_; lean_object* v___x_6008_; lean_object* v_bs_x27_6009_; lean_object* v___y_6011_; 
v_v_6007_ = lean_array_uget(v_bs_5997_, v_i_5996_);
v___x_6008_ = lean_unsigned_to_nat(0u);
v_bs_x27_6009_ = lean_array_uset(v_bs_5997_, v_i_5996_, v___x_6008_);
if (v_text_5994_ == 0)
{
lean_object* v___x_6016_; 
lean_inc_ref(v___y_6002_);
lean_inc(v___y_6001_);
lean_inc(v___y_6000_);
lean_inc(v___y_5999_);
lean_inc_ref(v___y_5998_);
v___x_6016_ = l_Lake_inputBinFile___redArg(v_v_6007_, v___y_5998_, v___y_5999_, v___y_6000_, v___y_6001_, v___y_6002_);
v___y_6011_ = v___x_6016_;
goto v___jp_6010_;
}
else
{
lean_object* v___x_6017_; 
lean_inc_ref(v___y_6002_);
lean_inc(v___y_6001_);
lean_inc(v___y_6000_);
lean_inc(v___y_5999_);
lean_inc_ref(v___y_5998_);
v___x_6017_ = l_Lake_inputTextFile___redArg(v_v_6007_, v___y_5998_, v___y_5999_, v___y_6000_, v___y_6001_, v___y_6002_);
v___y_6011_ = v___x_6017_;
goto v___jp_6010_;
}
v___jp_6010_:
{
size_t v___x_6012_; size_t v___x_6013_; lean_object* v___x_6014_; 
v___x_6012_ = ((size_t)1ULL);
v___x_6013_ = lean_usize_add(v_i_5996_, v___x_6012_);
v___x_6014_ = lean_array_uset(v_bs_x27_6009_, v_i_5996_, v___y_6011_);
v_i_5996_ = v___x_6013_;
v_bs_5997_ = v___x_6014_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0___boxed(lean_object* v_text_6018_, lean_object* v_sz_6019_, lean_object* v_i_6020_, lean_object* v_bs_6021_, lean_object* v___y_6022_, lean_object* v___y_6023_, lean_object* v___y_6024_, lean_object* v___y_6025_, lean_object* v___y_6026_, lean_object* v___y_6027_, lean_object* v___y_6028_){
_start:
{
uint8_t v_text_boxed_6029_; size_t v_sz_boxed_6030_; size_t v_i_boxed_6031_; lean_object* v_res_6032_; 
v_text_boxed_6029_ = lean_unbox(v_text_6018_);
v_sz_boxed_6030_ = lean_unbox_usize(v_sz_6019_);
lean_dec(v_sz_6019_);
v_i_boxed_6031_ = lean_unbox_usize(v_i_6020_);
lean_dec(v_i_6020_);
v_res_6032_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(v_text_boxed_6029_, v_sz_boxed_6030_, v_i_boxed_6031_, v_bs_6021_, v___y_6022_, v___y_6023_, v___y_6024_, v___y_6025_, v___y_6026_, v___y_6027_);
return v_res_6032_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2(uint8_t v_text_6033_, lean_object* v_path_6034_, lean_object* v_ps_6035_, lean_object* v___y_6036_, lean_object* v___y_6037_, lean_object* v___y_6038_, lean_object* v___y_6039_, lean_object* v___y_6040_, lean_object* v___y_6041_){
_start:
{
size_t v_sz_6043_; size_t v___x_6044_; lean_object* v___x_6045_; 
v_sz_6043_ = lean_array_size(v_ps_6035_);
v___x_6044_ = ((size_t)0ULL);
v___x_6045_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(v_text_6033_, v_sz_6043_, v___x_6044_, v_ps_6035_, v___y_6036_, v___y_6037_, v___y_6038_, v___y_6039_, v___y_6040_, v___y_6041_);
if (lean_obj_tag(v___x_6045_) == 0)
{
lean_object* v_a_6046_; lean_object* v_a_6047_; lean_object* v___x_6049_; uint8_t v_isShared_6050_; uint8_t v_isSharedCheck_6055_; 
v_a_6046_ = lean_ctor_get(v___x_6045_, 0);
v_a_6047_ = lean_ctor_get(v___x_6045_, 1);
v_isSharedCheck_6055_ = !lean_is_exclusive(v___x_6045_);
if (v_isSharedCheck_6055_ == 0)
{
v___x_6049_ = v___x_6045_;
v_isShared_6050_ = v_isSharedCheck_6055_;
goto v_resetjp_6048_;
}
else
{
lean_inc(v_a_6047_);
lean_inc(v_a_6046_);
lean_dec(v___x_6045_);
v___x_6049_ = lean_box(0);
v_isShared_6050_ = v_isSharedCheck_6055_;
goto v_resetjp_6048_;
}
v_resetjp_6048_:
{
lean_object* v___x_6051_; lean_object* v___x_6053_; 
v___x_6051_ = l_Lake_Job_collectArray___redArg(v_a_6046_, v_path_6034_);
lean_dec(v_a_6046_);
if (v_isShared_6050_ == 0)
{
lean_ctor_set(v___x_6049_, 0, v___x_6051_);
v___x_6053_ = v___x_6049_;
goto v_reusejp_6052_;
}
else
{
lean_object* v_reuseFailAlloc_6054_; 
v_reuseFailAlloc_6054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6054_, 0, v___x_6051_);
lean_ctor_set(v_reuseFailAlloc_6054_, 1, v_a_6047_);
v___x_6053_ = v_reuseFailAlloc_6054_;
goto v_reusejp_6052_;
}
v_reusejp_6052_:
{
return v___x_6053_;
}
}
}
else
{
lean_object* v_a_6056_; lean_object* v_a_6057_; lean_object* v___x_6059_; uint8_t v_isShared_6060_; uint8_t v_isSharedCheck_6064_; 
lean_dec_ref(v_path_6034_);
v_a_6056_ = lean_ctor_get(v___x_6045_, 0);
v_a_6057_ = lean_ctor_get(v___x_6045_, 1);
v_isSharedCheck_6064_ = !lean_is_exclusive(v___x_6045_);
if (v_isSharedCheck_6064_ == 0)
{
v___x_6059_ = v___x_6045_;
v_isShared_6060_ = v_isSharedCheck_6064_;
goto v_resetjp_6058_;
}
else
{
lean_inc(v_a_6057_);
lean_inc(v_a_6056_);
lean_dec(v___x_6045_);
v___x_6059_ = lean_box(0);
v_isShared_6060_ = v_isSharedCheck_6064_;
goto v_resetjp_6058_;
}
v_resetjp_6058_:
{
lean_object* v___x_6062_; 
if (v_isShared_6060_ == 0)
{
v___x_6062_ = v___x_6059_;
goto v_reusejp_6061_;
}
else
{
lean_object* v_reuseFailAlloc_6063_; 
v_reuseFailAlloc_6063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6063_, 0, v_a_6056_);
lean_ctor_set(v_reuseFailAlloc_6063_, 1, v_a_6057_);
v___x_6062_ = v_reuseFailAlloc_6063_;
goto v_reusejp_6061_;
}
v_reusejp_6061_:
{
return v___x_6062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2___boxed(lean_object* v_text_6065_, lean_object* v_path_6066_, lean_object* v_ps_6067_, lean_object* v___y_6068_, lean_object* v___y_6069_, lean_object* v___y_6070_, lean_object* v___y_6071_, lean_object* v___y_6072_, lean_object* v___y_6073_, lean_object* v___y_6074_){
_start:
{
uint8_t v_text_boxed_6075_; lean_object* v_res_6076_; 
v_text_boxed_6075_ = lean_unbox(v_text_6065_);
v_res_6076_ = l_Lake_inputDir___lam__2(v_text_boxed_6075_, v_path_6066_, v_ps_6067_, v___y_6068_, v___y_6069_, v___y_6070_, v___y_6071_, v___y_6072_, v___y_6073_);
return v_res_6076_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir(lean_object* v_path_6078_, uint8_t v_text_6079_, lean_object* v_filter_6080_, lean_object* v_a_6081_, lean_object* v_a_6082_, lean_object* v_a_6083_, lean_object* v_a_6084_, lean_object* v_a_6085_, lean_object* v_a_6086_){
_start:
{
lean_object* v___f_6088_; lean_object* v___f_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___f_6095_; uint8_t v___x_6096_; lean_object* v___x_6097_; 
v___f_6088_ = ((lean_object*)(l_Lake_inputDir___closed__0));
lean_inc_ref(v_path_6078_);
v___f_6089_ = lean_alloc_closure((void*)(l_Lake_inputDir___lam__1___boxed), 10, 3);
lean_closure_set(v___f_6089_, 0, v_path_6078_);
lean_closure_set(v___f_6089_, 1, v___f_6088_);
lean_closure_set(v___f_6089_, 2, v_filter_6080_);
v___x_6090_ = lean_box(0);
v___x_6091_ = lean_unsigned_to_nat(0u);
v___x_6092_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
lean_inc_ref(v_a_6085_);
lean_inc(v_a_6084_);
lean_inc(v_a_6083_);
lean_inc(v_a_6082_);
lean_inc_ref(v_a_6081_);
v___x_6093_ = l_Lake_Job_async___redArg(v___x_6090_, v___f_6089_, v___x_6091_, v___x_6092_, v_a_6081_, v_a_6082_, v_a_6083_, v_a_6084_, v_a_6085_);
v___x_6094_ = lean_box(v_text_6079_);
v___f_6095_ = lean_alloc_closure((void*)(l_Lake_inputDir___lam__2___boxed), 10, 2);
lean_closure_set(v___f_6095_, 0, v___x_6094_);
lean_closure_set(v___f_6095_, 1, v_path_6078_);
v___x_6096_ = 0;
v___x_6097_ = l_Lake_Job_bindM___redArg(v___x_6090_, v___x_6093_, v___f_6095_, v___x_6091_, v___x_6096_, v_a_6081_, v_a_6082_, v_a_6083_, v_a_6084_, v_a_6085_, v_a_6086_);
return v___x_6097_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___boxed(lean_object* v_path_6098_, lean_object* v_text_6099_, lean_object* v_filter_6100_, lean_object* v_a_6101_, lean_object* v_a_6102_, lean_object* v_a_6103_, lean_object* v_a_6104_, lean_object* v_a_6105_, lean_object* v_a_6106_, lean_object* v_a_6107_){
_start:
{
uint8_t v_text_boxed_6108_; lean_object* v_res_6109_; 
v_text_boxed_6108_ = lean_unbox(v_text_6099_);
v_res_6109_ = l_Lake_inputDir(v_path_6098_, v_text_boxed_6108_, v_filter_6100_, v_a_6101_, v_a_6102_, v_a_6103_, v_a_6104_, v_a_6105_, v_a_6106_);
return v_res_6109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(lean_object* v_n_6110_, lean_object* v_as_6111_, lean_object* v_lo_6112_, lean_object* v_hi_6113_, lean_object* v_w_6114_, lean_object* v_hlo_6115_, lean_object* v_hhi_6116_){
_start:
{
lean_object* v___x_6117_; 
v___x_6117_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_as_6111_, v_lo_6112_, v_hi_6113_);
return v___x_6117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___boxed(lean_object* v_n_6118_, lean_object* v_as_6119_, lean_object* v_lo_6120_, lean_object* v_hi_6121_, lean_object* v_w_6122_, lean_object* v_hlo_6123_, lean_object* v_hhi_6124_){
_start:
{
lean_object* v_res_6125_; 
v_res_6125_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(v_n_6118_, v_as_6119_, v_lo_6120_, v_hi_6121_, v_w_6122_, v_hlo_6123_, v_hhi_6124_);
lean_dec(v_hi_6121_);
lean_dec(v_n_6118_);
return v_res_6125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(lean_object* v_filter_6126_, lean_object* v_as_6127_, size_t v_i_6128_, size_t v_stop_6129_, lean_object* v_b_6130_, lean_object* v___y_6131_, lean_object* v___y_6132_, lean_object* v___y_6133_, lean_object* v___y_6134_, lean_object* v___y_6135_, lean_object* v___y_6136_){
_start:
{
lean_object* v___x_6138_; 
v___x_6138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6126_, v_as_6127_, v_i_6128_, v_stop_6129_, v_b_6130_, v___y_6136_);
return v___x_6138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___boxed(lean_object* v_filter_6139_, lean_object* v_as_6140_, lean_object* v_i_6141_, lean_object* v_stop_6142_, lean_object* v_b_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_, lean_object* v___y_6148_, lean_object* v___y_6149_, lean_object* v___y_6150_){
_start:
{
size_t v_i_boxed_6151_; size_t v_stop_boxed_6152_; lean_object* v_res_6153_; 
v_i_boxed_6151_ = lean_unbox_usize(v_i_6141_);
lean_dec(v_i_6141_);
v_stop_boxed_6152_ = lean_unbox_usize(v_stop_6142_);
lean_dec(v_stop_6142_);
v_res_6153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(v_filter_6139_, v_as_6140_, v_i_boxed_6151_, v_stop_boxed_6152_, v_b_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_);
lean_dec_ref(v___y_6148_);
lean_dec(v___y_6147_);
lean_dec(v___y_6146_);
lean_dec(v___y_6145_);
lean_dec_ref(v___y_6144_);
lean_dec_ref(v_as_6140_);
return v_res_6153_;
}
}
LEAN_EXPORT uint64_t l_Lake_buildO___lam__0(uint64_t v_ts_6154_, lean_object* v_t_6155_){
_start:
{
uint64_t v___x_6156_; uint64_t v___x_6157_; uint64_t v___x_6158_; uint64_t v___x_6159_; 
v___x_6156_ = l_Lake_Hash_nil;
v___x_6157_ = lean_string_hash(v_t_6155_);
v___x_6158_ = lean_uint64_mix_hash(v___x_6156_, v___x_6157_);
v___x_6159_ = lean_uint64_mix_hash(v_ts_6154_, v___x_6158_);
return v___x_6159_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__0___boxed(lean_object* v_ts_6160_, lean_object* v_t_6161_){
_start:
{
uint64_t v_ts_boxed_6162_; uint64_t v_res_6163_; lean_object* v_r_6164_; 
v_ts_boxed_6162_ = lean_unbox_uint64(v_ts_6160_);
lean_dec_ref(v_ts_6160_);
v_res_6163_ = l_Lake_buildO___lam__0(v_ts_boxed_6162_, v_t_6161_);
lean_dec_ref(v_t_6161_);
v_r_6164_ = lean_box_uint64(v_res_6163_);
return v_r_6164_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1(lean_object* v_oFile_6165_, lean_object* v_srcFile_6166_, lean_object* v___x_6167_, lean_object* v_compiler_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_){
_start:
{
lean_object* v_log_6176_; uint8_t v_action_6177_; uint8_t v_wantsRebuild_6178_; lean_object* v_trace_6179_; lean_object* v_buildTime_6180_; lean_object* v___x_6182_; uint8_t v_isShared_6183_; uint8_t v_isSharedCheck_6209_; 
v_log_6176_ = lean_ctor_get(v___y_6174_, 0);
v_action_6177_ = lean_ctor_get_uint8(v___y_6174_, sizeof(void*)*3);
v_wantsRebuild_6178_ = lean_ctor_get_uint8(v___y_6174_, sizeof(void*)*3 + 1);
v_trace_6179_ = lean_ctor_get(v___y_6174_, 1);
v_buildTime_6180_ = lean_ctor_get(v___y_6174_, 2);
v_isSharedCheck_6209_ = !lean_is_exclusive(v___y_6174_);
if (v_isSharedCheck_6209_ == 0)
{
v___x_6182_ = v___y_6174_;
v_isShared_6183_ = v_isSharedCheck_6209_;
goto v_resetjp_6181_;
}
else
{
lean_inc(v_buildTime_6180_);
lean_inc(v_trace_6179_);
lean_inc(v_log_6176_);
lean_dec(v___y_6174_);
v___x_6182_ = lean_box(0);
v_isShared_6183_ = v_isSharedCheck_6209_;
goto v_resetjp_6181_;
}
v_resetjp_6181_:
{
lean_object* v___x_6184_; 
v___x_6184_ = l_Lake_compileO(v_oFile_6165_, v_srcFile_6166_, v___x_6167_, v_compiler_6168_, v_log_6176_);
if (lean_obj_tag(v___x_6184_) == 0)
{
lean_object* v_a_6185_; lean_object* v_a_6186_; lean_object* v___x_6188_; uint8_t v_isShared_6189_; uint8_t v_isSharedCheck_6196_; 
v_a_6185_ = lean_ctor_get(v___x_6184_, 0);
v_a_6186_ = lean_ctor_get(v___x_6184_, 1);
v_isSharedCheck_6196_ = !lean_is_exclusive(v___x_6184_);
if (v_isSharedCheck_6196_ == 0)
{
v___x_6188_ = v___x_6184_;
v_isShared_6189_ = v_isSharedCheck_6196_;
goto v_resetjp_6187_;
}
else
{
lean_inc(v_a_6186_);
lean_inc(v_a_6185_);
lean_dec(v___x_6184_);
v___x_6188_ = lean_box(0);
v_isShared_6189_ = v_isSharedCheck_6196_;
goto v_resetjp_6187_;
}
v_resetjp_6187_:
{
lean_object* v___x_6191_; 
if (v_isShared_6183_ == 0)
{
lean_ctor_set(v___x_6182_, 0, v_a_6186_);
v___x_6191_ = v___x_6182_;
goto v_reusejp_6190_;
}
else
{
lean_object* v_reuseFailAlloc_6195_; 
v_reuseFailAlloc_6195_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6195_, 0, v_a_6186_);
lean_ctor_set(v_reuseFailAlloc_6195_, 1, v_trace_6179_);
lean_ctor_set(v_reuseFailAlloc_6195_, 2, v_buildTime_6180_);
lean_ctor_set_uint8(v_reuseFailAlloc_6195_, sizeof(void*)*3, v_action_6177_);
lean_ctor_set_uint8(v_reuseFailAlloc_6195_, sizeof(void*)*3 + 1, v_wantsRebuild_6178_);
v___x_6191_ = v_reuseFailAlloc_6195_;
goto v_reusejp_6190_;
}
v_reusejp_6190_:
{
lean_object* v___x_6193_; 
if (v_isShared_6189_ == 0)
{
lean_ctor_set(v___x_6188_, 1, v___x_6191_);
v___x_6193_ = v___x_6188_;
goto v_reusejp_6192_;
}
else
{
lean_object* v_reuseFailAlloc_6194_; 
v_reuseFailAlloc_6194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6194_, 0, v_a_6185_);
lean_ctor_set(v_reuseFailAlloc_6194_, 1, v___x_6191_);
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
else
{
lean_object* v_a_6197_; lean_object* v_a_6198_; lean_object* v___x_6200_; uint8_t v_isShared_6201_; uint8_t v_isSharedCheck_6208_; 
v_a_6197_ = lean_ctor_get(v___x_6184_, 0);
v_a_6198_ = lean_ctor_get(v___x_6184_, 1);
v_isSharedCheck_6208_ = !lean_is_exclusive(v___x_6184_);
if (v_isSharedCheck_6208_ == 0)
{
v___x_6200_ = v___x_6184_;
v_isShared_6201_ = v_isSharedCheck_6208_;
goto v_resetjp_6199_;
}
else
{
lean_inc(v_a_6198_);
lean_inc(v_a_6197_);
lean_dec(v___x_6184_);
v___x_6200_ = lean_box(0);
v_isShared_6201_ = v_isSharedCheck_6208_;
goto v_resetjp_6199_;
}
v_resetjp_6199_:
{
lean_object* v___x_6203_; 
if (v_isShared_6183_ == 0)
{
lean_ctor_set(v___x_6182_, 0, v_a_6198_);
v___x_6203_ = v___x_6182_;
goto v_reusejp_6202_;
}
else
{
lean_object* v_reuseFailAlloc_6207_; 
v_reuseFailAlloc_6207_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6207_, 0, v_a_6198_);
lean_ctor_set(v_reuseFailAlloc_6207_, 1, v_trace_6179_);
lean_ctor_set(v_reuseFailAlloc_6207_, 2, v_buildTime_6180_);
lean_ctor_set_uint8(v_reuseFailAlloc_6207_, sizeof(void*)*3, v_action_6177_);
lean_ctor_set_uint8(v_reuseFailAlloc_6207_, sizeof(void*)*3 + 1, v_wantsRebuild_6178_);
v___x_6203_ = v_reuseFailAlloc_6207_;
goto v_reusejp_6202_;
}
v_reusejp_6202_:
{
lean_object* v___x_6205_; 
if (v_isShared_6201_ == 0)
{
lean_ctor_set(v___x_6200_, 1, v___x_6203_);
v___x_6205_ = v___x_6200_;
goto v_reusejp_6204_;
}
else
{
lean_object* v_reuseFailAlloc_6206_; 
v_reuseFailAlloc_6206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6206_, 0, v_a_6197_);
lean_ctor_set(v_reuseFailAlloc_6206_, 1, v___x_6203_);
v___x_6205_ = v_reuseFailAlloc_6206_;
goto v_reusejp_6204_;
}
v_reusejp_6204_:
{
return v___x_6205_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1___boxed(lean_object* v_oFile_6210_, lean_object* v_srcFile_6211_, lean_object* v___x_6212_, lean_object* v_compiler_6213_, lean_object* v___y_6214_, lean_object* v___y_6215_, lean_object* v___y_6216_, lean_object* v___y_6217_, lean_object* v___y_6218_, lean_object* v___y_6219_, lean_object* v___y_6220_){
_start:
{
lean_object* v_res_6221_; 
v_res_6221_ = l_Lake_buildO___lam__1(v_oFile_6210_, v_srcFile_6211_, v___x_6212_, v_compiler_6213_, v___y_6214_, v___y_6215_, v___y_6216_, v___y_6217_, v___y_6218_, v___y_6219_);
lean_dec_ref(v___y_6218_);
lean_dec(v___y_6217_);
lean_dec(v___y_6216_);
lean_dec(v___y_6215_);
lean_dec_ref(v___y_6214_);
lean_dec_ref(v___x_6212_);
return v_res_6221_;
}
}
static lean_object* _init_l_Lake_buildO___lam__2___boxed__const__1(void){
_start:
{
uint64_t v___x_6225_; lean_object* v___x_6226_; 
v___x_6225_ = l_Lake_Hash_nil;
v___x_6226_ = lean_box_uint64(v___x_6225_);
return v___x_6226_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2(lean_object* v_traceArgs_6227_, lean_object* v___f_6228_, lean_object* v_extraDepTrace_6229_, lean_object* v_weakArgs_6230_, lean_object* v_oFile_6231_, lean_object* v_compiler_6232_, lean_object* v___x_6233_, lean_object* v___f_6234_, lean_object* v_srcFile_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_, lean_object* v___y_6238_, lean_object* v___y_6239_, lean_object* v___y_6240_, lean_object* v___y_6241_){
_start:
{
lean_object* v_log_6243_; uint8_t v_action_6244_; uint8_t v_wantsRebuild_6245_; lean_object* v_trace_6246_; lean_object* v_buildTime_6247_; lean_object* v___x_6249_; uint8_t v_isShared_6250_; uint8_t v_isSharedCheck_6332_; 
v_log_6243_ = lean_ctor_get(v___y_6241_, 0);
v_action_6244_ = lean_ctor_get_uint8(v___y_6241_, sizeof(void*)*3);
v_wantsRebuild_6245_ = lean_ctor_get_uint8(v___y_6241_, sizeof(void*)*3 + 1);
v_trace_6246_ = lean_ctor_get(v___y_6241_, 1);
v_buildTime_6247_ = lean_ctor_get(v___y_6241_, 2);
v_isSharedCheck_6332_ = !lean_is_exclusive(v___y_6241_);
if (v_isSharedCheck_6332_ == 0)
{
v___x_6249_ = v___y_6241_;
v_isShared_6250_ = v_isSharedCheck_6332_;
goto v_resetjp_6248_;
}
else
{
lean_inc(v_buildTime_6247_);
lean_inc(v_trace_6246_);
lean_inc(v_log_6243_);
lean_dec(v___y_6241_);
v___x_6249_ = lean_box(0);
v_isShared_6250_ = v_isSharedCheck_6332_;
goto v_resetjp_6248_;
}
v_resetjp_6248_:
{
lean_object* v___x_6251_; lean_object* v___x_6252_; uint64_t v___y_6254_; uint64_t v___x_6317_; lean_object* v___x_6318_; lean_object* v___x_6319_; uint8_t v___x_6320_; 
v___x_6251_ = l_Lake_platformTrace;
v___x_6252_ = l_Lake_BuildTrace_mix(v_trace_6246_, v___x_6251_);
v___x_6317_ = l_Lake_Hash_nil;
v___x_6318_ = lean_unsigned_to_nat(0u);
v___x_6319_ = lean_array_get_size(v_traceArgs_6227_);
v___x_6320_ = lean_nat_dec_lt(v___x_6318_, v___x_6319_);
if (v___x_6320_ == 0)
{
lean_dec_ref(v___f_6234_);
lean_dec_ref(v___x_6233_);
v___y_6254_ = v___x_6317_;
goto v___jp_6253_;
}
else
{
uint8_t v___x_6321_; 
v___x_6321_ = lean_nat_dec_le(v___x_6319_, v___x_6319_);
if (v___x_6321_ == 0)
{
if (v___x_6320_ == 0)
{
lean_dec_ref(v___f_6234_);
lean_dec_ref(v___x_6233_);
v___y_6254_ = v___x_6317_;
goto v___jp_6253_;
}
else
{
size_t v___x_6322_; size_t v___x_6323_; lean_object* v___x_6324_; lean_object* v___x_6325_; uint64_t v___x_6326_; 
v___x_6322_ = ((size_t)0ULL);
v___x_6323_ = lean_usize_of_nat(v___x_6319_);
v___x_6324_ = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(v_traceArgs_6227_);
v___x_6325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_6233_, v___f_6234_, v_traceArgs_6227_, v___x_6322_, v___x_6323_, v___x_6324_);
v___x_6326_ = lean_unbox_uint64(v___x_6325_);
lean_dec(v___x_6325_);
v___y_6254_ = v___x_6326_;
goto v___jp_6253_;
}
}
else
{
size_t v___x_6327_; size_t v___x_6328_; lean_object* v___x_6329_; lean_object* v___x_6330_; uint64_t v___x_6331_; 
v___x_6327_ = ((size_t)0ULL);
v___x_6328_ = lean_usize_of_nat(v___x_6319_);
v___x_6329_ = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(v_traceArgs_6227_);
v___x_6330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_6233_, v___f_6234_, v_traceArgs_6227_, v___x_6327_, v___x_6328_, v___x_6329_);
v___x_6331_ = lean_unbox_uint64(v___x_6330_);
lean_dec(v___x_6330_);
v___y_6254_ = v___x_6331_;
goto v___jp_6253_;
}
}
v___jp_6253_:
{
lean_object* v___x_6255_; lean_object* v___x_6256_; lean_object* v___x_6257_; lean_object* v___x_6258_; lean_object* v___x_6259_; lean_object* v___x_6260_; lean_object* v___x_6261_; lean_object* v___x_6262_; lean_object* v___x_6263_; lean_object* v___x_6264_; lean_object* v___x_6266_; 
v___x_6255_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_6256_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_6227_);
v___x_6257_ = lean_array_to_list(v_traceArgs_6227_);
v___x_6258_ = l_List_toString___redArg(v___f_6228_, v___x_6257_);
v___x_6259_ = lean_string_append(v___x_6256_, v___x_6258_);
lean_dec_ref(v___x_6258_);
v___x_6260_ = lean_string_append(v___x_6255_, v___x_6259_);
lean_dec_ref(v___x_6259_);
v___x_6261_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_6262_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_6263_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6263_, 0, v___x_6260_);
lean_ctor_set(v___x_6263_, 1, v___x_6261_);
lean_ctor_set(v___x_6263_, 2, v___x_6262_);
lean_ctor_set_uint64(v___x_6263_, sizeof(void*)*3, v___y_6254_);
v___x_6264_ = l_Lake_BuildTrace_mix(v___x_6252_, v___x_6263_);
if (v_isShared_6250_ == 0)
{
lean_ctor_set(v___x_6249_, 1, v___x_6264_);
v___x_6266_ = v___x_6249_;
goto v_reusejp_6265_;
}
else
{
lean_object* v_reuseFailAlloc_6316_; 
v_reuseFailAlloc_6316_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6316_, 0, v_log_6243_);
lean_ctor_set(v_reuseFailAlloc_6316_, 1, v___x_6264_);
lean_ctor_set(v_reuseFailAlloc_6316_, 2, v_buildTime_6247_);
lean_ctor_set_uint8(v_reuseFailAlloc_6316_, sizeof(void*)*3, v_action_6244_);
lean_ctor_set_uint8(v_reuseFailAlloc_6316_, sizeof(void*)*3 + 1, v_wantsRebuild_6245_);
v___x_6266_ = v_reuseFailAlloc_6316_;
goto v_reusejp_6265_;
}
v_reusejp_6265_:
{
lean_object* v___x_6267_; 
lean_inc_ref(v___y_6240_);
lean_inc(v___y_6239_);
lean_inc(v___y_6238_);
lean_inc(v___y_6237_);
lean_inc_ref(v___y_6236_);
v___x_6267_ = lean_apply_7(v_extraDepTrace_6229_, v___y_6236_, v___y_6237_, v___y_6238_, v___y_6239_, v___y_6240_, v___x_6266_, lean_box(0));
if (lean_obj_tag(v___x_6267_) == 0)
{
lean_object* v_a_6268_; lean_object* v_a_6269_; lean_object* v_log_6270_; uint8_t v_action_6271_; uint8_t v_wantsRebuild_6272_; lean_object* v_trace_6273_; lean_object* v_buildTime_6274_; lean_object* v___x_6276_; uint8_t v_isShared_6277_; uint8_t v_isSharedCheck_6306_; 
v_a_6268_ = lean_ctor_get(v___x_6267_, 1);
lean_inc(v_a_6268_);
v_a_6269_ = lean_ctor_get(v___x_6267_, 0);
lean_inc(v_a_6269_);
lean_dec_ref(v___x_6267_);
v_log_6270_ = lean_ctor_get(v_a_6268_, 0);
v_action_6271_ = lean_ctor_get_uint8(v_a_6268_, sizeof(void*)*3);
v_wantsRebuild_6272_ = lean_ctor_get_uint8(v_a_6268_, sizeof(void*)*3 + 1);
v_trace_6273_ = lean_ctor_get(v_a_6268_, 1);
v_buildTime_6274_ = lean_ctor_get(v_a_6268_, 2);
v_isSharedCheck_6306_ = !lean_is_exclusive(v_a_6268_);
if (v_isSharedCheck_6306_ == 0)
{
v___x_6276_ = v_a_6268_;
v_isShared_6277_ = v_isSharedCheck_6306_;
goto v_resetjp_6275_;
}
else
{
lean_inc(v_buildTime_6274_);
lean_inc(v_trace_6273_);
lean_inc(v_log_6270_);
lean_dec(v_a_6268_);
v___x_6276_ = lean_box(0);
v_isShared_6277_ = v_isSharedCheck_6306_;
goto v_resetjp_6275_;
}
v_resetjp_6275_:
{
lean_object* v___x_6278_; lean_object* v___x_6280_; 
v___x_6278_ = l_Lake_BuildTrace_mix(v_trace_6273_, v_a_6269_);
if (v_isShared_6277_ == 0)
{
lean_ctor_set(v___x_6276_, 1, v___x_6278_);
v___x_6280_ = v___x_6276_;
goto v_reusejp_6279_;
}
else
{
lean_object* v_reuseFailAlloc_6305_; 
v_reuseFailAlloc_6305_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6305_, 0, v_log_6270_);
lean_ctor_set(v_reuseFailAlloc_6305_, 1, v___x_6278_);
lean_ctor_set(v_reuseFailAlloc_6305_, 2, v_buildTime_6274_);
lean_ctor_set_uint8(v_reuseFailAlloc_6305_, sizeof(void*)*3, v_action_6271_);
lean_ctor_set_uint8(v_reuseFailAlloc_6305_, sizeof(void*)*3 + 1, v_wantsRebuild_6272_);
v___x_6280_ = v_reuseFailAlloc_6305_;
goto v_reusejp_6279_;
}
v_reusejp_6279_:
{
lean_object* v___x_6281_; lean_object* v___f_6282_; uint8_t v___x_6283_; lean_object* v___x_6284_; lean_object* v___x_6285_; 
v___x_6281_ = l_Array_append___redArg(v_weakArgs_6230_, v_traceArgs_6227_);
lean_dec_ref(v_traceArgs_6227_);
lean_inc_ref(v_oFile_6231_);
v___f_6282_ = lean_alloc_closure((void*)(l_Lake_buildO___lam__1___boxed), 11, 4);
lean_closure_set(v___f_6282_, 0, v_oFile_6231_);
lean_closure_set(v___f_6282_, 1, v_srcFile_6235_);
lean_closure_set(v___f_6282_, 2, v___x_6281_);
lean_closure_set(v___f_6282_, 3, v_compiler_6232_);
v___x_6283_ = 0;
v___x_6284_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
v___x_6285_ = l_Lake_buildArtifactUnlessUpToDate(v_oFile_6231_, v___f_6282_, v___x_6283_, v___x_6284_, v___x_6283_, v___x_6283_, v___y_6236_, v___y_6237_, v___y_6238_, v___y_6239_, v___y_6240_, v___x_6280_);
if (lean_obj_tag(v___x_6285_) == 0)
{
lean_object* v_a_6286_; lean_object* v_a_6287_; lean_object* v___x_6289_; uint8_t v_isShared_6290_; uint8_t v_isSharedCheck_6295_; 
v_a_6286_ = lean_ctor_get(v___x_6285_, 0);
v_a_6287_ = lean_ctor_get(v___x_6285_, 1);
v_isSharedCheck_6295_ = !lean_is_exclusive(v___x_6285_);
if (v_isSharedCheck_6295_ == 0)
{
v___x_6289_ = v___x_6285_;
v_isShared_6290_ = v_isSharedCheck_6295_;
goto v_resetjp_6288_;
}
else
{
lean_inc(v_a_6287_);
lean_inc(v_a_6286_);
lean_dec(v___x_6285_);
v___x_6289_ = lean_box(0);
v_isShared_6290_ = v_isSharedCheck_6295_;
goto v_resetjp_6288_;
}
v_resetjp_6288_:
{
lean_object* v_path_6291_; lean_object* v___x_6293_; 
v_path_6291_ = lean_ctor_get(v_a_6286_, 1);
lean_inc_ref(v_path_6291_);
lean_dec(v_a_6286_);
if (v_isShared_6290_ == 0)
{
lean_ctor_set(v___x_6289_, 0, v_path_6291_);
v___x_6293_ = v___x_6289_;
goto v_reusejp_6292_;
}
else
{
lean_object* v_reuseFailAlloc_6294_; 
v_reuseFailAlloc_6294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6294_, 0, v_path_6291_);
lean_ctor_set(v_reuseFailAlloc_6294_, 1, v_a_6287_);
v___x_6293_ = v_reuseFailAlloc_6294_;
goto v_reusejp_6292_;
}
v_reusejp_6292_:
{
return v___x_6293_;
}
}
}
else
{
lean_object* v_a_6296_; lean_object* v_a_6297_; lean_object* v___x_6299_; uint8_t v_isShared_6300_; uint8_t v_isSharedCheck_6304_; 
v_a_6296_ = lean_ctor_get(v___x_6285_, 0);
v_a_6297_ = lean_ctor_get(v___x_6285_, 1);
v_isSharedCheck_6304_ = !lean_is_exclusive(v___x_6285_);
if (v_isSharedCheck_6304_ == 0)
{
v___x_6299_ = v___x_6285_;
v_isShared_6300_ = v_isSharedCheck_6304_;
goto v_resetjp_6298_;
}
else
{
lean_inc(v_a_6297_);
lean_inc(v_a_6296_);
lean_dec(v___x_6285_);
v___x_6299_ = lean_box(0);
v_isShared_6300_ = v_isSharedCheck_6304_;
goto v_resetjp_6298_;
}
v_resetjp_6298_:
{
lean_object* v___x_6302_; 
if (v_isShared_6300_ == 0)
{
v___x_6302_ = v___x_6299_;
goto v_reusejp_6301_;
}
else
{
lean_object* v_reuseFailAlloc_6303_; 
v_reuseFailAlloc_6303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6303_, 0, v_a_6296_);
lean_ctor_set(v_reuseFailAlloc_6303_, 1, v_a_6297_);
v___x_6302_ = v_reuseFailAlloc_6303_;
goto v_reusejp_6301_;
}
v_reusejp_6301_:
{
return v___x_6302_;
}
}
}
}
}
}
else
{
lean_object* v_a_6307_; lean_object* v_a_6308_; lean_object* v___x_6310_; uint8_t v_isShared_6311_; uint8_t v_isSharedCheck_6315_; 
lean_dec_ref(v___y_6240_);
lean_dec(v___y_6239_);
lean_dec(v___y_6238_);
lean_dec(v___y_6237_);
lean_dec_ref(v___y_6236_);
lean_dec_ref(v_srcFile_6235_);
lean_dec_ref(v_compiler_6232_);
lean_dec_ref(v_oFile_6231_);
lean_dec_ref(v_weakArgs_6230_);
lean_dec_ref(v_traceArgs_6227_);
v_a_6307_ = lean_ctor_get(v___x_6267_, 0);
v_a_6308_ = lean_ctor_get(v___x_6267_, 1);
v_isSharedCheck_6315_ = !lean_is_exclusive(v___x_6267_);
if (v_isSharedCheck_6315_ == 0)
{
v___x_6310_ = v___x_6267_;
v_isShared_6311_ = v_isSharedCheck_6315_;
goto v_resetjp_6309_;
}
else
{
lean_inc(v_a_6308_);
lean_inc(v_a_6307_);
lean_dec(v___x_6267_);
v___x_6310_ = lean_box(0);
v_isShared_6311_ = v_isSharedCheck_6315_;
goto v_resetjp_6309_;
}
v_resetjp_6309_:
{
lean_object* v___x_6313_; 
if (v_isShared_6311_ == 0)
{
v___x_6313_ = v___x_6310_;
goto v_reusejp_6312_;
}
else
{
lean_object* v_reuseFailAlloc_6314_; 
v_reuseFailAlloc_6314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6314_, 0, v_a_6307_);
lean_ctor_set(v_reuseFailAlloc_6314_, 1, v_a_6308_);
v___x_6313_ = v_reuseFailAlloc_6314_;
goto v_reusejp_6312_;
}
v_reusejp_6312_:
{
return v___x_6313_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed(lean_object* v_traceArgs_6333_, lean_object* v___f_6334_, lean_object* v_extraDepTrace_6335_, lean_object* v_weakArgs_6336_, lean_object* v_oFile_6337_, lean_object* v_compiler_6338_, lean_object* v___x_6339_, lean_object* v___f_6340_, lean_object* v_srcFile_6341_, lean_object* v___y_6342_, lean_object* v___y_6343_, lean_object* v___y_6344_, lean_object* v___y_6345_, lean_object* v___y_6346_, lean_object* v___y_6347_, lean_object* v___y_6348_){
_start:
{
lean_object* v_res_6349_; 
v_res_6349_ = l_Lake_buildO___lam__2(v_traceArgs_6333_, v___f_6334_, v_extraDepTrace_6335_, v_weakArgs_6336_, v_oFile_6337_, v_compiler_6338_, v___x_6339_, v___f_6340_, v_srcFile_6341_, v___y_6342_, v___y_6343_, v___y_6344_, v___y_6345_, v___y_6346_, v___y_6347_);
return v_res_6349_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object* v_oFile_6352_, lean_object* v_srcJob_6353_, lean_object* v_weakArgs_6354_, lean_object* v_traceArgs_6355_, lean_object* v_compiler_6356_, lean_object* v_extraDepTrace_6357_, lean_object* v_a_6358_, lean_object* v_a_6359_, lean_object* v_a_6360_, lean_object* v_a_6361_, lean_object* v_a_6362_, lean_object* v_a_6363_){
_start:
{
lean_object* v___f_6365_; lean_object* v___x_6366_; lean_object* v___f_6367_; lean_object* v___x_6368_; lean_object* v___f_6369_; lean_object* v___x_6370_; uint8_t v___x_6371_; lean_object* v___x_6372_; 
v___f_6365_ = ((lean_object*)(l_Lake_buildO___closed__0));
v___x_6366_ = l_Lake_instDataKindFilePath;
v___f_6367_ = ((lean_object*)(l_Lake_buildO___closed__1));
v___x_6368_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__10));
v___f_6369_ = lean_alloc_closure((void*)(l_Lake_buildO___lam__2___boxed), 16, 8);
lean_closure_set(v___f_6369_, 0, v_traceArgs_6355_);
lean_closure_set(v___f_6369_, 1, v___f_6367_);
lean_closure_set(v___f_6369_, 2, v_extraDepTrace_6357_);
lean_closure_set(v___f_6369_, 3, v_weakArgs_6354_);
lean_closure_set(v___f_6369_, 4, v_oFile_6352_);
lean_closure_set(v___f_6369_, 5, v_compiler_6356_);
lean_closure_set(v___f_6369_, 6, v___x_6368_);
lean_closure_set(v___f_6369_, 7, v___f_6365_);
v___x_6370_ = lean_unsigned_to_nat(0u);
v___x_6371_ = 0;
v___x_6372_ = l_Lake_Job_mapM___redArg(v___x_6366_, v_srcJob_6353_, v___f_6369_, v___x_6370_, v___x_6371_, v_a_6358_, v_a_6359_, v_a_6360_, v_a_6361_, v_a_6362_, v_a_6363_);
return v___x_6372_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___boxed(lean_object* v_oFile_6373_, lean_object* v_srcJob_6374_, lean_object* v_weakArgs_6375_, lean_object* v_traceArgs_6376_, lean_object* v_compiler_6377_, lean_object* v_extraDepTrace_6378_, lean_object* v_a_6379_, lean_object* v_a_6380_, lean_object* v_a_6381_, lean_object* v_a_6382_, lean_object* v_a_6383_, lean_object* v_a_6384_, lean_object* v_a_6385_){
_start:
{
lean_object* v_res_6386_; 
v_res_6386_ = l_Lake_buildO(v_oFile_6373_, v_srcJob_6374_, v_weakArgs_6375_, v_traceArgs_6376_, v_compiler_6377_, v_extraDepTrace_6378_, v_a_6379_, v_a_6380_, v_a_6381_, v_a_6382_, v_a_6383_, v_a_6384_);
return v_res_6386_;
}
}
static lean_object* _init_l_Lake_buildLeanO___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6388_; lean_object* v___x_6389_; lean_object* v___x_6390_; lean_object* v___x_6391_; 
v___x_6388_ = ((lean_object*)(l_Lake_buildLeanO___lam__0___closed__0));
v___x_6389_ = lean_unsigned_to_nat(2u);
v___x_6390_ = lean_mk_empty_array_with_capacity(v___x_6389_);
v___x_6391_ = lean_array_push(v___x_6390_, v___x_6388_);
return v___x_6391_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0(lean_object* v_weakArgs_6392_, lean_object* v_traceArgs_6393_, lean_object* v_oFile_6394_, lean_object* v_srcFile_6395_, lean_object* v_leanIncludeDir_x3f_6396_, lean_object* v___y_6397_, lean_object* v___y_6398_, lean_object* v___y_6399_, lean_object* v___y_6400_, lean_object* v___y_6401_, lean_object* v___y_6402_){
_start:
{
lean_object* v_toContext_6404_; lean_object* v_lakeEnv_6405_; lean_object* v_log_6406_; uint8_t v_action_6407_; uint8_t v_wantsRebuild_6408_; lean_object* v_trace_6409_; lean_object* v_buildTime_6410_; lean_object* v___x_6412_; uint8_t v_isShared_6413_; uint8_t v_isSharedCheck_6451_; 
v_toContext_6404_ = lean_ctor_get(v___y_6401_, 1);
lean_inc(v_toContext_6404_);
lean_dec_ref(v___y_6401_);
v_lakeEnv_6405_ = lean_ctor_get(v_toContext_6404_, 1);
lean_inc_ref(v_lakeEnv_6405_);
lean_dec(v_toContext_6404_);
v_log_6406_ = lean_ctor_get(v___y_6402_, 0);
v_action_6407_ = lean_ctor_get_uint8(v___y_6402_, sizeof(void*)*3);
v_wantsRebuild_6408_ = lean_ctor_get_uint8(v___y_6402_, sizeof(void*)*3 + 1);
v_trace_6409_ = lean_ctor_get(v___y_6402_, 1);
v_buildTime_6410_ = lean_ctor_get(v___y_6402_, 2);
v_isSharedCheck_6451_ = !lean_is_exclusive(v___y_6402_);
if (v_isSharedCheck_6451_ == 0)
{
v___x_6412_ = v___y_6402_;
v_isShared_6413_ = v_isSharedCheck_6451_;
goto v_resetjp_6411_;
}
else
{
lean_inc(v_buildTime_6410_);
lean_inc(v_trace_6409_);
lean_inc(v_log_6406_);
lean_dec(v___y_6402_);
v___x_6412_ = lean_box(0);
v_isShared_6413_ = v_isSharedCheck_6451_;
goto v_resetjp_6411_;
}
v_resetjp_6411_:
{
lean_object* v_lean_6414_; lean_object* v___y_6416_; 
v_lean_6414_ = lean_ctor_get(v_lakeEnv_6405_, 1);
lean_inc_ref(v_lean_6414_);
lean_dec_ref(v_lakeEnv_6405_);
if (lean_obj_tag(v_leanIncludeDir_x3f_6396_) == 0)
{
lean_object* v_includeDir_6449_; 
v_includeDir_6449_ = lean_ctor_get(v_lean_6414_, 4);
lean_inc_ref(v_includeDir_6449_);
v___y_6416_ = v_includeDir_6449_;
goto v___jp_6415_;
}
else
{
lean_object* v_val_6450_; 
v_val_6450_ = lean_ctor_get(v_leanIncludeDir_x3f_6396_, 0);
lean_inc(v_val_6450_);
lean_dec_ref(v_leanIncludeDir_x3f_6396_);
v___y_6416_ = v_val_6450_;
goto v___jp_6415_;
}
v___jp_6415_:
{
lean_object* v_cc_6417_; lean_object* v_ccFlags_6418_; lean_object* v___x_6419_; lean_object* v___x_6420_; lean_object* v___x_6421_; lean_object* v___x_6422_; lean_object* v___x_6423_; lean_object* v___x_6424_; 
v_cc_6417_ = lean_ctor_get(v_lean_6414_, 13);
lean_inc_ref(v_cc_6417_);
v_ccFlags_6418_ = lean_ctor_get(v_lean_6414_, 17);
lean_inc_ref(v_ccFlags_6418_);
lean_dec_ref(v_lean_6414_);
v___x_6419_ = lean_obj_once(&l_Lake_buildLeanO___lam__0___closed__1, &l_Lake_buildLeanO___lam__0___closed__1_once, _init_l_Lake_buildLeanO___lam__0___closed__1);
v___x_6420_ = lean_array_push(v___x_6419_, v___y_6416_);
v___x_6421_ = l_Array_append___redArg(v___x_6420_, v_ccFlags_6418_);
lean_dec_ref(v_ccFlags_6418_);
v___x_6422_ = l_Array_append___redArg(v___x_6421_, v_weakArgs_6392_);
v___x_6423_ = l_Array_append___redArg(v___x_6422_, v_traceArgs_6393_);
v___x_6424_ = l_Lake_compileO(v_oFile_6394_, v_srcFile_6395_, v___x_6423_, v_cc_6417_, v_log_6406_);
lean_dec_ref(v___x_6423_);
if (lean_obj_tag(v___x_6424_) == 0)
{
lean_object* v_a_6425_; lean_object* v_a_6426_; lean_object* v___x_6428_; uint8_t v_isShared_6429_; uint8_t v_isSharedCheck_6436_; 
v_a_6425_ = lean_ctor_get(v___x_6424_, 0);
v_a_6426_ = lean_ctor_get(v___x_6424_, 1);
v_isSharedCheck_6436_ = !lean_is_exclusive(v___x_6424_);
if (v_isSharedCheck_6436_ == 0)
{
v___x_6428_ = v___x_6424_;
v_isShared_6429_ = v_isSharedCheck_6436_;
goto v_resetjp_6427_;
}
else
{
lean_inc(v_a_6426_);
lean_inc(v_a_6425_);
lean_dec(v___x_6424_);
v___x_6428_ = lean_box(0);
v_isShared_6429_ = v_isSharedCheck_6436_;
goto v_resetjp_6427_;
}
v_resetjp_6427_:
{
lean_object* v___x_6431_; 
if (v_isShared_6413_ == 0)
{
lean_ctor_set(v___x_6412_, 0, v_a_6426_);
v___x_6431_ = v___x_6412_;
goto v_reusejp_6430_;
}
else
{
lean_object* v_reuseFailAlloc_6435_; 
v_reuseFailAlloc_6435_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6435_, 0, v_a_6426_);
lean_ctor_set(v_reuseFailAlloc_6435_, 1, v_trace_6409_);
lean_ctor_set(v_reuseFailAlloc_6435_, 2, v_buildTime_6410_);
lean_ctor_set_uint8(v_reuseFailAlloc_6435_, sizeof(void*)*3, v_action_6407_);
lean_ctor_set_uint8(v_reuseFailAlloc_6435_, sizeof(void*)*3 + 1, v_wantsRebuild_6408_);
v___x_6431_ = v_reuseFailAlloc_6435_;
goto v_reusejp_6430_;
}
v_reusejp_6430_:
{
lean_object* v___x_6433_; 
if (v_isShared_6429_ == 0)
{
lean_ctor_set(v___x_6428_, 1, v___x_6431_);
v___x_6433_ = v___x_6428_;
goto v_reusejp_6432_;
}
else
{
lean_object* v_reuseFailAlloc_6434_; 
v_reuseFailAlloc_6434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6434_, 0, v_a_6425_);
lean_ctor_set(v_reuseFailAlloc_6434_, 1, v___x_6431_);
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
else
{
lean_object* v_a_6437_; lean_object* v_a_6438_; lean_object* v___x_6440_; uint8_t v_isShared_6441_; uint8_t v_isSharedCheck_6448_; 
v_a_6437_ = lean_ctor_get(v___x_6424_, 0);
v_a_6438_ = lean_ctor_get(v___x_6424_, 1);
v_isSharedCheck_6448_ = !lean_is_exclusive(v___x_6424_);
if (v_isSharedCheck_6448_ == 0)
{
v___x_6440_ = v___x_6424_;
v_isShared_6441_ = v_isSharedCheck_6448_;
goto v_resetjp_6439_;
}
else
{
lean_inc(v_a_6438_);
lean_inc(v_a_6437_);
lean_dec(v___x_6424_);
v___x_6440_ = lean_box(0);
v_isShared_6441_ = v_isSharedCheck_6448_;
goto v_resetjp_6439_;
}
v_resetjp_6439_:
{
lean_object* v___x_6443_; 
if (v_isShared_6413_ == 0)
{
lean_ctor_set(v___x_6412_, 0, v_a_6438_);
v___x_6443_ = v___x_6412_;
goto v_reusejp_6442_;
}
else
{
lean_object* v_reuseFailAlloc_6447_; 
v_reuseFailAlloc_6447_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6447_, 0, v_a_6438_);
lean_ctor_set(v_reuseFailAlloc_6447_, 1, v_trace_6409_);
lean_ctor_set(v_reuseFailAlloc_6447_, 2, v_buildTime_6410_);
lean_ctor_set_uint8(v_reuseFailAlloc_6447_, sizeof(void*)*3, v_action_6407_);
lean_ctor_set_uint8(v_reuseFailAlloc_6447_, sizeof(void*)*3 + 1, v_wantsRebuild_6408_);
v___x_6443_ = v_reuseFailAlloc_6447_;
goto v_reusejp_6442_;
}
v_reusejp_6442_:
{
lean_object* v___x_6445_; 
if (v_isShared_6441_ == 0)
{
lean_ctor_set(v___x_6440_, 1, v___x_6443_);
v___x_6445_ = v___x_6440_;
goto v_reusejp_6444_;
}
else
{
lean_object* v_reuseFailAlloc_6446_; 
v_reuseFailAlloc_6446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6446_, 0, v_a_6437_);
lean_ctor_set(v_reuseFailAlloc_6446_, 1, v___x_6443_);
v___x_6445_ = v_reuseFailAlloc_6446_;
goto v_reusejp_6444_;
}
v_reusejp_6444_:
{
return v___x_6445_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0___boxed(lean_object* v_weakArgs_6452_, lean_object* v_traceArgs_6453_, lean_object* v_oFile_6454_, lean_object* v_srcFile_6455_, lean_object* v_leanIncludeDir_x3f_6456_, lean_object* v___y_6457_, lean_object* v___y_6458_, lean_object* v___y_6459_, lean_object* v___y_6460_, lean_object* v___y_6461_, lean_object* v___y_6462_, lean_object* v___y_6463_){
_start:
{
lean_object* v_res_6464_; 
v_res_6464_ = l_Lake_buildLeanO___lam__0(v_weakArgs_6452_, v_traceArgs_6453_, v_oFile_6454_, v_srcFile_6455_, v_leanIncludeDir_x3f_6456_, v___y_6457_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_);
lean_dec(v___y_6460_);
lean_dec(v___y_6459_);
lean_dec(v___y_6458_);
lean_dec_ref(v___y_6457_);
lean_dec_ref(v_traceArgs_6453_);
lean_dec_ref(v_weakArgs_6452_);
return v_res_6464_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(lean_object* v_as_6465_, size_t v_i_6466_, size_t v_stop_6467_, uint64_t v_b_6468_){
_start:
{
uint8_t v___x_6469_; 
v___x_6469_ = lean_usize_dec_eq(v_i_6466_, v_stop_6467_);
if (v___x_6469_ == 0)
{
lean_object* v___x_6470_; uint64_t v___x_6471_; uint64_t v___x_6472_; uint64_t v___x_6473_; uint64_t v___x_6474_; size_t v___x_6475_; size_t v___x_6476_; 
v___x_6470_ = lean_array_uget_borrowed(v_as_6465_, v_i_6466_);
v___x_6471_ = l_Lake_Hash_nil;
v___x_6472_ = lean_string_hash(v___x_6470_);
v___x_6473_ = lean_uint64_mix_hash(v___x_6471_, v___x_6472_);
v___x_6474_ = lean_uint64_mix_hash(v_b_6468_, v___x_6473_);
v___x_6475_ = ((size_t)1ULL);
v___x_6476_ = lean_usize_add(v_i_6466_, v___x_6475_);
v_i_6466_ = v___x_6476_;
v_b_6468_ = v___x_6474_;
goto _start;
}
else
{
return v_b_6468_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1___boxed(lean_object* v_as_6478_, lean_object* v_i_6479_, lean_object* v_stop_6480_, lean_object* v_b_6481_){
_start:
{
size_t v_i_boxed_6482_; size_t v_stop_boxed_6483_; uint64_t v_b_boxed_6484_; uint64_t v_res_6485_; lean_object* v_r_6486_; 
v_i_boxed_6482_ = lean_unbox_usize(v_i_6479_);
lean_dec(v_i_6479_);
v_stop_boxed_6483_ = lean_unbox_usize(v_stop_6480_);
lean_dec(v_stop_6480_);
v_b_boxed_6484_ = lean_unbox_uint64(v_b_6481_);
lean_dec_ref(v_b_6481_);
v_res_6485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_as_6478_, v_i_boxed_6482_, v_stop_boxed_6483_, v_b_boxed_6484_);
lean_dec_ref(v_as_6478_);
v_r_6486_ = lean_box_uint64(v_res_6485_);
return v_r_6486_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(lean_object* v_x_6488_, lean_object* v_x_6489_){
_start:
{
if (lean_obj_tag(v_x_6489_) == 0)
{
return v_x_6488_;
}
else
{
lean_object* v_head_6490_; lean_object* v_tail_6491_; lean_object* v___x_6492_; lean_object* v___x_6493_; lean_object* v___x_6494_; 
v_head_6490_ = lean_ctor_get(v_x_6489_, 0);
v_tail_6491_ = lean_ctor_get(v_x_6489_, 1);
v___x_6492_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0));
v___x_6493_ = lean_string_append(v_x_6488_, v___x_6492_);
v___x_6494_ = lean_string_append(v___x_6493_, v_head_6490_);
v_x_6488_ = v___x_6494_;
v_x_6489_ = v_tail_6491_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___boxed(lean_object* v_x_6496_, lean_object* v_x_6497_){
_start:
{
lean_object* v_res_6498_; 
v_res_6498_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(v_x_6496_, v_x_6497_);
lean_dec(v_x_6497_);
return v_res_6498_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0(lean_object* v_x_6502_){
_start:
{
if (lean_obj_tag(v_x_6502_) == 0)
{
lean_object* v___x_6503_; 
v___x_6503_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0));
return v___x_6503_;
}
else
{
lean_object* v_tail_6504_; 
v_tail_6504_ = lean_ctor_get(v_x_6502_, 1);
if (lean_obj_tag(v_tail_6504_) == 0)
{
lean_object* v_head_6505_; lean_object* v___x_6506_; lean_object* v___x_6507_; lean_object* v___x_6508_; lean_object* v___x_6509_; 
v_head_6505_ = lean_ctor_get(v_x_6502_, 0);
v___x_6506_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1));
v___x_6507_ = lean_string_append(v___x_6506_, v_head_6505_);
v___x_6508_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2));
v___x_6509_ = lean_string_append(v___x_6507_, v___x_6508_);
return v___x_6509_;
}
else
{
lean_object* v_head_6510_; lean_object* v___x_6511_; lean_object* v___x_6512_; lean_object* v___x_6513_; uint32_t v___x_6514_; lean_object* v___x_6515_; 
v_head_6510_ = lean_ctor_get(v_x_6502_, 0);
v___x_6511_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1));
v___x_6512_ = lean_string_append(v___x_6511_, v_head_6510_);
v___x_6513_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(v___x_6512_, v_tail_6504_);
v___x_6514_ = 93;
v___x_6515_ = lean_string_push(v___x_6513_, v___x_6514_);
return v___x_6515_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___boxed(lean_object* v_x_6516_){
_start:
{
lean_object* v_res_6517_; 
v_res_6517_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v_x_6516_);
lean_dec(v_x_6516_);
return v_res_6517_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1(lean_object* v_weakArgs_6518_, lean_object* v_traceArgs_6519_, lean_object* v_oFile_6520_, lean_object* v_leanIncludeDir_x3f_6521_, lean_object* v_srcFile_6522_, lean_object* v___y_6523_, lean_object* v___y_6524_, lean_object* v___y_6525_, lean_object* v___y_6526_, lean_object* v___y_6527_, lean_object* v___y_6528_){
_start:
{
lean_object* v_log_6530_; uint8_t v_action_6531_; uint8_t v_wantsRebuild_6532_; lean_object* v_trace_6533_; lean_object* v_buildTime_6534_; lean_object* v___x_6536_; uint8_t v_isShared_6537_; uint8_t v_isSharedCheck_6591_; 
v_log_6530_ = lean_ctor_get(v___y_6528_, 0);
v_action_6531_ = lean_ctor_get_uint8(v___y_6528_, sizeof(void*)*3);
v_wantsRebuild_6532_ = lean_ctor_get_uint8(v___y_6528_, sizeof(void*)*3 + 1);
v_trace_6533_ = lean_ctor_get(v___y_6528_, 1);
v_buildTime_6534_ = lean_ctor_get(v___y_6528_, 2);
v_isSharedCheck_6591_ = !lean_is_exclusive(v___y_6528_);
if (v_isSharedCheck_6591_ == 0)
{
v___x_6536_ = v___y_6528_;
v_isShared_6537_ = v_isSharedCheck_6591_;
goto v_resetjp_6535_;
}
else
{
lean_inc(v_buildTime_6534_);
lean_inc(v_trace_6533_);
lean_inc(v_log_6530_);
lean_dec(v___y_6528_);
v___x_6536_ = lean_box(0);
v_isShared_6537_ = v_isSharedCheck_6591_;
goto v_resetjp_6535_;
}
v_resetjp_6535_:
{
lean_object* v_leanTrace_6538_; lean_object* v___f_6539_; lean_object* v___x_6540_; uint64_t v___y_6542_; uint64_t v___x_6580_; lean_object* v___x_6581_; lean_object* v___x_6582_; uint8_t v___x_6583_; 
v_leanTrace_6538_ = lean_ctor_get(v___y_6527_, 2);
lean_inc_ref(v_oFile_6520_);
lean_inc_ref(v_traceArgs_6519_);
v___f_6539_ = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__0___boxed), 12, 5);
lean_closure_set(v___f_6539_, 0, v_weakArgs_6518_);
lean_closure_set(v___f_6539_, 1, v_traceArgs_6519_);
lean_closure_set(v___f_6539_, 2, v_oFile_6520_);
lean_closure_set(v___f_6539_, 3, v_srcFile_6522_);
lean_closure_set(v___f_6539_, 4, v_leanIncludeDir_x3f_6521_);
lean_inc_ref(v_leanTrace_6538_);
v___x_6540_ = l_Lake_BuildTrace_mix(v_trace_6533_, v_leanTrace_6538_);
v___x_6580_ = l_Lake_Hash_nil;
v___x_6581_ = lean_unsigned_to_nat(0u);
v___x_6582_ = lean_array_get_size(v_traceArgs_6519_);
v___x_6583_ = lean_nat_dec_lt(v___x_6581_, v___x_6582_);
if (v___x_6583_ == 0)
{
v___y_6542_ = v___x_6580_;
goto v___jp_6541_;
}
else
{
uint8_t v___x_6584_; 
v___x_6584_ = lean_nat_dec_le(v___x_6582_, v___x_6582_);
if (v___x_6584_ == 0)
{
if (v___x_6583_ == 0)
{
v___y_6542_ = v___x_6580_;
goto v___jp_6541_;
}
else
{
size_t v___x_6585_; size_t v___x_6586_; uint64_t v___x_6587_; 
v___x_6585_ = ((size_t)0ULL);
v___x_6586_ = lean_usize_of_nat(v___x_6582_);
v___x_6587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_6519_, v___x_6585_, v___x_6586_, v___x_6580_);
v___y_6542_ = v___x_6587_;
goto v___jp_6541_;
}
}
else
{
size_t v___x_6588_; size_t v___x_6589_; uint64_t v___x_6590_; 
v___x_6588_ = ((size_t)0ULL);
v___x_6589_ = lean_usize_of_nat(v___x_6582_);
v___x_6590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_6519_, v___x_6588_, v___x_6589_, v___x_6580_);
v___y_6542_ = v___x_6590_;
goto v___jp_6541_;
}
}
v___jp_6541_:
{
lean_object* v___x_6543_; lean_object* v___x_6544_; lean_object* v___x_6545_; lean_object* v___x_6546_; lean_object* v___x_6547_; lean_object* v___x_6548_; lean_object* v___x_6549_; lean_object* v___x_6550_; lean_object* v___x_6551_; lean_object* v___x_6552_; lean_object* v___x_6553_; lean_object* v___x_6554_; lean_object* v___x_6556_; 
v___x_6543_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_6544_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_6545_ = lean_array_to_list(v_traceArgs_6519_);
v___x_6546_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_6545_);
lean_dec(v___x_6545_);
v___x_6547_ = lean_string_append(v___x_6544_, v___x_6546_);
lean_dec_ref(v___x_6546_);
v___x_6548_ = lean_string_append(v___x_6543_, v___x_6547_);
lean_dec_ref(v___x_6547_);
v___x_6549_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_6550_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_6551_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6551_, 0, v___x_6548_);
lean_ctor_set(v___x_6551_, 1, v___x_6549_);
lean_ctor_set(v___x_6551_, 2, v___x_6550_);
lean_ctor_set_uint64(v___x_6551_, sizeof(void*)*3, v___y_6542_);
v___x_6552_ = l_Lake_BuildTrace_mix(v___x_6540_, v___x_6551_);
v___x_6553_ = l_Lake_platformTrace;
v___x_6554_ = l_Lake_BuildTrace_mix(v___x_6552_, v___x_6553_);
if (v_isShared_6537_ == 0)
{
lean_ctor_set(v___x_6536_, 1, v___x_6554_);
v___x_6556_ = v___x_6536_;
goto v_reusejp_6555_;
}
else
{
lean_object* v_reuseFailAlloc_6579_; 
v_reuseFailAlloc_6579_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6579_, 0, v_log_6530_);
lean_ctor_set(v_reuseFailAlloc_6579_, 1, v___x_6554_);
lean_ctor_set(v_reuseFailAlloc_6579_, 2, v_buildTime_6534_);
lean_ctor_set_uint8(v_reuseFailAlloc_6579_, sizeof(void*)*3, v_action_6531_);
lean_ctor_set_uint8(v_reuseFailAlloc_6579_, sizeof(void*)*3 + 1, v_wantsRebuild_6532_);
v___x_6556_ = v_reuseFailAlloc_6579_;
goto v_reusejp_6555_;
}
v_reusejp_6555_:
{
uint8_t v___x_6557_; lean_object* v___x_6558_; lean_object* v___x_6559_; 
v___x_6557_ = 0;
v___x_6558_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
v___x_6559_ = l_Lake_buildArtifactUnlessUpToDate(v_oFile_6520_, v___f_6539_, v___x_6557_, v___x_6558_, v___x_6557_, v___x_6557_, v___y_6523_, v___y_6524_, v___y_6525_, v___y_6526_, v___y_6527_, v___x_6556_);
if (lean_obj_tag(v___x_6559_) == 0)
{
lean_object* v_a_6560_; lean_object* v_a_6561_; lean_object* v___x_6563_; uint8_t v_isShared_6564_; uint8_t v_isSharedCheck_6569_; 
v_a_6560_ = lean_ctor_get(v___x_6559_, 0);
v_a_6561_ = lean_ctor_get(v___x_6559_, 1);
v_isSharedCheck_6569_ = !lean_is_exclusive(v___x_6559_);
if (v_isSharedCheck_6569_ == 0)
{
v___x_6563_ = v___x_6559_;
v_isShared_6564_ = v_isSharedCheck_6569_;
goto v_resetjp_6562_;
}
else
{
lean_inc(v_a_6561_);
lean_inc(v_a_6560_);
lean_dec(v___x_6559_);
v___x_6563_ = lean_box(0);
v_isShared_6564_ = v_isSharedCheck_6569_;
goto v_resetjp_6562_;
}
v_resetjp_6562_:
{
lean_object* v_path_6565_; lean_object* v___x_6567_; 
v_path_6565_ = lean_ctor_get(v_a_6560_, 1);
lean_inc_ref(v_path_6565_);
lean_dec(v_a_6560_);
if (v_isShared_6564_ == 0)
{
lean_ctor_set(v___x_6563_, 0, v_path_6565_);
v___x_6567_ = v___x_6563_;
goto v_reusejp_6566_;
}
else
{
lean_object* v_reuseFailAlloc_6568_; 
v_reuseFailAlloc_6568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6568_, 0, v_path_6565_);
lean_ctor_set(v_reuseFailAlloc_6568_, 1, v_a_6561_);
v___x_6567_ = v_reuseFailAlloc_6568_;
goto v_reusejp_6566_;
}
v_reusejp_6566_:
{
return v___x_6567_;
}
}
}
else
{
lean_object* v_a_6570_; lean_object* v_a_6571_; lean_object* v___x_6573_; uint8_t v_isShared_6574_; uint8_t v_isSharedCheck_6578_; 
v_a_6570_ = lean_ctor_get(v___x_6559_, 0);
v_a_6571_ = lean_ctor_get(v___x_6559_, 1);
v_isSharedCheck_6578_ = !lean_is_exclusive(v___x_6559_);
if (v_isSharedCheck_6578_ == 0)
{
v___x_6573_ = v___x_6559_;
v_isShared_6574_ = v_isSharedCheck_6578_;
goto v_resetjp_6572_;
}
else
{
lean_inc(v_a_6571_);
lean_inc(v_a_6570_);
lean_dec(v___x_6559_);
v___x_6573_ = lean_box(0);
v_isShared_6574_ = v_isSharedCheck_6578_;
goto v_resetjp_6572_;
}
v_resetjp_6572_:
{
lean_object* v___x_6576_; 
if (v_isShared_6574_ == 0)
{
v___x_6576_ = v___x_6573_;
goto v_reusejp_6575_;
}
else
{
lean_object* v_reuseFailAlloc_6577_; 
v_reuseFailAlloc_6577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6577_, 0, v_a_6570_);
lean_ctor_set(v_reuseFailAlloc_6577_, 1, v_a_6571_);
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
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1___boxed(lean_object* v_weakArgs_6592_, lean_object* v_traceArgs_6593_, lean_object* v_oFile_6594_, lean_object* v_leanIncludeDir_x3f_6595_, lean_object* v_srcFile_6596_, lean_object* v___y_6597_, lean_object* v___y_6598_, lean_object* v___y_6599_, lean_object* v___y_6600_, lean_object* v___y_6601_, lean_object* v___y_6602_, lean_object* v___y_6603_){
_start:
{
lean_object* v_res_6604_; 
v_res_6604_ = l_Lake_buildLeanO___lam__1(v_weakArgs_6592_, v_traceArgs_6593_, v_oFile_6594_, v_leanIncludeDir_x3f_6595_, v_srcFile_6596_, v___y_6597_, v___y_6598_, v___y_6599_, v___y_6600_, v___y_6601_, v___y_6602_);
return v_res_6604_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object* v_oFile_6605_, lean_object* v_srcJob_6606_, lean_object* v_weakArgs_6607_, lean_object* v_traceArgs_6608_, lean_object* v_leanIncludeDir_x3f_6609_, lean_object* v_a_6610_, lean_object* v_a_6611_, lean_object* v_a_6612_, lean_object* v_a_6613_, lean_object* v_a_6614_, lean_object* v_a_6615_){
_start:
{
lean_object* v___f_6617_; lean_object* v___x_6618_; lean_object* v___x_6619_; uint8_t v___x_6620_; lean_object* v___x_6621_; 
v___f_6617_ = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__1___boxed), 12, 4);
lean_closure_set(v___f_6617_, 0, v_weakArgs_6607_);
lean_closure_set(v___f_6617_, 1, v_traceArgs_6608_);
lean_closure_set(v___f_6617_, 2, v_oFile_6605_);
lean_closure_set(v___f_6617_, 3, v_leanIncludeDir_x3f_6609_);
v___x_6618_ = l_Lake_instDataKindFilePath;
v___x_6619_ = lean_unsigned_to_nat(0u);
v___x_6620_ = 0;
v___x_6621_ = l_Lake_Job_mapM___redArg(v___x_6618_, v_srcJob_6606_, v___f_6617_, v___x_6619_, v___x_6620_, v_a_6610_, v_a_6611_, v_a_6612_, v_a_6613_, v_a_6614_, v_a_6615_);
return v___x_6621_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___boxed(lean_object* v_oFile_6622_, lean_object* v_srcJob_6623_, lean_object* v_weakArgs_6624_, lean_object* v_traceArgs_6625_, lean_object* v_leanIncludeDir_x3f_6626_, lean_object* v_a_6627_, lean_object* v_a_6628_, lean_object* v_a_6629_, lean_object* v_a_6630_, lean_object* v_a_6631_, lean_object* v_a_6632_, lean_object* v_a_6633_){
_start:
{
lean_object* v_res_6634_; 
v_res_6634_ = l_Lake_buildLeanO(v_oFile_6622_, v_srcJob_6623_, v_weakArgs_6624_, v_traceArgs_6625_, v_leanIncludeDir_x3f_6626_, v_a_6627_, v_a_6628_, v_a_6629_, v_a_6630_, v_a_6631_, v_a_6632_);
return v_res_6634_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0(lean_object* v_libFile_6635_, lean_object* v_oFiles_6636_, uint8_t v_thin_6637_, lean_object* v___y_6638_, lean_object* v___y_6639_, lean_object* v___y_6640_, lean_object* v___y_6641_, lean_object* v___y_6642_, lean_object* v___y_6643_){
_start:
{
lean_object* v_toContext_6645_; lean_object* v_lakeEnv_6646_; lean_object* v_lean_6647_; lean_object* v_log_6648_; uint8_t v_action_6649_; uint8_t v_wantsRebuild_6650_; lean_object* v_trace_6651_; lean_object* v_buildTime_6652_; lean_object* v___x_6654_; uint8_t v_isShared_6655_; uint8_t v_isSharedCheck_6682_; 
v_toContext_6645_ = lean_ctor_get(v___y_6642_, 1);
lean_inc(v_toContext_6645_);
lean_dec_ref(v___y_6642_);
v_lakeEnv_6646_ = lean_ctor_get(v_toContext_6645_, 1);
lean_inc_ref(v_lakeEnv_6646_);
lean_dec(v_toContext_6645_);
v_lean_6647_ = lean_ctor_get(v_lakeEnv_6646_, 1);
lean_inc_ref(v_lean_6647_);
lean_dec_ref(v_lakeEnv_6646_);
v_log_6648_ = lean_ctor_get(v___y_6643_, 0);
v_action_6649_ = lean_ctor_get_uint8(v___y_6643_, sizeof(void*)*3);
v_wantsRebuild_6650_ = lean_ctor_get_uint8(v___y_6643_, sizeof(void*)*3 + 1);
v_trace_6651_ = lean_ctor_get(v___y_6643_, 1);
v_buildTime_6652_ = lean_ctor_get(v___y_6643_, 2);
v_isSharedCheck_6682_ = !lean_is_exclusive(v___y_6643_);
if (v_isSharedCheck_6682_ == 0)
{
v___x_6654_ = v___y_6643_;
v_isShared_6655_ = v_isSharedCheck_6682_;
goto v_resetjp_6653_;
}
else
{
lean_inc(v_buildTime_6652_);
lean_inc(v_trace_6651_);
lean_inc(v_log_6648_);
lean_dec(v___y_6643_);
v___x_6654_ = lean_box(0);
v_isShared_6655_ = v_isSharedCheck_6682_;
goto v_resetjp_6653_;
}
v_resetjp_6653_:
{
lean_object* v_ar_6656_; lean_object* v___x_6657_; 
v_ar_6656_ = lean_ctor_get(v_lean_6647_, 12);
lean_inc_ref(v_ar_6656_);
lean_dec_ref(v_lean_6647_);
v___x_6657_ = l_Lake_compileStaticLib(v_libFile_6635_, v_oFiles_6636_, v_ar_6656_, v_thin_6637_, v_log_6648_);
if (lean_obj_tag(v___x_6657_) == 0)
{
lean_object* v_a_6658_; lean_object* v_a_6659_; lean_object* v___x_6661_; uint8_t v_isShared_6662_; uint8_t v_isSharedCheck_6669_; 
v_a_6658_ = lean_ctor_get(v___x_6657_, 0);
v_a_6659_ = lean_ctor_get(v___x_6657_, 1);
v_isSharedCheck_6669_ = !lean_is_exclusive(v___x_6657_);
if (v_isSharedCheck_6669_ == 0)
{
v___x_6661_ = v___x_6657_;
v_isShared_6662_ = v_isSharedCheck_6669_;
goto v_resetjp_6660_;
}
else
{
lean_inc(v_a_6659_);
lean_inc(v_a_6658_);
lean_dec(v___x_6657_);
v___x_6661_ = lean_box(0);
v_isShared_6662_ = v_isSharedCheck_6669_;
goto v_resetjp_6660_;
}
v_resetjp_6660_:
{
lean_object* v___x_6664_; 
if (v_isShared_6655_ == 0)
{
lean_ctor_set(v___x_6654_, 0, v_a_6659_);
v___x_6664_ = v___x_6654_;
goto v_reusejp_6663_;
}
else
{
lean_object* v_reuseFailAlloc_6668_; 
v_reuseFailAlloc_6668_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6668_, 0, v_a_6659_);
lean_ctor_set(v_reuseFailAlloc_6668_, 1, v_trace_6651_);
lean_ctor_set(v_reuseFailAlloc_6668_, 2, v_buildTime_6652_);
lean_ctor_set_uint8(v_reuseFailAlloc_6668_, sizeof(void*)*3, v_action_6649_);
lean_ctor_set_uint8(v_reuseFailAlloc_6668_, sizeof(void*)*3 + 1, v_wantsRebuild_6650_);
v___x_6664_ = v_reuseFailAlloc_6668_;
goto v_reusejp_6663_;
}
v_reusejp_6663_:
{
lean_object* v___x_6666_; 
if (v_isShared_6662_ == 0)
{
lean_ctor_set(v___x_6661_, 1, v___x_6664_);
v___x_6666_ = v___x_6661_;
goto v_reusejp_6665_;
}
else
{
lean_object* v_reuseFailAlloc_6667_; 
v_reuseFailAlloc_6667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6667_, 0, v_a_6658_);
lean_ctor_set(v_reuseFailAlloc_6667_, 1, v___x_6664_);
v___x_6666_ = v_reuseFailAlloc_6667_;
goto v_reusejp_6665_;
}
v_reusejp_6665_:
{
return v___x_6666_;
}
}
}
}
else
{
lean_object* v_a_6670_; lean_object* v_a_6671_; lean_object* v___x_6673_; uint8_t v_isShared_6674_; uint8_t v_isSharedCheck_6681_; 
v_a_6670_ = lean_ctor_get(v___x_6657_, 0);
v_a_6671_ = lean_ctor_get(v___x_6657_, 1);
v_isSharedCheck_6681_ = !lean_is_exclusive(v___x_6657_);
if (v_isSharedCheck_6681_ == 0)
{
v___x_6673_ = v___x_6657_;
v_isShared_6674_ = v_isSharedCheck_6681_;
goto v_resetjp_6672_;
}
else
{
lean_inc(v_a_6671_);
lean_inc(v_a_6670_);
lean_dec(v___x_6657_);
v___x_6673_ = lean_box(0);
v_isShared_6674_ = v_isSharedCheck_6681_;
goto v_resetjp_6672_;
}
v_resetjp_6672_:
{
lean_object* v___x_6676_; 
if (v_isShared_6655_ == 0)
{
lean_ctor_set(v___x_6654_, 0, v_a_6671_);
v___x_6676_ = v___x_6654_;
goto v_reusejp_6675_;
}
else
{
lean_object* v_reuseFailAlloc_6680_; 
v_reuseFailAlloc_6680_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6680_, 0, v_a_6671_);
lean_ctor_set(v_reuseFailAlloc_6680_, 1, v_trace_6651_);
lean_ctor_set(v_reuseFailAlloc_6680_, 2, v_buildTime_6652_);
lean_ctor_set_uint8(v_reuseFailAlloc_6680_, sizeof(void*)*3, v_action_6649_);
lean_ctor_set_uint8(v_reuseFailAlloc_6680_, sizeof(void*)*3 + 1, v_wantsRebuild_6650_);
v___x_6676_ = v_reuseFailAlloc_6680_;
goto v_reusejp_6675_;
}
v_reusejp_6675_:
{
lean_object* v___x_6678_; 
if (v_isShared_6674_ == 0)
{
lean_ctor_set(v___x_6673_, 1, v___x_6676_);
v___x_6678_ = v___x_6673_;
goto v_reusejp_6677_;
}
else
{
lean_object* v_reuseFailAlloc_6679_; 
v_reuseFailAlloc_6679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6679_, 0, v_a_6670_);
lean_ctor_set(v_reuseFailAlloc_6679_, 1, v___x_6676_);
v___x_6678_ = v_reuseFailAlloc_6679_;
goto v_reusejp_6677_;
}
v_reusejp_6677_:
{
return v___x_6678_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0___boxed(lean_object* v_libFile_6683_, lean_object* v_oFiles_6684_, lean_object* v_thin_6685_, lean_object* v___y_6686_, lean_object* v___y_6687_, lean_object* v___y_6688_, lean_object* v___y_6689_, lean_object* v___y_6690_, lean_object* v___y_6691_, lean_object* v___y_6692_){
_start:
{
uint8_t v_thin_boxed_6693_; lean_object* v_res_6694_; 
v_thin_boxed_6693_ = lean_unbox(v_thin_6685_);
v_res_6694_ = l_Lake_buildStaticLib___lam__0(v_libFile_6683_, v_oFiles_6684_, v_thin_boxed_6693_, v___y_6686_, v___y_6687_, v___y_6688_, v___y_6689_, v___y_6690_, v___y_6691_);
lean_dec(v___y_6689_);
lean_dec(v___y_6688_);
lean_dec(v___y_6687_);
lean_dec_ref(v___y_6686_);
return v_res_6694_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1(lean_object* v_libFile_6696_, uint8_t v_thin_6697_, lean_object* v_oFiles_6698_, lean_object* v___y_6699_, lean_object* v___y_6700_, lean_object* v___y_6701_, lean_object* v___y_6702_, lean_object* v___y_6703_, lean_object* v___y_6704_){
_start:
{
lean_object* v___x_6706_; lean_object* v___f_6707_; uint8_t v___x_6708_; lean_object* v___x_6709_; uint8_t v___x_6710_; lean_object* v___x_6711_; 
v___x_6706_ = lean_box(v_thin_6697_);
lean_inc_ref(v_libFile_6696_);
v___f_6707_ = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6707_, 0, v_libFile_6696_);
lean_closure_set(v___f_6707_, 1, v_oFiles_6698_);
lean_closure_set(v___f_6707_, 2, v___x_6706_);
v___x_6708_ = 0;
v___x_6709_ = ((lean_object*)(l_Lake_buildStaticLib___lam__1___closed__0));
v___x_6710_ = 1;
v___x_6711_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_6696_, v___f_6707_, v___x_6708_, v___x_6709_, v___x_6710_, v___x_6708_, v___y_6699_, v___y_6700_, v___y_6701_, v___y_6702_, v___y_6703_, v___y_6704_);
if (lean_obj_tag(v___x_6711_) == 0)
{
lean_object* v_a_6712_; lean_object* v_a_6713_; lean_object* v___x_6715_; uint8_t v_isShared_6716_; uint8_t v_isSharedCheck_6721_; 
v_a_6712_ = lean_ctor_get(v___x_6711_, 0);
v_a_6713_ = lean_ctor_get(v___x_6711_, 1);
v_isSharedCheck_6721_ = !lean_is_exclusive(v___x_6711_);
if (v_isSharedCheck_6721_ == 0)
{
v___x_6715_ = v___x_6711_;
v_isShared_6716_ = v_isSharedCheck_6721_;
goto v_resetjp_6714_;
}
else
{
lean_inc(v_a_6713_);
lean_inc(v_a_6712_);
lean_dec(v___x_6711_);
v___x_6715_ = lean_box(0);
v_isShared_6716_ = v_isSharedCheck_6721_;
goto v_resetjp_6714_;
}
v_resetjp_6714_:
{
lean_object* v_path_6717_; lean_object* v___x_6719_; 
v_path_6717_ = lean_ctor_get(v_a_6712_, 1);
lean_inc_ref(v_path_6717_);
lean_dec(v_a_6712_);
if (v_isShared_6716_ == 0)
{
lean_ctor_set(v___x_6715_, 0, v_path_6717_);
v___x_6719_ = v___x_6715_;
goto v_reusejp_6718_;
}
else
{
lean_object* v_reuseFailAlloc_6720_; 
v_reuseFailAlloc_6720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6720_, 0, v_path_6717_);
lean_ctor_set(v_reuseFailAlloc_6720_, 1, v_a_6713_);
v___x_6719_ = v_reuseFailAlloc_6720_;
goto v_reusejp_6718_;
}
v_reusejp_6718_:
{
return v___x_6719_;
}
}
}
else
{
lean_object* v_a_6722_; lean_object* v_a_6723_; lean_object* v___x_6725_; uint8_t v_isShared_6726_; uint8_t v_isSharedCheck_6730_; 
v_a_6722_ = lean_ctor_get(v___x_6711_, 0);
v_a_6723_ = lean_ctor_get(v___x_6711_, 1);
v_isSharedCheck_6730_ = !lean_is_exclusive(v___x_6711_);
if (v_isSharedCheck_6730_ == 0)
{
v___x_6725_ = v___x_6711_;
v_isShared_6726_ = v_isSharedCheck_6730_;
goto v_resetjp_6724_;
}
else
{
lean_inc(v_a_6723_);
lean_inc(v_a_6722_);
lean_dec(v___x_6711_);
v___x_6725_ = lean_box(0);
v_isShared_6726_ = v_isSharedCheck_6730_;
goto v_resetjp_6724_;
}
v_resetjp_6724_:
{
lean_object* v___x_6728_; 
if (v_isShared_6726_ == 0)
{
v___x_6728_ = v___x_6725_;
goto v_reusejp_6727_;
}
else
{
lean_object* v_reuseFailAlloc_6729_; 
v_reuseFailAlloc_6729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6729_, 0, v_a_6722_);
lean_ctor_set(v_reuseFailAlloc_6729_, 1, v_a_6723_);
v___x_6728_ = v_reuseFailAlloc_6729_;
goto v_reusejp_6727_;
}
v_reusejp_6727_:
{
return v___x_6728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1___boxed(lean_object* v_libFile_6731_, lean_object* v_thin_6732_, lean_object* v_oFiles_6733_, lean_object* v___y_6734_, lean_object* v___y_6735_, lean_object* v___y_6736_, lean_object* v___y_6737_, lean_object* v___y_6738_, lean_object* v___y_6739_, lean_object* v___y_6740_){
_start:
{
uint8_t v_thin_boxed_6741_; lean_object* v_res_6742_; 
v_thin_boxed_6741_ = lean_unbox(v_thin_6732_);
v_res_6742_ = l_Lake_buildStaticLib___lam__1(v_libFile_6731_, v_thin_boxed_6741_, v_oFiles_6733_, v___y_6734_, v___y_6735_, v___y_6736_, v___y_6737_, v___y_6738_, v___y_6739_);
return v_res_6742_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object* v_libFile_6744_, lean_object* v_oFileJobs_6745_, uint8_t v_thin_6746_, lean_object* v_a_6747_, lean_object* v_a_6748_, lean_object* v_a_6749_, lean_object* v_a_6750_, lean_object* v_a_6751_, lean_object* v_a_6752_){
_start:
{
lean_object* v___x_6754_; lean_object* v___f_6755_; lean_object* v___x_6756_; lean_object* v___x_6757_; lean_object* v___x_6758_; lean_object* v___x_6759_; uint8_t v___x_6760_; lean_object* v___x_6761_; 
v___x_6754_ = lean_box(v_thin_6746_);
v___f_6755_ = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__1___boxed), 10, 2);
lean_closure_set(v___f_6755_, 0, v_libFile_6744_);
lean_closure_set(v___f_6755_, 1, v___x_6754_);
v___x_6756_ = l_Lake_instDataKindFilePath;
v___x_6757_ = ((lean_object*)(l_Lake_buildStaticLib___closed__0));
v___x_6758_ = l_Lake_Job_collectArray___redArg(v_oFileJobs_6745_, v___x_6757_);
v___x_6759_ = lean_unsigned_to_nat(0u);
v___x_6760_ = 0;
v___x_6761_ = l_Lake_Job_mapM___redArg(v___x_6756_, v___x_6758_, v___f_6755_, v___x_6759_, v___x_6760_, v_a_6747_, v_a_6748_, v_a_6749_, v_a_6750_, v_a_6751_, v_a_6752_);
return v___x_6761_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object* v_libFile_6762_, lean_object* v_oFileJobs_6763_, lean_object* v_thin_6764_, lean_object* v_a_6765_, lean_object* v_a_6766_, lean_object* v_a_6767_, lean_object* v_a_6768_, lean_object* v_a_6769_, lean_object* v_a_6770_, lean_object* v_a_6771_){
_start:
{
uint8_t v_thin_boxed_6772_; lean_object* v_res_6773_; 
v_thin_boxed_6772_ = lean_unbox(v_thin_6764_);
v_res_6773_ = l_Lake_buildStaticLib(v_libFile_6762_, v_oFileJobs_6763_, v_thin_boxed_6772_, v_a_6765_, v_a_6766_, v_a_6767_, v_a_6768_, v_a_6769_, v_a_6770_);
lean_dec_ref(v_oFileJobs_6763_);
return v_res_6773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(lean_object* v_as_6774_, size_t v_sz_6775_, size_t v_i_6776_, lean_object* v_b_6777_){
_start:
{
uint8_t v___x_6778_; 
v___x_6778_ = lean_usize_dec_lt(v_i_6776_, v_sz_6775_);
if (v___x_6778_ == 0)
{
return v_b_6777_;
}
else
{
lean_object* v_a_6779_; lean_object* v___x_6780_; size_t v___x_6781_; size_t v___x_6782_; 
v_a_6779_ = lean_array_uget_borrowed(v_as_6774_, v_i_6776_);
lean_inc(v_a_6779_);
v___x_6780_ = lean_array_push(v_b_6777_, v_a_6779_);
v___x_6781_ = ((size_t)1ULL);
v___x_6782_ = lean_usize_add(v_i_6776_, v___x_6781_);
v_i_6776_ = v___x_6782_;
v_b_6777_ = v___x_6780_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0___boxed(lean_object* v_as_6784_, lean_object* v_sz_6785_, lean_object* v_i_6786_, lean_object* v_b_6787_){
_start:
{
size_t v_sz_boxed_6788_; size_t v_i_boxed_6789_; lean_object* v_res_6790_; 
v_sz_boxed_6788_ = lean_unbox_usize(v_sz_6785_);
lean_dec(v_sz_6785_);
v_i_boxed_6789_ = lean_unbox_usize(v_i_6786_);
lean_dec(v_i_6786_);
v_res_6790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(v_as_6784_, v_sz_boxed_6788_, v_i_boxed_6789_, v_b_6787_);
lean_dec_ref(v_as_6784_);
return v_res_6790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(lean_object* v_as_6793_, size_t v_sz_6794_, size_t v_i_6795_, lean_object* v_b_6796_){
_start:
{
uint8_t v___x_6797_; 
v___x_6797_ = lean_usize_dec_lt(v_i_6795_, v_sz_6794_);
if (v___x_6797_ == 0)
{
return v_b_6796_;
}
else
{
lean_object* v_a_6798_; lean_object* v_args_6800_; lean_object* v___x_6808_; 
v_a_6798_ = lean_array_uget_borrowed(v_as_6793_, v_i_6795_);
lean_inc(v_a_6798_);
v___x_6808_ = l_Lake_Dynlib_dir_x3f(v_a_6798_);
if (lean_obj_tag(v___x_6808_) == 1)
{
lean_object* v_val_6809_; lean_object* v___x_6810_; lean_object* v___x_6811_; lean_object* v___x_6812_; 
v_val_6809_ = lean_ctor_get(v___x_6808_, 0);
lean_inc(v_val_6809_);
lean_dec_ref(v___x_6808_);
v___x_6810_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
v___x_6811_ = lean_string_append(v___x_6810_, v_val_6809_);
lean_dec(v_val_6809_);
v___x_6812_ = lean_array_push(v_b_6796_, v___x_6811_);
v_args_6800_ = v___x_6812_;
goto v___jp_6799_;
}
else
{
lean_dec(v___x_6808_);
v_args_6800_ = v_b_6796_;
goto v___jp_6799_;
}
v___jp_6799_:
{
lean_object* v_name_6801_; lean_object* v___x_6802_; lean_object* v___x_6803_; lean_object* v___x_6804_; size_t v___x_6805_; size_t v___x_6806_; 
v_name_6801_ = lean_ctor_get(v_a_6798_, 1);
v___x_6802_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0));
v___x_6803_ = lean_string_append(v___x_6802_, v_name_6801_);
v___x_6804_ = lean_array_push(v_args_6800_, v___x_6803_);
v___x_6805_ = ((size_t)1ULL);
v___x_6806_ = lean_usize_add(v_i_6795_, v___x_6805_);
v_i_6795_ = v___x_6806_;
v_b_6796_ = v___x_6804_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___boxed(lean_object* v_as_6813_, lean_object* v_sz_6814_, lean_object* v_i_6815_, lean_object* v_b_6816_){
_start:
{
size_t v_sz_boxed_6817_; size_t v_i_boxed_6818_; lean_object* v_res_6819_; 
v_sz_boxed_6817_ = lean_unbox_usize(v_sz_6814_);
lean_dec(v_sz_6814_);
v_i_boxed_6818_ = lean_unbox_usize(v_i_6815_);
lean_dec(v_i_6815_);
v_res_6819_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(v_as_6813_, v_sz_boxed_6817_, v_i_boxed_6818_, v_b_6816_);
lean_dec_ref(v_as_6813_);
return v_res_6819_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(lean_object* v_objs_6820_, lean_object* v_libs_6821_){
_start:
{
lean_object* v_args_6822_; size_t v_sz_6823_; size_t v___x_6824_; lean_object* v___x_6825_; size_t v_sz_6826_; lean_object* v___x_6827_; 
v_args_6822_ = ((lean_object*)(l_Lake_inputDir___lam__1___closed__0));
v_sz_6823_ = lean_array_size(v_objs_6820_);
v___x_6824_ = ((size_t)0ULL);
v___x_6825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(v_objs_6820_, v_sz_6823_, v___x_6824_, v_args_6822_);
v_sz_6826_ = lean_array_size(v_libs_6821_);
v___x_6827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(v_libs_6821_, v_sz_6826_, v___x_6824_, v___x_6825_);
return v___x_6827_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs___boxed(lean_object* v_objs_6828_, lean_object* v_libs_6829_){
_start:
{
lean_object* v_res_6830_; 
v_res_6830_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_6828_, v_libs_6829_);
lean_dec_ref(v_libs_6829_);
lean_dec_ref(v_objs_6828_);
return v_res_6830_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(lean_object* v_k_6831_, lean_object* v_t_6832_){
_start:
{
if (lean_obj_tag(v_t_6832_) == 0)
{
lean_object* v_k_6833_; lean_object* v_l_6834_; lean_object* v_r_6835_; uint8_t v___x_6836_; 
v_k_6833_ = lean_ctor_get(v_t_6832_, 1);
v_l_6834_ = lean_ctor_get(v_t_6832_, 3);
v_r_6835_ = lean_ctor_get(v_t_6832_, 4);
v___x_6836_ = lean_string_dec_lt(v_k_6831_, v_k_6833_);
if (v___x_6836_ == 0)
{
uint8_t v___x_6837_; 
v___x_6837_ = lean_string_dec_eq(v_k_6831_, v_k_6833_);
if (v___x_6837_ == 0)
{
v_t_6832_ = v_r_6835_;
goto _start;
}
else
{
return v___x_6837_;
}
}
else
{
v_t_6832_ = v_l_6834_;
goto _start;
}
}
else
{
uint8_t v___x_6840_; 
v___x_6840_ = 0;
return v___x_6840_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg___boxed(lean_object* v_k_6841_, lean_object* v_t_6842_){
_start:
{
uint8_t v_res_6843_; lean_object* v_r_6844_; 
v_res_6843_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_k_6841_, v_t_6842_);
lean_dec(v_t_6842_);
lean_dec_ref(v_k_6841_);
v_r_6844_ = lean_box(v_res_6843_);
return v_r_6844_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(lean_object* v_a_6845_, lean_object* v_x_6846_){
_start:
{
if (lean_obj_tag(v_x_6846_) == 0)
{
uint8_t v___x_6847_; 
v___x_6847_ = 0;
return v___x_6847_;
}
else
{
lean_object* v_head_6848_; lean_object* v_tail_6849_; uint8_t v___x_6850_; 
v_head_6848_ = lean_ctor_get(v_x_6846_, 0);
v_tail_6849_ = lean_ctor_get(v_x_6846_, 1);
v___x_6850_ = lean_string_dec_eq(v_a_6845_, v_head_6848_);
if (v___x_6850_ == 0)
{
v_x_6846_ = v_tail_6849_;
goto _start;
}
else
{
return v___x_6850_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1___boxed(lean_object* v_a_6852_, lean_object* v_x_6853_){
_start:
{
uint8_t v_res_6854_; lean_object* v_r_6855_; 
v_res_6854_ = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(v_a_6852_, v_x_6853_);
lean_dec(v_x_6853_);
lean_dec_ref(v_a_6852_);
v_r_6855_ = lean_box(v_res_6854_);
return v_r_6855_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(lean_object* v_k_6856_, lean_object* v_v_6857_, lean_object* v_t_6858_){
_start:
{
if (lean_obj_tag(v_t_6858_) == 0)
{
lean_object* v_size_6859_; lean_object* v_k_6860_; lean_object* v_v_6861_; lean_object* v_l_6862_; lean_object* v_r_6863_; lean_object* v___x_6865_; uint8_t v_isShared_6866_; uint8_t v_isSharedCheck_7144_; 
v_size_6859_ = lean_ctor_get(v_t_6858_, 0);
v_k_6860_ = lean_ctor_get(v_t_6858_, 1);
v_v_6861_ = lean_ctor_get(v_t_6858_, 2);
v_l_6862_ = lean_ctor_get(v_t_6858_, 3);
v_r_6863_ = lean_ctor_get(v_t_6858_, 4);
v_isSharedCheck_7144_ = !lean_is_exclusive(v_t_6858_);
if (v_isSharedCheck_7144_ == 0)
{
v___x_6865_ = v_t_6858_;
v_isShared_6866_ = v_isSharedCheck_7144_;
goto v_resetjp_6864_;
}
else
{
lean_inc(v_r_6863_);
lean_inc(v_l_6862_);
lean_inc(v_v_6861_);
lean_inc(v_k_6860_);
lean_inc(v_size_6859_);
lean_dec(v_t_6858_);
v___x_6865_ = lean_box(0);
v_isShared_6866_ = v_isSharedCheck_7144_;
goto v_resetjp_6864_;
}
v_resetjp_6864_:
{
uint8_t v___x_6867_; 
v___x_6867_ = lean_string_dec_lt(v_k_6856_, v_k_6860_);
if (v___x_6867_ == 0)
{
uint8_t v___x_6868_; 
v___x_6868_ = lean_string_dec_eq(v_k_6856_, v_k_6860_);
if (v___x_6868_ == 0)
{
lean_object* v_impl_6869_; lean_object* v___x_6870_; 
lean_dec(v_size_6859_);
v_impl_6869_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_6856_, v_v_6857_, v_r_6863_);
v___x_6870_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_6862_) == 0)
{
lean_object* v_size_6871_; lean_object* v_size_6872_; lean_object* v_k_6873_; lean_object* v_v_6874_; lean_object* v_l_6875_; lean_object* v_r_6876_; lean_object* v___x_6877_; lean_object* v___x_6878_; uint8_t v___x_6879_; 
v_size_6871_ = lean_ctor_get(v_l_6862_, 0);
v_size_6872_ = lean_ctor_get(v_impl_6869_, 0);
lean_inc(v_size_6872_);
v_k_6873_ = lean_ctor_get(v_impl_6869_, 1);
lean_inc(v_k_6873_);
v_v_6874_ = lean_ctor_get(v_impl_6869_, 2);
lean_inc(v_v_6874_);
v_l_6875_ = lean_ctor_get(v_impl_6869_, 3);
lean_inc(v_l_6875_);
v_r_6876_ = lean_ctor_get(v_impl_6869_, 4);
lean_inc(v_r_6876_);
v___x_6877_ = lean_unsigned_to_nat(3u);
v___x_6878_ = lean_nat_mul(v___x_6877_, v_size_6871_);
v___x_6879_ = lean_nat_dec_lt(v___x_6878_, v_size_6872_);
lean_dec(v___x_6878_);
if (v___x_6879_ == 0)
{
lean_object* v___x_6880_; lean_object* v___x_6881_; lean_object* v___x_6883_; 
lean_dec(v_r_6876_);
lean_dec(v_l_6875_);
lean_dec(v_v_6874_);
lean_dec(v_k_6873_);
v___x_6880_ = lean_nat_add(v___x_6870_, v_size_6871_);
v___x_6881_ = lean_nat_add(v___x_6880_, v_size_6872_);
lean_dec(v_size_6872_);
lean_dec(v___x_6880_);
if (v_isShared_6866_ == 0)
{
lean_ctor_set(v___x_6865_, 4, v_impl_6869_);
lean_ctor_set(v___x_6865_, 0, v___x_6881_);
v___x_6883_ = v___x_6865_;
goto v_reusejp_6882_;
}
else
{
lean_object* v_reuseFailAlloc_6884_; 
v_reuseFailAlloc_6884_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6884_, 0, v___x_6881_);
lean_ctor_set(v_reuseFailAlloc_6884_, 1, v_k_6860_);
lean_ctor_set(v_reuseFailAlloc_6884_, 2, v_v_6861_);
lean_ctor_set(v_reuseFailAlloc_6884_, 3, v_l_6862_);
lean_ctor_set(v_reuseFailAlloc_6884_, 4, v_impl_6869_);
v___x_6883_ = v_reuseFailAlloc_6884_;
goto v_reusejp_6882_;
}
v_reusejp_6882_:
{
return v___x_6883_;
}
}
else
{
lean_object* v___x_6886_; uint8_t v_isShared_6887_; uint8_t v_isSharedCheck_6948_; 
v_isSharedCheck_6948_ = !lean_is_exclusive(v_impl_6869_);
if (v_isSharedCheck_6948_ == 0)
{
lean_object* v_unused_6949_; lean_object* v_unused_6950_; lean_object* v_unused_6951_; lean_object* v_unused_6952_; lean_object* v_unused_6953_; 
v_unused_6949_ = lean_ctor_get(v_impl_6869_, 4);
lean_dec(v_unused_6949_);
v_unused_6950_ = lean_ctor_get(v_impl_6869_, 3);
lean_dec(v_unused_6950_);
v_unused_6951_ = lean_ctor_get(v_impl_6869_, 2);
lean_dec(v_unused_6951_);
v_unused_6952_ = lean_ctor_get(v_impl_6869_, 1);
lean_dec(v_unused_6952_);
v_unused_6953_ = lean_ctor_get(v_impl_6869_, 0);
lean_dec(v_unused_6953_);
v___x_6886_ = v_impl_6869_;
v_isShared_6887_ = v_isSharedCheck_6948_;
goto v_resetjp_6885_;
}
else
{
lean_dec(v_impl_6869_);
v___x_6886_ = lean_box(0);
v_isShared_6887_ = v_isSharedCheck_6948_;
goto v_resetjp_6885_;
}
v_resetjp_6885_:
{
lean_object* v_size_6888_; lean_object* v_k_6889_; lean_object* v_v_6890_; lean_object* v_l_6891_; lean_object* v_r_6892_; lean_object* v_size_6893_; lean_object* v___x_6894_; lean_object* v___x_6895_; uint8_t v___x_6896_; 
v_size_6888_ = lean_ctor_get(v_l_6875_, 0);
v_k_6889_ = lean_ctor_get(v_l_6875_, 1);
v_v_6890_ = lean_ctor_get(v_l_6875_, 2);
v_l_6891_ = lean_ctor_get(v_l_6875_, 3);
v_r_6892_ = lean_ctor_get(v_l_6875_, 4);
v_size_6893_ = lean_ctor_get(v_r_6876_, 0);
v___x_6894_ = lean_unsigned_to_nat(2u);
v___x_6895_ = lean_nat_mul(v___x_6894_, v_size_6893_);
v___x_6896_ = lean_nat_dec_lt(v_size_6888_, v___x_6895_);
lean_dec(v___x_6895_);
if (v___x_6896_ == 0)
{
lean_object* v___x_6898_; uint8_t v_isShared_6899_; uint8_t v_isSharedCheck_6924_; 
lean_inc(v_r_6892_);
lean_inc(v_l_6891_);
lean_inc(v_v_6890_);
lean_inc(v_k_6889_);
v_isSharedCheck_6924_ = !lean_is_exclusive(v_l_6875_);
if (v_isSharedCheck_6924_ == 0)
{
lean_object* v_unused_6925_; lean_object* v_unused_6926_; lean_object* v_unused_6927_; lean_object* v_unused_6928_; lean_object* v_unused_6929_; 
v_unused_6925_ = lean_ctor_get(v_l_6875_, 4);
lean_dec(v_unused_6925_);
v_unused_6926_ = lean_ctor_get(v_l_6875_, 3);
lean_dec(v_unused_6926_);
v_unused_6927_ = lean_ctor_get(v_l_6875_, 2);
lean_dec(v_unused_6927_);
v_unused_6928_ = lean_ctor_get(v_l_6875_, 1);
lean_dec(v_unused_6928_);
v_unused_6929_ = lean_ctor_get(v_l_6875_, 0);
lean_dec(v_unused_6929_);
v___x_6898_ = v_l_6875_;
v_isShared_6899_ = v_isSharedCheck_6924_;
goto v_resetjp_6897_;
}
else
{
lean_dec(v_l_6875_);
v___x_6898_ = lean_box(0);
v_isShared_6899_ = v_isSharedCheck_6924_;
goto v_resetjp_6897_;
}
v_resetjp_6897_:
{
lean_object* v___x_6900_; lean_object* v___x_6901_; lean_object* v___y_6903_; lean_object* v___y_6904_; lean_object* v___y_6905_; lean_object* v___y_6914_; 
v___x_6900_ = lean_nat_add(v___x_6870_, v_size_6871_);
v___x_6901_ = lean_nat_add(v___x_6900_, v_size_6872_);
lean_dec(v_size_6872_);
if (lean_obj_tag(v_l_6891_) == 0)
{
lean_object* v_size_6922_; 
v_size_6922_ = lean_ctor_get(v_l_6891_, 0);
lean_inc(v_size_6922_);
v___y_6914_ = v_size_6922_;
goto v___jp_6913_;
}
else
{
lean_object* v___x_6923_; 
v___x_6923_ = lean_unsigned_to_nat(0u);
v___y_6914_ = v___x_6923_;
goto v___jp_6913_;
}
v___jp_6902_:
{
lean_object* v___x_6906_; lean_object* v___x_6908_; 
v___x_6906_ = lean_nat_add(v___y_6904_, v___y_6905_);
lean_dec(v___y_6905_);
lean_dec(v___y_6904_);
if (v_isShared_6899_ == 0)
{
lean_ctor_set(v___x_6898_, 4, v_r_6876_);
lean_ctor_set(v___x_6898_, 3, v_r_6892_);
lean_ctor_set(v___x_6898_, 2, v_v_6874_);
lean_ctor_set(v___x_6898_, 1, v_k_6873_);
lean_ctor_set(v___x_6898_, 0, v___x_6906_);
v___x_6908_ = v___x_6898_;
goto v_reusejp_6907_;
}
else
{
lean_object* v_reuseFailAlloc_6912_; 
v_reuseFailAlloc_6912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6912_, 0, v___x_6906_);
lean_ctor_set(v_reuseFailAlloc_6912_, 1, v_k_6873_);
lean_ctor_set(v_reuseFailAlloc_6912_, 2, v_v_6874_);
lean_ctor_set(v_reuseFailAlloc_6912_, 3, v_r_6892_);
lean_ctor_set(v_reuseFailAlloc_6912_, 4, v_r_6876_);
v___x_6908_ = v_reuseFailAlloc_6912_;
goto v_reusejp_6907_;
}
v_reusejp_6907_:
{
lean_object* v___x_6910_; 
if (v_isShared_6887_ == 0)
{
lean_ctor_set(v___x_6886_, 4, v___x_6908_);
lean_ctor_set(v___x_6886_, 3, v___y_6903_);
lean_ctor_set(v___x_6886_, 2, v_v_6890_);
lean_ctor_set(v___x_6886_, 1, v_k_6889_);
lean_ctor_set(v___x_6886_, 0, v___x_6901_);
v___x_6910_ = v___x_6886_;
goto v_reusejp_6909_;
}
else
{
lean_object* v_reuseFailAlloc_6911_; 
v_reuseFailAlloc_6911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6911_, 0, v___x_6901_);
lean_ctor_set(v_reuseFailAlloc_6911_, 1, v_k_6889_);
lean_ctor_set(v_reuseFailAlloc_6911_, 2, v_v_6890_);
lean_ctor_set(v_reuseFailAlloc_6911_, 3, v___y_6903_);
lean_ctor_set(v_reuseFailAlloc_6911_, 4, v___x_6908_);
v___x_6910_ = v_reuseFailAlloc_6911_;
goto v_reusejp_6909_;
}
v_reusejp_6909_:
{
return v___x_6910_;
}
}
}
v___jp_6913_:
{
lean_object* v___x_6915_; lean_object* v___x_6917_; 
v___x_6915_ = lean_nat_add(v___x_6900_, v___y_6914_);
lean_dec(v___y_6914_);
lean_dec(v___x_6900_);
if (v_isShared_6866_ == 0)
{
lean_ctor_set(v___x_6865_, 4, v_l_6891_);
lean_ctor_set(v___x_6865_, 0, v___x_6915_);
v___x_6917_ = v___x_6865_;
goto v_reusejp_6916_;
}
else
{
lean_object* v_reuseFailAlloc_6921_; 
v_reuseFailAlloc_6921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6921_, 0, v___x_6915_);
lean_ctor_set(v_reuseFailAlloc_6921_, 1, v_k_6860_);
lean_ctor_set(v_reuseFailAlloc_6921_, 2, v_v_6861_);
lean_ctor_set(v_reuseFailAlloc_6921_, 3, v_l_6862_);
lean_ctor_set(v_reuseFailAlloc_6921_, 4, v_l_6891_);
v___x_6917_ = v_reuseFailAlloc_6921_;
goto v_reusejp_6916_;
}
v_reusejp_6916_:
{
lean_object* v___x_6918_; 
v___x_6918_ = lean_nat_add(v___x_6870_, v_size_6893_);
if (lean_obj_tag(v_r_6892_) == 0)
{
lean_object* v_size_6919_; 
v_size_6919_ = lean_ctor_get(v_r_6892_, 0);
lean_inc(v_size_6919_);
v___y_6903_ = v___x_6917_;
v___y_6904_ = v___x_6918_;
v___y_6905_ = v_size_6919_;
goto v___jp_6902_;
}
else
{
lean_object* v___x_6920_; 
v___x_6920_ = lean_unsigned_to_nat(0u);
v___y_6903_ = v___x_6917_;
v___y_6904_ = v___x_6918_;
v___y_6905_ = v___x_6920_;
goto v___jp_6902_;
}
}
}
}
}
else
{
lean_object* v___x_6930_; lean_object* v___x_6931_; lean_object* v___x_6932_; lean_object* v___x_6934_; 
lean_del_object(v___x_6865_);
v___x_6930_ = lean_nat_add(v___x_6870_, v_size_6871_);
v___x_6931_ = lean_nat_add(v___x_6930_, v_size_6872_);
lean_dec(v_size_6872_);
v___x_6932_ = lean_nat_add(v___x_6930_, v_size_6888_);
lean_dec(v___x_6930_);
lean_inc_ref(v_l_6862_);
if (v_isShared_6887_ == 0)
{
lean_ctor_set(v___x_6886_, 4, v_l_6875_);
lean_ctor_set(v___x_6886_, 3, v_l_6862_);
lean_ctor_set(v___x_6886_, 2, v_v_6861_);
lean_ctor_set(v___x_6886_, 1, v_k_6860_);
lean_ctor_set(v___x_6886_, 0, v___x_6932_);
v___x_6934_ = v___x_6886_;
goto v_reusejp_6933_;
}
else
{
lean_object* v_reuseFailAlloc_6947_; 
v_reuseFailAlloc_6947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6947_, 0, v___x_6932_);
lean_ctor_set(v_reuseFailAlloc_6947_, 1, v_k_6860_);
lean_ctor_set(v_reuseFailAlloc_6947_, 2, v_v_6861_);
lean_ctor_set(v_reuseFailAlloc_6947_, 3, v_l_6862_);
lean_ctor_set(v_reuseFailAlloc_6947_, 4, v_l_6875_);
v___x_6934_ = v_reuseFailAlloc_6947_;
goto v_reusejp_6933_;
}
v_reusejp_6933_:
{
lean_object* v___x_6936_; uint8_t v_isShared_6937_; uint8_t v_isSharedCheck_6941_; 
v_isSharedCheck_6941_ = !lean_is_exclusive(v_l_6862_);
if (v_isSharedCheck_6941_ == 0)
{
lean_object* v_unused_6942_; lean_object* v_unused_6943_; lean_object* v_unused_6944_; lean_object* v_unused_6945_; lean_object* v_unused_6946_; 
v_unused_6942_ = lean_ctor_get(v_l_6862_, 4);
lean_dec(v_unused_6942_);
v_unused_6943_ = lean_ctor_get(v_l_6862_, 3);
lean_dec(v_unused_6943_);
v_unused_6944_ = lean_ctor_get(v_l_6862_, 2);
lean_dec(v_unused_6944_);
v_unused_6945_ = lean_ctor_get(v_l_6862_, 1);
lean_dec(v_unused_6945_);
v_unused_6946_ = lean_ctor_get(v_l_6862_, 0);
lean_dec(v_unused_6946_);
v___x_6936_ = v_l_6862_;
v_isShared_6937_ = v_isSharedCheck_6941_;
goto v_resetjp_6935_;
}
else
{
lean_dec(v_l_6862_);
v___x_6936_ = lean_box(0);
v_isShared_6937_ = v_isSharedCheck_6941_;
goto v_resetjp_6935_;
}
v_resetjp_6935_:
{
lean_object* v___x_6939_; 
if (v_isShared_6937_ == 0)
{
lean_ctor_set(v___x_6936_, 4, v_r_6876_);
lean_ctor_set(v___x_6936_, 3, v___x_6934_);
lean_ctor_set(v___x_6936_, 2, v_v_6874_);
lean_ctor_set(v___x_6936_, 1, v_k_6873_);
lean_ctor_set(v___x_6936_, 0, v___x_6931_);
v___x_6939_ = v___x_6936_;
goto v_reusejp_6938_;
}
else
{
lean_object* v_reuseFailAlloc_6940_; 
v_reuseFailAlloc_6940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6940_, 0, v___x_6931_);
lean_ctor_set(v_reuseFailAlloc_6940_, 1, v_k_6873_);
lean_ctor_set(v_reuseFailAlloc_6940_, 2, v_v_6874_);
lean_ctor_set(v_reuseFailAlloc_6940_, 3, v___x_6934_);
lean_ctor_set(v_reuseFailAlloc_6940_, 4, v_r_6876_);
v___x_6939_ = v_reuseFailAlloc_6940_;
goto v_reusejp_6938_;
}
v_reusejp_6938_:
{
return v___x_6939_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_6954_; 
v_l_6954_ = lean_ctor_get(v_impl_6869_, 3);
lean_inc(v_l_6954_);
if (lean_obj_tag(v_l_6954_) == 0)
{
lean_object* v_r_6955_; lean_object* v_k_6956_; lean_object* v_v_6957_; lean_object* v___x_6959_; uint8_t v_isShared_6960_; uint8_t v_isSharedCheck_6980_; 
v_r_6955_ = lean_ctor_get(v_impl_6869_, 4);
v_k_6956_ = lean_ctor_get(v_impl_6869_, 1);
v_v_6957_ = lean_ctor_get(v_impl_6869_, 2);
v_isSharedCheck_6980_ = !lean_is_exclusive(v_impl_6869_);
if (v_isSharedCheck_6980_ == 0)
{
lean_object* v_unused_6981_; lean_object* v_unused_6982_; 
v_unused_6981_ = lean_ctor_get(v_impl_6869_, 3);
lean_dec(v_unused_6981_);
v_unused_6982_ = lean_ctor_get(v_impl_6869_, 0);
lean_dec(v_unused_6982_);
v___x_6959_ = v_impl_6869_;
v_isShared_6960_ = v_isSharedCheck_6980_;
goto v_resetjp_6958_;
}
else
{
lean_inc(v_r_6955_);
lean_inc(v_v_6957_);
lean_inc(v_k_6956_);
lean_dec(v_impl_6869_);
v___x_6959_ = lean_box(0);
v_isShared_6960_ = v_isSharedCheck_6980_;
goto v_resetjp_6958_;
}
v_resetjp_6958_:
{
lean_object* v_k_6961_; lean_object* v_v_6962_; lean_object* v___x_6964_; uint8_t v_isShared_6965_; uint8_t v_isSharedCheck_6976_; 
v_k_6961_ = lean_ctor_get(v_l_6954_, 1);
v_v_6962_ = lean_ctor_get(v_l_6954_, 2);
v_isSharedCheck_6976_ = !lean_is_exclusive(v_l_6954_);
if (v_isSharedCheck_6976_ == 0)
{
lean_object* v_unused_6977_; lean_object* v_unused_6978_; lean_object* v_unused_6979_; 
v_unused_6977_ = lean_ctor_get(v_l_6954_, 4);
lean_dec(v_unused_6977_);
v_unused_6978_ = lean_ctor_get(v_l_6954_, 3);
lean_dec(v_unused_6978_);
v_unused_6979_ = lean_ctor_get(v_l_6954_, 0);
lean_dec(v_unused_6979_);
v___x_6964_ = v_l_6954_;
v_isShared_6965_ = v_isSharedCheck_6976_;
goto v_resetjp_6963_;
}
else
{
lean_inc(v_v_6962_);
lean_inc(v_k_6961_);
lean_dec(v_l_6954_);
v___x_6964_ = lean_box(0);
v_isShared_6965_ = v_isSharedCheck_6976_;
goto v_resetjp_6963_;
}
v_resetjp_6963_:
{
lean_object* v___x_6966_; lean_object* v___x_6968_; 
v___x_6966_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_6955_, 2);
if (v_isShared_6965_ == 0)
{
lean_ctor_set(v___x_6964_, 4, v_r_6955_);
lean_ctor_set(v___x_6964_, 3, v_r_6955_);
lean_ctor_set(v___x_6964_, 2, v_v_6861_);
lean_ctor_set(v___x_6964_, 1, v_k_6860_);
lean_ctor_set(v___x_6964_, 0, v___x_6870_);
v___x_6968_ = v___x_6964_;
goto v_reusejp_6967_;
}
else
{
lean_object* v_reuseFailAlloc_6975_; 
v_reuseFailAlloc_6975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6975_, 0, v___x_6870_);
lean_ctor_set(v_reuseFailAlloc_6975_, 1, v_k_6860_);
lean_ctor_set(v_reuseFailAlloc_6975_, 2, v_v_6861_);
lean_ctor_set(v_reuseFailAlloc_6975_, 3, v_r_6955_);
lean_ctor_set(v_reuseFailAlloc_6975_, 4, v_r_6955_);
v___x_6968_ = v_reuseFailAlloc_6975_;
goto v_reusejp_6967_;
}
v_reusejp_6967_:
{
lean_object* v___x_6970_; 
lean_inc(v_r_6955_);
if (v_isShared_6960_ == 0)
{
lean_ctor_set(v___x_6959_, 3, v_r_6955_);
lean_ctor_set(v___x_6959_, 0, v___x_6870_);
v___x_6970_ = v___x_6959_;
goto v_reusejp_6969_;
}
else
{
lean_object* v_reuseFailAlloc_6974_; 
v_reuseFailAlloc_6974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6974_, 0, v___x_6870_);
lean_ctor_set(v_reuseFailAlloc_6974_, 1, v_k_6956_);
lean_ctor_set(v_reuseFailAlloc_6974_, 2, v_v_6957_);
lean_ctor_set(v_reuseFailAlloc_6974_, 3, v_r_6955_);
lean_ctor_set(v_reuseFailAlloc_6974_, 4, v_r_6955_);
v___x_6970_ = v_reuseFailAlloc_6974_;
goto v_reusejp_6969_;
}
v_reusejp_6969_:
{
lean_object* v___x_6972_; 
if (v_isShared_6866_ == 0)
{
lean_ctor_set(v___x_6865_, 4, v___x_6970_);
lean_ctor_set(v___x_6865_, 3, v___x_6968_);
lean_ctor_set(v___x_6865_, 2, v_v_6962_);
lean_ctor_set(v___x_6865_, 1, v_k_6961_);
lean_ctor_set(v___x_6865_, 0, v___x_6966_);
v___x_6972_ = v___x_6865_;
goto v_reusejp_6971_;
}
else
{
lean_object* v_reuseFailAlloc_6973_; 
v_reuseFailAlloc_6973_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6973_, 0, v___x_6966_);
lean_ctor_set(v_reuseFailAlloc_6973_, 1, v_k_6961_);
lean_ctor_set(v_reuseFailAlloc_6973_, 2, v_v_6962_);
lean_ctor_set(v_reuseFailAlloc_6973_, 3, v___x_6968_);
lean_ctor_set(v_reuseFailAlloc_6973_, 4, v___x_6970_);
v___x_6972_ = v_reuseFailAlloc_6973_;
goto v_reusejp_6971_;
}
v_reusejp_6971_:
{
return v___x_6972_;
}
}
}
}
}
}
else
{
lean_object* v_r_6983_; 
v_r_6983_ = lean_ctor_get(v_impl_6869_, 4);
lean_inc(v_r_6983_);
if (lean_obj_tag(v_r_6983_) == 0)
{
lean_object* v_k_6984_; lean_object* v_v_6985_; lean_object* v___x_6987_; uint8_t v_isShared_6988_; uint8_t v_isSharedCheck_6996_; 
v_k_6984_ = lean_ctor_get(v_impl_6869_, 1);
v_v_6985_ = lean_ctor_get(v_impl_6869_, 2);
v_isSharedCheck_6996_ = !lean_is_exclusive(v_impl_6869_);
if (v_isSharedCheck_6996_ == 0)
{
lean_object* v_unused_6997_; lean_object* v_unused_6998_; lean_object* v_unused_6999_; 
v_unused_6997_ = lean_ctor_get(v_impl_6869_, 4);
lean_dec(v_unused_6997_);
v_unused_6998_ = lean_ctor_get(v_impl_6869_, 3);
lean_dec(v_unused_6998_);
v_unused_6999_ = lean_ctor_get(v_impl_6869_, 0);
lean_dec(v_unused_6999_);
v___x_6987_ = v_impl_6869_;
v_isShared_6988_ = v_isSharedCheck_6996_;
goto v_resetjp_6986_;
}
else
{
lean_inc(v_v_6985_);
lean_inc(v_k_6984_);
lean_dec(v_impl_6869_);
v___x_6987_ = lean_box(0);
v_isShared_6988_ = v_isSharedCheck_6996_;
goto v_resetjp_6986_;
}
v_resetjp_6986_:
{
lean_object* v___x_6989_; lean_object* v___x_6991_; 
v___x_6989_ = lean_unsigned_to_nat(3u);
if (v_isShared_6988_ == 0)
{
lean_ctor_set(v___x_6987_, 4, v_l_6954_);
lean_ctor_set(v___x_6987_, 2, v_v_6861_);
lean_ctor_set(v___x_6987_, 1, v_k_6860_);
lean_ctor_set(v___x_6987_, 0, v___x_6870_);
v___x_6991_ = v___x_6987_;
goto v_reusejp_6990_;
}
else
{
lean_object* v_reuseFailAlloc_6995_; 
v_reuseFailAlloc_6995_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6995_, 0, v___x_6870_);
lean_ctor_set(v_reuseFailAlloc_6995_, 1, v_k_6860_);
lean_ctor_set(v_reuseFailAlloc_6995_, 2, v_v_6861_);
lean_ctor_set(v_reuseFailAlloc_6995_, 3, v_l_6954_);
lean_ctor_set(v_reuseFailAlloc_6995_, 4, v_l_6954_);
v___x_6991_ = v_reuseFailAlloc_6995_;
goto v_reusejp_6990_;
}
v_reusejp_6990_:
{
lean_object* v___x_6993_; 
if (v_isShared_6866_ == 0)
{
lean_ctor_set(v___x_6865_, 4, v_r_6983_);
lean_ctor_set(v___x_6865_, 3, v___x_6991_);
lean_ctor_set(v___x_6865_, 2, v_v_6985_);
lean_ctor_set(v___x_6865_, 1, v_k_6984_);
lean_ctor_set(v___x_6865_, 0, v___x_6989_);
v___x_6993_ = v___x_6865_;
goto v_reusejp_6992_;
}
else
{
lean_object* v_reuseFailAlloc_6994_; 
v_reuseFailAlloc_6994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6994_, 0, v___x_6989_);
lean_ctor_set(v_reuseFailAlloc_6994_, 1, v_k_6984_);
lean_ctor_set(v_reuseFailAlloc_6994_, 2, v_v_6985_);
lean_ctor_set(v_reuseFailAlloc_6994_, 3, v___x_6991_);
lean_ctor_set(v_reuseFailAlloc_6994_, 4, v_r_6983_);
v___x_6993_ = v_reuseFailAlloc_6994_;
goto v_reusejp_6992_;
}
v_reusejp_6992_:
{
return v___x_6993_;
}
}
}
}
else
{
lean_object* v___x_7000_; lean_object* v___x_7002_; 
v___x_7000_ = lean_unsigned_to_nat(2u);
if (v_isShared_6866_ == 0)
{
lean_ctor_set(v___x_6865_, 4, v_impl_6869_);
lean_ctor_set(v___x_6865_, 3, v_r_6983_);
lean_ctor_set(v___x_6865_, 0, v___x_7000_);
v___x_7002_ = v___x_6865_;
goto v_reusejp_7001_;
}
else
{
lean_object* v_reuseFailAlloc_7003_; 
v_reuseFailAlloc_7003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7003_, 0, v___x_7000_);
lean_ctor_set(v_reuseFailAlloc_7003_, 1, v_k_6860_);
lean_ctor_set(v_reuseFailAlloc_7003_, 2, v_v_6861_);
lean_ctor_set(v_reuseFailAlloc_7003_, 3, v_r_6983_);
lean_ctor_set(v_reuseFailAlloc_7003_, 4, v_impl_6869_);
v___x_7002_ = v_reuseFailAlloc_7003_;
goto v_reusejp_7001_;
}
v_reusejp_7001_:
{
return v___x_7002_;
}
}
}
}
}
else
{
lean_object* v___x_7005_; 
lean_dec(v_v_6861_);
lean_dec(v_k_6860_);
if (v_isShared_6866_ == 0)
{
lean_ctor_set(v___x_6865_, 2, v_v_6857_);
lean_ctor_set(v___x_6865_, 1, v_k_6856_);
v___x_7005_ = v___x_6865_;
goto v_reusejp_7004_;
}
else
{
lean_object* v_reuseFailAlloc_7006_; 
v_reuseFailAlloc_7006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7006_, 0, v_size_6859_);
lean_ctor_set(v_reuseFailAlloc_7006_, 1, v_k_6856_);
lean_ctor_set(v_reuseFailAlloc_7006_, 2, v_v_6857_);
lean_ctor_set(v_reuseFailAlloc_7006_, 3, v_l_6862_);
lean_ctor_set(v_reuseFailAlloc_7006_, 4, v_r_6863_);
v___x_7005_ = v_reuseFailAlloc_7006_;
goto v_reusejp_7004_;
}
v_reusejp_7004_:
{
return v___x_7005_;
}
}
}
else
{
lean_object* v_impl_7007_; lean_object* v___x_7008_; 
lean_dec(v_size_6859_);
v_impl_7007_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_6856_, v_v_6857_, v_l_6862_);
v___x_7008_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_6863_) == 0)
{
lean_object* v_size_7009_; lean_object* v_size_7010_; lean_object* v_k_7011_; lean_object* v_v_7012_; lean_object* v_l_7013_; lean_object* v_r_7014_; lean_object* v___x_7015_; lean_object* v___x_7016_; uint8_t v___x_7017_; 
v_size_7009_ = lean_ctor_get(v_r_6863_, 0);
v_size_7010_ = lean_ctor_get(v_impl_7007_, 0);
lean_inc(v_size_7010_);
v_k_7011_ = lean_ctor_get(v_impl_7007_, 1);
lean_inc(v_k_7011_);
v_v_7012_ = lean_ctor_get(v_impl_7007_, 2);
lean_inc(v_v_7012_);
v_l_7013_ = lean_ctor_get(v_impl_7007_, 3);
lean_inc(v_l_7013_);
v_r_7014_ = lean_ctor_get(v_impl_7007_, 4);
lean_inc(v_r_7014_);
v___x_7015_ = lean_unsigned_to_nat(3u);
v___x_7016_ = lean_nat_mul(v___x_7015_, v_size_7009_);
v___x_7017_ = lean_nat_dec_lt(v___x_7016_, v_size_7010_);
lean_dec(v___x_7016_);
if (v___x_7017_ == 0)
{
lean_object* v___x_7018_; lean_object* v___x_7019_; lean_object* v___x_7021_; 
lean_dec(v_r_7014_);
lean_dec(v_l_7013_);
lean_dec(v_v_7012_);
lean_dec(v_k_7011_);
v___x_7018_ = lean_nat_add(v___x_7008_, v_size_7010_);
lean_dec(v_size_7010_);
v___x_7019_ = lean_nat_add(v___x_7018_, v_size_7009_);
lean_dec(v___x_7018_);
if (v_isShared_6866_ == 0)
{
lean_ctor_set(v___x_6865_, 3, v_impl_7007_);
lean_ctor_set(v___x_6865_, 0, v___x_7019_);
v___x_7021_ = v___x_6865_;
goto v_reusejp_7020_;
}
else
{
lean_object* v_reuseFailAlloc_7022_; 
v_reuseFailAlloc_7022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7022_, 0, v___x_7019_);
lean_ctor_set(v_reuseFailAlloc_7022_, 1, v_k_6860_);
lean_ctor_set(v_reuseFailAlloc_7022_, 2, v_v_6861_);
lean_ctor_set(v_reuseFailAlloc_7022_, 3, v_impl_7007_);
lean_ctor_set(v_reuseFailAlloc_7022_, 4, v_r_6863_);
v___x_7021_ = v_reuseFailAlloc_7022_;
goto v_reusejp_7020_;
}
v_reusejp_7020_:
{
return v___x_7021_;
}
}
else
{
lean_object* v___x_7024_; uint8_t v_isShared_7025_; uint8_t v_isSharedCheck_7088_; 
v_isSharedCheck_7088_ = !lean_is_exclusive(v_impl_7007_);
if (v_isSharedCheck_7088_ == 0)
{
lean_object* v_unused_7089_; lean_object* v_unused_7090_; lean_object* v_unused_7091_; lean_object* v_unused_7092_; lean_object* v_unused_7093_; 
v_unused_7089_ = lean_ctor_get(v_impl_7007_, 4);
lean_dec(v_unused_7089_);
v_unused_7090_ = lean_ctor_get(v_impl_7007_, 3);
lean_dec(v_unused_7090_);
v_unused_7091_ = lean_ctor_get(v_impl_7007_, 2);
lean_dec(v_unused_7091_);
v_unused_7092_ = lean_ctor_get(v_impl_7007_, 1);
lean_dec(v_unused_7092_);
v_unused_7093_ = lean_ctor_get(v_impl_7007_, 0);
lean_dec(v_unused_7093_);
v___x_7024_ = v_impl_7007_;
v_isShared_7025_ = v_isSharedCheck_7088_;
goto v_resetjp_7023_;
}
else
{
lean_dec(v_impl_7007_);
v___x_7024_ = lean_box(0);
v_isShared_7025_ = v_isSharedCheck_7088_;
goto v_resetjp_7023_;
}
v_resetjp_7023_:
{
lean_object* v_size_7026_; lean_object* v_size_7027_; lean_object* v_k_7028_; lean_object* v_v_7029_; lean_object* v_l_7030_; lean_object* v_r_7031_; lean_object* v___x_7032_; lean_object* v___x_7033_; uint8_t v___x_7034_; 
v_size_7026_ = lean_ctor_get(v_l_7013_, 0);
v_size_7027_ = lean_ctor_get(v_r_7014_, 0);
v_k_7028_ = lean_ctor_get(v_r_7014_, 1);
v_v_7029_ = lean_ctor_get(v_r_7014_, 2);
v_l_7030_ = lean_ctor_get(v_r_7014_, 3);
v_r_7031_ = lean_ctor_get(v_r_7014_, 4);
v___x_7032_ = lean_unsigned_to_nat(2u);
v___x_7033_ = lean_nat_mul(v___x_7032_, v_size_7026_);
v___x_7034_ = lean_nat_dec_lt(v_size_7027_, v___x_7033_);
lean_dec(v___x_7033_);
if (v___x_7034_ == 0)
{
lean_object* v___x_7036_; uint8_t v_isShared_7037_; uint8_t v_isSharedCheck_7063_; 
lean_inc(v_r_7031_);
lean_inc(v_l_7030_);
lean_inc(v_v_7029_);
lean_inc(v_k_7028_);
v_isSharedCheck_7063_ = !lean_is_exclusive(v_r_7014_);
if (v_isSharedCheck_7063_ == 0)
{
lean_object* v_unused_7064_; lean_object* v_unused_7065_; lean_object* v_unused_7066_; lean_object* v_unused_7067_; lean_object* v_unused_7068_; 
v_unused_7064_ = lean_ctor_get(v_r_7014_, 4);
lean_dec(v_unused_7064_);
v_unused_7065_ = lean_ctor_get(v_r_7014_, 3);
lean_dec(v_unused_7065_);
v_unused_7066_ = lean_ctor_get(v_r_7014_, 2);
lean_dec(v_unused_7066_);
v_unused_7067_ = lean_ctor_get(v_r_7014_, 1);
lean_dec(v_unused_7067_);
v_unused_7068_ = lean_ctor_get(v_r_7014_, 0);
lean_dec(v_unused_7068_);
v___x_7036_ = v_r_7014_;
v_isShared_7037_ = v_isSharedCheck_7063_;
goto v_resetjp_7035_;
}
else
{
lean_dec(v_r_7014_);
v___x_7036_ = lean_box(0);
v_isShared_7037_ = v_isSharedCheck_7063_;
goto v_resetjp_7035_;
}
v_resetjp_7035_:
{
lean_object* v___x_7038_; lean_object* v___x_7039_; lean_object* v___y_7041_; lean_object* v___y_7042_; lean_object* v___y_7043_; lean_object* v___x_7051_; lean_object* v___y_7053_; 
v___x_7038_ = lean_nat_add(v___x_7008_, v_size_7010_);
lean_dec(v_size_7010_);
v___x_7039_ = lean_nat_add(v___x_7038_, v_size_7009_);
lean_dec(v___x_7038_);
v___x_7051_ = lean_nat_add(v___x_7008_, v_size_7026_);
if (lean_obj_tag(v_l_7030_) == 0)
{
lean_object* v_size_7061_; 
v_size_7061_ = lean_ctor_get(v_l_7030_, 0);
lean_inc(v_size_7061_);
v___y_7053_ = v_size_7061_;
goto v___jp_7052_;
}
else
{
lean_object* v___x_7062_; 
v___x_7062_ = lean_unsigned_to_nat(0u);
v___y_7053_ = v___x_7062_;
goto v___jp_7052_;
}
v___jp_7040_:
{
lean_object* v___x_7044_; lean_object* v___x_7046_; 
v___x_7044_ = lean_nat_add(v___y_7041_, v___y_7043_);
lean_dec(v___y_7043_);
lean_dec(v___y_7041_);
if (v_isShared_7037_ == 0)
{
lean_ctor_set(v___x_7036_, 4, v_r_6863_);
lean_ctor_set(v___x_7036_, 3, v_r_7031_);
lean_ctor_set(v___x_7036_, 2, v_v_6861_);
lean_ctor_set(v___x_7036_, 1, v_k_6860_);
lean_ctor_set(v___x_7036_, 0, v___x_7044_);
v___x_7046_ = v___x_7036_;
goto v_reusejp_7045_;
}
else
{
lean_object* v_reuseFailAlloc_7050_; 
v_reuseFailAlloc_7050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7050_, 0, v___x_7044_);
lean_ctor_set(v_reuseFailAlloc_7050_, 1, v_k_6860_);
lean_ctor_set(v_reuseFailAlloc_7050_, 2, v_v_6861_);
lean_ctor_set(v_reuseFailAlloc_7050_, 3, v_r_7031_);
lean_ctor_set(v_reuseFailAlloc_7050_, 4, v_r_6863_);
v___x_7046_ = v_reuseFailAlloc_7050_;
goto v_reusejp_7045_;
}
v_reusejp_7045_:
{
lean_object* v___x_7048_; 
if (v_isShared_7025_ == 0)
{
lean_ctor_set(v___x_7024_, 4, v___x_7046_);
lean_ctor_set(v___x_7024_, 3, v___y_7042_);
lean_ctor_set(v___x_7024_, 2, v_v_7029_);
lean_ctor_set(v___x_7024_, 1, v_k_7028_);
lean_ctor_set(v___x_7024_, 0, v___x_7039_);
v___x_7048_ = v___x_7024_;
goto v_reusejp_7047_;
}
else
{
lean_object* v_reuseFailAlloc_7049_; 
v_reuseFailAlloc_7049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7049_, 0, v___x_7039_);
lean_ctor_set(v_reuseFailAlloc_7049_, 1, v_k_7028_);
lean_ctor_set(v_reuseFailAlloc_7049_, 2, v_v_7029_);
lean_ctor_set(v_reuseFailAlloc_7049_, 3, v___y_7042_);
lean_ctor_set(v_reuseFailAlloc_7049_, 4, v___x_7046_);
v___x_7048_ = v_reuseFailAlloc_7049_;
goto v_reusejp_7047_;
}
v_reusejp_7047_:
{
return v___x_7048_;
}
}
}
v___jp_7052_:
{
lean_object* v___x_7054_; lean_object* v___x_7056_; 
v___x_7054_ = lean_nat_add(v___x_7051_, v___y_7053_);
lean_dec(v___y_7053_);
lean_dec(v___x_7051_);
if (v_isShared_6866_ == 0)
{
lean_ctor_set(v___x_6865_, 4, v_l_7030_);
lean_ctor_set(v___x_6865_, 3, v_l_7013_);
lean_ctor_set(v___x_6865_, 2, v_v_7012_);
lean_ctor_set(v___x_6865_, 1, v_k_7011_);
lean_ctor_set(v___x_6865_, 0, v___x_7054_);
v___x_7056_ = v___x_6865_;
goto v_reusejp_7055_;
}
else
{
lean_object* v_reuseFailAlloc_7060_; 
v_reuseFailAlloc_7060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7060_, 0, v___x_7054_);
lean_ctor_set(v_reuseFailAlloc_7060_, 1, v_k_7011_);
lean_ctor_set(v_reuseFailAlloc_7060_, 2, v_v_7012_);
lean_ctor_set(v_reuseFailAlloc_7060_, 3, v_l_7013_);
lean_ctor_set(v_reuseFailAlloc_7060_, 4, v_l_7030_);
v___x_7056_ = v_reuseFailAlloc_7060_;
goto v_reusejp_7055_;
}
v_reusejp_7055_:
{
lean_object* v___x_7057_; 
v___x_7057_ = lean_nat_add(v___x_7008_, v_size_7009_);
if (lean_obj_tag(v_r_7031_) == 0)
{
lean_object* v_size_7058_; 
v_size_7058_ = lean_ctor_get(v_r_7031_, 0);
lean_inc(v_size_7058_);
v___y_7041_ = v___x_7057_;
v___y_7042_ = v___x_7056_;
v___y_7043_ = v_size_7058_;
goto v___jp_7040_;
}
else
{
lean_object* v___x_7059_; 
v___x_7059_ = lean_unsigned_to_nat(0u);
v___y_7041_ = v___x_7057_;
v___y_7042_ = v___x_7056_;
v___y_7043_ = v___x_7059_;
goto v___jp_7040_;
}
}
}
}
}
else
{
lean_object* v___x_7069_; lean_object* v___x_7070_; lean_object* v___x_7071_; lean_object* v___x_7072_; lean_object* v___x_7074_; 
lean_del_object(v___x_6865_);
v___x_7069_ = lean_nat_add(v___x_7008_, v_size_7010_);
lean_dec(v_size_7010_);
v___x_7070_ = lean_nat_add(v___x_7069_, v_size_7009_);
lean_dec(v___x_7069_);
v___x_7071_ = lean_nat_add(v___x_7008_, v_size_7009_);
v___x_7072_ = lean_nat_add(v___x_7071_, v_size_7027_);
lean_dec(v___x_7071_);
lean_inc_ref(v_r_6863_);
if (v_isShared_7025_ == 0)
{
lean_ctor_set(v___x_7024_, 4, v_r_6863_);
lean_ctor_set(v___x_7024_, 3, v_r_7014_);
lean_ctor_set(v___x_7024_, 2, v_v_6861_);
lean_ctor_set(v___x_7024_, 1, v_k_6860_);
lean_ctor_set(v___x_7024_, 0, v___x_7072_);
v___x_7074_ = v___x_7024_;
goto v_reusejp_7073_;
}
else
{
lean_object* v_reuseFailAlloc_7087_; 
v_reuseFailAlloc_7087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7087_, 0, v___x_7072_);
lean_ctor_set(v_reuseFailAlloc_7087_, 1, v_k_6860_);
lean_ctor_set(v_reuseFailAlloc_7087_, 2, v_v_6861_);
lean_ctor_set(v_reuseFailAlloc_7087_, 3, v_r_7014_);
lean_ctor_set(v_reuseFailAlloc_7087_, 4, v_r_6863_);
v___x_7074_ = v_reuseFailAlloc_7087_;
goto v_reusejp_7073_;
}
v_reusejp_7073_:
{
lean_object* v___x_7076_; uint8_t v_isShared_7077_; uint8_t v_isSharedCheck_7081_; 
v_isSharedCheck_7081_ = !lean_is_exclusive(v_r_6863_);
if (v_isSharedCheck_7081_ == 0)
{
lean_object* v_unused_7082_; lean_object* v_unused_7083_; lean_object* v_unused_7084_; lean_object* v_unused_7085_; lean_object* v_unused_7086_; 
v_unused_7082_ = lean_ctor_get(v_r_6863_, 4);
lean_dec(v_unused_7082_);
v_unused_7083_ = lean_ctor_get(v_r_6863_, 3);
lean_dec(v_unused_7083_);
v_unused_7084_ = lean_ctor_get(v_r_6863_, 2);
lean_dec(v_unused_7084_);
v_unused_7085_ = lean_ctor_get(v_r_6863_, 1);
lean_dec(v_unused_7085_);
v_unused_7086_ = lean_ctor_get(v_r_6863_, 0);
lean_dec(v_unused_7086_);
v___x_7076_ = v_r_6863_;
v_isShared_7077_ = v_isSharedCheck_7081_;
goto v_resetjp_7075_;
}
else
{
lean_dec(v_r_6863_);
v___x_7076_ = lean_box(0);
v_isShared_7077_ = v_isSharedCheck_7081_;
goto v_resetjp_7075_;
}
v_resetjp_7075_:
{
lean_object* v___x_7079_; 
if (v_isShared_7077_ == 0)
{
lean_ctor_set(v___x_7076_, 4, v___x_7074_);
lean_ctor_set(v___x_7076_, 3, v_l_7013_);
lean_ctor_set(v___x_7076_, 2, v_v_7012_);
lean_ctor_set(v___x_7076_, 1, v_k_7011_);
lean_ctor_set(v___x_7076_, 0, v___x_7070_);
v___x_7079_ = v___x_7076_;
goto v_reusejp_7078_;
}
else
{
lean_object* v_reuseFailAlloc_7080_; 
v_reuseFailAlloc_7080_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7080_, 0, v___x_7070_);
lean_ctor_set(v_reuseFailAlloc_7080_, 1, v_k_7011_);
lean_ctor_set(v_reuseFailAlloc_7080_, 2, v_v_7012_);
lean_ctor_set(v_reuseFailAlloc_7080_, 3, v_l_7013_);
lean_ctor_set(v_reuseFailAlloc_7080_, 4, v___x_7074_);
v___x_7079_ = v_reuseFailAlloc_7080_;
goto v_reusejp_7078_;
}
v_reusejp_7078_:
{
return v___x_7079_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_7094_; 
v_l_7094_ = lean_ctor_get(v_impl_7007_, 3);
lean_inc(v_l_7094_);
if (lean_obj_tag(v_l_7094_) == 0)
{
lean_object* v_r_7095_; lean_object* v_k_7096_; lean_object* v_v_7097_; lean_object* v___x_7099_; uint8_t v_isShared_7100_; uint8_t v_isSharedCheck_7108_; 
v_r_7095_ = lean_ctor_get(v_impl_7007_, 4);
v_k_7096_ = lean_ctor_get(v_impl_7007_, 1);
v_v_7097_ = lean_ctor_get(v_impl_7007_, 2);
v_isSharedCheck_7108_ = !lean_is_exclusive(v_impl_7007_);
if (v_isSharedCheck_7108_ == 0)
{
lean_object* v_unused_7109_; lean_object* v_unused_7110_; 
v_unused_7109_ = lean_ctor_get(v_impl_7007_, 3);
lean_dec(v_unused_7109_);
v_unused_7110_ = lean_ctor_get(v_impl_7007_, 0);
lean_dec(v_unused_7110_);
v___x_7099_ = v_impl_7007_;
v_isShared_7100_ = v_isSharedCheck_7108_;
goto v_resetjp_7098_;
}
else
{
lean_inc(v_r_7095_);
lean_inc(v_v_7097_);
lean_inc(v_k_7096_);
lean_dec(v_impl_7007_);
v___x_7099_ = lean_box(0);
v_isShared_7100_ = v_isSharedCheck_7108_;
goto v_resetjp_7098_;
}
v_resetjp_7098_:
{
lean_object* v___x_7101_; lean_object* v___x_7103_; 
v___x_7101_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_7095_);
if (v_isShared_7100_ == 0)
{
lean_ctor_set(v___x_7099_, 3, v_r_7095_);
lean_ctor_set(v___x_7099_, 2, v_v_6861_);
lean_ctor_set(v___x_7099_, 1, v_k_6860_);
lean_ctor_set(v___x_7099_, 0, v___x_7008_);
v___x_7103_ = v___x_7099_;
goto v_reusejp_7102_;
}
else
{
lean_object* v_reuseFailAlloc_7107_; 
v_reuseFailAlloc_7107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7107_, 0, v___x_7008_);
lean_ctor_set(v_reuseFailAlloc_7107_, 1, v_k_6860_);
lean_ctor_set(v_reuseFailAlloc_7107_, 2, v_v_6861_);
lean_ctor_set(v_reuseFailAlloc_7107_, 3, v_r_7095_);
lean_ctor_set(v_reuseFailAlloc_7107_, 4, v_r_7095_);
v___x_7103_ = v_reuseFailAlloc_7107_;
goto v_reusejp_7102_;
}
v_reusejp_7102_:
{
lean_object* v___x_7105_; 
if (v_isShared_6866_ == 0)
{
lean_ctor_set(v___x_6865_, 4, v___x_7103_);
lean_ctor_set(v___x_6865_, 3, v_l_7094_);
lean_ctor_set(v___x_6865_, 2, v_v_7097_);
lean_ctor_set(v___x_6865_, 1, v_k_7096_);
lean_ctor_set(v___x_6865_, 0, v___x_7101_);
v___x_7105_ = v___x_6865_;
goto v_reusejp_7104_;
}
else
{
lean_object* v_reuseFailAlloc_7106_; 
v_reuseFailAlloc_7106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7106_, 0, v___x_7101_);
lean_ctor_set(v_reuseFailAlloc_7106_, 1, v_k_7096_);
lean_ctor_set(v_reuseFailAlloc_7106_, 2, v_v_7097_);
lean_ctor_set(v_reuseFailAlloc_7106_, 3, v_l_7094_);
lean_ctor_set(v_reuseFailAlloc_7106_, 4, v___x_7103_);
v___x_7105_ = v_reuseFailAlloc_7106_;
goto v_reusejp_7104_;
}
v_reusejp_7104_:
{
return v___x_7105_;
}
}
}
}
else
{
lean_object* v_r_7111_; 
v_r_7111_ = lean_ctor_get(v_impl_7007_, 4);
lean_inc(v_r_7111_);
if (lean_obj_tag(v_r_7111_) == 0)
{
lean_object* v_k_7112_; lean_object* v_v_7113_; lean_object* v___x_7115_; uint8_t v_isShared_7116_; uint8_t v_isSharedCheck_7136_; 
v_k_7112_ = lean_ctor_get(v_impl_7007_, 1);
v_v_7113_ = lean_ctor_get(v_impl_7007_, 2);
v_isSharedCheck_7136_ = !lean_is_exclusive(v_impl_7007_);
if (v_isSharedCheck_7136_ == 0)
{
lean_object* v_unused_7137_; lean_object* v_unused_7138_; lean_object* v_unused_7139_; 
v_unused_7137_ = lean_ctor_get(v_impl_7007_, 4);
lean_dec(v_unused_7137_);
v_unused_7138_ = lean_ctor_get(v_impl_7007_, 3);
lean_dec(v_unused_7138_);
v_unused_7139_ = lean_ctor_get(v_impl_7007_, 0);
lean_dec(v_unused_7139_);
v___x_7115_ = v_impl_7007_;
v_isShared_7116_ = v_isSharedCheck_7136_;
goto v_resetjp_7114_;
}
else
{
lean_inc(v_v_7113_);
lean_inc(v_k_7112_);
lean_dec(v_impl_7007_);
v___x_7115_ = lean_box(0);
v_isShared_7116_ = v_isSharedCheck_7136_;
goto v_resetjp_7114_;
}
v_resetjp_7114_:
{
lean_object* v_k_7117_; lean_object* v_v_7118_; lean_object* v___x_7120_; uint8_t v_isShared_7121_; uint8_t v_isSharedCheck_7132_; 
v_k_7117_ = lean_ctor_get(v_r_7111_, 1);
v_v_7118_ = lean_ctor_get(v_r_7111_, 2);
v_isSharedCheck_7132_ = !lean_is_exclusive(v_r_7111_);
if (v_isSharedCheck_7132_ == 0)
{
lean_object* v_unused_7133_; lean_object* v_unused_7134_; lean_object* v_unused_7135_; 
v_unused_7133_ = lean_ctor_get(v_r_7111_, 4);
lean_dec(v_unused_7133_);
v_unused_7134_ = lean_ctor_get(v_r_7111_, 3);
lean_dec(v_unused_7134_);
v_unused_7135_ = lean_ctor_get(v_r_7111_, 0);
lean_dec(v_unused_7135_);
v___x_7120_ = v_r_7111_;
v_isShared_7121_ = v_isSharedCheck_7132_;
goto v_resetjp_7119_;
}
else
{
lean_inc(v_v_7118_);
lean_inc(v_k_7117_);
lean_dec(v_r_7111_);
v___x_7120_ = lean_box(0);
v_isShared_7121_ = v_isSharedCheck_7132_;
goto v_resetjp_7119_;
}
v_resetjp_7119_:
{
lean_object* v___x_7122_; lean_object* v___x_7124_; 
v___x_7122_ = lean_unsigned_to_nat(3u);
if (v_isShared_7121_ == 0)
{
lean_ctor_set(v___x_7120_, 4, v_l_7094_);
lean_ctor_set(v___x_7120_, 3, v_l_7094_);
lean_ctor_set(v___x_7120_, 2, v_v_7113_);
lean_ctor_set(v___x_7120_, 1, v_k_7112_);
lean_ctor_set(v___x_7120_, 0, v___x_7008_);
v___x_7124_ = v___x_7120_;
goto v_reusejp_7123_;
}
else
{
lean_object* v_reuseFailAlloc_7131_; 
v_reuseFailAlloc_7131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7131_, 0, v___x_7008_);
lean_ctor_set(v_reuseFailAlloc_7131_, 1, v_k_7112_);
lean_ctor_set(v_reuseFailAlloc_7131_, 2, v_v_7113_);
lean_ctor_set(v_reuseFailAlloc_7131_, 3, v_l_7094_);
lean_ctor_set(v_reuseFailAlloc_7131_, 4, v_l_7094_);
v___x_7124_ = v_reuseFailAlloc_7131_;
goto v_reusejp_7123_;
}
v_reusejp_7123_:
{
lean_object* v___x_7126_; 
if (v_isShared_7116_ == 0)
{
lean_ctor_set(v___x_7115_, 4, v_l_7094_);
lean_ctor_set(v___x_7115_, 2, v_v_6861_);
lean_ctor_set(v___x_7115_, 1, v_k_6860_);
lean_ctor_set(v___x_7115_, 0, v___x_7008_);
v___x_7126_ = v___x_7115_;
goto v_reusejp_7125_;
}
else
{
lean_object* v_reuseFailAlloc_7130_; 
v_reuseFailAlloc_7130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7130_, 0, v___x_7008_);
lean_ctor_set(v_reuseFailAlloc_7130_, 1, v_k_6860_);
lean_ctor_set(v_reuseFailAlloc_7130_, 2, v_v_6861_);
lean_ctor_set(v_reuseFailAlloc_7130_, 3, v_l_7094_);
lean_ctor_set(v_reuseFailAlloc_7130_, 4, v_l_7094_);
v___x_7126_ = v_reuseFailAlloc_7130_;
goto v_reusejp_7125_;
}
v_reusejp_7125_:
{
lean_object* v___x_7128_; 
if (v_isShared_6866_ == 0)
{
lean_ctor_set(v___x_6865_, 4, v___x_7126_);
lean_ctor_set(v___x_6865_, 3, v___x_7124_);
lean_ctor_set(v___x_6865_, 2, v_v_7118_);
lean_ctor_set(v___x_6865_, 1, v_k_7117_);
lean_ctor_set(v___x_6865_, 0, v___x_7122_);
v___x_7128_ = v___x_6865_;
goto v_reusejp_7127_;
}
else
{
lean_object* v_reuseFailAlloc_7129_; 
v_reuseFailAlloc_7129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7129_, 0, v___x_7122_);
lean_ctor_set(v_reuseFailAlloc_7129_, 1, v_k_7117_);
lean_ctor_set(v_reuseFailAlloc_7129_, 2, v_v_7118_);
lean_ctor_set(v_reuseFailAlloc_7129_, 3, v___x_7124_);
lean_ctor_set(v_reuseFailAlloc_7129_, 4, v___x_7126_);
v___x_7128_ = v_reuseFailAlloc_7129_;
goto v_reusejp_7127_;
}
v_reusejp_7127_:
{
return v___x_7128_;
}
}
}
}
}
}
else
{
lean_object* v___x_7140_; lean_object* v___x_7142_; 
v___x_7140_ = lean_unsigned_to_nat(2u);
if (v_isShared_6866_ == 0)
{
lean_ctor_set(v___x_6865_, 4, v_r_7111_);
lean_ctor_set(v___x_6865_, 3, v_impl_7007_);
lean_ctor_set(v___x_6865_, 0, v___x_7140_);
v___x_7142_ = v___x_6865_;
goto v_reusejp_7141_;
}
else
{
lean_object* v_reuseFailAlloc_7143_; 
v_reuseFailAlloc_7143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7143_, 0, v___x_7140_);
lean_ctor_set(v_reuseFailAlloc_7143_, 1, v_k_6860_);
lean_ctor_set(v_reuseFailAlloc_7143_, 2, v_v_6861_);
lean_ctor_set(v_reuseFailAlloc_7143_, 3, v_impl_7007_);
lean_ctor_set(v_reuseFailAlloc_7143_, 4, v_r_7111_);
v___x_7142_ = v_reuseFailAlloc_7143_;
goto v_reusejp_7141_;
}
v_reusejp_7141_:
{
return v___x_7142_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_7145_; lean_object* v___x_7146_; 
v___x_7145_ = lean_unsigned_to_nat(1u);
v___x_7146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_7146_, 0, v___x_7145_);
lean_ctor_set(v___x_7146_, 1, v_k_6856_);
lean_ctor_set(v___x_7146_, 2, v_v_6857_);
lean_ctor_set(v___x_7146_, 3, v_t_6858_);
lean_ctor_set(v___x_7146_, 4, v_t_6858_);
return v___x_7146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(lean_object* v_lib_7147_, lean_object* v_ps_7148_, lean_object* v_v_7149_, lean_object* v_o_7150_){
_start:
{
lean_object* v_name_7151_; lean_object* v_deps_7152_; lean_object* v_o_7153_; uint8_t v___x_7154_; 
v_name_7151_ = lean_ctor_get(v_lib_7147_, 1);
lean_inc_ref(v_name_7151_);
v_deps_7152_ = lean_ctor_get(v_lib_7147_, 2);
lean_inc_ref(v_deps_7152_);
v_o_7153_ = lean_array_push(v_o_7150_, v_lib_7147_);
v___x_7154_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_name_7151_, v_v_7149_);
if (v___x_7154_ == 0)
{
uint8_t v___x_7155_; 
v___x_7155_ = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(v_name_7151_, v_ps_7148_);
if (v___x_7155_ == 0)
{
lean_object* v_ps_7156_; lean_object* v___y_7158_; 
lean_inc_ref(v_name_7151_);
v_ps_7156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_ps_7156_, 0, v_name_7151_);
lean_ctor_set(v_ps_7156_, 1, v_ps_7148_);
if (v___x_7154_ == 0)
{
lean_object* v___x_7172_; lean_object* v___x_7173_; 
v___x_7172_ = lean_box(0);
v___x_7173_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_name_7151_, v___x_7172_, v_v_7149_);
v___y_7158_ = v___x_7173_;
goto v___jp_7157_;
}
else
{
lean_dec_ref(v_name_7151_);
v___y_7158_ = v_v_7149_;
goto v___jp_7157_;
}
v___jp_7157_:
{
lean_object* v___x_7159_; lean_object* v___x_7160_; lean_object* v___x_7161_; uint8_t v___x_7162_; 
v___x_7159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7159_, 0, v___y_7158_);
lean_ctor_set(v___x_7159_, 1, v_o_7153_);
v___x_7160_ = lean_unsigned_to_nat(0u);
v___x_7161_ = lean_array_get_size(v_deps_7152_);
v___x_7162_ = lean_nat_dec_lt(v___x_7160_, v___x_7161_);
if (v___x_7162_ == 0)
{
lean_object* v___x_7163_; 
lean_dec_ref(v_ps_7156_);
lean_dec_ref(v_deps_7152_);
v___x_7163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7163_, 0, v___x_7159_);
return v___x_7163_;
}
else
{
uint8_t v___x_7164_; 
v___x_7164_ = lean_nat_dec_le(v___x_7161_, v___x_7161_);
if (v___x_7164_ == 0)
{
if (v___x_7162_ == 0)
{
lean_object* v___x_7165_; 
lean_dec_ref(v_ps_7156_);
lean_dec_ref(v_deps_7152_);
v___x_7165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7165_, 0, v___x_7159_);
return v___x_7165_;
}
else
{
size_t v___x_7166_; size_t v___x_7167_; lean_object* v___x_7168_; 
v___x_7166_ = ((size_t)0ULL);
v___x_7167_ = lean_usize_of_nat(v___x_7161_);
v___x_7168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7156_, v_deps_7152_, v___x_7166_, v___x_7167_, v___x_7159_);
lean_dec_ref(v_deps_7152_);
return v___x_7168_;
}
}
else
{
size_t v___x_7169_; size_t v___x_7170_; lean_object* v___x_7171_; 
v___x_7169_ = ((size_t)0ULL);
v___x_7170_ = lean_usize_of_nat(v___x_7161_);
v___x_7171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7156_, v_deps_7152_, v___x_7169_, v___x_7170_, v___x_7159_);
lean_dec_ref(v_deps_7152_);
return v___x_7171_;
}
}
}
}
else
{
lean_object* v___x_7174_; lean_object* v___x_7175_; 
lean_dec_ref(v_o_7153_);
lean_dec_ref(v_deps_7152_);
lean_dec(v_v_7149_);
v___x_7174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7174_, 0, v_name_7151_);
lean_ctor_set(v___x_7174_, 1, v_ps_7148_);
v___x_7175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7175_, 0, v___x_7174_);
return v___x_7175_;
}
}
else
{
lean_object* v___x_7176_; lean_object* v___x_7177_; 
lean_dec_ref(v_deps_7152_);
lean_dec_ref(v_name_7151_);
lean_dec(v_ps_7148_);
v___x_7176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7176_, 0, v_v_7149_);
lean_ctor_set(v___x_7176_, 1, v_o_7153_);
v___x_7177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7177_, 0, v___x_7176_);
return v___x_7177_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(lean_object* v_ps_7178_, lean_object* v_as_7179_, size_t v_i_7180_, size_t v_stop_7181_, lean_object* v_b_7182_){
_start:
{
uint8_t v___x_7183_; 
v___x_7183_ = lean_usize_dec_eq(v_i_7180_, v_stop_7181_);
if (v___x_7183_ == 0)
{
lean_object* v_fst_7184_; lean_object* v_snd_7185_; lean_object* v___x_7186_; lean_object* v___x_7187_; 
v_fst_7184_ = lean_ctor_get(v_b_7182_, 0);
lean_inc(v_fst_7184_);
v_snd_7185_ = lean_ctor_get(v_b_7182_, 1);
lean_inc(v_snd_7185_);
lean_dec_ref(v_b_7182_);
v___x_7186_ = lean_array_uget_borrowed(v_as_7179_, v_i_7180_);
lean_inc(v_ps_7178_);
lean_inc(v___x_7186_);
v___x_7187_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(v___x_7186_, v_ps_7178_, v_fst_7184_, v_snd_7185_);
if (lean_obj_tag(v___x_7187_) == 0)
{
lean_dec(v_ps_7178_);
return v___x_7187_;
}
else
{
lean_object* v_a_7188_; size_t v___x_7189_; size_t v___x_7190_; 
v_a_7188_ = lean_ctor_get(v___x_7187_, 0);
lean_inc(v_a_7188_);
lean_dec_ref(v___x_7187_);
v___x_7189_ = ((size_t)1ULL);
v___x_7190_ = lean_usize_add(v_i_7180_, v___x_7189_);
v_i_7180_ = v___x_7190_;
v_b_7182_ = v_a_7188_;
goto _start;
}
}
else
{
lean_object* v___x_7192_; 
lean_dec(v_ps_7178_);
v___x_7192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7192_, 0, v_b_7182_);
return v___x_7192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2___boxed(lean_object* v_ps_7193_, lean_object* v_as_7194_, lean_object* v_i_7195_, lean_object* v_stop_7196_, lean_object* v_b_7197_){
_start:
{
size_t v_i_boxed_7198_; size_t v_stop_boxed_7199_; lean_object* v_res_7200_; 
v_i_boxed_7198_ = lean_unbox_usize(v_i_7195_);
lean_dec(v_i_7195_);
v_stop_boxed_7199_ = lean_unbox_usize(v_stop_7196_);
lean_dec(v_stop_7196_);
v_res_7200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7193_, v_as_7194_, v_i_boxed_7198_, v_stop_boxed_7199_, v_b_7197_);
lean_dec_ref(v_as_7194_);
return v_res_7200_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(lean_object* v_00_u03b2_7201_, lean_object* v_k_7202_, lean_object* v_t_7203_){
_start:
{
uint8_t v___x_7204_; 
v___x_7204_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_k_7202_, v_t_7203_);
return v___x_7204_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___boxed(lean_object* v_00_u03b2_7205_, lean_object* v_k_7206_, lean_object* v_t_7207_){
_start:
{
uint8_t v_res_7208_; lean_object* v_r_7209_; 
v_res_7208_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(v_00_u03b2_7205_, v_k_7206_, v_t_7207_);
lean_dec(v_t_7207_);
lean_dec_ref(v_k_7206_);
v_r_7209_ = lean_box(v_res_7208_);
return v_r_7209_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3(lean_object* v_00_u03b2_7210_, lean_object* v_k_7211_, lean_object* v_v_7212_, lean_object* v_t_7213_, lean_object* v_hl_7214_){
_start:
{
lean_object* v___x_7215_; 
v___x_7215_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7211_, v_v_7212_, v_t_7213_);
return v___x_7215_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0(lean_object* v_a_7217_, lean_object* v_a_7218_){
_start:
{
if (lean_obj_tag(v_a_7217_) == 0)
{
lean_object* v___x_7219_; 
v___x_7219_ = l_List_reverse___redArg(v_a_7218_);
return v___x_7219_;
}
else
{
lean_object* v_head_7220_; lean_object* v_tail_7221_; lean_object* v___x_7223_; uint8_t v_isShared_7224_; uint8_t v_isSharedCheck_7231_; 
v_head_7220_ = lean_ctor_get(v_a_7217_, 0);
v_tail_7221_ = lean_ctor_get(v_a_7217_, 1);
v_isSharedCheck_7231_ = !lean_is_exclusive(v_a_7217_);
if (v_isSharedCheck_7231_ == 0)
{
v___x_7223_ = v_a_7217_;
v_isShared_7224_ = v_isSharedCheck_7231_;
goto v_resetjp_7222_;
}
else
{
lean_inc(v_tail_7221_);
lean_inc(v_head_7220_);
lean_dec(v_a_7217_);
v___x_7223_ = lean_box(0);
v_isShared_7224_ = v_isSharedCheck_7231_;
goto v_resetjp_7222_;
}
v_resetjp_7222_:
{
lean_object* v___x_7225_; lean_object* v___x_7226_; lean_object* v___x_7228_; 
v___x_7225_ = ((lean_object*)(l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0));
v___x_7226_ = lean_string_append(v___x_7225_, v_head_7220_);
lean_dec(v_head_7220_);
if (v_isShared_7224_ == 0)
{
lean_ctor_set(v___x_7223_, 1, v_a_7218_);
lean_ctor_set(v___x_7223_, 0, v___x_7226_);
v___x_7228_ = v___x_7223_;
goto v_reusejp_7227_;
}
else
{
lean_object* v_reuseFailAlloc_7230_; 
v_reuseFailAlloc_7230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7230_, 0, v___x_7226_);
lean_ctor_set(v_reuseFailAlloc_7230_, 1, v_a_7218_);
v___x_7228_ = v_reuseFailAlloc_7230_;
goto v_reusejp_7227_;
}
v_reusejp_7227_:
{
v_a_7217_ = v_tail_7221_;
v_a_7218_ = v___x_7228_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(lean_object* v_cycle_7232_){
_start:
{
lean_object* v___x_7233_; lean_object* v___x_7234_; lean_object* v___x_7235_; lean_object* v___x_7236_; 
v___x_7233_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput___redArg___closed__1));
v___x_7234_ = lean_box(0);
v___x_7235_ = l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0(v_cycle_7232_, v___x_7234_);
v___x_7236_ = l_String_intercalate(v___x_7233_, v___x_7235_);
return v___x_7236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(lean_object* v_as_7237_, size_t v_i_7238_, size_t v_stop_7239_, lean_object* v_b_7240_){
_start:
{
uint8_t v___x_7241_; 
v___x_7241_ = lean_usize_dec_eq(v_i_7238_, v_stop_7239_);
if (v___x_7241_ == 0)
{
lean_object* v_fst_7242_; lean_object* v_snd_7243_; lean_object* v___x_7244_; lean_object* v___x_7245_; lean_object* v___x_7246_; 
v_fst_7242_ = lean_ctor_get(v_b_7240_, 0);
lean_inc(v_fst_7242_);
v_snd_7243_ = lean_ctor_get(v_b_7240_, 1);
lean_inc(v_snd_7243_);
lean_dec_ref(v_b_7240_);
v___x_7244_ = lean_array_uget_borrowed(v_as_7237_, v_i_7238_);
v___x_7245_ = lean_box(0);
lean_inc(v___x_7244_);
v___x_7246_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(v___x_7244_, v___x_7245_, v_fst_7242_, v_snd_7243_);
if (lean_obj_tag(v___x_7246_) == 0)
{
return v___x_7246_;
}
else
{
lean_object* v_a_7247_; size_t v___x_7248_; size_t v___x_7249_; 
v_a_7247_ = lean_ctor_get(v___x_7246_, 0);
lean_inc(v_a_7247_);
lean_dec_ref(v___x_7246_);
v___x_7248_ = ((size_t)1ULL);
v___x_7249_ = lean_usize_add(v_i_7238_, v___x_7248_);
v_i_7238_ = v___x_7249_;
v_b_7240_ = v_a_7247_;
goto _start;
}
}
else
{
lean_object* v___x_7251_; 
v___x_7251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7251_, 0, v_b_7240_);
return v___x_7251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1___boxed(lean_object* v_as_7252_, lean_object* v_i_7253_, lean_object* v_stop_7254_, lean_object* v_b_7255_){
_start:
{
size_t v_i_boxed_7256_; size_t v_stop_boxed_7257_; lean_object* v_res_7258_; 
v_i_boxed_7256_ = lean_unbox_usize(v_i_7253_);
lean_dec(v_i_7253_);
v_stop_boxed_7257_ = lean_unbox_usize(v_stop_7254_);
lean_dec(v_stop_7254_);
v_res_7258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(v_as_7252_, v_i_boxed_7256_, v_stop_boxed_7257_, v_b_7255_);
lean_dec_ref(v_as_7252_);
return v_res_7258_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(lean_object* v_libs_7265_, lean_object* v_a_7266_){
_start:
{
lean_object* v_snd_7269_; lean_object* v___y_7272_; lean_object* v___x_7296_; lean_object* v___x_7297_; lean_object* v___x_7298_; uint8_t v___x_7299_; 
v___x_7296_ = lean_unsigned_to_nat(0u);
v___x_7297_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1));
v___x_7298_ = lean_array_get_size(v_libs_7265_);
v___x_7299_ = lean_nat_dec_lt(v___x_7296_, v___x_7298_);
if (v___x_7299_ == 0)
{
v_snd_7269_ = v___x_7297_;
goto v___jp_7268_;
}
else
{
lean_object* v___x_7300_; uint8_t v___x_7301_; 
v___x_7300_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2));
v___x_7301_ = lean_nat_dec_le(v___x_7298_, v___x_7298_);
if (v___x_7301_ == 0)
{
if (v___x_7299_ == 0)
{
v_snd_7269_ = v___x_7297_;
goto v___jp_7268_;
}
else
{
size_t v___x_7302_; size_t v___x_7303_; lean_object* v___x_7304_; 
v___x_7302_ = ((size_t)0ULL);
v___x_7303_ = lean_usize_of_nat(v___x_7298_);
v___x_7304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(v_libs_7265_, v___x_7302_, v___x_7303_, v___x_7300_);
v___y_7272_ = v___x_7304_;
goto v___jp_7271_;
}
}
else
{
size_t v___x_7305_; size_t v___x_7306_; lean_object* v___x_7307_; 
v___x_7305_ = ((size_t)0ULL);
v___x_7306_ = lean_usize_of_nat(v___x_7298_);
v___x_7307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(v_libs_7265_, v___x_7305_, v___x_7306_, v___x_7300_);
v___y_7272_ = v___x_7307_;
goto v___jp_7271_;
}
}
v___jp_7268_:
{
lean_object* v___x_7270_; 
v___x_7270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7270_, 0, v_snd_7269_);
lean_ctor_set(v___x_7270_, 1, v_a_7266_);
return v___x_7270_;
}
v___jp_7271_:
{
if (lean_obj_tag(v___y_7272_) == 0)
{
lean_object* v_a_7273_; lean_object* v_log_7274_; uint8_t v_action_7275_; uint8_t v_wantsRebuild_7276_; lean_object* v_trace_7277_; lean_object* v_buildTime_7278_; lean_object* v___x_7280_; uint8_t v_isShared_7281_; uint8_t v_isSharedCheck_7293_; 
v_a_7273_ = lean_ctor_get(v___y_7272_, 0);
lean_inc(v_a_7273_);
lean_dec_ref(v___y_7272_);
v_log_7274_ = lean_ctor_get(v_a_7266_, 0);
v_action_7275_ = lean_ctor_get_uint8(v_a_7266_, sizeof(void*)*3);
v_wantsRebuild_7276_ = lean_ctor_get_uint8(v_a_7266_, sizeof(void*)*3 + 1);
v_trace_7277_ = lean_ctor_get(v_a_7266_, 1);
v_buildTime_7278_ = lean_ctor_get(v_a_7266_, 2);
v_isSharedCheck_7293_ = !lean_is_exclusive(v_a_7266_);
if (v_isSharedCheck_7293_ == 0)
{
v___x_7280_ = v_a_7266_;
v_isShared_7281_ = v_isSharedCheck_7293_;
goto v_resetjp_7279_;
}
else
{
lean_inc(v_buildTime_7278_);
lean_inc(v_trace_7277_);
lean_inc(v_log_7274_);
lean_dec(v_a_7266_);
v___x_7280_ = lean_box(0);
v_isShared_7281_ = v_isSharedCheck_7293_;
goto v_resetjp_7279_;
}
v_resetjp_7279_:
{
lean_object* v___x_7282_; lean_object* v___x_7283_; lean_object* v___x_7284_; uint8_t v___x_7285_; lean_object* v___x_7286_; lean_object* v___x_7287_; lean_object* v___x_7288_; lean_object* v___x_7290_; 
v___x_7282_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0));
v___x_7283_ = l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(v_a_7273_);
v___x_7284_ = lean_string_append(v___x_7282_, v___x_7283_);
lean_dec_ref(v___x_7283_);
v___x_7285_ = 3;
v___x_7286_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7286_, 0, v___x_7284_);
lean_ctor_set_uint8(v___x_7286_, sizeof(void*)*1, v___x_7285_);
v___x_7287_ = lean_array_get_size(v_log_7274_);
v___x_7288_ = lean_array_push(v_log_7274_, v___x_7286_);
if (v_isShared_7281_ == 0)
{
lean_ctor_set(v___x_7280_, 0, v___x_7288_);
v___x_7290_ = v___x_7280_;
goto v_reusejp_7289_;
}
else
{
lean_object* v_reuseFailAlloc_7292_; 
v_reuseFailAlloc_7292_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7292_, 0, v___x_7288_);
lean_ctor_set(v_reuseFailAlloc_7292_, 1, v_trace_7277_);
lean_ctor_set(v_reuseFailAlloc_7292_, 2, v_buildTime_7278_);
lean_ctor_set_uint8(v_reuseFailAlloc_7292_, sizeof(void*)*3, v_action_7275_);
lean_ctor_set_uint8(v_reuseFailAlloc_7292_, sizeof(void*)*3 + 1, v_wantsRebuild_7276_);
v___x_7290_ = v_reuseFailAlloc_7292_;
goto v_reusejp_7289_;
}
v_reusejp_7289_:
{
lean_object* v___x_7291_; 
v___x_7291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7291_, 0, v___x_7287_);
lean_ctor_set(v___x_7291_, 1, v___x_7290_);
return v___x_7291_;
}
}
}
else
{
lean_object* v_a_7294_; lean_object* v_snd_7295_; 
v_a_7294_ = lean_ctor_get(v___y_7272_, 0);
lean_inc(v_a_7294_);
lean_dec_ref(v___y_7272_);
v_snd_7295_ = lean_ctor_get(v_a_7294_, 1);
lean_inc(v_snd_7295_);
lean_dec(v_a_7294_);
v_snd_7269_ = v_snd_7295_;
goto v___jp_7268_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___boxed(lean_object* v_libs_7308_, lean_object* v_a_7309_, lean_object* v_a_7310_){
_start:
{
lean_object* v_res_7311_; 
v_res_7311_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7308_, v_a_7309_);
lean_dec_ref(v_libs_7308_);
return v_res_7311_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder(lean_object* v_libs_7312_, lean_object* v_a_7313_, lean_object* v_a_7314_, lean_object* v_a_7315_, lean_object* v_a_7316_, lean_object* v_a_7317_, lean_object* v_a_7318_){
_start:
{
lean_object* v___x_7320_; 
v___x_7320_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7312_, v_a_7318_);
return v___x_7320_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___boxed(lean_object* v_libs_7321_, lean_object* v_a_7322_, lean_object* v_a_7323_, lean_object* v_a_7324_, lean_object* v_a_7325_, lean_object* v_a_7326_, lean_object* v_a_7327_, lean_object* v_a_7328_){
_start:
{
lean_object* v_res_7329_; 
v_res_7329_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder(v_libs_7321_, v_a_7322_, v_a_7323_, v_a_7324_, v_a_7325_, v_a_7326_, v_a_7327_);
lean_dec_ref(v_a_7326_);
lean_dec(v_a_7325_);
lean_dec(v_a_7324_);
lean_dec(v_a_7323_);
lean_dec_ref(v_a_7322_);
lean_dec_ref(v_libs_7321_);
return v_res_7329_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0(lean_object* v_objs_7330_, lean_object* v_weakArgs_7331_, lean_object* v_traceArgs_7332_, lean_object* v_libFile_7333_, lean_object* v_linker_7334_, lean_object* v_libs_7335_, lean_object* v___y_7336_, lean_object* v___y_7337_, lean_object* v___y_7338_, lean_object* v___y_7339_, lean_object* v___y_7340_, lean_object* v___y_7341_){
_start:
{
lean_object* v_log_7343_; uint8_t v_action_7344_; uint8_t v_wantsRebuild_7345_; lean_object* v_trace_7346_; lean_object* v_buildTime_7347_; lean_object* v___x_7349_; uint8_t v_isShared_7350_; uint8_t v_isSharedCheck_7379_; 
v_log_7343_ = lean_ctor_get(v___y_7341_, 0);
v_action_7344_ = lean_ctor_get_uint8(v___y_7341_, sizeof(void*)*3);
v_wantsRebuild_7345_ = lean_ctor_get_uint8(v___y_7341_, sizeof(void*)*3 + 1);
v_trace_7346_ = lean_ctor_get(v___y_7341_, 1);
v_buildTime_7347_ = lean_ctor_get(v___y_7341_, 2);
v_isSharedCheck_7379_ = !lean_is_exclusive(v___y_7341_);
if (v_isSharedCheck_7379_ == 0)
{
v___x_7349_ = v___y_7341_;
v_isShared_7350_ = v_isSharedCheck_7379_;
goto v_resetjp_7348_;
}
else
{
lean_inc(v_buildTime_7347_);
lean_inc(v_trace_7346_);
lean_inc(v_log_7343_);
lean_dec(v___y_7341_);
v___x_7349_ = lean_box(0);
v_isShared_7350_ = v_isSharedCheck_7379_;
goto v_resetjp_7348_;
}
v_resetjp_7348_:
{
lean_object* v___x_7351_; lean_object* v___x_7352_; lean_object* v___x_7353_; lean_object* v___x_7354_; 
v___x_7351_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7330_, v_libs_7335_);
v___x_7352_ = l_Array_append___redArg(v___x_7351_, v_weakArgs_7331_);
v___x_7353_ = l_Array_append___redArg(v___x_7352_, v_traceArgs_7332_);
v___x_7354_ = l_Lake_compileSharedLib(v_libFile_7333_, v___x_7353_, v_linker_7334_, v_log_7343_);
if (lean_obj_tag(v___x_7354_) == 0)
{
lean_object* v_a_7355_; lean_object* v_a_7356_; lean_object* v___x_7358_; uint8_t v_isShared_7359_; uint8_t v_isSharedCheck_7366_; 
v_a_7355_ = lean_ctor_get(v___x_7354_, 0);
v_a_7356_ = lean_ctor_get(v___x_7354_, 1);
v_isSharedCheck_7366_ = !lean_is_exclusive(v___x_7354_);
if (v_isSharedCheck_7366_ == 0)
{
v___x_7358_ = v___x_7354_;
v_isShared_7359_ = v_isSharedCheck_7366_;
goto v_resetjp_7357_;
}
else
{
lean_inc(v_a_7356_);
lean_inc(v_a_7355_);
lean_dec(v___x_7354_);
v___x_7358_ = lean_box(0);
v_isShared_7359_ = v_isSharedCheck_7366_;
goto v_resetjp_7357_;
}
v_resetjp_7357_:
{
lean_object* v___x_7361_; 
if (v_isShared_7350_ == 0)
{
lean_ctor_set(v___x_7349_, 0, v_a_7356_);
v___x_7361_ = v___x_7349_;
goto v_reusejp_7360_;
}
else
{
lean_object* v_reuseFailAlloc_7365_; 
v_reuseFailAlloc_7365_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7365_, 0, v_a_7356_);
lean_ctor_set(v_reuseFailAlloc_7365_, 1, v_trace_7346_);
lean_ctor_set(v_reuseFailAlloc_7365_, 2, v_buildTime_7347_);
lean_ctor_set_uint8(v_reuseFailAlloc_7365_, sizeof(void*)*3, v_action_7344_);
lean_ctor_set_uint8(v_reuseFailAlloc_7365_, sizeof(void*)*3 + 1, v_wantsRebuild_7345_);
v___x_7361_ = v_reuseFailAlloc_7365_;
goto v_reusejp_7360_;
}
v_reusejp_7360_:
{
lean_object* v___x_7363_; 
if (v_isShared_7359_ == 0)
{
lean_ctor_set(v___x_7358_, 1, v___x_7361_);
v___x_7363_ = v___x_7358_;
goto v_reusejp_7362_;
}
else
{
lean_object* v_reuseFailAlloc_7364_; 
v_reuseFailAlloc_7364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7364_, 0, v_a_7355_);
lean_ctor_set(v_reuseFailAlloc_7364_, 1, v___x_7361_);
v___x_7363_ = v_reuseFailAlloc_7364_;
goto v_reusejp_7362_;
}
v_reusejp_7362_:
{
return v___x_7363_;
}
}
}
}
else
{
lean_object* v_a_7367_; lean_object* v_a_7368_; lean_object* v___x_7370_; uint8_t v_isShared_7371_; uint8_t v_isSharedCheck_7378_; 
v_a_7367_ = lean_ctor_get(v___x_7354_, 0);
v_a_7368_ = lean_ctor_get(v___x_7354_, 1);
v_isSharedCheck_7378_ = !lean_is_exclusive(v___x_7354_);
if (v_isSharedCheck_7378_ == 0)
{
v___x_7370_ = v___x_7354_;
v_isShared_7371_ = v_isSharedCheck_7378_;
goto v_resetjp_7369_;
}
else
{
lean_inc(v_a_7368_);
lean_inc(v_a_7367_);
lean_dec(v___x_7354_);
v___x_7370_ = lean_box(0);
v_isShared_7371_ = v_isSharedCheck_7378_;
goto v_resetjp_7369_;
}
v_resetjp_7369_:
{
lean_object* v___x_7373_; 
if (v_isShared_7350_ == 0)
{
lean_ctor_set(v___x_7349_, 0, v_a_7368_);
v___x_7373_ = v___x_7349_;
goto v_reusejp_7372_;
}
else
{
lean_object* v_reuseFailAlloc_7377_; 
v_reuseFailAlloc_7377_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7377_, 0, v_a_7368_);
lean_ctor_set(v_reuseFailAlloc_7377_, 1, v_trace_7346_);
lean_ctor_set(v_reuseFailAlloc_7377_, 2, v_buildTime_7347_);
lean_ctor_set_uint8(v_reuseFailAlloc_7377_, sizeof(void*)*3, v_action_7344_);
lean_ctor_set_uint8(v_reuseFailAlloc_7377_, sizeof(void*)*3 + 1, v_wantsRebuild_7345_);
v___x_7373_ = v_reuseFailAlloc_7377_;
goto v_reusejp_7372_;
}
v_reusejp_7372_:
{
lean_object* v___x_7375_; 
if (v_isShared_7371_ == 0)
{
lean_ctor_set(v___x_7370_, 1, v___x_7373_);
v___x_7375_ = v___x_7370_;
goto v_reusejp_7374_;
}
else
{
lean_object* v_reuseFailAlloc_7376_; 
v_reuseFailAlloc_7376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7376_, 0, v_a_7367_);
lean_ctor_set(v_reuseFailAlloc_7376_, 1, v___x_7373_);
v___x_7375_ = v_reuseFailAlloc_7376_;
goto v_reusejp_7374_;
}
v_reusejp_7374_:
{
return v___x_7375_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object* v_objs_7380_, lean_object* v_weakArgs_7381_, lean_object* v_traceArgs_7382_, lean_object* v_libFile_7383_, lean_object* v_linker_7384_, lean_object* v_libs_7385_, lean_object* v___y_7386_, lean_object* v___y_7387_, lean_object* v___y_7388_, lean_object* v___y_7389_, lean_object* v___y_7390_, lean_object* v___y_7391_, lean_object* v___y_7392_){
_start:
{
lean_object* v_res_7393_; 
v_res_7393_ = l_Lake_buildSharedLib___lam__0(v_objs_7380_, v_weakArgs_7381_, v_traceArgs_7382_, v_libFile_7383_, v_linker_7384_, v_libs_7385_, v___y_7386_, v___y_7387_, v___y_7388_, v___y_7389_, v___y_7390_, v___y_7391_);
lean_dec_ref(v___y_7390_);
lean_dec(v___y_7389_);
lean_dec(v___y_7388_);
lean_dec(v___y_7387_);
lean_dec_ref(v___y_7386_);
lean_dec_ref(v_libs_7385_);
lean_dec_ref(v_traceArgs_7382_);
lean_dec_ref(v_weakArgs_7381_);
lean_dec_ref(v_objs_7380_);
return v_res_7393_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1(uint8_t v_linkDeps_7394_, lean_object* v___x_7395_, lean_object* v___f_7396_, lean_object* v_libs_7397_, lean_object* v___y_7398_, lean_object* v___y_7399_, lean_object* v___y_7400_, lean_object* v___y_7401_, lean_object* v___y_7402_, lean_object* v___y_7403_){
_start:
{
if (v_linkDeps_7394_ == 0)
{
lean_object* v___x_7405_; lean_object* v___x_7406_; 
v___x_7405_ = lean_mk_empty_array_with_capacity(v___x_7395_);
v___x_7406_ = lean_apply_8(v___f_7396_, v___x_7405_, v___y_7398_, v___y_7399_, v___y_7400_, v___y_7401_, v___y_7402_, v___y_7403_, lean_box(0));
return v___x_7406_;
}
else
{
lean_object* v___x_7407_; 
v___x_7407_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7397_, v___y_7403_);
if (lean_obj_tag(v___x_7407_) == 0)
{
lean_object* v_a_7408_; lean_object* v_a_7409_; lean_object* v___x_7410_; 
v_a_7408_ = lean_ctor_get(v___x_7407_, 0);
lean_inc(v_a_7408_);
v_a_7409_ = lean_ctor_get(v___x_7407_, 1);
lean_inc(v_a_7409_);
lean_dec_ref(v___x_7407_);
v___x_7410_ = lean_apply_8(v___f_7396_, v_a_7408_, v___y_7398_, v___y_7399_, v___y_7400_, v___y_7401_, v___y_7402_, v_a_7409_, lean_box(0));
return v___x_7410_;
}
else
{
lean_object* v_a_7411_; lean_object* v_a_7412_; lean_object* v___x_7414_; uint8_t v_isShared_7415_; uint8_t v_isSharedCheck_7419_; 
lean_dec_ref(v___y_7402_);
lean_dec(v___y_7401_);
lean_dec(v___y_7400_);
lean_dec(v___y_7399_);
lean_dec_ref(v___y_7398_);
lean_dec_ref(v___f_7396_);
v_a_7411_ = lean_ctor_get(v___x_7407_, 0);
v_a_7412_ = lean_ctor_get(v___x_7407_, 1);
v_isSharedCheck_7419_ = !lean_is_exclusive(v___x_7407_);
if (v_isSharedCheck_7419_ == 0)
{
v___x_7414_ = v___x_7407_;
v_isShared_7415_ = v_isSharedCheck_7419_;
goto v_resetjp_7413_;
}
else
{
lean_inc(v_a_7412_);
lean_inc(v_a_7411_);
lean_dec(v___x_7407_);
v___x_7414_ = lean_box(0);
v_isShared_7415_ = v_isSharedCheck_7419_;
goto v_resetjp_7413_;
}
v_resetjp_7413_:
{
lean_object* v___x_7417_; 
if (v_isShared_7415_ == 0)
{
v___x_7417_ = v___x_7414_;
goto v_reusejp_7416_;
}
else
{
lean_object* v_reuseFailAlloc_7418_; 
v_reuseFailAlloc_7418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7418_, 0, v_a_7411_);
lean_ctor_set(v_reuseFailAlloc_7418_, 1, v_a_7412_);
v___x_7417_ = v_reuseFailAlloc_7418_;
goto v_reusejp_7416_;
}
v_reusejp_7416_:
{
return v___x_7417_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1___boxed(lean_object* v_linkDeps_7420_, lean_object* v___x_7421_, lean_object* v___f_7422_, lean_object* v_libs_7423_, lean_object* v___y_7424_, lean_object* v___y_7425_, lean_object* v___y_7426_, lean_object* v___y_7427_, lean_object* v___y_7428_, lean_object* v___y_7429_, lean_object* v___y_7430_){
_start:
{
uint8_t v_linkDeps_boxed_7431_; lean_object* v_res_7432_; 
v_linkDeps_boxed_7431_ = lean_unbox(v_linkDeps_7420_);
v_res_7432_ = l_Lake_buildSharedLib___lam__1(v_linkDeps_boxed_7431_, v___x_7421_, v___f_7422_, v_libs_7423_, v___y_7424_, v___y_7425_, v___y_7426_, v___y_7427_, v___y_7428_, v___y_7429_);
lean_dec_ref(v_libs_7423_);
lean_dec(v___x_7421_);
return v_res_7432_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2(lean_object* v_traceArgs_7433_, lean_object* v_extraDepTrace_7434_, uint8_t v_linkDeps_7435_, lean_object* v___f_7436_, lean_object* v_libFile_7437_, lean_object* v_libName_7438_, uint8_t v_plugin_7439_, lean_object* v_libs_7440_, lean_object* v___y_7441_, lean_object* v___y_7442_, lean_object* v___y_7443_, lean_object* v___y_7444_, lean_object* v___y_7445_, lean_object* v___y_7446_){
_start:
{
uint64_t v___y_7449_; uint64_t v___x_7526_; lean_object* v___x_7527_; lean_object* v___x_7528_; uint8_t v___x_7529_; 
v___x_7526_ = l_Lake_Hash_nil;
v___x_7527_ = lean_unsigned_to_nat(0u);
v___x_7528_ = lean_array_get_size(v_traceArgs_7433_);
v___x_7529_ = lean_nat_dec_lt(v___x_7527_, v___x_7528_);
if (v___x_7529_ == 0)
{
v___y_7449_ = v___x_7526_;
goto v___jp_7448_;
}
else
{
uint8_t v___x_7530_; 
v___x_7530_ = lean_nat_dec_le(v___x_7528_, v___x_7528_);
if (v___x_7530_ == 0)
{
if (v___x_7529_ == 0)
{
v___y_7449_ = v___x_7526_;
goto v___jp_7448_;
}
else
{
size_t v___x_7531_; size_t v___x_7532_; uint64_t v___x_7533_; 
v___x_7531_ = ((size_t)0ULL);
v___x_7532_ = lean_usize_of_nat(v___x_7528_);
v___x_7533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7433_, v___x_7531_, v___x_7532_, v___x_7526_);
v___y_7449_ = v___x_7533_;
goto v___jp_7448_;
}
}
else
{
size_t v___x_7534_; size_t v___x_7535_; uint64_t v___x_7536_; 
v___x_7534_ = ((size_t)0ULL);
v___x_7535_ = lean_usize_of_nat(v___x_7528_);
v___x_7536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7433_, v___x_7534_, v___x_7535_, v___x_7526_);
v___y_7449_ = v___x_7536_;
goto v___jp_7448_;
}
}
v___jp_7448_:
{
lean_object* v_log_7450_; uint8_t v_action_7451_; uint8_t v_wantsRebuild_7452_; lean_object* v_trace_7453_; lean_object* v_buildTime_7454_; lean_object* v___x_7456_; uint8_t v_isShared_7457_; uint8_t v_isSharedCheck_7525_; 
v_log_7450_ = lean_ctor_get(v___y_7446_, 0);
v_action_7451_ = lean_ctor_get_uint8(v___y_7446_, sizeof(void*)*3);
v_wantsRebuild_7452_ = lean_ctor_get_uint8(v___y_7446_, sizeof(void*)*3 + 1);
v_trace_7453_ = lean_ctor_get(v___y_7446_, 1);
v_buildTime_7454_ = lean_ctor_get(v___y_7446_, 2);
v_isSharedCheck_7525_ = !lean_is_exclusive(v___y_7446_);
if (v_isSharedCheck_7525_ == 0)
{
v___x_7456_ = v___y_7446_;
v_isShared_7457_ = v_isSharedCheck_7525_;
goto v_resetjp_7455_;
}
else
{
lean_inc(v_buildTime_7454_);
lean_inc(v_trace_7453_);
lean_inc(v_log_7450_);
lean_dec(v___y_7446_);
v___x_7456_ = lean_box(0);
v_isShared_7457_ = v_isSharedCheck_7525_;
goto v_resetjp_7455_;
}
v_resetjp_7455_:
{
lean_object* v___x_7458_; lean_object* v___x_7459_; lean_object* v___x_7460_; lean_object* v___x_7461_; lean_object* v___x_7462_; lean_object* v___x_7463_; lean_object* v___x_7464_; lean_object* v___x_7465_; lean_object* v___x_7466_; lean_object* v___x_7467_; lean_object* v___x_7468_; lean_object* v___x_7469_; lean_object* v___x_7470_; lean_object* v___x_7472_; 
v___x_7458_ = lean_unsigned_to_nat(0u);
v___x_7459_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_7460_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_7461_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_7462_ = lean_array_to_list(v_traceArgs_7433_);
v___x_7463_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_7462_);
lean_dec(v___x_7462_);
v___x_7464_ = lean_string_append(v___x_7461_, v___x_7463_);
lean_dec_ref(v___x_7463_);
v___x_7465_ = lean_string_append(v___x_7460_, v___x_7464_);
lean_dec_ref(v___x_7464_);
v___x_7466_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_7467_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_7467_, 0, v___x_7465_);
lean_ctor_set(v___x_7467_, 1, v___x_7459_);
lean_ctor_set(v___x_7467_, 2, v___x_7466_);
lean_ctor_set_uint64(v___x_7467_, sizeof(void*)*3, v___y_7449_);
v___x_7468_ = l_Lake_BuildTrace_mix(v_trace_7453_, v___x_7467_);
v___x_7469_ = l_Lake_platformTrace;
v___x_7470_ = l_Lake_BuildTrace_mix(v___x_7468_, v___x_7469_);
if (v_isShared_7457_ == 0)
{
lean_ctor_set(v___x_7456_, 1, v___x_7470_);
v___x_7472_ = v___x_7456_;
goto v_reusejp_7471_;
}
else
{
lean_object* v_reuseFailAlloc_7524_; 
v_reuseFailAlloc_7524_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7524_, 0, v_log_7450_);
lean_ctor_set(v_reuseFailAlloc_7524_, 1, v___x_7470_);
lean_ctor_set(v_reuseFailAlloc_7524_, 2, v_buildTime_7454_);
lean_ctor_set_uint8(v_reuseFailAlloc_7524_, sizeof(void*)*3, v_action_7451_);
lean_ctor_set_uint8(v_reuseFailAlloc_7524_, sizeof(void*)*3 + 1, v_wantsRebuild_7452_);
v___x_7472_ = v_reuseFailAlloc_7524_;
goto v_reusejp_7471_;
}
v_reusejp_7471_:
{
lean_object* v___x_7473_; 
lean_inc_ref(v___y_7445_);
lean_inc(v___y_7444_);
lean_inc(v___y_7443_);
lean_inc(v___y_7442_);
lean_inc_ref(v___y_7441_);
v___x_7473_ = lean_apply_7(v_extraDepTrace_7434_, v___y_7441_, v___y_7442_, v___y_7443_, v___y_7444_, v___y_7445_, v___x_7472_, lean_box(0));
if (lean_obj_tag(v___x_7473_) == 0)
{
lean_object* v_a_7474_; lean_object* v_a_7475_; lean_object* v_log_7476_; uint8_t v_action_7477_; uint8_t v_wantsRebuild_7478_; lean_object* v_trace_7479_; lean_object* v_buildTime_7480_; lean_object* v___x_7482_; uint8_t v_isShared_7483_; uint8_t v_isSharedCheck_7514_; 
v_a_7474_ = lean_ctor_get(v___x_7473_, 1);
lean_inc(v_a_7474_);
v_a_7475_ = lean_ctor_get(v___x_7473_, 0);
lean_inc(v_a_7475_);
lean_dec_ref(v___x_7473_);
v_log_7476_ = lean_ctor_get(v_a_7474_, 0);
v_action_7477_ = lean_ctor_get_uint8(v_a_7474_, sizeof(void*)*3);
v_wantsRebuild_7478_ = lean_ctor_get_uint8(v_a_7474_, sizeof(void*)*3 + 1);
v_trace_7479_ = lean_ctor_get(v_a_7474_, 1);
v_buildTime_7480_ = lean_ctor_get(v_a_7474_, 2);
v_isSharedCheck_7514_ = !lean_is_exclusive(v_a_7474_);
if (v_isSharedCheck_7514_ == 0)
{
v___x_7482_ = v_a_7474_;
v_isShared_7483_ = v_isSharedCheck_7514_;
goto v_resetjp_7481_;
}
else
{
lean_inc(v_buildTime_7480_);
lean_inc(v_trace_7479_);
lean_inc(v_log_7476_);
lean_dec(v_a_7474_);
v___x_7482_ = lean_box(0);
v_isShared_7483_ = v_isSharedCheck_7514_;
goto v_resetjp_7481_;
}
v_resetjp_7481_:
{
lean_object* v___x_7484_; lean_object* v___y_7485_; lean_object* v___x_7486_; lean_object* v___x_7488_; 
v___x_7484_ = lean_box(v_linkDeps_7435_);
lean_inc_ref(v_libs_7440_);
v___y_7485_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__1___boxed), 11, 4);
lean_closure_set(v___y_7485_, 0, v___x_7484_);
lean_closure_set(v___y_7485_, 1, v___x_7458_);
lean_closure_set(v___y_7485_, 2, v___f_7436_);
lean_closure_set(v___y_7485_, 3, v_libs_7440_);
v___x_7486_ = l_Lake_BuildTrace_mix(v_trace_7479_, v_a_7475_);
if (v_isShared_7483_ == 0)
{
lean_ctor_set(v___x_7482_, 1, v___x_7486_);
v___x_7488_ = v___x_7482_;
goto v_reusejp_7487_;
}
else
{
lean_object* v_reuseFailAlloc_7513_; 
v_reuseFailAlloc_7513_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7513_, 0, v_log_7476_);
lean_ctor_set(v_reuseFailAlloc_7513_, 1, v___x_7486_);
lean_ctor_set(v_reuseFailAlloc_7513_, 2, v_buildTime_7480_);
lean_ctor_set_uint8(v_reuseFailAlloc_7513_, sizeof(void*)*3, v_action_7477_);
lean_ctor_set_uint8(v_reuseFailAlloc_7513_, sizeof(void*)*3 + 1, v_wantsRebuild_7478_);
v___x_7488_ = v_reuseFailAlloc_7513_;
goto v_reusejp_7487_;
}
v_reusejp_7487_:
{
uint8_t v___x_7489_; uint8_t v___x_7490_; lean_object* v___x_7491_; lean_object* v___x_7492_; 
v___x_7489_ = 1;
v___x_7490_ = 0;
v___x_7491_ = l_Lake_sharedLibExt;
v___x_7492_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_7437_, v___y_7485_, v___x_7490_, v___x_7491_, v___x_7489_, v___x_7490_, v___y_7441_, v___y_7442_, v___y_7443_, v___y_7444_, v___y_7445_, v___x_7488_);
if (lean_obj_tag(v___x_7492_) == 0)
{
lean_object* v_a_7493_; lean_object* v_a_7494_; lean_object* v___x_7496_; uint8_t v_isShared_7497_; uint8_t v_isSharedCheck_7503_; 
v_a_7493_ = lean_ctor_get(v___x_7492_, 0);
v_a_7494_ = lean_ctor_get(v___x_7492_, 1);
v_isSharedCheck_7503_ = !lean_is_exclusive(v___x_7492_);
if (v_isSharedCheck_7503_ == 0)
{
v___x_7496_ = v___x_7492_;
v_isShared_7497_ = v_isSharedCheck_7503_;
goto v_resetjp_7495_;
}
else
{
lean_inc(v_a_7494_);
lean_inc(v_a_7493_);
lean_dec(v___x_7492_);
v___x_7496_ = lean_box(0);
v_isShared_7497_ = v_isSharedCheck_7503_;
goto v_resetjp_7495_;
}
v_resetjp_7495_:
{
lean_object* v_path_7498_; lean_object* v___x_7499_; lean_object* v___x_7501_; 
v_path_7498_ = lean_ctor_get(v_a_7493_, 1);
lean_inc_ref(v_path_7498_);
lean_dec(v_a_7493_);
v___x_7499_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_7499_, 0, v_path_7498_);
lean_ctor_set(v___x_7499_, 1, v_libName_7438_);
lean_ctor_set(v___x_7499_, 2, v_libs_7440_);
lean_ctor_set_uint8(v___x_7499_, sizeof(void*)*3, v_plugin_7439_);
if (v_isShared_7497_ == 0)
{
lean_ctor_set(v___x_7496_, 0, v___x_7499_);
v___x_7501_ = v___x_7496_;
goto v_reusejp_7500_;
}
else
{
lean_object* v_reuseFailAlloc_7502_; 
v_reuseFailAlloc_7502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7502_, 0, v___x_7499_);
lean_ctor_set(v_reuseFailAlloc_7502_, 1, v_a_7494_);
v___x_7501_ = v_reuseFailAlloc_7502_;
goto v_reusejp_7500_;
}
v_reusejp_7500_:
{
return v___x_7501_;
}
}
}
else
{
lean_object* v_a_7504_; lean_object* v_a_7505_; lean_object* v___x_7507_; uint8_t v_isShared_7508_; uint8_t v_isSharedCheck_7512_; 
lean_dec_ref(v_libs_7440_);
lean_dec_ref(v_libName_7438_);
v_a_7504_ = lean_ctor_get(v___x_7492_, 0);
v_a_7505_ = lean_ctor_get(v___x_7492_, 1);
v_isSharedCheck_7512_ = !lean_is_exclusive(v___x_7492_);
if (v_isSharedCheck_7512_ == 0)
{
v___x_7507_ = v___x_7492_;
v_isShared_7508_ = v_isSharedCheck_7512_;
goto v_resetjp_7506_;
}
else
{
lean_inc(v_a_7505_);
lean_inc(v_a_7504_);
lean_dec(v___x_7492_);
v___x_7507_ = lean_box(0);
v_isShared_7508_ = v_isSharedCheck_7512_;
goto v_resetjp_7506_;
}
v_resetjp_7506_:
{
lean_object* v___x_7510_; 
if (v_isShared_7508_ == 0)
{
v___x_7510_ = v___x_7507_;
goto v_reusejp_7509_;
}
else
{
lean_object* v_reuseFailAlloc_7511_; 
v_reuseFailAlloc_7511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7511_, 0, v_a_7504_);
lean_ctor_set(v_reuseFailAlloc_7511_, 1, v_a_7505_);
v___x_7510_ = v_reuseFailAlloc_7511_;
goto v_reusejp_7509_;
}
v_reusejp_7509_:
{
return v___x_7510_;
}
}
}
}
}
}
else
{
lean_object* v_a_7515_; lean_object* v_a_7516_; lean_object* v___x_7518_; uint8_t v_isShared_7519_; uint8_t v_isSharedCheck_7523_; 
lean_dec_ref(v___y_7445_);
lean_dec(v___y_7444_);
lean_dec(v___y_7443_);
lean_dec(v___y_7442_);
lean_dec_ref(v___y_7441_);
lean_dec_ref(v_libs_7440_);
lean_dec_ref(v_libName_7438_);
lean_dec_ref(v_libFile_7437_);
lean_dec_ref(v___f_7436_);
v_a_7515_ = lean_ctor_get(v___x_7473_, 0);
v_a_7516_ = lean_ctor_get(v___x_7473_, 1);
v_isSharedCheck_7523_ = !lean_is_exclusive(v___x_7473_);
if (v_isSharedCheck_7523_ == 0)
{
v___x_7518_ = v___x_7473_;
v_isShared_7519_ = v_isSharedCheck_7523_;
goto v_resetjp_7517_;
}
else
{
lean_inc(v_a_7516_);
lean_inc(v_a_7515_);
lean_dec(v___x_7473_);
v___x_7518_ = lean_box(0);
v_isShared_7519_ = v_isSharedCheck_7523_;
goto v_resetjp_7517_;
}
v_resetjp_7517_:
{
lean_object* v___x_7521_; 
if (v_isShared_7519_ == 0)
{
v___x_7521_ = v___x_7518_;
goto v_reusejp_7520_;
}
else
{
lean_object* v_reuseFailAlloc_7522_; 
v_reuseFailAlloc_7522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7522_, 0, v_a_7515_);
lean_ctor_set(v_reuseFailAlloc_7522_, 1, v_a_7516_);
v___x_7521_ = v_reuseFailAlloc_7522_;
goto v_reusejp_7520_;
}
v_reusejp_7520_:
{
return v___x_7521_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2___boxed(lean_object* v_traceArgs_7537_, lean_object* v_extraDepTrace_7538_, lean_object* v_linkDeps_7539_, lean_object* v___f_7540_, lean_object* v_libFile_7541_, lean_object* v_libName_7542_, lean_object* v_plugin_7543_, lean_object* v_libs_7544_, lean_object* v___y_7545_, lean_object* v___y_7546_, lean_object* v___y_7547_, lean_object* v___y_7548_, lean_object* v___y_7549_, lean_object* v___y_7550_, lean_object* v___y_7551_){
_start:
{
uint8_t v_linkDeps_boxed_7552_; uint8_t v_plugin_boxed_7553_; lean_object* v_res_7554_; 
v_linkDeps_boxed_7552_ = lean_unbox(v_linkDeps_7539_);
v_plugin_boxed_7553_ = lean_unbox(v_plugin_7543_);
v_res_7554_ = l_Lake_buildSharedLib___lam__2(v_traceArgs_7537_, v_extraDepTrace_7538_, v_linkDeps_boxed_7552_, v___f_7540_, v_libFile_7541_, v_libName_7542_, v_plugin_boxed_7553_, v_libs_7544_, v___y_7545_, v___y_7546_, v___y_7547_, v___y_7548_, v___y_7549_, v___y_7550_);
return v_res_7554_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3(lean_object* v_weakArgs_7556_, lean_object* v_traceArgs_7557_, lean_object* v_libFile_7558_, lean_object* v_linker_7559_, lean_object* v_extraDepTrace_7560_, uint8_t v_linkDeps_7561_, lean_object* v_libName_7562_, uint8_t v_plugin_7563_, lean_object* v_linkLibs_7564_, lean_object* v___x_7565_, lean_object* v_objs_7566_, lean_object* v___y_7567_, lean_object* v___y_7568_, lean_object* v___y_7569_, lean_object* v___y_7570_, lean_object* v___y_7571_, lean_object* v___y_7572_){
_start:
{
lean_object* v_trace_7574_; lean_object* v___f_7575_; lean_object* v___x_7576_; lean_object* v___x_7577_; lean_object* v___f_7578_; lean_object* v___x_7579_; lean_object* v___x_7580_; lean_object* v___x_7581_; uint8_t v___x_7582_; lean_object* v___x_7583_; lean_object* v___x_7584_; 
v_trace_7574_ = lean_ctor_get(v___y_7572_, 1);
lean_inc_ref(v_libFile_7558_);
lean_inc_ref(v_traceArgs_7557_);
v___f_7575_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__0___boxed), 13, 5);
lean_closure_set(v___f_7575_, 0, v_objs_7566_);
lean_closure_set(v___f_7575_, 1, v_weakArgs_7556_);
lean_closure_set(v___f_7575_, 2, v_traceArgs_7557_);
lean_closure_set(v___f_7575_, 3, v_libFile_7558_);
lean_closure_set(v___f_7575_, 4, v_linker_7559_);
v___x_7576_ = lean_box(v_linkDeps_7561_);
v___x_7577_ = lean_box(v_plugin_7563_);
v___f_7578_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__2___boxed), 15, 7);
lean_closure_set(v___f_7578_, 0, v_traceArgs_7557_);
lean_closure_set(v___f_7578_, 1, v_extraDepTrace_7560_);
lean_closure_set(v___f_7578_, 2, v___x_7576_);
lean_closure_set(v___f_7578_, 3, v___f_7575_);
lean_closure_set(v___f_7578_, 4, v_libFile_7558_);
lean_closure_set(v___f_7578_, 5, v_libName_7562_);
lean_closure_set(v___f_7578_, 6, v___x_7577_);
v___x_7579_ = ((lean_object*)(l_Lake_buildSharedLib___lam__3___closed__0));
v___x_7580_ = l_Lake_Job_collectArray___redArg(v_linkLibs_7564_, v___x_7579_);
v___x_7581_ = lean_unsigned_to_nat(0u);
v___x_7582_ = 0;
lean_inc_ref(v_trace_7574_);
v___x_7583_ = l_Lake_Job_mapM___redArg(v___x_7565_, v___x_7580_, v___f_7578_, v___x_7581_, v___x_7582_, v___y_7567_, v___y_7568_, v___y_7569_, v___y_7570_, v___y_7571_, v_trace_7574_);
v___x_7584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7584_, 0, v___x_7583_);
lean_ctor_set(v___x_7584_, 1, v___y_7572_);
return v___x_7584_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3___boxed(lean_object** _args){
lean_object* v_weakArgs_7585_ = _args[0];
lean_object* v_traceArgs_7586_ = _args[1];
lean_object* v_libFile_7587_ = _args[2];
lean_object* v_linker_7588_ = _args[3];
lean_object* v_extraDepTrace_7589_ = _args[4];
lean_object* v_linkDeps_7590_ = _args[5];
lean_object* v_libName_7591_ = _args[6];
lean_object* v_plugin_7592_ = _args[7];
lean_object* v_linkLibs_7593_ = _args[8];
lean_object* v___x_7594_ = _args[9];
lean_object* v_objs_7595_ = _args[10];
lean_object* v___y_7596_ = _args[11];
lean_object* v___y_7597_ = _args[12];
lean_object* v___y_7598_ = _args[13];
lean_object* v___y_7599_ = _args[14];
lean_object* v___y_7600_ = _args[15];
lean_object* v___y_7601_ = _args[16];
lean_object* v___y_7602_ = _args[17];
_start:
{
uint8_t v_linkDeps_boxed_7603_; uint8_t v_plugin_boxed_7604_; lean_object* v_res_7605_; 
v_linkDeps_boxed_7603_ = lean_unbox(v_linkDeps_7590_);
v_plugin_boxed_7604_ = lean_unbox(v_plugin_7592_);
v_res_7605_ = l_Lake_buildSharedLib___lam__3(v_weakArgs_7585_, v_traceArgs_7586_, v_libFile_7587_, v_linker_7588_, v_extraDepTrace_7589_, v_linkDeps_boxed_7603_, v_libName_7591_, v_plugin_boxed_7604_, v_linkLibs_7593_, v___x_7594_, v_objs_7595_, v___y_7596_, v___y_7597_, v___y_7598_, v___y_7599_, v___y_7600_, v___y_7601_);
lean_dec_ref(v_linkLibs_7593_);
return v_res_7605_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib(lean_object* v_libName_7607_, lean_object* v_libFile_7608_, lean_object* v_linkObjs_7609_, lean_object* v_linkLibs_7610_, lean_object* v_weakArgs_7611_, lean_object* v_traceArgs_7612_, lean_object* v_linker_7613_, lean_object* v_extraDepTrace_7614_, uint8_t v_plugin_7615_, uint8_t v_linkDeps_7616_, lean_object* v_a_7617_, lean_object* v_a_7618_, lean_object* v_a_7619_, lean_object* v_a_7620_, lean_object* v_a_7621_, lean_object* v_a_7622_){
_start:
{
lean_object* v___x_7624_; lean_object* v___x_7625_; lean_object* v___x_7626_; lean_object* v___f_7627_; lean_object* v___x_7628_; lean_object* v___x_7629_; lean_object* v___x_7630_; uint8_t v___x_7631_; lean_object* v___x_7632_; 
v___x_7624_ = l_Lake_instDataKindDynlib;
v___x_7625_ = lean_box(v_linkDeps_7616_);
v___x_7626_ = lean_box(v_plugin_7615_);
v___f_7627_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__3___boxed), 18, 10);
lean_closure_set(v___f_7627_, 0, v_weakArgs_7611_);
lean_closure_set(v___f_7627_, 1, v_traceArgs_7612_);
lean_closure_set(v___f_7627_, 2, v_libFile_7608_);
lean_closure_set(v___f_7627_, 3, v_linker_7613_);
lean_closure_set(v___f_7627_, 4, v_extraDepTrace_7614_);
lean_closure_set(v___f_7627_, 5, v___x_7625_);
lean_closure_set(v___f_7627_, 6, v_libName_7607_);
lean_closure_set(v___f_7627_, 7, v___x_7626_);
lean_closure_set(v___f_7627_, 8, v_linkLibs_7610_);
lean_closure_set(v___f_7627_, 9, v___x_7624_);
v___x_7628_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_7629_ = l_Lake_Job_collectArray___redArg(v_linkObjs_7609_, v___x_7628_);
v___x_7630_ = lean_unsigned_to_nat(0u);
v___x_7631_ = 1;
v___x_7632_ = l_Lake_Job_bindM___redArg(v___x_7624_, v___x_7629_, v___f_7627_, v___x_7630_, v___x_7631_, v_a_7617_, v_a_7618_, v_a_7619_, v_a_7620_, v_a_7621_, v_a_7622_);
return v___x_7632_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___boxed(lean_object** _args){
lean_object* v_libName_7633_ = _args[0];
lean_object* v_libFile_7634_ = _args[1];
lean_object* v_linkObjs_7635_ = _args[2];
lean_object* v_linkLibs_7636_ = _args[3];
lean_object* v_weakArgs_7637_ = _args[4];
lean_object* v_traceArgs_7638_ = _args[5];
lean_object* v_linker_7639_ = _args[6];
lean_object* v_extraDepTrace_7640_ = _args[7];
lean_object* v_plugin_7641_ = _args[8];
lean_object* v_linkDeps_7642_ = _args[9];
lean_object* v_a_7643_ = _args[10];
lean_object* v_a_7644_ = _args[11];
lean_object* v_a_7645_ = _args[12];
lean_object* v_a_7646_ = _args[13];
lean_object* v_a_7647_ = _args[14];
lean_object* v_a_7648_ = _args[15];
lean_object* v_a_7649_ = _args[16];
_start:
{
uint8_t v_plugin_boxed_7650_; uint8_t v_linkDeps_boxed_7651_; lean_object* v_res_7652_; 
v_plugin_boxed_7650_ = lean_unbox(v_plugin_7641_);
v_linkDeps_boxed_7651_ = lean_unbox(v_linkDeps_7642_);
v_res_7652_ = l_Lake_buildSharedLib(v_libName_7633_, v_libFile_7634_, v_linkObjs_7635_, v_linkLibs_7636_, v_weakArgs_7637_, v_traceArgs_7638_, v_linker_7639_, v_extraDepTrace_7640_, v_plugin_boxed_7650_, v_linkDeps_boxed_7651_, v_a_7643_, v_a_7644_, v_a_7645_, v_a_7646_, v_a_7647_, v_a_7648_);
lean_dec_ref(v_linkObjs_7635_);
return v_res_7652_;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLib___lam__0___closed__0(void){
_start:
{
lean_object* v___x_7653_; lean_object* v___x_7654_; lean_object* v___x_7655_; lean_object* v___x_7656_; 
v___x_7653_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
v___x_7654_ = lean_unsigned_to_nat(2u);
v___x_7655_ = lean_mk_empty_array_with_capacity(v___x_7654_);
v___x_7656_ = lean_array_push(v___x_7655_, v___x_7653_);
return v___x_7656_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object* v_objs_7657_, lean_object* v_weakArgs_7658_, lean_object* v_traceArgs_7659_, lean_object* v_libFile_7660_, uint8_t v_linkDeps_7661_, lean_object* v_libs_7662_, lean_object* v___y_7663_, lean_object* v___y_7664_, lean_object* v___y_7665_, lean_object* v___y_7666_, lean_object* v___y_7667_, lean_object* v___y_7668_){
_start:
{
lean_object* v_toContext_7670_; lean_object* v_lakeEnv_7671_; lean_object* v_lean_7672_; lean_object* v_libs_7674_; lean_object* v___y_7675_; 
v_toContext_7670_ = lean_ctor_get(v___y_7667_, 1);
lean_inc(v_toContext_7670_);
lean_dec_ref(v___y_7667_);
v_lakeEnv_7671_ = lean_ctor_get(v_toContext_7670_, 1);
lean_inc_ref(v_lakeEnv_7671_);
lean_dec(v_toContext_7670_);
v_lean_7672_ = lean_ctor_get(v_lakeEnv_7671_, 1);
lean_inc_ref(v_lean_7672_);
lean_dec_ref(v_lakeEnv_7671_);
if (v_linkDeps_7661_ == 0)
{
lean_object* v___x_7720_; 
v___x_7720_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1));
v_libs_7674_ = v___x_7720_;
v___y_7675_ = v___y_7668_;
goto v___jp_7673_;
}
else
{
lean_object* v___x_7721_; 
v___x_7721_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7662_, v___y_7668_);
if (lean_obj_tag(v___x_7721_) == 0)
{
lean_object* v_a_7722_; lean_object* v_a_7723_; 
v_a_7722_ = lean_ctor_get(v___x_7721_, 0);
lean_inc(v_a_7722_);
v_a_7723_ = lean_ctor_get(v___x_7721_, 1);
lean_inc(v_a_7723_);
lean_dec_ref(v___x_7721_);
v_libs_7674_ = v_a_7722_;
v___y_7675_ = v_a_7723_;
goto v___jp_7673_;
}
else
{
lean_object* v_a_7724_; lean_object* v_a_7725_; lean_object* v___x_7727_; uint8_t v_isShared_7728_; uint8_t v_isSharedCheck_7732_; 
lean_dec_ref(v_lean_7672_);
lean_dec_ref(v_libFile_7660_);
v_a_7724_ = lean_ctor_get(v___x_7721_, 0);
v_a_7725_ = lean_ctor_get(v___x_7721_, 1);
v_isSharedCheck_7732_ = !lean_is_exclusive(v___x_7721_);
if (v_isSharedCheck_7732_ == 0)
{
v___x_7727_ = v___x_7721_;
v_isShared_7728_ = v_isSharedCheck_7732_;
goto v_resetjp_7726_;
}
else
{
lean_inc(v_a_7725_);
lean_inc(v_a_7724_);
lean_dec(v___x_7721_);
v___x_7727_ = lean_box(0);
v_isShared_7728_ = v_isSharedCheck_7732_;
goto v_resetjp_7726_;
}
v_resetjp_7726_:
{
lean_object* v___x_7730_; 
if (v_isShared_7728_ == 0)
{
v___x_7730_ = v___x_7727_;
goto v_reusejp_7729_;
}
else
{
lean_object* v_reuseFailAlloc_7731_; 
v_reuseFailAlloc_7731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7731_, 0, v_a_7724_);
lean_ctor_set(v_reuseFailAlloc_7731_, 1, v_a_7725_);
v___x_7730_ = v_reuseFailAlloc_7731_;
goto v_reusejp_7729_;
}
v_reusejp_7729_:
{
return v___x_7730_;
}
}
}
}
v___jp_7673_:
{
lean_object* v_leanLibDir_7676_; lean_object* v_cc_7677_; lean_object* v_ccLinkSharedFlags_7678_; lean_object* v_log_7679_; uint8_t v_action_7680_; uint8_t v_wantsRebuild_7681_; lean_object* v_trace_7682_; lean_object* v_buildTime_7683_; lean_object* v___x_7685_; uint8_t v_isShared_7686_; uint8_t v_isSharedCheck_7719_; 
v_leanLibDir_7676_ = lean_ctor_get(v_lean_7672_, 3);
lean_inc_ref(v_leanLibDir_7676_);
v_cc_7677_ = lean_ctor_get(v_lean_7672_, 13);
lean_inc_ref(v_cc_7677_);
v_ccLinkSharedFlags_7678_ = lean_ctor_get(v_lean_7672_, 19);
lean_inc_ref(v_ccLinkSharedFlags_7678_);
lean_dec_ref(v_lean_7672_);
v_log_7679_ = lean_ctor_get(v___y_7675_, 0);
v_action_7680_ = lean_ctor_get_uint8(v___y_7675_, sizeof(void*)*3);
v_wantsRebuild_7681_ = lean_ctor_get_uint8(v___y_7675_, sizeof(void*)*3 + 1);
v_trace_7682_ = lean_ctor_get(v___y_7675_, 1);
v_buildTime_7683_ = lean_ctor_get(v___y_7675_, 2);
v_isSharedCheck_7719_ = !lean_is_exclusive(v___y_7675_);
if (v_isSharedCheck_7719_ == 0)
{
v___x_7685_ = v___y_7675_;
v_isShared_7686_ = v_isSharedCheck_7719_;
goto v_resetjp_7684_;
}
else
{
lean_inc(v_buildTime_7683_);
lean_inc(v_trace_7682_);
lean_inc(v_log_7679_);
lean_dec(v___y_7675_);
v___x_7685_ = lean_box(0);
v_isShared_7686_ = v_isSharedCheck_7719_;
goto v_resetjp_7684_;
}
v_resetjp_7684_:
{
lean_object* v___x_7687_; lean_object* v___x_7688_; lean_object* v___x_7689_; lean_object* v___x_7690_; lean_object* v___x_7691_; lean_object* v___x_7692_; lean_object* v___x_7693_; lean_object* v___x_7694_; 
v___x_7687_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7657_, v_libs_7674_);
lean_dec_ref(v_libs_7674_);
v___x_7688_ = l_Array_append___redArg(v___x_7687_, v_weakArgs_7658_);
v___x_7689_ = l_Array_append___redArg(v___x_7688_, v_traceArgs_7659_);
v___x_7690_ = lean_obj_once(&l_Lake_buildLeanSharedLib___lam__0___closed__0, &l_Lake_buildLeanSharedLib___lam__0___closed__0_once, _init_l_Lake_buildLeanSharedLib___lam__0___closed__0);
v___x_7691_ = lean_array_push(v___x_7690_, v_leanLibDir_7676_);
v___x_7692_ = l_Array_append___redArg(v___x_7689_, v___x_7691_);
lean_dec_ref(v___x_7691_);
v___x_7693_ = l_Array_append___redArg(v___x_7692_, v_ccLinkSharedFlags_7678_);
lean_dec_ref(v_ccLinkSharedFlags_7678_);
v___x_7694_ = l_Lake_compileSharedLib(v_libFile_7660_, v___x_7693_, v_cc_7677_, v_log_7679_);
if (lean_obj_tag(v___x_7694_) == 0)
{
lean_object* v_a_7695_; lean_object* v_a_7696_; lean_object* v___x_7698_; uint8_t v_isShared_7699_; uint8_t v_isSharedCheck_7706_; 
v_a_7695_ = lean_ctor_get(v___x_7694_, 0);
v_a_7696_ = lean_ctor_get(v___x_7694_, 1);
v_isSharedCheck_7706_ = !lean_is_exclusive(v___x_7694_);
if (v_isSharedCheck_7706_ == 0)
{
v___x_7698_ = v___x_7694_;
v_isShared_7699_ = v_isSharedCheck_7706_;
goto v_resetjp_7697_;
}
else
{
lean_inc(v_a_7696_);
lean_inc(v_a_7695_);
lean_dec(v___x_7694_);
v___x_7698_ = lean_box(0);
v_isShared_7699_ = v_isSharedCheck_7706_;
goto v_resetjp_7697_;
}
v_resetjp_7697_:
{
lean_object* v___x_7701_; 
if (v_isShared_7686_ == 0)
{
lean_ctor_set(v___x_7685_, 0, v_a_7696_);
v___x_7701_ = v___x_7685_;
goto v_reusejp_7700_;
}
else
{
lean_object* v_reuseFailAlloc_7705_; 
v_reuseFailAlloc_7705_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7705_, 0, v_a_7696_);
lean_ctor_set(v_reuseFailAlloc_7705_, 1, v_trace_7682_);
lean_ctor_set(v_reuseFailAlloc_7705_, 2, v_buildTime_7683_);
lean_ctor_set_uint8(v_reuseFailAlloc_7705_, sizeof(void*)*3, v_action_7680_);
lean_ctor_set_uint8(v_reuseFailAlloc_7705_, sizeof(void*)*3 + 1, v_wantsRebuild_7681_);
v___x_7701_ = v_reuseFailAlloc_7705_;
goto v_reusejp_7700_;
}
v_reusejp_7700_:
{
lean_object* v___x_7703_; 
if (v_isShared_7699_ == 0)
{
lean_ctor_set(v___x_7698_, 1, v___x_7701_);
v___x_7703_ = v___x_7698_;
goto v_reusejp_7702_;
}
else
{
lean_object* v_reuseFailAlloc_7704_; 
v_reuseFailAlloc_7704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7704_, 0, v_a_7695_);
lean_ctor_set(v_reuseFailAlloc_7704_, 1, v___x_7701_);
v___x_7703_ = v_reuseFailAlloc_7704_;
goto v_reusejp_7702_;
}
v_reusejp_7702_:
{
return v___x_7703_;
}
}
}
}
else
{
lean_object* v_a_7707_; lean_object* v_a_7708_; lean_object* v___x_7710_; uint8_t v_isShared_7711_; uint8_t v_isSharedCheck_7718_; 
v_a_7707_ = lean_ctor_get(v___x_7694_, 0);
v_a_7708_ = lean_ctor_get(v___x_7694_, 1);
v_isSharedCheck_7718_ = !lean_is_exclusive(v___x_7694_);
if (v_isSharedCheck_7718_ == 0)
{
v___x_7710_ = v___x_7694_;
v_isShared_7711_ = v_isSharedCheck_7718_;
goto v_resetjp_7709_;
}
else
{
lean_inc(v_a_7708_);
lean_inc(v_a_7707_);
lean_dec(v___x_7694_);
v___x_7710_ = lean_box(0);
v_isShared_7711_ = v_isSharedCheck_7718_;
goto v_resetjp_7709_;
}
v_resetjp_7709_:
{
lean_object* v___x_7713_; 
if (v_isShared_7686_ == 0)
{
lean_ctor_set(v___x_7685_, 0, v_a_7708_);
v___x_7713_ = v___x_7685_;
goto v_reusejp_7712_;
}
else
{
lean_object* v_reuseFailAlloc_7717_; 
v_reuseFailAlloc_7717_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7717_, 0, v_a_7708_);
lean_ctor_set(v_reuseFailAlloc_7717_, 1, v_trace_7682_);
lean_ctor_set(v_reuseFailAlloc_7717_, 2, v_buildTime_7683_);
lean_ctor_set_uint8(v_reuseFailAlloc_7717_, sizeof(void*)*3, v_action_7680_);
lean_ctor_set_uint8(v_reuseFailAlloc_7717_, sizeof(void*)*3 + 1, v_wantsRebuild_7681_);
v___x_7713_ = v_reuseFailAlloc_7717_;
goto v_reusejp_7712_;
}
v_reusejp_7712_:
{
lean_object* v___x_7715_; 
if (v_isShared_7711_ == 0)
{
lean_ctor_set(v___x_7710_, 1, v___x_7713_);
v___x_7715_ = v___x_7710_;
goto v_reusejp_7714_;
}
else
{
lean_object* v_reuseFailAlloc_7716_; 
v_reuseFailAlloc_7716_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7716_, 0, v_a_7707_);
lean_ctor_set(v_reuseFailAlloc_7716_, 1, v___x_7713_);
v___x_7715_ = v_reuseFailAlloc_7716_;
goto v_reusejp_7714_;
}
v_reusejp_7714_:
{
return v___x_7715_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object* v_objs_7733_, lean_object* v_weakArgs_7734_, lean_object* v_traceArgs_7735_, lean_object* v_libFile_7736_, lean_object* v_linkDeps_7737_, lean_object* v_libs_7738_, lean_object* v___y_7739_, lean_object* v___y_7740_, lean_object* v___y_7741_, lean_object* v___y_7742_, lean_object* v___y_7743_, lean_object* v___y_7744_, lean_object* v___y_7745_){
_start:
{
uint8_t v_linkDeps_boxed_7746_; lean_object* v_res_7747_; 
v_linkDeps_boxed_7746_ = lean_unbox(v_linkDeps_7737_);
v_res_7747_ = l_Lake_buildLeanSharedLib___lam__0(v_objs_7733_, v_weakArgs_7734_, v_traceArgs_7735_, v_libFile_7736_, v_linkDeps_boxed_7746_, v_libs_7738_, v___y_7739_, v___y_7740_, v___y_7741_, v___y_7742_, v___y_7743_, v___y_7744_);
lean_dec(v___y_7742_);
lean_dec(v___y_7741_);
lean_dec(v___y_7740_);
lean_dec_ref(v___y_7739_);
lean_dec_ref(v_libs_7738_);
lean_dec_ref(v_traceArgs_7735_);
lean_dec_ref(v_weakArgs_7734_);
lean_dec_ref(v_objs_7733_);
return v_res_7747_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object* v_objs_7748_, lean_object* v_weakArgs_7749_, lean_object* v_traceArgs_7750_, lean_object* v_libFile_7751_, uint8_t v_linkDeps_7752_, lean_object* v_libName_7753_, uint8_t v_plugin_7754_, lean_object* v_libs_7755_, lean_object* v___y_7756_, lean_object* v___y_7757_, lean_object* v___y_7758_, lean_object* v___y_7759_, lean_object* v___y_7760_, lean_object* v___y_7761_){
_start:
{
lean_object* v_log_7763_; uint8_t v_action_7764_; uint8_t v_wantsRebuild_7765_; lean_object* v_trace_7766_; lean_object* v_buildTime_7767_; lean_object* v___x_7769_; uint8_t v_isShared_7770_; uint8_t v_isSharedCheck_7827_; 
v_log_7763_ = lean_ctor_get(v___y_7761_, 0);
v_action_7764_ = lean_ctor_get_uint8(v___y_7761_, sizeof(void*)*3);
v_wantsRebuild_7765_ = lean_ctor_get_uint8(v___y_7761_, sizeof(void*)*3 + 1);
v_trace_7766_ = lean_ctor_get(v___y_7761_, 1);
v_buildTime_7767_ = lean_ctor_get(v___y_7761_, 2);
v_isSharedCheck_7827_ = !lean_is_exclusive(v___y_7761_);
if (v_isSharedCheck_7827_ == 0)
{
v___x_7769_ = v___y_7761_;
v_isShared_7770_ = v_isSharedCheck_7827_;
goto v_resetjp_7768_;
}
else
{
lean_inc(v_buildTime_7767_);
lean_inc(v_trace_7766_);
lean_inc(v_log_7763_);
lean_dec(v___y_7761_);
v___x_7769_ = lean_box(0);
v_isShared_7770_ = v_isSharedCheck_7827_;
goto v_resetjp_7768_;
}
v_resetjp_7768_:
{
lean_object* v_leanTrace_7771_; lean_object* v___x_7772_; lean_object* v___f_7773_; lean_object* v___x_7774_; uint64_t v___y_7776_; uint64_t v___x_7816_; lean_object* v___x_7817_; lean_object* v___x_7818_; uint8_t v___x_7819_; 
v_leanTrace_7771_ = lean_ctor_get(v___y_7760_, 2);
v___x_7772_ = lean_box(v_linkDeps_7752_);
lean_inc_ref(v_libs_7755_);
lean_inc_ref(v_libFile_7751_);
lean_inc_ref(v_traceArgs_7750_);
v___f_7773_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__0___boxed), 13, 6);
lean_closure_set(v___f_7773_, 0, v_objs_7748_);
lean_closure_set(v___f_7773_, 1, v_weakArgs_7749_);
lean_closure_set(v___f_7773_, 2, v_traceArgs_7750_);
lean_closure_set(v___f_7773_, 3, v_libFile_7751_);
lean_closure_set(v___f_7773_, 4, v___x_7772_);
lean_closure_set(v___f_7773_, 5, v_libs_7755_);
lean_inc_ref(v_leanTrace_7771_);
v___x_7774_ = l_Lake_BuildTrace_mix(v_trace_7766_, v_leanTrace_7771_);
v___x_7816_ = l_Lake_Hash_nil;
v___x_7817_ = lean_unsigned_to_nat(0u);
v___x_7818_ = lean_array_get_size(v_traceArgs_7750_);
v___x_7819_ = lean_nat_dec_lt(v___x_7817_, v___x_7818_);
if (v___x_7819_ == 0)
{
v___y_7776_ = v___x_7816_;
goto v___jp_7775_;
}
else
{
uint8_t v___x_7820_; 
v___x_7820_ = lean_nat_dec_le(v___x_7818_, v___x_7818_);
if (v___x_7820_ == 0)
{
if (v___x_7819_ == 0)
{
v___y_7776_ = v___x_7816_;
goto v___jp_7775_;
}
else
{
size_t v___x_7821_; size_t v___x_7822_; uint64_t v___x_7823_; 
v___x_7821_ = ((size_t)0ULL);
v___x_7822_ = lean_usize_of_nat(v___x_7818_);
v___x_7823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7750_, v___x_7821_, v___x_7822_, v___x_7816_);
v___y_7776_ = v___x_7823_;
goto v___jp_7775_;
}
}
else
{
size_t v___x_7824_; size_t v___x_7825_; uint64_t v___x_7826_; 
v___x_7824_ = ((size_t)0ULL);
v___x_7825_ = lean_usize_of_nat(v___x_7818_);
v___x_7826_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7750_, v___x_7824_, v___x_7825_, v___x_7816_);
v___y_7776_ = v___x_7826_;
goto v___jp_7775_;
}
}
v___jp_7775_:
{
lean_object* v___x_7777_; lean_object* v___x_7778_; lean_object* v___x_7779_; lean_object* v___x_7780_; lean_object* v___x_7781_; lean_object* v___x_7782_; lean_object* v___x_7783_; lean_object* v___x_7784_; lean_object* v___x_7785_; lean_object* v___x_7786_; lean_object* v___x_7787_; lean_object* v___x_7788_; lean_object* v___x_7790_; 
v___x_7777_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_7778_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_7779_ = lean_array_to_list(v_traceArgs_7750_);
v___x_7780_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_7779_);
lean_dec(v___x_7779_);
v___x_7781_ = lean_string_append(v___x_7778_, v___x_7780_);
lean_dec_ref(v___x_7780_);
v___x_7782_ = lean_string_append(v___x_7777_, v___x_7781_);
lean_dec_ref(v___x_7781_);
v___x_7783_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_7784_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_7785_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_7785_, 0, v___x_7782_);
lean_ctor_set(v___x_7785_, 1, v___x_7783_);
lean_ctor_set(v___x_7785_, 2, v___x_7784_);
lean_ctor_set_uint64(v___x_7785_, sizeof(void*)*3, v___y_7776_);
v___x_7786_ = l_Lake_BuildTrace_mix(v___x_7774_, v___x_7785_);
v___x_7787_ = l_Lake_platformTrace;
v___x_7788_ = l_Lake_BuildTrace_mix(v___x_7786_, v___x_7787_);
if (v_isShared_7770_ == 0)
{
lean_ctor_set(v___x_7769_, 1, v___x_7788_);
v___x_7790_ = v___x_7769_;
goto v_reusejp_7789_;
}
else
{
lean_object* v_reuseFailAlloc_7815_; 
v_reuseFailAlloc_7815_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7815_, 0, v_log_7763_);
lean_ctor_set(v_reuseFailAlloc_7815_, 1, v___x_7788_);
lean_ctor_set(v_reuseFailAlloc_7815_, 2, v_buildTime_7767_);
lean_ctor_set_uint8(v_reuseFailAlloc_7815_, sizeof(void*)*3, v_action_7764_);
lean_ctor_set_uint8(v_reuseFailAlloc_7815_, sizeof(void*)*3 + 1, v_wantsRebuild_7765_);
v___x_7790_ = v_reuseFailAlloc_7815_;
goto v_reusejp_7789_;
}
v_reusejp_7789_:
{
uint8_t v___x_7791_; lean_object* v___x_7792_; uint8_t v___x_7793_; lean_object* v___x_7794_; 
v___x_7791_ = 0;
v___x_7792_ = l_Lake_sharedLibExt;
v___x_7793_ = 1;
v___x_7794_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_7751_, v___f_7773_, v___x_7791_, v___x_7792_, v___x_7793_, v___x_7791_, v___y_7756_, v___y_7757_, v___y_7758_, v___y_7759_, v___y_7760_, v___x_7790_);
if (lean_obj_tag(v___x_7794_) == 0)
{
lean_object* v_a_7795_; lean_object* v_a_7796_; lean_object* v___x_7798_; uint8_t v_isShared_7799_; uint8_t v_isSharedCheck_7805_; 
v_a_7795_ = lean_ctor_get(v___x_7794_, 0);
v_a_7796_ = lean_ctor_get(v___x_7794_, 1);
v_isSharedCheck_7805_ = !lean_is_exclusive(v___x_7794_);
if (v_isSharedCheck_7805_ == 0)
{
v___x_7798_ = v___x_7794_;
v_isShared_7799_ = v_isSharedCheck_7805_;
goto v_resetjp_7797_;
}
else
{
lean_inc(v_a_7796_);
lean_inc(v_a_7795_);
lean_dec(v___x_7794_);
v___x_7798_ = lean_box(0);
v_isShared_7799_ = v_isSharedCheck_7805_;
goto v_resetjp_7797_;
}
v_resetjp_7797_:
{
lean_object* v_path_7800_; lean_object* v___x_7801_; lean_object* v___x_7803_; 
v_path_7800_ = lean_ctor_get(v_a_7795_, 1);
lean_inc_ref(v_path_7800_);
lean_dec(v_a_7795_);
v___x_7801_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_7801_, 0, v_path_7800_);
lean_ctor_set(v___x_7801_, 1, v_libName_7753_);
lean_ctor_set(v___x_7801_, 2, v_libs_7755_);
lean_ctor_set_uint8(v___x_7801_, sizeof(void*)*3, v_plugin_7754_);
if (v_isShared_7799_ == 0)
{
lean_ctor_set(v___x_7798_, 0, v___x_7801_);
v___x_7803_ = v___x_7798_;
goto v_reusejp_7802_;
}
else
{
lean_object* v_reuseFailAlloc_7804_; 
v_reuseFailAlloc_7804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7804_, 0, v___x_7801_);
lean_ctor_set(v_reuseFailAlloc_7804_, 1, v_a_7796_);
v___x_7803_ = v_reuseFailAlloc_7804_;
goto v_reusejp_7802_;
}
v_reusejp_7802_:
{
return v___x_7803_;
}
}
}
else
{
lean_object* v_a_7806_; lean_object* v_a_7807_; lean_object* v___x_7809_; uint8_t v_isShared_7810_; uint8_t v_isSharedCheck_7814_; 
lean_dec_ref(v_libs_7755_);
lean_dec_ref(v_libName_7753_);
v_a_7806_ = lean_ctor_get(v___x_7794_, 0);
v_a_7807_ = lean_ctor_get(v___x_7794_, 1);
v_isSharedCheck_7814_ = !lean_is_exclusive(v___x_7794_);
if (v_isSharedCheck_7814_ == 0)
{
v___x_7809_ = v___x_7794_;
v_isShared_7810_ = v_isSharedCheck_7814_;
goto v_resetjp_7808_;
}
else
{
lean_inc(v_a_7807_);
lean_inc(v_a_7806_);
lean_dec(v___x_7794_);
v___x_7809_ = lean_box(0);
v_isShared_7810_ = v_isSharedCheck_7814_;
goto v_resetjp_7808_;
}
v_resetjp_7808_:
{
lean_object* v___x_7812_; 
if (v_isShared_7810_ == 0)
{
v___x_7812_ = v___x_7809_;
goto v_reusejp_7811_;
}
else
{
lean_object* v_reuseFailAlloc_7813_; 
v_reuseFailAlloc_7813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7813_, 0, v_a_7806_);
lean_ctor_set(v_reuseFailAlloc_7813_, 1, v_a_7807_);
v___x_7812_ = v_reuseFailAlloc_7813_;
goto v_reusejp_7811_;
}
v_reusejp_7811_:
{
return v___x_7812_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1___boxed(lean_object* v_objs_7828_, lean_object* v_weakArgs_7829_, lean_object* v_traceArgs_7830_, lean_object* v_libFile_7831_, lean_object* v_linkDeps_7832_, lean_object* v_libName_7833_, lean_object* v_plugin_7834_, lean_object* v_libs_7835_, lean_object* v___y_7836_, lean_object* v___y_7837_, lean_object* v___y_7838_, lean_object* v___y_7839_, lean_object* v___y_7840_, lean_object* v___y_7841_, lean_object* v___y_7842_){
_start:
{
uint8_t v_linkDeps_boxed_7843_; uint8_t v_plugin_boxed_7844_; lean_object* v_res_7845_; 
v_linkDeps_boxed_7843_ = lean_unbox(v_linkDeps_7832_);
v_plugin_boxed_7844_ = lean_unbox(v_plugin_7834_);
v_res_7845_ = l_Lake_buildLeanSharedLib___lam__1(v_objs_7828_, v_weakArgs_7829_, v_traceArgs_7830_, v_libFile_7831_, v_linkDeps_boxed_7843_, v_libName_7833_, v_plugin_boxed_7844_, v_libs_7835_, v___y_7836_, v___y_7837_, v___y_7838_, v___y_7839_, v___y_7840_, v___y_7841_);
return v_res_7845_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2(lean_object* v_weakArgs_7846_, lean_object* v_traceArgs_7847_, lean_object* v_libFile_7848_, uint8_t v_linkDeps_7849_, lean_object* v_libName_7850_, uint8_t v_plugin_7851_, lean_object* v_linkLibs_7852_, lean_object* v___x_7853_, lean_object* v_objs_7854_, lean_object* v___y_7855_, lean_object* v___y_7856_, lean_object* v___y_7857_, lean_object* v___y_7858_, lean_object* v___y_7859_, lean_object* v___y_7860_){
_start:
{
lean_object* v_trace_7862_; lean_object* v___x_7863_; lean_object* v___x_7864_; lean_object* v___f_7865_; lean_object* v___x_7866_; lean_object* v___x_7867_; lean_object* v___x_7868_; uint8_t v___x_7869_; lean_object* v___x_7870_; lean_object* v___x_7871_; 
v_trace_7862_ = lean_ctor_get(v___y_7860_, 1);
v___x_7863_ = lean_box(v_linkDeps_7849_);
v___x_7864_ = lean_box(v_plugin_7851_);
v___f_7865_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__1___boxed), 15, 7);
lean_closure_set(v___f_7865_, 0, v_objs_7854_);
lean_closure_set(v___f_7865_, 1, v_weakArgs_7846_);
lean_closure_set(v___f_7865_, 2, v_traceArgs_7847_);
lean_closure_set(v___f_7865_, 3, v_libFile_7848_);
lean_closure_set(v___f_7865_, 4, v___x_7863_);
lean_closure_set(v___f_7865_, 5, v_libName_7850_);
lean_closure_set(v___f_7865_, 6, v___x_7864_);
v___x_7866_ = ((lean_object*)(l_Lake_buildSharedLib___lam__3___closed__0));
v___x_7867_ = l_Lake_Job_collectArray___redArg(v_linkLibs_7852_, v___x_7866_);
v___x_7868_ = lean_unsigned_to_nat(0u);
v___x_7869_ = 0;
lean_inc_ref(v_trace_7862_);
v___x_7870_ = l_Lake_Job_mapM___redArg(v___x_7853_, v___x_7867_, v___f_7865_, v___x_7868_, v___x_7869_, v___y_7855_, v___y_7856_, v___y_7857_, v___y_7858_, v___y_7859_, v_trace_7862_);
v___x_7871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7871_, 0, v___x_7870_);
lean_ctor_set(v___x_7871_, 1, v___y_7860_);
return v___x_7871_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2___boxed(lean_object* v_weakArgs_7872_, lean_object* v_traceArgs_7873_, lean_object* v_libFile_7874_, lean_object* v_linkDeps_7875_, lean_object* v_libName_7876_, lean_object* v_plugin_7877_, lean_object* v_linkLibs_7878_, lean_object* v___x_7879_, lean_object* v_objs_7880_, lean_object* v___y_7881_, lean_object* v___y_7882_, lean_object* v___y_7883_, lean_object* v___y_7884_, lean_object* v___y_7885_, lean_object* v___y_7886_, lean_object* v___y_7887_){
_start:
{
uint8_t v_linkDeps_boxed_7888_; uint8_t v_plugin_boxed_7889_; lean_object* v_res_7890_; 
v_linkDeps_boxed_7888_ = lean_unbox(v_linkDeps_7875_);
v_plugin_boxed_7889_ = lean_unbox(v_plugin_7877_);
v_res_7890_ = l_Lake_buildLeanSharedLib___lam__2(v_weakArgs_7872_, v_traceArgs_7873_, v_libFile_7874_, v_linkDeps_boxed_7888_, v_libName_7876_, v_plugin_boxed_7889_, v_linkLibs_7878_, v___x_7879_, v_objs_7880_, v___y_7881_, v___y_7882_, v___y_7883_, v___y_7884_, v___y_7885_, v___y_7886_);
lean_dec_ref(v_linkLibs_7878_);
return v_res_7890_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object* v_libName_7891_, lean_object* v_libFile_7892_, lean_object* v_linkObjs_7893_, lean_object* v_linkLibs_7894_, lean_object* v_weakArgs_7895_, lean_object* v_traceArgs_7896_, uint8_t v_plugin_7897_, uint8_t v_linkDeps_7898_, lean_object* v_a_7899_, lean_object* v_a_7900_, lean_object* v_a_7901_, lean_object* v_a_7902_, lean_object* v_a_7903_, lean_object* v_a_7904_){
_start:
{
lean_object* v___x_7906_; lean_object* v___x_7907_; lean_object* v___x_7908_; lean_object* v___f_7909_; lean_object* v___x_7910_; lean_object* v___x_7911_; lean_object* v___x_7912_; uint8_t v___x_7913_; lean_object* v___x_7914_; 
v___x_7906_ = l_Lake_instDataKindDynlib;
v___x_7907_ = lean_box(v_linkDeps_7898_);
v___x_7908_ = lean_box(v_plugin_7897_);
v___f_7909_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__2___boxed), 16, 8);
lean_closure_set(v___f_7909_, 0, v_weakArgs_7895_);
lean_closure_set(v___f_7909_, 1, v_traceArgs_7896_);
lean_closure_set(v___f_7909_, 2, v_libFile_7892_);
lean_closure_set(v___f_7909_, 3, v___x_7907_);
lean_closure_set(v___f_7909_, 4, v_libName_7891_);
lean_closure_set(v___f_7909_, 5, v___x_7908_);
lean_closure_set(v___f_7909_, 6, v_linkLibs_7894_);
lean_closure_set(v___f_7909_, 7, v___x_7906_);
v___x_7910_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_7911_ = l_Lake_Job_collectArray___redArg(v_linkObjs_7893_, v___x_7910_);
v___x_7912_ = lean_unsigned_to_nat(0u);
v___x_7913_ = 1;
v___x_7914_ = l_Lake_Job_bindM___redArg(v___x_7906_, v___x_7911_, v___f_7909_, v___x_7912_, v___x_7913_, v_a_7899_, v_a_7900_, v_a_7901_, v_a_7902_, v_a_7903_, v_a_7904_);
return v___x_7914_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object* v_libName_7915_, lean_object* v_libFile_7916_, lean_object* v_linkObjs_7917_, lean_object* v_linkLibs_7918_, lean_object* v_weakArgs_7919_, lean_object* v_traceArgs_7920_, lean_object* v_plugin_7921_, lean_object* v_linkDeps_7922_, lean_object* v_a_7923_, lean_object* v_a_7924_, lean_object* v_a_7925_, lean_object* v_a_7926_, lean_object* v_a_7927_, lean_object* v_a_7928_, lean_object* v_a_7929_){
_start:
{
uint8_t v_plugin_boxed_7930_; uint8_t v_linkDeps_boxed_7931_; lean_object* v_res_7932_; 
v_plugin_boxed_7930_ = lean_unbox(v_plugin_7921_);
v_linkDeps_boxed_7931_ = lean_unbox(v_linkDeps_7922_);
v_res_7932_ = l_Lake_buildLeanSharedLib(v_libName_7915_, v_libFile_7916_, v_linkObjs_7917_, v_linkLibs_7918_, v_weakArgs_7919_, v_traceArgs_7920_, v_plugin_boxed_7930_, v_linkDeps_boxed_7931_, v_a_7923_, v_a_7924_, v_a_7925_, v_a_7926_, v_a_7927_, v_a_7928_);
lean_dec_ref(v_linkObjs_7917_);
return v_res_7932_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0(lean_object* v_libs_7933_, lean_object* v_objs_7934_, lean_object* v_weakArgs_7935_, lean_object* v_traceArgs_7936_, uint8_t v_sharedLean_7937_, lean_object* v_exeFile_7938_, lean_object* v___y_7939_, lean_object* v___y_7940_, lean_object* v___y_7941_, lean_object* v___y_7942_, lean_object* v___y_7943_, lean_object* v___y_7944_){
_start:
{
lean_object* v___x_7946_; 
v___x_7946_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7933_, v___y_7944_);
if (lean_obj_tag(v___x_7946_) == 0)
{
lean_object* v_toContext_7947_; lean_object* v_lakeEnv_7948_; lean_object* v_lean_7949_; lean_object* v_a_7950_; lean_object* v_a_7951_; lean_object* v_leanLibDir_7952_; lean_object* v_cc_7953_; lean_object* v_log_7954_; uint8_t v_action_7955_; uint8_t v_wantsRebuild_7956_; lean_object* v_trace_7957_; lean_object* v_buildTime_7958_; lean_object* v___x_7960_; uint8_t v_isShared_7961_; uint8_t v_isSharedCheck_7997_; 
v_toContext_7947_ = lean_ctor_get(v___y_7943_, 1);
lean_inc(v_toContext_7947_);
lean_dec_ref(v___y_7943_);
v_lakeEnv_7948_ = lean_ctor_get(v_toContext_7947_, 1);
lean_inc_ref(v_lakeEnv_7948_);
lean_dec(v_toContext_7947_);
v_lean_7949_ = lean_ctor_get(v_lakeEnv_7948_, 1);
lean_inc_ref(v_lean_7949_);
lean_dec_ref(v_lakeEnv_7948_);
v_a_7950_ = lean_ctor_get(v___x_7946_, 1);
lean_inc(v_a_7950_);
v_a_7951_ = lean_ctor_get(v___x_7946_, 0);
lean_inc(v_a_7951_);
lean_dec_ref(v___x_7946_);
v_leanLibDir_7952_ = lean_ctor_get(v_lean_7949_, 3);
v_cc_7953_ = lean_ctor_get(v_lean_7949_, 13);
lean_inc_ref(v_cc_7953_);
v_log_7954_ = lean_ctor_get(v_a_7950_, 0);
v_action_7955_ = lean_ctor_get_uint8(v_a_7950_, sizeof(void*)*3);
v_wantsRebuild_7956_ = lean_ctor_get_uint8(v_a_7950_, sizeof(void*)*3 + 1);
v_trace_7957_ = lean_ctor_get(v_a_7950_, 1);
v_buildTime_7958_ = lean_ctor_get(v_a_7950_, 2);
v_isSharedCheck_7997_ = !lean_is_exclusive(v_a_7950_);
if (v_isSharedCheck_7997_ == 0)
{
v___x_7960_ = v_a_7950_;
v_isShared_7961_ = v_isSharedCheck_7997_;
goto v_resetjp_7959_;
}
else
{
lean_inc(v_buildTime_7958_);
lean_inc(v_trace_7957_);
lean_inc(v_log_7954_);
lean_dec(v_a_7950_);
v___x_7960_ = lean_box(0);
v_isShared_7961_ = v_isSharedCheck_7997_;
goto v_resetjp_7959_;
}
v_resetjp_7959_:
{
lean_object* v___x_7962_; lean_object* v___x_7963_; lean_object* v___x_7964_; lean_object* v___x_7965_; lean_object* v___x_7966_; lean_object* v___x_7967_; lean_object* v___x_7968_; lean_object* v___x_7969_; lean_object* v___x_7970_; lean_object* v___x_7971_; lean_object* v___x_7972_; 
v___x_7962_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7934_, v_a_7951_);
lean_dec(v_a_7951_);
v___x_7963_ = l_Array_append___redArg(v___x_7962_, v_weakArgs_7935_);
v___x_7964_ = l_Array_append___redArg(v___x_7963_, v_traceArgs_7936_);
v___x_7965_ = lean_unsigned_to_nat(2u);
v___x_7966_ = lean_mk_empty_array_with_capacity(v___x_7965_);
lean_dec_ref(v___x_7966_);
v___x_7967_ = lean_obj_once(&l_Lake_buildLeanSharedLib___lam__0___closed__0, &l_Lake_buildLeanSharedLib___lam__0___closed__0_once, _init_l_Lake_buildLeanSharedLib___lam__0___closed__0);
lean_inc_ref(v_leanLibDir_7952_);
v___x_7968_ = lean_array_push(v___x_7967_, v_leanLibDir_7952_);
v___x_7969_ = l_Array_append___redArg(v___x_7964_, v___x_7968_);
lean_dec_ref(v___x_7968_);
v___x_7970_ = l_Lake_LeanInstall_ccLinkFlags(v_sharedLean_7937_, v_lean_7949_);
lean_dec_ref(v_lean_7949_);
v___x_7971_ = l_Array_append___redArg(v___x_7969_, v___x_7970_);
lean_dec_ref(v___x_7970_);
v___x_7972_ = l_Lake_compileExe(v_exeFile_7938_, v___x_7971_, v_cc_7953_, v_log_7954_);
if (lean_obj_tag(v___x_7972_) == 0)
{
lean_object* v_a_7973_; lean_object* v_a_7974_; lean_object* v___x_7976_; uint8_t v_isShared_7977_; uint8_t v_isSharedCheck_7984_; 
v_a_7973_ = lean_ctor_get(v___x_7972_, 0);
v_a_7974_ = lean_ctor_get(v___x_7972_, 1);
v_isSharedCheck_7984_ = !lean_is_exclusive(v___x_7972_);
if (v_isSharedCheck_7984_ == 0)
{
v___x_7976_ = v___x_7972_;
v_isShared_7977_ = v_isSharedCheck_7984_;
goto v_resetjp_7975_;
}
else
{
lean_inc(v_a_7974_);
lean_inc(v_a_7973_);
lean_dec(v___x_7972_);
v___x_7976_ = lean_box(0);
v_isShared_7977_ = v_isSharedCheck_7984_;
goto v_resetjp_7975_;
}
v_resetjp_7975_:
{
lean_object* v___x_7979_; 
if (v_isShared_7961_ == 0)
{
lean_ctor_set(v___x_7960_, 0, v_a_7974_);
v___x_7979_ = v___x_7960_;
goto v_reusejp_7978_;
}
else
{
lean_object* v_reuseFailAlloc_7983_; 
v_reuseFailAlloc_7983_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7983_, 0, v_a_7974_);
lean_ctor_set(v_reuseFailAlloc_7983_, 1, v_trace_7957_);
lean_ctor_set(v_reuseFailAlloc_7983_, 2, v_buildTime_7958_);
lean_ctor_set_uint8(v_reuseFailAlloc_7983_, sizeof(void*)*3, v_action_7955_);
lean_ctor_set_uint8(v_reuseFailAlloc_7983_, sizeof(void*)*3 + 1, v_wantsRebuild_7956_);
v___x_7979_ = v_reuseFailAlloc_7983_;
goto v_reusejp_7978_;
}
v_reusejp_7978_:
{
lean_object* v___x_7981_; 
if (v_isShared_7977_ == 0)
{
lean_ctor_set(v___x_7976_, 1, v___x_7979_);
v___x_7981_ = v___x_7976_;
goto v_reusejp_7980_;
}
else
{
lean_object* v_reuseFailAlloc_7982_; 
v_reuseFailAlloc_7982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7982_, 0, v_a_7973_);
lean_ctor_set(v_reuseFailAlloc_7982_, 1, v___x_7979_);
v___x_7981_ = v_reuseFailAlloc_7982_;
goto v_reusejp_7980_;
}
v_reusejp_7980_:
{
return v___x_7981_;
}
}
}
}
else
{
lean_object* v_a_7985_; lean_object* v_a_7986_; lean_object* v___x_7988_; uint8_t v_isShared_7989_; uint8_t v_isSharedCheck_7996_; 
v_a_7985_ = lean_ctor_get(v___x_7972_, 0);
v_a_7986_ = lean_ctor_get(v___x_7972_, 1);
v_isSharedCheck_7996_ = !lean_is_exclusive(v___x_7972_);
if (v_isSharedCheck_7996_ == 0)
{
v___x_7988_ = v___x_7972_;
v_isShared_7989_ = v_isSharedCheck_7996_;
goto v_resetjp_7987_;
}
else
{
lean_inc(v_a_7986_);
lean_inc(v_a_7985_);
lean_dec(v___x_7972_);
v___x_7988_ = lean_box(0);
v_isShared_7989_ = v_isSharedCheck_7996_;
goto v_resetjp_7987_;
}
v_resetjp_7987_:
{
lean_object* v___x_7991_; 
if (v_isShared_7961_ == 0)
{
lean_ctor_set(v___x_7960_, 0, v_a_7986_);
v___x_7991_ = v___x_7960_;
goto v_reusejp_7990_;
}
else
{
lean_object* v_reuseFailAlloc_7995_; 
v_reuseFailAlloc_7995_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7995_, 0, v_a_7986_);
lean_ctor_set(v_reuseFailAlloc_7995_, 1, v_trace_7957_);
lean_ctor_set(v_reuseFailAlloc_7995_, 2, v_buildTime_7958_);
lean_ctor_set_uint8(v_reuseFailAlloc_7995_, sizeof(void*)*3, v_action_7955_);
lean_ctor_set_uint8(v_reuseFailAlloc_7995_, sizeof(void*)*3 + 1, v_wantsRebuild_7956_);
v___x_7991_ = v_reuseFailAlloc_7995_;
goto v_reusejp_7990_;
}
v_reusejp_7990_:
{
lean_object* v___x_7993_; 
if (v_isShared_7989_ == 0)
{
lean_ctor_set(v___x_7988_, 1, v___x_7991_);
v___x_7993_ = v___x_7988_;
goto v_reusejp_7992_;
}
else
{
lean_object* v_reuseFailAlloc_7994_; 
v_reuseFailAlloc_7994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7994_, 0, v_a_7985_);
lean_ctor_set(v_reuseFailAlloc_7994_, 1, v___x_7991_);
v___x_7993_ = v_reuseFailAlloc_7994_;
goto v_reusejp_7992_;
}
v_reusejp_7992_:
{
return v___x_7993_;
}
}
}
}
}
}
else
{
lean_object* v_a_7998_; lean_object* v_a_7999_; lean_object* v___x_8001_; uint8_t v_isShared_8002_; uint8_t v_isSharedCheck_8006_; 
lean_dec_ref(v___y_7943_);
lean_dec_ref(v_exeFile_7938_);
v_a_7998_ = lean_ctor_get(v___x_7946_, 0);
v_a_7999_ = lean_ctor_get(v___x_7946_, 1);
v_isSharedCheck_8006_ = !lean_is_exclusive(v___x_7946_);
if (v_isSharedCheck_8006_ == 0)
{
v___x_8001_ = v___x_7946_;
v_isShared_8002_ = v_isSharedCheck_8006_;
goto v_resetjp_8000_;
}
else
{
lean_inc(v_a_7999_);
lean_inc(v_a_7998_);
lean_dec(v___x_7946_);
v___x_8001_ = lean_box(0);
v_isShared_8002_ = v_isSharedCheck_8006_;
goto v_resetjp_8000_;
}
v_resetjp_8000_:
{
lean_object* v___x_8004_; 
if (v_isShared_8002_ == 0)
{
v___x_8004_ = v___x_8001_;
goto v_reusejp_8003_;
}
else
{
lean_object* v_reuseFailAlloc_8005_; 
v_reuseFailAlloc_8005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8005_, 0, v_a_7998_);
lean_ctor_set(v_reuseFailAlloc_8005_, 1, v_a_7999_);
v___x_8004_ = v_reuseFailAlloc_8005_;
goto v_reusejp_8003_;
}
v_reusejp_8003_:
{
return v___x_8004_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object* v_libs_8007_, lean_object* v_objs_8008_, lean_object* v_weakArgs_8009_, lean_object* v_traceArgs_8010_, lean_object* v_sharedLean_8011_, lean_object* v_exeFile_8012_, lean_object* v___y_8013_, lean_object* v___y_8014_, lean_object* v___y_8015_, lean_object* v___y_8016_, lean_object* v___y_8017_, lean_object* v___y_8018_, lean_object* v___y_8019_){
_start:
{
uint8_t v_sharedLean_boxed_8020_; lean_object* v_res_8021_; 
v_sharedLean_boxed_8020_ = lean_unbox(v_sharedLean_8011_);
v_res_8021_ = l_Lake_buildLeanExe___lam__0(v_libs_8007_, v_objs_8008_, v_weakArgs_8009_, v_traceArgs_8010_, v_sharedLean_boxed_8020_, v_exeFile_8012_, v___y_8013_, v___y_8014_, v___y_8015_, v___y_8016_, v___y_8017_, v___y_8018_);
lean_dec(v___y_8016_);
lean_dec(v___y_8015_);
lean_dec(v___y_8014_);
lean_dec_ref(v___y_8013_);
lean_dec_ref(v_traceArgs_8010_);
lean_dec_ref(v_weakArgs_8009_);
lean_dec_ref(v_objs_8008_);
lean_dec_ref(v_libs_8007_);
return v_res_8021_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object* v_objs_8022_, lean_object* v_weakArgs_8023_, lean_object* v_traceArgs_8024_, uint8_t v_sharedLean_8025_, lean_object* v_exeFile_8026_, lean_object* v_libs_8027_, lean_object* v___y_8028_, lean_object* v___y_8029_, lean_object* v___y_8030_, lean_object* v___y_8031_, lean_object* v___y_8032_, lean_object* v___y_8033_){
_start:
{
lean_object* v_log_8035_; uint8_t v_action_8036_; uint8_t v_wantsRebuild_8037_; lean_object* v_trace_8038_; lean_object* v_buildTime_8039_; lean_object* v___x_8041_; uint8_t v_isShared_8042_; uint8_t v_isSharedCheck_8098_; 
v_log_8035_ = lean_ctor_get(v___y_8033_, 0);
v_action_8036_ = lean_ctor_get_uint8(v___y_8033_, sizeof(void*)*3);
v_wantsRebuild_8037_ = lean_ctor_get_uint8(v___y_8033_, sizeof(void*)*3 + 1);
v_trace_8038_ = lean_ctor_get(v___y_8033_, 1);
v_buildTime_8039_ = lean_ctor_get(v___y_8033_, 2);
v_isSharedCheck_8098_ = !lean_is_exclusive(v___y_8033_);
if (v_isSharedCheck_8098_ == 0)
{
v___x_8041_ = v___y_8033_;
v_isShared_8042_ = v_isSharedCheck_8098_;
goto v_resetjp_8040_;
}
else
{
lean_inc(v_buildTime_8039_);
lean_inc(v_trace_8038_);
lean_inc(v_log_8035_);
lean_dec(v___y_8033_);
v___x_8041_ = lean_box(0);
v_isShared_8042_ = v_isSharedCheck_8098_;
goto v_resetjp_8040_;
}
v_resetjp_8040_:
{
lean_object* v_leanTrace_8043_; lean_object* v___x_8044_; lean_object* v___f_8045_; lean_object* v___x_8046_; uint64_t v___y_8048_; uint64_t v___x_8087_; lean_object* v___x_8088_; lean_object* v___x_8089_; uint8_t v___x_8090_; 
v_leanTrace_8043_ = lean_ctor_get(v___y_8032_, 2);
v___x_8044_ = lean_box(v_sharedLean_8025_);
lean_inc_ref(v_exeFile_8026_);
lean_inc_ref(v_traceArgs_8024_);
v___f_8045_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__0___boxed), 13, 6);
lean_closure_set(v___f_8045_, 0, v_libs_8027_);
lean_closure_set(v___f_8045_, 1, v_objs_8022_);
lean_closure_set(v___f_8045_, 2, v_weakArgs_8023_);
lean_closure_set(v___f_8045_, 3, v_traceArgs_8024_);
lean_closure_set(v___f_8045_, 4, v___x_8044_);
lean_closure_set(v___f_8045_, 5, v_exeFile_8026_);
lean_inc_ref(v_leanTrace_8043_);
v___x_8046_ = l_Lake_BuildTrace_mix(v_trace_8038_, v_leanTrace_8043_);
v___x_8087_ = l_Lake_Hash_nil;
v___x_8088_ = lean_unsigned_to_nat(0u);
v___x_8089_ = lean_array_get_size(v_traceArgs_8024_);
v___x_8090_ = lean_nat_dec_lt(v___x_8088_, v___x_8089_);
if (v___x_8090_ == 0)
{
v___y_8048_ = v___x_8087_;
goto v___jp_8047_;
}
else
{
uint8_t v___x_8091_; 
v___x_8091_ = lean_nat_dec_le(v___x_8089_, v___x_8089_);
if (v___x_8091_ == 0)
{
if (v___x_8090_ == 0)
{
v___y_8048_ = v___x_8087_;
goto v___jp_8047_;
}
else
{
size_t v___x_8092_; size_t v___x_8093_; uint64_t v___x_8094_; 
v___x_8092_ = ((size_t)0ULL);
v___x_8093_ = lean_usize_of_nat(v___x_8089_);
v___x_8094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8024_, v___x_8092_, v___x_8093_, v___x_8087_);
v___y_8048_ = v___x_8094_;
goto v___jp_8047_;
}
}
else
{
size_t v___x_8095_; size_t v___x_8096_; uint64_t v___x_8097_; 
v___x_8095_ = ((size_t)0ULL);
v___x_8096_ = lean_usize_of_nat(v___x_8089_);
v___x_8097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8024_, v___x_8095_, v___x_8096_, v___x_8087_);
v___y_8048_ = v___x_8097_;
goto v___jp_8047_;
}
}
v___jp_8047_:
{
lean_object* v___x_8049_; lean_object* v___x_8050_; lean_object* v___x_8051_; lean_object* v___x_8052_; lean_object* v___x_8053_; lean_object* v___x_8054_; lean_object* v___x_8055_; lean_object* v___x_8056_; lean_object* v___x_8057_; lean_object* v___x_8058_; lean_object* v___x_8059_; lean_object* v___x_8060_; lean_object* v___x_8062_; 
v___x_8049_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_8050_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_8051_ = lean_array_to_list(v_traceArgs_8024_);
v___x_8052_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_8051_);
lean_dec(v___x_8051_);
v___x_8053_ = lean_string_append(v___x_8050_, v___x_8052_);
lean_dec_ref(v___x_8052_);
v___x_8054_ = lean_string_append(v___x_8049_, v___x_8053_);
lean_dec_ref(v___x_8053_);
v___x_8055_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_8056_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_8057_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_8057_, 0, v___x_8054_);
lean_ctor_set(v___x_8057_, 1, v___x_8055_);
lean_ctor_set(v___x_8057_, 2, v___x_8056_);
lean_ctor_set_uint64(v___x_8057_, sizeof(void*)*3, v___y_8048_);
v___x_8058_ = l_Lake_BuildTrace_mix(v___x_8046_, v___x_8057_);
v___x_8059_ = l_Lake_platformTrace;
v___x_8060_ = l_Lake_BuildTrace_mix(v___x_8058_, v___x_8059_);
if (v_isShared_8042_ == 0)
{
lean_ctor_set(v___x_8041_, 1, v___x_8060_);
v___x_8062_ = v___x_8041_;
goto v_reusejp_8061_;
}
else
{
lean_object* v_reuseFailAlloc_8086_; 
v_reuseFailAlloc_8086_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8086_, 0, v_log_8035_);
lean_ctor_set(v_reuseFailAlloc_8086_, 1, v___x_8060_);
lean_ctor_set(v_reuseFailAlloc_8086_, 2, v_buildTime_8039_);
lean_ctor_set_uint8(v_reuseFailAlloc_8086_, sizeof(void*)*3, v_action_8036_);
lean_ctor_set_uint8(v_reuseFailAlloc_8086_, sizeof(void*)*3 + 1, v_wantsRebuild_8037_);
v___x_8062_ = v_reuseFailAlloc_8086_;
goto v_reusejp_8061_;
}
v_reusejp_8061_:
{
uint8_t v___x_8063_; lean_object* v___x_8064_; uint8_t v___x_8065_; lean_object* v___x_8066_; 
v___x_8063_ = 0;
v___x_8064_ = l_System_FilePath_exeExtension;
v___x_8065_ = 1;
v___x_8066_ = l_Lake_buildArtifactUnlessUpToDate(v_exeFile_8026_, v___f_8045_, v___x_8063_, v___x_8064_, v___x_8065_, v___x_8065_, v___y_8028_, v___y_8029_, v___y_8030_, v___y_8031_, v___y_8032_, v___x_8062_);
if (lean_obj_tag(v___x_8066_) == 0)
{
lean_object* v_a_8067_; lean_object* v_a_8068_; lean_object* v___x_8070_; uint8_t v_isShared_8071_; uint8_t v_isSharedCheck_8076_; 
v_a_8067_ = lean_ctor_get(v___x_8066_, 0);
v_a_8068_ = lean_ctor_get(v___x_8066_, 1);
v_isSharedCheck_8076_ = !lean_is_exclusive(v___x_8066_);
if (v_isSharedCheck_8076_ == 0)
{
v___x_8070_ = v___x_8066_;
v_isShared_8071_ = v_isSharedCheck_8076_;
goto v_resetjp_8069_;
}
else
{
lean_inc(v_a_8068_);
lean_inc(v_a_8067_);
lean_dec(v___x_8066_);
v___x_8070_ = lean_box(0);
v_isShared_8071_ = v_isSharedCheck_8076_;
goto v_resetjp_8069_;
}
v_resetjp_8069_:
{
lean_object* v_path_8072_; lean_object* v___x_8074_; 
v_path_8072_ = lean_ctor_get(v_a_8067_, 1);
lean_inc_ref(v_path_8072_);
lean_dec(v_a_8067_);
if (v_isShared_8071_ == 0)
{
lean_ctor_set(v___x_8070_, 0, v_path_8072_);
v___x_8074_ = v___x_8070_;
goto v_reusejp_8073_;
}
else
{
lean_object* v_reuseFailAlloc_8075_; 
v_reuseFailAlloc_8075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8075_, 0, v_path_8072_);
lean_ctor_set(v_reuseFailAlloc_8075_, 1, v_a_8068_);
v___x_8074_ = v_reuseFailAlloc_8075_;
goto v_reusejp_8073_;
}
v_reusejp_8073_:
{
return v___x_8074_;
}
}
}
else
{
lean_object* v_a_8077_; lean_object* v_a_8078_; lean_object* v___x_8080_; uint8_t v_isShared_8081_; uint8_t v_isSharedCheck_8085_; 
v_a_8077_ = lean_ctor_get(v___x_8066_, 0);
v_a_8078_ = lean_ctor_get(v___x_8066_, 1);
v_isSharedCheck_8085_ = !lean_is_exclusive(v___x_8066_);
if (v_isSharedCheck_8085_ == 0)
{
v___x_8080_ = v___x_8066_;
v_isShared_8081_ = v_isSharedCheck_8085_;
goto v_resetjp_8079_;
}
else
{
lean_inc(v_a_8078_);
lean_inc(v_a_8077_);
lean_dec(v___x_8066_);
v___x_8080_ = lean_box(0);
v_isShared_8081_ = v_isSharedCheck_8085_;
goto v_resetjp_8079_;
}
v_resetjp_8079_:
{
lean_object* v___x_8083_; 
if (v_isShared_8081_ == 0)
{
v___x_8083_ = v___x_8080_;
goto v_reusejp_8082_;
}
else
{
lean_object* v_reuseFailAlloc_8084_; 
v_reuseFailAlloc_8084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8084_, 0, v_a_8077_);
lean_ctor_set(v_reuseFailAlloc_8084_, 1, v_a_8078_);
v___x_8083_ = v_reuseFailAlloc_8084_;
goto v_reusejp_8082_;
}
v_reusejp_8082_:
{
return v___x_8083_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object* v_objs_8099_, lean_object* v_weakArgs_8100_, lean_object* v_traceArgs_8101_, lean_object* v_sharedLean_8102_, lean_object* v_exeFile_8103_, lean_object* v_libs_8104_, lean_object* v___y_8105_, lean_object* v___y_8106_, lean_object* v___y_8107_, lean_object* v___y_8108_, lean_object* v___y_8109_, lean_object* v___y_8110_, lean_object* v___y_8111_){
_start:
{
uint8_t v_sharedLean_boxed_8112_; lean_object* v_res_8113_; 
v_sharedLean_boxed_8112_ = lean_unbox(v_sharedLean_8102_);
v_res_8113_ = l_Lake_buildLeanExe___lam__1(v_objs_8099_, v_weakArgs_8100_, v_traceArgs_8101_, v_sharedLean_boxed_8112_, v_exeFile_8103_, v_libs_8104_, v___y_8105_, v___y_8106_, v___y_8107_, v___y_8108_, v___y_8109_, v___y_8110_);
return v_res_8113_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2(lean_object* v_weakArgs_8114_, lean_object* v_traceArgs_8115_, uint8_t v_sharedLean_8116_, lean_object* v_exeFile_8117_, lean_object* v_linkLibs_8118_, lean_object* v___x_8119_, lean_object* v_objs_8120_, lean_object* v___y_8121_, lean_object* v___y_8122_, lean_object* v___y_8123_, lean_object* v___y_8124_, lean_object* v___y_8125_, lean_object* v___y_8126_){
_start:
{
lean_object* v_trace_8128_; lean_object* v___x_8129_; lean_object* v___f_8130_; lean_object* v___x_8131_; lean_object* v___x_8132_; lean_object* v___x_8133_; uint8_t v___x_8134_; lean_object* v___x_8135_; lean_object* v___x_8136_; 
v_trace_8128_ = lean_ctor_get(v___y_8126_, 1);
v___x_8129_ = lean_box(v_sharedLean_8116_);
v___f_8130_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__1___boxed), 13, 5);
lean_closure_set(v___f_8130_, 0, v_objs_8120_);
lean_closure_set(v___f_8130_, 1, v_weakArgs_8114_);
lean_closure_set(v___f_8130_, 2, v_traceArgs_8115_);
lean_closure_set(v___f_8130_, 3, v___x_8129_);
lean_closure_set(v___f_8130_, 4, v_exeFile_8117_);
v___x_8131_ = ((lean_object*)(l_Lake_buildSharedLib___lam__3___closed__0));
v___x_8132_ = l_Lake_Job_collectArray___redArg(v_linkLibs_8118_, v___x_8131_);
v___x_8133_ = lean_unsigned_to_nat(0u);
v___x_8134_ = 0;
lean_inc_ref(v_trace_8128_);
v___x_8135_ = l_Lake_Job_mapM___redArg(v___x_8119_, v___x_8132_, v___f_8130_, v___x_8133_, v___x_8134_, v___y_8121_, v___y_8122_, v___y_8123_, v___y_8124_, v___y_8125_, v_trace_8128_);
v___x_8136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8136_, 0, v___x_8135_);
lean_ctor_set(v___x_8136_, 1, v___y_8126_);
return v___x_8136_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2___boxed(lean_object* v_weakArgs_8137_, lean_object* v_traceArgs_8138_, lean_object* v_sharedLean_8139_, lean_object* v_exeFile_8140_, lean_object* v_linkLibs_8141_, lean_object* v___x_8142_, lean_object* v_objs_8143_, lean_object* v___y_8144_, lean_object* v___y_8145_, lean_object* v___y_8146_, lean_object* v___y_8147_, lean_object* v___y_8148_, lean_object* v___y_8149_, lean_object* v___y_8150_){
_start:
{
uint8_t v_sharedLean_boxed_8151_; lean_object* v_res_8152_; 
v_sharedLean_boxed_8151_ = lean_unbox(v_sharedLean_8139_);
v_res_8152_ = l_Lake_buildLeanExe___lam__2(v_weakArgs_8137_, v_traceArgs_8138_, v_sharedLean_boxed_8151_, v_exeFile_8140_, v_linkLibs_8141_, v___x_8142_, v_objs_8143_, v___y_8144_, v___y_8145_, v___y_8146_, v___y_8147_, v___y_8148_, v___y_8149_);
lean_dec_ref(v_linkLibs_8141_);
return v_res_8152_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object* v_exeFile_8153_, lean_object* v_linkObjs_8154_, lean_object* v_linkLibs_8155_, lean_object* v_weakArgs_8156_, lean_object* v_traceArgs_8157_, uint8_t v_sharedLean_8158_, lean_object* v_a_8159_, lean_object* v_a_8160_, lean_object* v_a_8161_, lean_object* v_a_8162_, lean_object* v_a_8163_, lean_object* v_a_8164_){
_start:
{
lean_object* v___x_8166_; lean_object* v___x_8167_; lean_object* v___f_8168_; lean_object* v___x_8169_; lean_object* v___x_8170_; lean_object* v___x_8171_; uint8_t v___x_8172_; lean_object* v___x_8173_; 
v___x_8166_ = l_Lake_instDataKindFilePath;
v___x_8167_ = lean_box(v_sharedLean_8158_);
v___f_8168_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__2___boxed), 14, 6);
lean_closure_set(v___f_8168_, 0, v_weakArgs_8156_);
lean_closure_set(v___f_8168_, 1, v_traceArgs_8157_);
lean_closure_set(v___f_8168_, 2, v___x_8167_);
lean_closure_set(v___f_8168_, 3, v_exeFile_8153_);
lean_closure_set(v___f_8168_, 4, v_linkLibs_8155_);
lean_closure_set(v___f_8168_, 5, v___x_8166_);
v___x_8169_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8170_ = l_Lake_Job_collectArray___redArg(v_linkObjs_8154_, v___x_8169_);
v___x_8171_ = lean_unsigned_to_nat(0u);
v___x_8172_ = 1;
v___x_8173_ = l_Lake_Job_bindM___redArg(v___x_8166_, v___x_8170_, v___f_8168_, v___x_8171_, v___x_8172_, v_a_8159_, v_a_8160_, v_a_8161_, v_a_8162_, v_a_8163_, v_a_8164_);
return v___x_8173_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object* v_exeFile_8174_, lean_object* v_linkObjs_8175_, lean_object* v_linkLibs_8176_, lean_object* v_weakArgs_8177_, lean_object* v_traceArgs_8178_, lean_object* v_sharedLean_8179_, lean_object* v_a_8180_, lean_object* v_a_8181_, lean_object* v_a_8182_, lean_object* v_a_8183_, lean_object* v_a_8184_, lean_object* v_a_8185_, lean_object* v_a_8186_){
_start:
{
uint8_t v_sharedLean_boxed_8187_; lean_object* v_res_8188_; 
v_sharedLean_boxed_8187_ = lean_unbox(v_sharedLean_8179_);
v_res_8188_ = l_Lake_buildLeanExe(v_exeFile_8174_, v_linkObjs_8175_, v_linkLibs_8176_, v_weakArgs_8177_, v_traceArgs_8178_, v_sharedLean_boxed_8187_, v_a_8180_, v_a_8181_, v_a_8182_, v_a_8183_, v_a_8184_, v_a_8185_);
lean_dec_ref(v_linkObjs_8175_);
return v_res_8188_;
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
