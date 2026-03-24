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
extern lean_object* l_instMonadBaseIO;
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
lean_object* l_StateRefT_x27_instAlternativeOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_read___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(lean_object*, lean_object*);
lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(lean_object*, lean_object*);
lean_object* l_instMonadBaseIO___aux__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
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
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__0 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__0_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__1 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__1_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__2 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__2_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__3 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__3_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__4 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__4_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__5 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__5_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__6 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__6_value;
static const lean_ctor_object l_Lake_instMonadWorkspaceJobM___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__0_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__1_value)}};
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__7 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__7_value;
static const lean_ctor_object l_Lake_instMonadWorkspaceJobM___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__7_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__2_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__3_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__4_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__5_value)}};
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__8 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__8_value;
static const lean_ctor_object l_Lake_instMonadWorkspaceJobM___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__8_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__6_value)}};
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__9 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__9_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instFunctorOfMonad___redArg___lam__0, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__7_value)} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__10 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__10_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instFunctorOfMonad___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__7_value)} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__11 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__11_value;
static const lean_ctor_object l_Lake_instMonadWorkspaceJobM___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__10_value),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__11_value)}};
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__12 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__12_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_read___boxed, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__9_value)} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__13 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__13_value;
static lean_once_cell_t l_Lake_instMonadWorkspaceJobM___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__14;
static lean_once_cell_t l_Lake_instMonadWorkspaceJobM___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__15;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadBaseIO___aux__5___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__16 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__16_value;
static const lean_closure_object l_Lake_instMonadWorkspaceJobM___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_EStateT_instPure___redArg___lam__0, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__16_value)} };
static const lean_object* l_Lake_instMonadWorkspaceJobM___closed__17 = (const lean_object*)&l_Lake_instMonadWorkspaceJobM___closed__17_value;
static lean_once_cell_t l_Lake_instMonadWorkspaceJobM___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__18;
static lean_once_cell_t l_Lake_instMonadWorkspaceJobM___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__19;
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
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_resolveArtifact___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "downloaded succeeded, but artifact failed to resolve: "};
static const lean_object* l_Lake_resolveArtifact___lam__1___closed__0 = (const lean_object*)&l_Lake_resolveArtifact___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_resolveArtifact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "downloaded artifact "};
static const lean_object* l_Lake_resolveArtifact___closed__0 = (const lean_object*)&l_Lake_resolveArtifact___closed__0_value;
static const lean_string_object l_Lake_resolveArtifact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\n  local path: "};
static const lean_object* l_Lake_resolveArtifact___closed__1 = (const lean_object*)&l_Lake_resolveArtifact___closed__1_value;
static const lean_string_object l_Lake_resolveArtifact___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\n  remote URL: "};
static const lean_object* l_Lake_resolveArtifact___closed__2 = (const lean_object*)&l_Lake_resolveArtifact___closed__2_value;
static const lean_string_object l_Lake_resolveArtifact___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "could not mark downloaded artifact read-only: "};
static const lean_object* l_Lake_resolveArtifact___closed__3 = (const lean_object*)&l_Lake_resolveArtifact___closed__3_value;
static const lean_string_object l_Lake_resolveArtifact___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "artifact with associated cache service but no scope"};
static const lean_object* l_Lake_resolveArtifact___closed__4 = (const lean_object*)&l_Lake_resolveArtifact___closed__4_value;
static const lean_ctor_object l_Lake_resolveArtifact___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_resolveArtifact___closed__4_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_resolveArtifact___closed__5 = (const lean_object*)&l_Lake_resolveArtifact___closed__5_value;
static const lean_string_object l_Lake_resolveArtifact___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "artifact cache service is not configured: "};
static const lean_object* l_Lake_resolveArtifact___closed__6 = (const lean_object*)&l_Lake_resolveArtifact___closed__6_value;
static const lean_string_object l_Lake_resolveArtifact___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "artifact not found in cache:\n  "};
static const lean_object* l_Lake_resolveArtifact___closed__7 = (const lean_object*)&l_Lake_resolveArtifact___closed__7_value;
static const lean_string_object l_Lake_resolveArtifact___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "failed to retrieve artifact from cache: "};
static const lean_object* l_Lake_resolveArtifact___closed__8 = (const lean_object*)&l_Lake_resolveArtifact___closed__8_value;
LEAN_EXPORT lean_object* l_Lake_resolveArtifact(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_resolveArtifactOutput___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "ill-formed artifact output:\n"};
static const lean_object* l_Lake_resolveArtifactOutput___closed__0 = (const lean_object*)&l_Lake_resolveArtifactOutput___closed__0_value;
static const lean_string_object l_Lake_resolveArtifactOutput___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lake_resolveArtifactOutput___closed__1 = (const lean_object*)&l_Lake_resolveArtifactOutput___closed__1_value;
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(uint8_t, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(uint8_t, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__14(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__12));
v___x_30_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__13));
v___x_31_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__15(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = l_instMonadBaseIO;
v___x_33_ = l_Lake_instAlternativeELogTOfMonad___redArg(v___x_32_);
return v___x_33_;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__18(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__12));
v___x_38_ = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__14, &l_Lake_instMonadWorkspaceJobM___closed__14_once, _init_l_Lake_instMonadWorkspaceJobM___closed__14);
v___x_39_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v___x_38_, v___x_37_);
return v___x_39_;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__19(void){
_start:
{
lean_object* v___x_40_; lean_object* v___f_41_; lean_object* v___x_42_; 
v___x_40_ = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__18, &l_Lake_instMonadWorkspaceJobM___closed__18_once, _init_l_Lake_instMonadWorkspaceJobM___closed__18);
v___f_41_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__17));
v___x_42_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0), 4, 3);
lean_closure_set(v___x_42_, 0, v___f_41_);
lean_closure_set(v___x_42_, 1, lean_box(0));
lean_closure_set(v___x_42_, 2, v___x_40_);
return v___x_42_;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM(void){
_start:
{
lean_object* v___x_43_; lean_object* v_toApplicative_44_; lean_object* v_toBind_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_122_; 
v___x_43_ = l_instMonadBaseIO;
v_toApplicative_44_ = lean_ctor_get(v___x_43_, 0);
v_toBind_45_ = lean_ctor_get(v___x_43_, 1);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_122_ == 0)
{
v___x_47_ = v___x_43_;
v_isShared_48_ = v_isSharedCheck_122_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_toBind_45_);
lean_inc(v_toApplicative_44_);
lean_dec(v___x_43_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_122_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v_toFunctor_49_; lean_object* v_toPure_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_118_; 
v_toFunctor_49_ = lean_ctor_get(v_toApplicative_44_, 0);
v_toPure_50_ = lean_ctor_get(v_toApplicative_44_, 1);
v_isSharedCheck_118_ = !lean_is_exclusive(v_toApplicative_44_);
if (v_isSharedCheck_118_ == 0)
{
lean_object* v_unused_119_; lean_object* v_unused_120_; lean_object* v_unused_121_; 
v_unused_119_ = lean_ctor_get(v_toApplicative_44_, 4);
lean_dec(v_unused_119_);
v_unused_120_ = lean_ctor_get(v_toApplicative_44_, 3);
lean_dec(v_unused_120_);
v_unused_121_ = lean_ctor_get(v_toApplicative_44_, 2);
lean_dec(v_unused_121_);
v___x_52_ = v_toApplicative_44_;
v_isShared_53_ = v_isSharedCheck_118_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_toPure_50_);
lean_inc(v_toFunctor_49_);
lean_dec(v_toApplicative_44_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_118_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___f_54_; lean_object* v___f_55_; lean_object* v___f_56_; lean_object* v___f_57_; lean_object* v___x_58_; lean_object* v___f_59_; lean_object* v___x_61_; 
lean_inc(v_toBind_45_);
lean_inc(v_toPure_50_);
v___f_54_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_54_, 0, v_toPure_50_);
lean_closure_set(v___f_54_, 1, v_toBind_45_);
lean_inc(v_toBind_45_);
lean_inc(v_toPure_50_);
v___f_55_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_55_, 0, v_toPure_50_);
lean_closure_set(v___f_55_, 1, v_toBind_45_);
lean_inc_ref(v___f_54_);
lean_inc(v_toPure_50_);
v___f_56_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_56_, 0, v_toPure_50_);
lean_closure_set(v___f_56_, 1, v___f_54_);
lean_inc(v_toPure_50_);
lean_inc_ref(v_toFunctor_49_);
v___f_57_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_57_, 0, v_toFunctor_49_);
lean_closure_set(v___f_57_, 1, v_toPure_50_);
lean_closure_set(v___f_57_, 2, v_toBind_45_);
v___x_58_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_49_);
v___f_59_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_59_, 0, v_toPure_50_);
lean_inc_ref(v___x_58_);
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 4, v___f_55_);
lean_ctor_set(v___x_52_, 3, v___f_56_);
lean_ctor_set(v___x_52_, 2, v___f_57_);
lean_ctor_set(v___x_52_, 1, v___f_59_);
lean_ctor_set(v___x_52_, 0, v___x_58_);
v___x_61_ = v___x_52_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_58_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v___f_59_);
lean_ctor_set(v_reuseFailAlloc_117_, 2, v___f_57_);
lean_ctor_set(v_reuseFailAlloc_117_, 3, v___f_56_);
lean_ctor_set(v_reuseFailAlloc_117_, 4, v___f_55_);
v___x_61_ = v_reuseFailAlloc_117_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
lean_object* v___x_63_; 
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 1, v___f_54_);
lean_ctor_set(v___x_47_, 0, v___x_61_);
v___x_63_ = v___x_47_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_61_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v___f_54_);
v___x_63_ = v_reuseFailAlloc_116_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
lean_object* v___f_64_; lean_object* v___f_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v_toApplicative_71_; lean_object* v_toFunctor_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v_toApplicative_76_; lean_object* v_toFunctor_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___f_81_; lean_object* v___f_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v_toApplicative_85_; lean_object* v_toFunctor_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___f_92_; lean_object* v___f_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v_toApplicative_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_114_; 
lean_inc_ref(v___x_58_);
v___f_64_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_64_, 0, v___x_58_);
v___f_65_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_65_, 0, v___x_58_);
v___x_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_66_, 0, v___f_64_);
lean_ctor_set(v___x_66_, 1, v___f_65_);
v___x_67_ = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__15, &l_Lake_instMonadWorkspaceJobM___closed__15_once, _init_l_Lake_instMonadWorkspaceJobM___closed__15);
lean_inc_ref(v___x_63_);
v___x_68_ = l_ReaderT_instAlternativeOfMonad___redArg(v___x_67_, v___x_63_);
v___x_69_ = l_ReaderT_instMonad___redArg(v___x_63_);
lean_inc_ref(v___x_69_);
v___x_70_ = l_StateRefT_x27_instAlternativeOfMonad___redArg(v___x_68_, v___x_69_);
v_toApplicative_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc_ref(v_toApplicative_71_);
lean_dec_ref(v___x_70_);
v_toFunctor_72_ = lean_ctor_get(v_toApplicative_71_, 0);
lean_inc_ref(v_toFunctor_72_);
lean_dec_ref(v_toApplicative_71_);
v___x_73_ = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__19, &l_Lake_instMonadWorkspaceJobM___closed__19_once, _init_l_Lake_instMonadWorkspaceJobM___closed__19);
lean_inc_ref(v___x_66_);
v___x_74_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_73_, v___x_66_);
v___x_75_ = l_StateRefT_x27_instMonad___redArg(v___x_69_);
v_toApplicative_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc_ref(v_toApplicative_76_);
v_toFunctor_77_ = lean_ctor_get(v_toApplicative_76_, 0);
lean_inc_ref(v_toFunctor_77_);
lean_dec_ref(v_toApplicative_76_);
v___x_78_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v___x_74_, v___x_66_);
v___x_79_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_79_, 0, lean_box(0));
lean_closure_set(v___x_79_, 1, lean_box(0));
lean_closure_set(v___x_79_, 2, lean_box(0));
lean_closure_set(v___x_79_, 3, lean_box(0));
lean_closure_set(v___x_79_, 4, v___x_78_);
lean_inc_ref(v_toFunctor_72_);
v___x_80_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_79_, v_toFunctor_72_);
lean_inc_ref(v_toFunctor_77_);
v___f_81_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_81_, 0, v_toFunctor_77_);
v___f_82_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_82_, 0, v_toFunctor_77_);
v___x_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_83_, 0, v___f_81_);
lean_ctor_set(v___x_83_, 1, v___f_82_);
v___x_84_ = l_ReaderT_instMonad___redArg(v___x_75_);
v_toApplicative_85_ = lean_ctor_get(v___x_84_, 0);
lean_inc_ref(v_toApplicative_85_);
v_toFunctor_86_ = lean_ctor_get(v_toApplicative_85_, 0);
lean_inc_ref(v_toFunctor_86_);
lean_dec_ref(v_toApplicative_85_);
v___x_87_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v___x_80_, v_toFunctor_72_);
v___x_88_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(v___x_88_, 0, lean_box(0));
lean_closure_set(v___x_88_, 1, v___x_87_);
lean_inc_ref(v___x_83_);
v___x_89_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_88_, v___x_83_);
v___x_90_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v___x_89_, v___x_83_);
v___x_91_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(v___x_91_, 0, lean_box(0));
lean_closure_set(v___x_91_, 1, v___x_90_);
lean_inc_ref(v_toFunctor_86_);
v___f_92_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_92_, 0, v_toFunctor_86_);
v___f_93_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_93_, 0, v_toFunctor_86_);
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v___f_92_);
lean_ctor_set(v___x_94_, 1, v___f_93_);
lean_inc_ref(v___x_94_);
v___x_95_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_91_, v___x_94_);
lean_inc_ref(v___x_94_);
v___x_96_ = l_Lake_EquipT_instFunctor___redArg(v___x_94_);
v_toApplicative_97_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_114_ == 0)
{
lean_object* v_unused_115_; 
v_unused_115_ = lean_ctor_get(v___x_84_, 1);
lean_dec(v_unused_115_);
v___x_99_ = v___x_84_;
v_isShared_100_ = v_isSharedCheck_114_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_toApplicative_97_);
lean_dec(v___x_84_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_114_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v_toFunctor_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___f_107_; lean_object* v___f_108_; lean_object* v___x_110_; 
v_toFunctor_101_ = lean_ctor_get(v_toApplicative_97_, 0);
lean_inc_ref(v_toFunctor_101_);
lean_dec_ref(v_toApplicative_97_);
v___x_102_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v___x_95_, v___x_94_);
v___x_103_ = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(v___x_103_, 0, lean_box(0));
lean_closure_set(v___x_103_, 1, lean_box(0));
lean_closure_set(v___x_103_, 2, lean_box(0));
lean_closure_set(v___x_103_, 3, v___x_102_);
lean_inc_ref(v___x_96_);
v___x_104_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_103_, v___x_96_);
v___x_105_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v___x_104_, v___x_96_);
v___x_106_ = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM___boxed), 9, 2);
lean_closure_set(v___x_106_, 0, lean_box(0));
lean_closure_set(v___x_106_, 1, v___x_105_);
lean_inc_ref(v_toFunctor_101_);
v___f_107_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_107_, 0, v_toFunctor_101_);
v___f_108_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_108_, 0, v_toFunctor_101_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 1, v___f_108_);
lean_ctor_set(v___x_99_, 0, v___f_107_);
v___x_110_ = v___x_99_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___f_107_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v___f_108_);
v___x_110_ = v_reuseFailAlloc_113_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = l_Lake_EquipT_instFunctor___redArg(v___x_110_);
v___x_112_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_106_, v___x_111_);
return v___x_112_;
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
lean_object* v___x_123_; uint64_t v___x_124_; 
v___x_123_ = l_System_Platform_target;
v___x_124_ = lean_string_hash(v___x_123_);
return v___x_124_;
}
}
static uint64_t _init_l_Lake_platformTrace___closed__1(void){
_start:
{
uint64_t v___x_125_; uint64_t v___x_126_; uint64_t v___x_127_; 
v___x_125_ = lean_uint64_once(&l_Lake_platformTrace___closed__0, &l_Lake_platformTrace___closed__0_once, _init_l_Lake_platformTrace___closed__0);
v___x_126_ = l_Lake_Hash_nil;
v___x_127_ = lean_uint64_mix_hash(v___x_126_, v___x_125_);
return v___x_127_;
}
}
static lean_object* _init_l_Lake_platformTrace___closed__3(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = lean_nat_to_int(v___x_130_);
return v___x_131_;
}
}
static lean_object* _init_l_Lake_platformTrace___closed__4(void){
_start:
{
uint32_t v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = 0;
v___x_133_ = lean_obj_once(&l_Lake_platformTrace___closed__3, &l_Lake_platformTrace___closed__3_once, _init_l_Lake_platformTrace___closed__3);
v___x_134_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set_uint32(v___x_134_, sizeof(void*)*1, v___x_132_);
return v___x_134_;
}
}
static lean_object* _init_l_Lake_platformTrace___closed__5(void){
_start:
{
lean_object* v___x_135_; uint64_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_135_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_136_ = lean_uint64_once(&l_Lake_platformTrace___closed__1, &l_Lake_platformTrace___closed__1_once, _init_l_Lake_platformTrace___closed__1);
v___x_137_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_138_ = l_System_Platform_target;
v___x_139_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v___x_137_);
lean_ctor_set(v___x_139_, 2, v___x_135_);
lean_ctor_set_uint64(v___x_139_, sizeof(void*)*3, v___x_136_);
return v___x_139_;
}
}
static lean_object* _init_l_Lake_platformTrace(void){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = lean_obj_once(&l_Lake_platformTrace___closed__5, &l_Lake_platformTrace___closed__5_once, _init_l_Lake_platformTrace___closed__5);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg(lean_object* v_a_141_){
_start:
{
lean_object* v_log_143_; uint8_t v_action_144_; uint8_t v_wantsRebuild_145_; lean_object* v_trace_146_; lean_object* v_buildTime_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_158_; 
v_log_143_ = lean_ctor_get(v_a_141_, 0);
v_action_144_ = lean_ctor_get_uint8(v_a_141_, sizeof(void*)*3);
v_wantsRebuild_145_ = lean_ctor_get_uint8(v_a_141_, sizeof(void*)*3 + 1);
v_trace_146_ = lean_ctor_get(v_a_141_, 1);
v_buildTime_147_ = lean_ctor_get(v_a_141_, 2);
v_isSharedCheck_158_ = !lean_is_exclusive(v_a_141_);
if (v_isSharedCheck_158_ == 0)
{
v___x_149_ = v_a_141_;
v_isShared_150_ = v_isSharedCheck_158_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_buildTime_147_);
lean_inc(v_trace_146_);
lean_inc(v_log_143_);
lean_dec(v_a_141_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_158_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_151_ = l_Lake_platformTrace;
v___x_152_ = lean_box(0);
v___x_153_ = l_Lake_BuildTrace_mix(v_trace_146_, v___x_151_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 1, v___x_153_);
v___x_155_ = v___x_149_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_log_143_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v___x_153_);
lean_ctor_set(v_reuseFailAlloc_157_, 2, v_buildTime_147_);
lean_ctor_set_uint8(v_reuseFailAlloc_157_, sizeof(void*)*3, v_action_144_);
lean_ctor_set_uint8(v_reuseFailAlloc_157_, sizeof(void*)*3 + 1, v_wantsRebuild_145_);
v___x_155_ = v_reuseFailAlloc_157_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_156_; 
v___x_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_152_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
return v___x_156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg___boxed(lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lake_addPlatformTrace___redArg(v_a_159_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace(lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_log_169_; uint8_t v_action_170_; uint8_t v_wantsRebuild_171_; lean_object* v_trace_172_; lean_object* v_buildTime_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_184_; 
v_log_169_ = lean_ctor_get(v_a_167_, 0);
v_action_170_ = lean_ctor_get_uint8(v_a_167_, sizeof(void*)*3);
v_wantsRebuild_171_ = lean_ctor_get_uint8(v_a_167_, sizeof(void*)*3 + 1);
v_trace_172_ = lean_ctor_get(v_a_167_, 1);
v_buildTime_173_ = lean_ctor_get(v_a_167_, 2);
v_isSharedCheck_184_ = !lean_is_exclusive(v_a_167_);
if (v_isSharedCheck_184_ == 0)
{
v___x_175_ = v_a_167_;
v_isShared_176_ = v_isSharedCheck_184_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_buildTime_173_);
lean_inc(v_trace_172_);
lean_inc(v_log_169_);
lean_dec(v_a_167_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_184_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_177_ = l_Lake_platformTrace;
v___x_178_ = lean_box(0);
v___x_179_ = l_Lake_BuildTrace_mix(v_trace_172_, v___x_177_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v___x_179_);
v___x_181_ = v___x_175_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_log_169_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_183_, 2, v_buildTime_173_);
lean_ctor_set_uint8(v_reuseFailAlloc_183_, sizeof(void*)*3, v_action_170_);
lean_ctor_set_uint8(v_reuseFailAlloc_183_, sizeof(void*)*3 + 1, v_wantsRebuild_171_);
v___x_181_ = v_reuseFailAlloc_183_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_182_; 
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_178_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
return v___x_182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___boxed(lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lake_addPlatformTrace(v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_);
lean_dec_ref(v_a_189_);
lean_dec(v_a_188_);
lean_dec(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg(lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v_log_196_; uint8_t v_action_197_; uint8_t v_wantsRebuild_198_; lean_object* v_trace_199_; lean_object* v_buildTime_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_211_; 
v_log_196_ = lean_ctor_get(v_a_194_, 0);
v_action_197_ = lean_ctor_get_uint8(v_a_194_, sizeof(void*)*3);
v_wantsRebuild_198_ = lean_ctor_get_uint8(v_a_194_, sizeof(void*)*3 + 1);
v_trace_199_ = lean_ctor_get(v_a_194_, 1);
v_buildTime_200_ = lean_ctor_get(v_a_194_, 2);
v_isSharedCheck_211_ = !lean_is_exclusive(v_a_194_);
if (v_isSharedCheck_211_ == 0)
{
v___x_202_ = v_a_194_;
v_isShared_203_ = v_isSharedCheck_211_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_buildTime_200_);
lean_inc(v_trace_199_);
lean_inc(v_log_196_);
lean_dec(v_a_194_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_211_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v_leanTrace_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_208_; 
v_leanTrace_204_ = lean_ctor_get(v_a_193_, 2);
lean_inc_ref(v_leanTrace_204_);
lean_dec_ref(v_a_193_);
v___x_205_ = lean_box(0);
v___x_206_ = l_Lake_BuildTrace_mix(v_trace_199_, v_leanTrace_204_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 1, v___x_206_);
v___x_208_ = v___x_202_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_log_196_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v___x_206_);
lean_ctor_set(v_reuseFailAlloc_210_, 2, v_buildTime_200_);
lean_ctor_set_uint8(v_reuseFailAlloc_210_, sizeof(void*)*3, v_action_197_);
lean_ctor_set_uint8(v_reuseFailAlloc_210_, sizeof(void*)*3 + 1, v_wantsRebuild_198_);
v___x_208_ = v_reuseFailAlloc_210_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_209_; 
v___x_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_205_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
return v___x_209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg___boxed(lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lake_addLeanTrace___redArg(v_a_212_, v_a_213_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace(lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_log_223_; uint8_t v_action_224_; uint8_t v_wantsRebuild_225_; lean_object* v_trace_226_; lean_object* v_buildTime_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_238_; 
v_log_223_ = lean_ctor_get(v_a_221_, 0);
v_action_224_ = lean_ctor_get_uint8(v_a_221_, sizeof(void*)*3);
v_wantsRebuild_225_ = lean_ctor_get_uint8(v_a_221_, sizeof(void*)*3 + 1);
v_trace_226_ = lean_ctor_get(v_a_221_, 1);
v_buildTime_227_ = lean_ctor_get(v_a_221_, 2);
v_isSharedCheck_238_ = !lean_is_exclusive(v_a_221_);
if (v_isSharedCheck_238_ == 0)
{
v___x_229_ = v_a_221_;
v_isShared_230_ = v_isSharedCheck_238_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_buildTime_227_);
lean_inc(v_trace_226_);
lean_inc(v_log_223_);
lean_dec(v_a_221_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_238_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v_leanTrace_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
v_leanTrace_231_ = lean_ctor_get(v_a_220_, 2);
lean_inc_ref(v_leanTrace_231_);
lean_dec_ref(v_a_220_);
v___x_232_ = lean_box(0);
v___x_233_ = l_Lake_BuildTrace_mix(v_trace_226_, v_leanTrace_231_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 1, v___x_233_);
v___x_235_ = v___x_229_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_log_223_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_237_, 2, v_buildTime_227_);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, sizeof(void*)*3, v_action_224_);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, sizeof(void*)*3 + 1, v_wantsRebuild_225_);
v___x_235_ = v_reuseFailAlloc_237_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_236_; 
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_232_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
return v___x_236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___boxed(lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lake_addLeanTrace(v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
lean_dec(v_a_242_);
lean_dec(v_a_241_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg(lean_object* v_inst_248_, lean_object* v_inst_249_, lean_object* v_a_250_, lean_object* v_caption_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_log_254_; uint8_t v_action_255_; uint8_t v_wantsRebuild_256_; lean_object* v_trace_257_; lean_object* v_buildTime_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_277_; 
v_log_254_ = lean_ctor_get(v_a_252_, 0);
v_action_255_ = lean_ctor_get_uint8(v_a_252_, sizeof(void*)*3);
v_wantsRebuild_256_ = lean_ctor_get_uint8(v_a_252_, sizeof(void*)*3 + 1);
v_trace_257_ = lean_ctor_get(v_a_252_, 1);
v_buildTime_258_ = lean_ctor_get(v_a_252_, 2);
v_isSharedCheck_277_ = !lean_is_exclusive(v_a_252_);
if (v_isSharedCheck_277_ == 0)
{
v___x_260_ = v_a_252_;
v_isShared_261_ = v_isSharedCheck_277_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_buildTime_258_);
lean_inc(v_trace_257_);
lean_inc(v_log_254_);
lean_dec(v_a_252_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_277_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; uint64_t v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
lean_inc(v_a_250_);
v___x_262_ = lean_apply_1(v_inst_249_, v_a_250_);
v___x_263_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_264_ = ((lean_object*)(l_Lake_addPureTrace___redArg___closed__0));
v___x_265_ = lean_string_append(v_caption_251_, v___x_264_);
v___x_266_ = lean_apply_1(v_inst_248_, v_a_250_);
v___x_267_ = lean_string_append(v___x_265_, v___x_266_);
lean_dec_ref(v___x_266_);
v___x_268_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_269_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_269_, 0, v___x_267_);
lean_ctor_set(v___x_269_, 1, v___x_263_);
lean_ctor_set(v___x_269_, 2, v___x_268_);
v___x_270_ = lean_unbox_uint64(v___x_262_);
lean_dec_ref(v___x_262_);
lean_ctor_set_uint64(v___x_269_, sizeof(void*)*3, v___x_270_);
v___x_271_ = lean_box(0);
v___x_272_ = l_Lake_BuildTrace_mix(v_trace_257_, v___x_269_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 1, v___x_272_);
v___x_274_ = v___x_260_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_log_254_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_276_, 2, v_buildTime_258_);
lean_ctor_set_uint8(v_reuseFailAlloc_276_, sizeof(void*)*3, v_action_255_);
lean_ctor_set_uint8(v_reuseFailAlloc_276_, sizeof(void*)*3 + 1, v_wantsRebuild_256_);
v___x_274_ = v_reuseFailAlloc_276_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_275_; 
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_271_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
return v___x_275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg___boxed(lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_a_280_, lean_object* v_caption_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lake_addPureTrace___redArg(v_inst_278_, v_inst_279_, v_a_280_, v_caption_281_, v_a_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace(lean_object* v_00_u03b1_285_, lean_object* v_inst_286_, lean_object* v_inst_287_, lean_object* v_a_288_, lean_object* v_caption_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v_log_297_; uint8_t v_action_298_; uint8_t v_wantsRebuild_299_; lean_object* v_trace_300_; lean_object* v_buildTime_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_320_; 
v_log_297_ = lean_ctor_get(v_a_295_, 0);
v_action_298_ = lean_ctor_get_uint8(v_a_295_, sizeof(void*)*3);
v_wantsRebuild_299_ = lean_ctor_get_uint8(v_a_295_, sizeof(void*)*3 + 1);
v_trace_300_ = lean_ctor_get(v_a_295_, 1);
v_buildTime_301_ = lean_ctor_get(v_a_295_, 2);
v_isSharedCheck_320_ = !lean_is_exclusive(v_a_295_);
if (v_isSharedCheck_320_ == 0)
{
v___x_303_ = v_a_295_;
v_isShared_304_ = v_isSharedCheck_320_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_buildTime_301_);
lean_inc(v_trace_300_);
lean_inc(v_log_297_);
lean_dec(v_a_295_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_320_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; uint64_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
lean_inc(v_a_288_);
v___x_305_ = lean_apply_1(v_inst_287_, v_a_288_);
v___x_306_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_307_ = ((lean_object*)(l_Lake_addPureTrace___redArg___closed__0));
v___x_308_ = lean_string_append(v_caption_289_, v___x_307_);
v___x_309_ = lean_apply_1(v_inst_286_, v_a_288_);
v___x_310_ = lean_string_append(v___x_308_, v___x_309_);
lean_dec_ref(v___x_309_);
v___x_311_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_312_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set(v___x_312_, 1, v___x_306_);
lean_ctor_set(v___x_312_, 2, v___x_311_);
v___x_313_ = lean_unbox_uint64(v___x_305_);
lean_dec_ref(v___x_305_);
lean_ctor_set_uint64(v___x_312_, sizeof(void*)*3, v___x_313_);
v___x_314_ = lean_box(0);
v___x_315_ = l_Lake_BuildTrace_mix(v_trace_300_, v___x_312_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v___x_315_);
v___x_317_ = v___x_303_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_log_297_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v___x_315_);
lean_ctor_set(v_reuseFailAlloc_319_, 2, v_buildTime_301_);
lean_ctor_set_uint8(v_reuseFailAlloc_319_, sizeof(void*)*3, v_action_298_);
lean_ctor_set_uint8(v_reuseFailAlloc_319_, sizeof(void*)*3 + 1, v_wantsRebuild_299_);
v___x_317_ = v_reuseFailAlloc_319_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
lean_object* v___x_318_; 
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_314_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
return v___x_318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace___boxed(lean_object* v_00_u03b1_321_, lean_object* v_inst_322_, lean_object* v_inst_323_, lean_object* v_a_324_, lean_object* v_caption_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lake_addPureTrace(v_00_u03b1_321_, v_inst_322_, v_inst_323_, v_a_324_, v_caption_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec(v_a_328_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(lean_object* v_x_336_){
_start:
{
if (lean_obj_tag(v_x_336_) == 0)
{
lean_object* v___x_337_; 
v___x_337_ = lean_box(0);
return v___x_337_;
}
else
{
lean_object* v_val_338_; 
v_val_338_ = lean_ctor_get(v_x_336_, 0);
lean_inc(v_val_338_);
return v_val_338_;
}
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1___boxed(lean_object* v_x_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(v_x_339_);
lean_dec(v_x_339_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0(lean_object* v_x_341_){
_start:
{
lean_object* v_fst_342_; lean_object* v_snd_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_fst_342_ = lean_ctor_get(v_x_341_, 0);
lean_inc(v_fst_342_);
v_snd_343_ = lean_ctor_get(v_x_341_, 1);
lean_inc(v_snd_343_);
lean_dec_ref(v_x_341_);
v___x_344_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_344_, 0, v_fst_342_);
v___x_345_ = lean_unsigned_to_nat(2u);
v___x_346_ = lean_mk_empty_array_with_capacity(v___x_345_);
v___x_347_ = lean_array_push(v___x_346_, v___x_344_);
v___x_348_ = lean_array_push(v___x_347_, v_snd_343_);
v___x_349_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(size_t v_sz_350_, size_t v_i_351_, lean_object* v_bs_352_){
_start:
{
uint8_t v___x_353_; 
v___x_353_ = lean_usize_dec_lt(v_i_351_, v_sz_350_);
if (v___x_353_ == 0)
{
return v_bs_352_;
}
else
{
lean_object* v_v_354_; lean_object* v___x_355_; lean_object* v_bs_x27_356_; lean_object* v___x_357_; size_t v___x_358_; size_t v___x_359_; lean_object* v___x_360_; 
v_v_354_ = lean_array_uget(v_bs_352_, v_i_351_);
v___x_355_ = lean_unsigned_to_nat(0u);
v_bs_x27_356_ = lean_array_uset(v_bs_352_, v_i_351_, v___x_355_);
v___x_357_ = l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0(v_v_354_);
v___x_358_ = ((size_t)1ULL);
v___x_359_ = lean_usize_add(v_i_351_, v___x_358_);
v___x_360_ = lean_array_uset(v_bs_x27_356_, v_i_351_, v___x_357_);
v_i_351_ = v___x_359_;
v_bs_352_ = v___x_360_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1___boxed(lean_object* v_sz_362_, lean_object* v_i_363_, lean_object* v_bs_364_){
_start:
{
size_t v_sz_boxed_365_; size_t v_i_boxed_366_; lean_object* v_res_367_; 
v_sz_boxed_365_ = lean_unbox_usize(v_sz_362_);
lean_dec(v_sz_362_);
v_i_boxed_366_ = lean_unbox_usize(v_i_363_);
lean_dec(v_i_363_);
v_res_367_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(v_sz_boxed_365_, v_i_boxed_366_, v_bs_364_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(lean_object* v_a_368_){
_start:
{
size_t v_sz_369_; size_t v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_sz_369_ = lean_array_size(v_a_368_);
v___x_370_ = ((size_t)0ULL);
v___x_371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(v_sz_369_, v___x_370_, v_a_368_);
v___x_372_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(size_t v_sz_373_, size_t v_i_374_, lean_object* v_bs_375_){
_start:
{
uint8_t v___x_376_; 
v___x_376_ = lean_usize_dec_lt(v_i_374_, v_sz_373_);
if (v___x_376_ == 0)
{
return v_bs_375_;
}
else
{
lean_object* v_v_377_; lean_object* v___x_378_; lean_object* v_bs_x27_379_; lean_object* v___x_380_; size_t v___x_381_; size_t v___x_382_; lean_object* v___x_383_; 
v_v_377_ = lean_array_uget(v_bs_375_, v_i_374_);
v___x_378_ = lean_unsigned_to_nat(0u);
v_bs_x27_379_ = lean_array_uset(v_bs_375_, v_i_374_, v___x_378_);
v___x_380_ = l_Lake_instToJsonLogEntry_toJson(v_v_377_);
lean_dec(v_v_377_);
v___x_381_ = ((size_t)1ULL);
v___x_382_ = lean_usize_add(v_i_374_, v___x_381_);
v___x_383_ = lean_array_uset(v_bs_x27_379_, v_i_374_, v___x_380_);
v_i_374_ = v___x_382_;
v_bs_375_ = v___x_383_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4___boxed(lean_object* v_sz_385_, lean_object* v_i_386_, lean_object* v_bs_387_){
_start:
{
size_t v_sz_boxed_388_; size_t v_i_boxed_389_; lean_object* v_res_390_; 
v_sz_boxed_388_ = lean_unbox_usize(v_sz_385_);
lean_dec(v_sz_385_);
v_i_boxed_389_ = lean_unbox_usize(v_i_386_);
lean_dec(v_i_386_);
v_res_390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(v_sz_boxed_388_, v_i_boxed_389_, v_bs_387_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2(lean_object* v_a_391_){
_start:
{
size_t v_sz_392_; size_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v_sz_392_ = lean_array_size(v_a_391_);
v___x_393_ = ((size_t)0ULL);
v___x_394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(v_sz_392_, v___x_393_, v_a_391_);
v___x_395_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
return v___x_395_;
}
}
static lean_object* _init_l_Lake_BuildMetadata_toJson___closed__2(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_399_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__1));
v___x_400_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__0));
v___x_401_ = lean_box(1);
v___x_402_ = l_Lake_JsonObject_insertJson(v___x_401_, v___x_400_, v___x_399_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_toJson(lean_object* v_self_408_){
_start:
{
uint64_t v_depHash_409_; lean_object* v_inputs_410_; lean_object* v_outputs_x3f_411_; lean_object* v_log_412_; uint8_t v_synthetic_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v_depHash_409_ = lean_ctor_get_uint64(v_self_408_, sizeof(void*)*3);
v_inputs_410_ = lean_ctor_get(v_self_408_, 0);
lean_inc_ref(v_inputs_410_);
v_outputs_x3f_411_ = lean_ctor_get(v_self_408_, 1);
lean_inc(v_outputs_x3f_411_);
v_log_412_ = lean_ctor_get(v_self_408_, 2);
lean_inc_ref(v_log_412_);
v_synthetic_413_ = lean_ctor_get_uint8(v_self_408_, sizeof(void*)*3 + 8);
lean_dec_ref(v_self_408_);
v___x_414_ = lean_obj_once(&l_Lake_BuildMetadata_toJson___closed__2, &l_Lake_BuildMetadata_toJson___closed__2_once, _init_l_Lake_BuildMetadata_toJson___closed__2);
v___x_415_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__3));
v___x_416_ = l_Lake_Hash_hex(v_depHash_409_);
v___x_417_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
v___x_418_ = l_Lake_JsonObject_insertJson(v___x_414_, v___x_415_, v___x_417_);
v___x_419_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__4));
v___x_420_ = l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(v_inputs_410_);
v___x_421_ = l_Lake_JsonObject_insertJson(v___x_418_, v___x_419_, v___x_420_);
v___x_422_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__5));
v___x_423_ = l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(v_outputs_x3f_411_);
lean_dec(v_outputs_x3f_411_);
v___x_424_ = l_Lake_JsonObject_insertJson(v___x_421_, v___x_422_, v___x_423_);
v___x_425_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__6));
v___x_426_ = l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2(v_log_412_);
v___x_427_ = l_Lake_JsonObject_insertJson(v___x_424_, v___x_425_, v___x_426_);
v___x_428_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__7));
v___x_429_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_429_, 0, v_synthetic_413_);
v___x_430_ = l_Lake_JsonObject_insertJson(v___x_427_, v___x_428_, v___x_429_);
v___x_431_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub(uint64_t v_hash_436_){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; lean_object* v___x_440_; 
v___x_437_ = ((lean_object*)(l_Lake_BuildMetadata_ofStub___closed__0));
v___x_438_ = lean_box(0);
v___x_439_ = 0;
v___x_440_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_440_, 0, v___x_437_);
lean_ctor_set(v___x_440_, 1, v___x_438_);
lean_ctor_set(v___x_440_, 2, v___x_437_);
lean_ctor_set_uint64(v___x_440_, sizeof(void*)*3, v_hash_436_);
lean_ctor_set_uint8(v___x_440_, sizeof(void*)*3 + 8, v___x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub___boxed(lean_object* v_hash_441_){
_start:
{
uint64_t v_hash_boxed_442_; lean_object* v_res_443_; 
v_hash_boxed_442_ = lean_unbox_uint64(v_hash_441_);
lean_dec_ref(v_hash_441_);
v_res_443_ = l_Lake_BuildMetadata_ofStub(v_hash_boxed_442_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(lean_object* v_x_446_){
_start:
{
if (lean_obj_tag(v_x_446_) == 0)
{
lean_object* v___x_447_; 
v___x_447_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0));
return v___x_447_;
}
else
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_Json_getBool_x3f(v_x_446_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_465_; 
v_a_457_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_465_ == 0)
{
v___x_459_ = v___x_448_;
v_isShared_460_ = v_isSharedCheck_465_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_448_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_465_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_461_, 0, v_a_457_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v___x_461_);
v___x_463_ = v___x_459_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___boxed(lean_object* v_x_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(v_x_466_);
lean_dec(v_x_466_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3(lean_object* v_x_470_){
_start:
{
if (lean_obj_tag(v_x_470_) == 0)
{
lean_object* v___x_471_; 
v___x_471_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0));
return v___x_471_;
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v_x_470_);
v___x_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2(lean_object* v_x_476_){
_start:
{
if (lean_obj_tag(v_x_476_) == 0)
{
lean_object* v___x_477_; 
v___x_477_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0));
return v___x_477_;
}
else
{
lean_object* v___x_478_; lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_487_; 
v___x_478_ = l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3(v_x_476_);
v_a_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_487_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_487_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_487_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_483_, 0, v_a_479_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_483_);
v___x_485_ = v___x_481_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(size_t v_sz_488_, size_t v_i_489_, lean_object* v_bs_490_){
_start:
{
uint8_t v___x_491_; 
v___x_491_ = lean_usize_dec_lt(v_i_489_, v_sz_488_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; 
v___x_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_492_, 0, v_bs_490_);
return v___x_492_;
}
else
{
lean_object* v_v_493_; lean_object* v___x_494_; 
v_v_493_ = lean_array_uget_borrowed(v_bs_490_, v_i_489_);
lean_inc(v_v_493_);
v___x_494_ = l_Lake_instFromJsonLogEntry_fromJson(v_v_493_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
lean_dec_ref(v_bs_490_);
v_a_495_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_494_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_494_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
else
{
lean_object* v_a_503_; lean_object* v___x_504_; lean_object* v_bs_x27_505_; size_t v___x_506_; size_t v___x_507_; lean_object* v___x_508_; 
v_a_503_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_a_503_);
lean_dec_ref(v___x_494_);
v___x_504_ = lean_unsigned_to_nat(0u);
v_bs_x27_505_ = lean_array_uset(v_bs_490_, v_i_489_, v___x_504_);
v___x_506_ = ((size_t)1ULL);
v___x_507_ = lean_usize_add(v_i_489_, v___x_506_);
v___x_508_ = lean_array_uset(v_bs_x27_505_, v_i_489_, v_a_503_);
v_i_489_ = v___x_507_;
v_bs_490_ = v___x_508_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_510_, lean_object* v_i_511_, lean_object* v_bs_512_){
_start:
{
size_t v_sz_boxed_513_; size_t v_i_boxed_514_; lean_object* v_res_515_; 
v_sz_boxed_513_ = lean_unbox_usize(v_sz_510_);
lean_dec(v_sz_510_);
v_i_boxed_514_ = lean_unbox_usize(v_i_511_);
lean_dec(v_i_511_);
v_res_515_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(v_sz_boxed_513_, v_i_boxed_514_, v_bs_512_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(lean_object* v_x_518_){
_start:
{
if (lean_obj_tag(v_x_518_) == 4)
{
lean_object* v_elems_519_; size_t v_sz_520_; size_t v___x_521_; lean_object* v___x_522_; 
v_elems_519_ = lean_ctor_get(v_x_518_, 0);
lean_inc_ref(v_elems_519_);
lean_dec_ref(v_x_518_);
v_sz_520_ = lean_array_size(v_elems_519_);
v___x_521_ = ((size_t)0ULL);
v___x_522_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(v_sz_520_, v___x_521_, v_elems_519_);
return v___x_522_;
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_523_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0));
v___x_524_ = lean_unsigned_to_nat(80u);
v___x_525_ = l_Lean_Json_pretty(v_x_518_, v___x_524_);
v___x_526_ = lean_string_append(v___x_523_, v___x_525_);
lean_dec_ref(v___x_525_);
v___x_527_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1));
v___x_528_ = lean_string_append(v___x_526_, v___x_527_);
v___x_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
return v___x_529_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1(lean_object* v_x_532_){
_start:
{
if (lean_obj_tag(v_x_532_) == 0)
{
lean_object* v___x_533_; 
v___x_533_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0));
return v___x_533_;
}
else
{
lean_object* v___x_534_; 
v___x_534_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(v_x_532_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_534_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_534_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
else
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_551_; 
v_a_543_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_551_ == 0)
{
v___x_545_ = v___x_534_;
v_isShared_546_ = v_isSharedCheck_551_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_534_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_551_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_547_, 0, v_a_543_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_547_);
v___x_549_ = v___x_545_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7(lean_object* v_x_553_){
_start:
{
lean_object* v_j_555_; 
if (lean_obj_tag(v_x_553_) == 4)
{
lean_object* v_elems_563_; lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v_elems_563_ = lean_ctor_get(v_x_553_, 0);
v___x_564_ = lean_array_get_size(v_elems_563_);
v___x_565_ = lean_unsigned_to_nat(2u);
v___x_566_ = lean_nat_dec_eq(v___x_564_, v___x_565_);
if (v___x_566_ == 0)
{
v_j_555_ = v_x_553_;
goto v___jp_554_;
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
lean_inc_ref(v_elems_563_);
lean_dec_ref(v_x_553_);
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_array_fget_borrowed(v_elems_563_, v___x_567_);
lean_inc(v___x_568_);
v___x_569_ = l_Lean_Json_getStr_x3f(v___x_568_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
lean_dec_ref(v_elems_563_);
v_a_570_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_569_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_569_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_588_; 
v_a_578_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_588_ == 0)
{
v___x_580_ = v___x_569_;
v_isShared_581_ = v_isSharedCheck_588_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_569_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_588_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_582_ = lean_unsigned_to_nat(1u);
v___x_583_ = lean_array_fget(v_elems_563_, v___x_582_);
lean_dec_ref(v_elems_563_);
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v_a_578_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v___x_584_);
v___x_586_ = v___x_580_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
else
{
v_j_555_ = v_x_553_;
goto v___jp_554_;
}
v___jp_554_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_556_ = ((lean_object*)(l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0));
v___x_557_ = lean_unsigned_to_nat(80u);
v___x_558_ = l_Lean_Json_pretty(v_j_555_, v___x_557_);
v___x_559_ = lean_string_append(v___x_556_, v___x_558_);
lean_dec_ref(v___x_558_);
v___x_560_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1));
v___x_561_ = lean_string_append(v___x_559_, v___x_560_);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(size_t v_sz_589_, size_t v_i_590_, lean_object* v_bs_591_){
_start:
{
uint8_t v___x_592_; 
v___x_592_ = lean_usize_dec_lt(v_i_590_, v_sz_589_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; 
v___x_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_593_, 0, v_bs_591_);
return v___x_593_;
}
else
{
lean_object* v_v_594_; lean_object* v___x_595_; 
v_v_594_ = lean_array_uget_borrowed(v_bs_591_, v_i_590_);
lean_inc(v_v_594_);
v___x_595_ = l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7(v_v_594_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec_ref(v_bs_591_);
v_a_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_605_; lean_object* v_bs_x27_606_; size_t v___x_607_; size_t v___x_608_; lean_object* v___x_609_; 
v_a_604_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_604_);
lean_dec_ref(v___x_595_);
v___x_605_ = lean_unsigned_to_nat(0u);
v_bs_x27_606_ = lean_array_uset(v_bs_591_, v_i_590_, v___x_605_);
v___x_607_ = ((size_t)1ULL);
v___x_608_ = lean_usize_add(v_i_590_, v___x_607_);
v___x_609_ = lean_array_uset(v_bs_x27_606_, v_i_590_, v_a_604_);
v_i_590_ = v___x_608_;
v_bs_591_ = v___x_609_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8___boxed(lean_object* v_sz_611_, lean_object* v_i_612_, lean_object* v_bs_613_){
_start:
{
size_t v_sz_boxed_614_; size_t v_i_boxed_615_; lean_object* v_res_616_; 
v_sz_boxed_614_ = lean_unbox_usize(v_sz_611_);
lean_dec(v_sz_611_);
v_i_boxed_615_ = lean_unbox_usize(v_i_612_);
lean_dec(v_i_612_);
v_res_616_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(v_sz_boxed_614_, v_i_boxed_615_, v_bs_613_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5(lean_object* v_x_617_){
_start:
{
if (lean_obj_tag(v_x_617_) == 4)
{
lean_object* v_elems_618_; size_t v_sz_619_; size_t v___x_620_; lean_object* v___x_621_; 
v_elems_618_ = lean_ctor_get(v_x_617_, 0);
lean_inc_ref(v_elems_618_);
lean_dec_ref(v_x_617_);
v_sz_619_ = lean_array_size(v_elems_618_);
v___x_620_ = ((size_t)0ULL);
v___x_621_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(v_sz_619_, v___x_620_, v_elems_618_);
return v___x_621_;
}
else
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_622_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0));
v___x_623_ = lean_unsigned_to_nat(80u);
v___x_624_ = l_Lean_Json_pretty(v_x_617_, v___x_623_);
v___x_625_ = lean_string_append(v___x_622_, v___x_624_);
lean_dec_ref(v___x_624_);
v___x_626_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1));
v___x_627_ = lean_string_append(v___x_625_, v___x_626_);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3(lean_object* v_x_631_){
_start:
{
if (lean_obj_tag(v_x_631_) == 0)
{
lean_object* v___x_632_; 
v___x_632_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0));
return v___x_632_;
}
else
{
lean_object* v___x_633_; 
v___x_633_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5(v_x_631_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_650_; 
v_a_642_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_650_ == 0)
{
v___x_644_ = v___x_633_;
v_isShared_645_ = v_isSharedCheck_650_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_633_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_650_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_646_, 0, v_a_642_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v___x_646_);
v___x_648_ = v___x_644_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f(lean_object* v_obj_666_){
_start:
{
lean_object* v___y_668_; uint64_t v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; uint8_t v_a_672_; lean_object* v___y_676_; uint64_t v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; uint64_t v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v_a_685_; uint64_t v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; uint64_t v___y_717_; lean_object* v___y_718_; lean_object* v_a_719_; uint64_t v___y_745_; lean_object* v___y_746_; uint64_t v___y_749_; lean_object* v_a_750_; uint64_t v___y_776_; uint64_t v_depHash_779_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__0));
v___x_805_ = l_Lake_JsonObject_getJson_x3f(v_obj_666_, v___x_804_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__3));
v___x_807_ = l_Lake_JsonObject_getJson_x3f(v_obj_666_, v___x_806_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v___x_808_; 
v___x_808_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7));
return v___x_808_;
}
else
{
lean_object* v_val_809_; lean_object* v___x_810_; 
v_val_809_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_val_809_);
lean_dec_ref(v___x_807_);
v___x_810_ = l_Lean_Json_getStr_x3f(v_val_809_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_820_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_820_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_820_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_820_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_815_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8));
v___x_816_ = lean_string_append(v___x_815_, v_a_811_);
lean_dec(v_a_811_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_816_);
v___x_818_ = v___x_813_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
else
{
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
v_a_821_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_810_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_810_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
lean_ctor_set_tag(v___x_823_, 0);
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_830_; 
v_a_829_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_a_829_);
lean_dec_ref(v___x_810_);
v___x_830_ = l_Lake_Hash_ofDecimal_x3f(v_a_829_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v___x_831_; 
v___x_831_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__10));
return v___x_831_;
}
else
{
lean_object* v_val_832_; uint64_t v___x_833_; 
v_val_832_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_val_832_);
lean_dec_ref(v___x_830_);
v___x_833_ = lean_unbox_uint64(v_val_832_);
lean_dec(v_val_832_);
v_depHash_779_ = v___x_833_;
goto v___jp_778_;
}
}
}
}
}
else
{
lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec_ref(v___x_805_);
v___x_834_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__3));
v___x_835_ = l_Lake_JsonObject_getJson_x3f(v_obj_666_, v___x_834_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v___x_836_; 
v___x_836_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7));
return v___x_836_;
}
else
{
lean_object* v_val_837_; lean_object* v___x_838_; 
v_val_837_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_val_837_);
lean_dec_ref(v___x_835_);
v___x_838_ = l_Lake_Hash_fromJson_x3f(v_val_837_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_848_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_848_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_848_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_848_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_843_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8));
v___x_844_ = lean_string_append(v___x_843_, v_a_839_);
lean_dec(v_a_839_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_844_);
v___x_846_ = v___x_841_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
else
{
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
v_a_849_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_838_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_838_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
lean_ctor_set_tag(v___x_851_, 0);
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
else
{
lean_object* v_a_857_; uint64_t v___x_858_; 
v_a_857_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_857_);
lean_dec_ref(v___x_838_);
v___x_858_ = lean_unbox_uint64(v_a_857_);
lean_dec(v_a_857_);
v_depHash_779_ = v___x_858_;
goto v___jp_778_;
}
}
}
}
v___jp_667_:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_673_, 0, v___y_671_);
lean_ctor_set(v___x_673_, 1, v___y_670_);
lean_ctor_set(v___x_673_, 2, v___y_668_);
lean_ctor_set_uint64(v___x_673_, sizeof(void*)*3, v___y_669_);
lean_ctor_set_uint8(v___x_673_, sizeof(void*)*3 + 8, v_a_672_);
v___x_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
return v___x_674_;
}
v___jp_675_:
{
uint8_t v___x_680_; 
v___x_680_ = 0;
v___y_668_ = v___y_676_;
v___y_669_ = v___y_677_;
v___y_670_ = v___y_679_;
v___y_671_ = v___y_678_;
v_a_672_ = v___x_680_;
goto v___jp_667_;
}
v___jp_681_:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__7));
v___x_687_ = l_Lake_JsonObject_getJson_x3f(v_obj_666_, v___x_686_);
if (lean_obj_tag(v___x_687_) == 0)
{
v___y_676_ = v_a_685_;
v___y_677_ = v___y_682_;
v___y_678_ = v___y_683_;
v___y_679_ = v___y_684_;
goto v___jp_675_;
}
else
{
lean_object* v_val_688_; lean_object* v___x_689_; 
v_val_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_val_688_);
lean_dec_ref(v___x_687_);
v___x_689_ = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(v_val_688_);
lean_dec(v_val_688_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_699_; 
lean_dec_ref(v_a_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_699_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_699_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_699_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_694_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__0));
v___x_695_ = lean_string_append(v___x_694_, v_a_690_);
lean_dec(v_a_690_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_695_);
v___x_697_ = v___x_692_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
else
{
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec_ref(v_a_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
v_a_700_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_689_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_689_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set_tag(v___x_702_, 0);
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
else
{
lean_object* v_a_708_; 
v_a_708_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_a_708_);
lean_dec_ref(v___x_689_);
if (lean_obj_tag(v_a_708_) == 0)
{
v___y_676_ = v_a_685_;
v___y_677_ = v___y_682_;
v___y_678_ = v___y_683_;
v___y_679_ = v___y_684_;
goto v___jp_675_;
}
else
{
lean_object* v_val_709_; uint8_t v___x_710_; 
v_val_709_ = lean_ctor_get(v_a_708_, 0);
lean_inc(v_val_709_);
lean_dec_ref(v_a_708_);
v___x_710_ = lean_unbox(v_val_709_);
lean_dec(v_val_709_);
v___y_668_ = v_a_685_;
v___y_669_ = v___y_682_;
v___y_670_ = v___y_684_;
v___y_671_ = v___y_683_;
v_a_672_ = v___x_710_;
goto v___jp_667_;
}
}
}
}
}
v___jp_711_:
{
lean_object* v___x_715_; 
v___x_715_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___y_682_ = v___y_712_;
v___y_683_ = v___y_714_;
v___y_684_ = v___y_713_;
v_a_685_ = v___x_715_;
goto v___jp_681_;
}
v___jp_716_:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__6));
v___x_721_ = l_Lake_JsonObject_getJson_x3f(v_obj_666_, v___x_720_);
if (lean_obj_tag(v___x_721_) == 0)
{
v___y_712_ = v___y_717_;
v___y_713_ = v_a_719_;
v___y_714_ = v___y_718_;
goto v___jp_711_;
}
else
{
lean_object* v_val_722_; lean_object* v___x_723_; 
v_val_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_val_722_);
lean_dec_ref(v___x_721_);
v___x_723_ = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1(v_val_722_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_733_; 
lean_dec(v_a_719_);
lean_dec_ref(v___y_718_);
v_a_724_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_733_ == 0)
{
v___x_726_ = v___x_723_;
v_isShared_727_ = v_isSharedCheck_733_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_723_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_733_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_728_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2));
v___x_729_ = lean_string_append(v___x_728_, v_a_724_);
lean_dec(v_a_724_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v___x_729_);
v___x_731_ = v___x_726_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
else
{
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec(v_a_719_);
lean_dec_ref(v___y_718_);
v_a_734_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_723_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_723_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set_tag(v___x_736_, 0);
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
else
{
lean_object* v_a_742_; 
v_a_742_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_742_);
lean_dec_ref(v___x_723_);
if (lean_obj_tag(v_a_742_) == 0)
{
v___y_712_ = v___y_717_;
v___y_713_ = v_a_719_;
v___y_714_ = v___y_718_;
goto v___jp_711_;
}
else
{
lean_object* v_val_743_; 
v_val_743_ = lean_ctor_get(v_a_742_, 0);
lean_inc(v_val_743_);
lean_dec_ref(v_a_742_);
v___y_682_ = v___y_717_;
v___y_683_ = v___y_718_;
v___y_684_ = v_a_719_;
v_a_685_ = v_val_743_;
goto v___jp_681_;
}
}
}
}
}
v___jp_744_:
{
lean_object* v___x_747_; 
v___x_747_ = lean_box(0);
v___y_717_ = v___y_745_;
v___y_718_ = v___y_746_;
v_a_719_ = v___x_747_;
goto v___jp_716_;
}
v___jp_748_:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__5));
v___x_752_ = l_Lake_JsonObject_getJson_x3f(v_obj_666_, v___x_751_);
if (lean_obj_tag(v___x_752_) == 0)
{
v___y_745_ = v___y_749_;
v___y_746_ = v_a_750_;
goto v___jp_744_;
}
else
{
lean_object* v_val_753_; lean_object* v___x_754_; 
v_val_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_val_753_);
lean_dec_ref(v___x_752_);
v___x_754_ = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2(v_val_753_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_764_; 
lean_dec_ref(v_a_750_);
v_a_755_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_764_ == 0)
{
v___x_757_ = v___x_754_;
v_isShared_758_ = v_isSharedCheck_764_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_754_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_764_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_759_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3));
v___x_760_ = lean_string_append(v___x_759_, v_a_755_);
lean_dec(v_a_755_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_760_);
v___x_762_ = v___x_757_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
else
{
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec_ref(v_a_750_);
v_a_765_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_754_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_754_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set_tag(v___x_767_, 0);
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
else
{
lean_object* v_a_773_; 
v_a_773_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_a_773_);
lean_dec_ref(v___x_754_);
if (lean_obj_tag(v_a_773_) == 0)
{
v___y_745_ = v___y_749_;
v___y_746_ = v_a_750_;
goto v___jp_744_;
}
else
{
lean_object* v_val_774_; 
v_val_774_ = lean_ctor_get(v_a_773_, 0);
lean_inc(v_val_774_);
lean_dec_ref(v_a_773_);
v___y_717_ = v___y_749_;
v___y_718_ = v_a_750_;
v_a_719_ = v_val_774_;
goto v___jp_716_;
}
}
}
}
}
v___jp_775_:
{
lean_object* v___x_777_; 
v___x_777_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4));
v___y_749_ = v___y_776_;
v_a_750_ = v___x_777_;
goto v___jp_748_;
}
v___jp_778_:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__4));
v___x_781_ = l_Lake_JsonObject_getJson_x3f(v_obj_666_, v___x_780_);
if (lean_obj_tag(v___x_781_) == 0)
{
v___y_776_ = v_depHash_779_;
goto v___jp_775_;
}
else
{
lean_object* v_val_782_; lean_object* v___x_783_; 
v_val_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_val_782_);
lean_dec_ref(v___x_781_);
v___x_783_ = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3(v_val_782_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_793_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_793_ == 0)
{
v___x_786_ = v___x_783_;
v_isShared_787_ = v_isSharedCheck_793_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_783_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_793_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_788_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5));
v___x_789_ = lean_string_append(v___x_788_, v_a_784_);
lean_dec(v_a_784_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_789_);
v___x_791_ = v___x_786_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
else
{
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
v_a_794_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_783_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_783_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set_tag(v___x_796_, 0);
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
else
{
lean_object* v_a_802_; 
v_a_802_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_802_);
lean_dec_ref(v___x_783_);
if (lean_obj_tag(v_a_802_) == 0)
{
v___y_776_ = v_depHash_779_;
goto v___jp_775_;
}
else
{
lean_object* v_val_803_; 
v_val_803_ = lean_ctor_get(v_a_802_, 0);
lean_inc(v_val_803_);
lean_dec_ref(v_a_802_);
v___y_749_ = v_depHash_779_;
v_a_750_ = v_val_803_;
goto v___jp_748_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___boxed(lean_object* v_obj_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lake_BuildMetadata_fromJsonObject_x3f(v_obj_859_);
lean_dec(v_obj_859_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f(lean_object* v_json_867_){
_start:
{
switch(lean_obj_tag(v_json_867_))
{
case 2:
{
lean_object* v_n_868_; lean_object* v___x_869_; 
v_n_868_ = lean_ctor_get(v_json_867_, 0);
v___x_869_ = l_Lake_Hash_ofJsonNumber_x3f(v_n_868_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_879_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_879_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_879_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_879_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_874_ = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__0));
v___x_875_ = lean_string_append(v___x_874_, v_a_870_);
lean_dec(v_a_870_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_875_);
v___x_877_ = v___x_872_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_889_; 
v_a_880_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_889_ == 0)
{
v___x_882_ = v___x_869_;
v_isShared_883_ = v_isSharedCheck_889_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_869_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_889_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
uint64_t v___x_884_; lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_884_ = lean_unbox_uint64(v_a_880_);
lean_dec(v_a_880_);
v___x_885_ = l_Lake_BuildMetadata_ofStub(v___x_884_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_885_);
v___x_887_ = v___x_882_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
case 5:
{
lean_object* v_kvPairs_890_; lean_object* v___x_891_; 
v_kvPairs_890_ = lean_ctor_get(v_json_867_, 0);
v___x_891_ = l_Lake_BuildMetadata_fromJsonObject_x3f(v_kvPairs_890_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_917_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_917_ == 0)
{
v___x_894_ = v___x_891_;
v_isShared_895_ = v_isSharedCheck_917_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_917_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__0));
v___x_903_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_890_, v___x_902_);
if (lean_obj_tag(v___x_903_) == 1)
{
lean_object* v_val_904_; 
v_val_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_val_904_);
lean_dec_ref(v___x_903_);
if (lean_obj_tag(v_val_904_) == 3)
{
lean_object* v_s_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_916_; 
v_s_905_ = lean_ctor_get(v_val_904_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v_val_904_);
if (v_isSharedCheck_916_ == 0)
{
v___x_907_ = v_val_904_;
v_isShared_908_ = v_isSharedCheck_916_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_s_905_);
lean_dec(v_val_904_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_916_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_909_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0));
v___x_910_ = lean_string_dec_eq(v_s_905_, v___x_909_);
lean_dec_ref(v_s_905_);
if (v___x_910_ == 0)
{
lean_del_object(v___x_907_);
goto v___jp_896_;
}
else
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
lean_del_object(v___x_894_);
v___x_911_ = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__2));
v___x_912_ = lean_string_append(v___x_911_, v_a_892_);
lean_dec(v_a_892_);
if (v_isShared_908_ == 0)
{
lean_ctor_set_tag(v___x_907_, 0);
lean_ctor_set(v___x_907_, 0, v___x_912_);
v___x_914_ = v___x_907_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
else
{
lean_dec(v_val_904_);
goto v___jp_896_;
}
}
else
{
lean_dec(v___x_903_);
goto v___jp_896_;
}
v___jp_896_:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_897_ = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__1));
v___x_898_ = lean_string_append(v___x_897_, v_a_892_);
lean_dec(v_a_892_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v___x_898_);
v___x_900_ = v___x_894_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
else
{
return v___x_891_;
}
}
default: 
{
lean_object* v___x_918_; 
v___x_918_ = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__4));
return v___x_918_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f___boxed(lean_object* v_json_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lake_BuildMetadata_fromJson_x3f(v_json_919_);
lean_dec(v_json_919_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_parse(lean_object* v_contents_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lean_Json_parse(v_contents_923_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_924_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_924_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_934_; 
v_a_933_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_933_);
lean_dec_ref(v___x_924_);
v___x_934_ = l_Lake_BuildMetadata_fromJson_x3f(v_a_933_);
lean_dec(v_a_933_);
return v___x_934_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch(uint64_t v_inputHash_935_, lean_object* v_outputs_936_){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; lean_object* v___x_940_; 
v___x_937_ = ((lean_object*)(l_Lake_BuildMetadata_ofStub___closed__0));
v___x_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_938_, 0, v_outputs_936_);
v___x_939_ = 1;
v___x_940_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_940_, 0, v___x_937_);
lean_ctor_set(v___x_940_, 1, v___x_938_);
lean_ctor_set(v___x_940_, 2, v___x_937_);
lean_ctor_set_uint64(v___x_940_, sizeof(void*)*3, v_inputHash_935_);
lean_ctor_set_uint8(v___x_940_, sizeof(void*)*3 + 8, v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch___boxed(lean_object* v_inputHash_941_, lean_object* v_outputs_942_){
_start:
{
uint64_t v_inputHash_boxed_943_; lean_object* v_res_944_; 
v_inputHash_boxed_943_ = lean_unbox_uint64(v_inputHash_941_);
lean_dec_ref(v_inputHash_941_);
v_res_944_ = l_Lake_BuildMetadata_ofFetch(v_inputHash_boxed_943_, v_outputs_942_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(lean_object* v_as_945_, size_t v_i_946_, size_t v_stop_947_, lean_object* v_b_948_){
_start:
{
uint8_t v___x_949_; 
v___x_949_ = lean_usize_dec_eq(v_i_946_, v_stop_947_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; lean_object* v___y_952_; lean_object* v_inputs_959_; uint64_t v_hash_960_; lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
v___x_950_ = lean_array_uget_borrowed(v_as_945_, v_i_946_);
v_inputs_959_ = lean_ctor_get(v___x_950_, 1);
v_hash_960_ = lean_ctor_get_uint64(v___x_950_, sizeof(void*)*3);
v___x_961_ = lean_array_get_size(v_inputs_959_);
v___x_962_ = lean_unsigned_to_nat(0u);
v___x_963_ = lean_nat_dec_eq(v___x_961_, v___x_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = l___private_Lake_Build_Common_0__Lake_serializeInputs(v_inputs_959_);
v___x_965_ = l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(v___x_964_);
v___y_952_ = v___x_965_;
goto v___jp_951_;
}
else
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = l_Lake_Hash_hex(v_hash_960_);
v___x_967_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
v___y_952_ = v___x_967_;
goto v___jp_951_;
}
v___jp_951_:
{
lean_object* v_caption_953_; lean_object* v___x_954_; lean_object* v___x_955_; size_t v___x_956_; size_t v___x_957_; 
v_caption_953_ = lean_ctor_get(v___x_950_, 0);
lean_inc_ref(v_caption_953_);
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v_caption_953_);
lean_ctor_set(v___x_954_, 1, v___y_952_);
v___x_955_ = lean_array_push(v_b_948_, v___x_954_);
v___x_956_ = ((size_t)1ULL);
v___x_957_ = lean_usize_add(v_i_946_, v___x_956_);
v_i_946_ = v___x_957_;
v_b_948_ = v___x_955_;
goto _start;
}
}
else
{
return v_b_948_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs(lean_object* v_inputs_968_){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; uint8_t v___x_972_; 
v___x_969_ = lean_unsigned_to_nat(0u);
v___x_970_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4));
v___x_971_ = lean_array_get_size(v_inputs_968_);
v___x_972_ = lean_nat_dec_lt(v___x_969_, v___x_971_);
if (v___x_972_ == 0)
{
return v___x_970_;
}
else
{
uint8_t v___x_973_; 
v___x_973_ = lean_nat_dec_le(v___x_971_, v___x_971_);
if (v___x_973_ == 0)
{
if (v___x_972_ == 0)
{
return v___x_970_;
}
else
{
size_t v___x_974_; size_t v___x_975_; lean_object* v___x_976_; 
v___x_974_ = ((size_t)0ULL);
v___x_975_ = lean_usize_of_nat(v___x_971_);
v___x_976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(v_inputs_968_, v___x_974_, v___x_975_, v___x_970_);
return v___x_976_;
}
}
else
{
size_t v___x_977_; size_t v___x_978_; lean_object* v___x_979_; 
v___x_977_ = ((size_t)0ULL);
v___x_978_ = lean_usize_of_nat(v___x_971_);
v___x_979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(v_inputs_968_, v___x_977_, v___x_978_, v___x_970_);
return v___x_979_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs___boxed(lean_object* v_inputs_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l___private_Lake_Build_Common_0__Lake_serializeInputs(v_inputs_980_);
lean_dec_ref(v_inputs_980_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0___boxed(lean_object* v_as_982_, lean_object* v_i_983_, lean_object* v_stop_984_, lean_object* v_b_985_){
_start:
{
size_t v_i_boxed_986_; size_t v_stop_boxed_987_; lean_object* v_res_988_; 
v_i_boxed_986_ = lean_unbox_usize(v_i_983_);
lean_dec(v_i_983_);
v_stop_boxed_987_ = lean_unbox_usize(v_stop_984_);
lean_dec(v_stop_984_);
v_res_988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(v_as_982_, v_i_boxed_986_, v_stop_boxed_987_, v_b_985_);
lean_dec_ref(v_as_982_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(lean_object* v_depTrace_989_, lean_object* v_outputs_990_, lean_object* v_log_991_){
_start:
{
lean_object* v_inputs_992_; uint64_t v_hash_993_; lean_object* v___x_994_; lean_object* v___x_995_; uint8_t v___x_996_; lean_object* v___x_997_; 
v_inputs_992_ = lean_ctor_get(v_depTrace_989_, 1);
v_hash_993_ = lean_ctor_get_uint64(v_depTrace_989_, sizeof(void*)*3);
v___x_994_ = l___private_Lake_Build_Common_0__Lake_serializeInputs(v_inputs_992_);
v___x_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_995_, 0, v_outputs_990_);
v___x_996_ = 0;
v___x_997_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_997_, 0, v___x_994_);
lean_ctor_set(v___x_997_, 1, v___x_995_);
lean_ctor_set(v___x_997_, 2, v_log_991_);
lean_ctor_set_uint64(v___x_997_, sizeof(void*)*3, v_hash_993_);
lean_ctor_set_uint8(v___x_997_, sizeof(void*)*3 + 8, v___x_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore___boxed(lean_object* v_depTrace_998_, lean_object* v_outputs_999_, lean_object* v_log_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_998_, v_outputs_999_, v_log_1000_);
lean_dec_ref(v_depTrace_998_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg(lean_object* v_inst_1002_, lean_object* v_depTrace_1003_, lean_object* v_outputs_1004_, lean_object* v_log_1005_){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = lean_apply_1(v_inst_1002_, v_outputs_1004_);
v___x_1007_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1003_, v___x_1006_, v_log_1005_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg___boxed(lean_object* v_inst_1008_, lean_object* v_depTrace_1009_, lean_object* v_outputs_1010_, lean_object* v_log_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lake_BuildMetadata_ofBuild___redArg(v_inst_1008_, v_depTrace_1009_, v_outputs_1010_, v_log_1011_);
lean_dec_ref(v_depTrace_1009_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild(lean_object* v_00_u03b1_1013_, lean_object* v_inst_1014_, lean_object* v_depTrace_1015_, lean_object* v_outputs_1016_, lean_object* v_log_1017_){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_apply_1(v_inst_1014_, v_outputs_1016_);
v___x_1019_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1015_, v___x_1018_, v_log_1017_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___boxed(lean_object* v_00_u03b1_1020_, lean_object* v_inst_1021_, lean_object* v_depTrace_1022_, lean_object* v_outputs_1023_, lean_object* v_log_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lake_BuildMetadata_ofBuild(v_00_u03b1_1020_, v_inst_1021_, v_depTrace_1022_, v_outputs_1023_, v_log_1024_);
lean_dec_ref(v_depTrace_1022_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorIdx(lean_object* v_x_1026_){
_start:
{
switch(lean_obj_tag(v_x_1026_))
{
case 0:
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_unsigned_to_nat(0u);
return v___x_1027_;
}
case 1:
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_unsigned_to_nat(1u);
return v___x_1028_;
}
default: 
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_unsigned_to_nat(2u);
return v___x_1029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorIdx___boxed(lean_object* v_x_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lake_SavedTrace_ctorIdx(v_x_1030_);
lean_dec(v_x_1030_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim___redArg(lean_object* v_t_1032_, lean_object* v_k_1033_){
_start:
{
if (lean_obj_tag(v_t_1032_) == 2)
{
lean_object* v_data_1034_; lean_object* v___x_1035_; 
v_data_1034_ = lean_ctor_get(v_t_1032_, 0);
lean_inc_ref(v_data_1034_);
lean_dec_ref(v_t_1032_);
v___x_1035_ = lean_apply_1(v_k_1033_, v_data_1034_);
return v___x_1035_;
}
else
{
lean_dec(v_t_1032_);
return v_k_1033_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim(lean_object* v_motive_1036_, lean_object* v_ctorIdx_1037_, lean_object* v_t_1038_, lean_object* v_h_1039_, lean_object* v_k_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1038_, v_k_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim___boxed(lean_object* v_motive_1042_, lean_object* v_ctorIdx_1043_, lean_object* v_t_1044_, lean_object* v_h_1045_, lean_object* v_k_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lake_SavedTrace_ctorElim(v_motive_1042_, v_ctorIdx_1043_, v_t_1044_, v_h_1045_, v_k_1046_);
lean_dec(v_ctorIdx_1043_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_missing_elim___redArg(lean_object* v_t_1048_, lean_object* v_missing_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1048_, v_missing_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_missing_elim(lean_object* v_motive_1051_, lean_object* v_t_1052_, lean_object* v_h_1053_, lean_object* v_missing_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1052_, v_missing_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_invalid_elim___redArg(lean_object* v_t_1056_, lean_object* v_invalid_1057_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1056_, v_invalid_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_invalid_elim(lean_object* v_motive_1059_, lean_object* v_t_1060_, lean_object* v_h_1061_, lean_object* v_invalid_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1060_, v_invalid_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ok_elim___redArg(lean_object* v_t_1064_, lean_object* v_ok_1065_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1064_, v_ok_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ok_elim(lean_object* v_motive_1067_, lean_object* v_t_1068_, lean_object* v_h_1069_, lean_object* v_ok_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1068_, v_ok_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lake_readTraceFile(lean_object* v_path_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_IO_FS_readFile(v_path_1073_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v_a_1079_; lean_object* v___x_1088_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref(v___x_1076_);
v___x_1088_ = l_Lean_Json_parse(v_a_1077_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref(v___x_1088_);
v_a_1079_ = v_a_1089_;
goto v___jp_1078_;
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1091_; 
v_a_1090_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1090_);
lean_dec_ref(v___x_1088_);
v___x_1091_ = l_Lake_BuildMetadata_fromJson_x3f(v_a_1090_);
lean_dec(v_a_1090_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref(v___x_1091_);
v_a_1079_ = v_a_1092_;
goto v___jp_1078_;
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1101_; 
lean_dec_ref(v_path_1073_);
v_a_1093_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1095_ = v___x_1091_;
v_isShared_1096_ = v_isSharedCheck_1101_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1091_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1101_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set_tag(v___x_1095_, 2);
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set(v___x_1099_, 1, v_a_1074_);
return v___x_1099_;
}
}
}
}
v___jp_1078_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1080_ = ((lean_object*)(l_Lake_addPureTrace___redArg___closed__0));
v___x_1081_ = lean_string_append(v_path_1073_, v___x_1080_);
v___x_1082_ = lean_string_append(v___x_1081_, v_a_1079_);
lean_dec_ref(v_a_1079_);
v___x_1083_ = 2;
v___x_1084_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1084_, 0, v___x_1082_);
lean_ctor_set_uint8(v___x_1084_, sizeof(void*)*1, v___x_1083_);
v___x_1085_ = lean_array_push(v_a_1074_, v___x_1084_);
v___x_1086_ = lean_box(1);
v___x_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
lean_ctor_set(v___x_1087_, 1, v___x_1085_);
return v___x_1087_;
}
}
else
{
lean_object* v_a_1102_; 
v_a_1102_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1102_);
lean_dec_ref(v___x_1076_);
if (lean_obj_tag(v_a_1102_) == 11)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_dec_ref(v_a_1102_);
lean_dec_ref(v_path_1073_);
v___x_1103_ = lean_box(0);
v___x_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
lean_ctor_set(v___x_1104_, 1, v_a_1074_);
return v___x_1104_;
}
else
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1105_ = ((lean_object*)(l_Lake_readTraceFile___closed__0));
v___x_1106_ = lean_string_append(v_path_1073_, v___x_1105_);
v___x_1107_ = lean_io_error_to_string(v_a_1102_);
v___x_1108_ = lean_string_append(v___x_1106_, v___x_1107_);
lean_dec_ref(v___x_1107_);
v___x_1109_ = 3;
v___x_1110_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1110_, 0, v___x_1108_);
lean_ctor_set_uint8(v___x_1110_, sizeof(void*)*1, v___x_1109_);
v___x_1111_ = lean_array_get_size(v_a_1074_);
v___x_1112_ = lean_array_push(v_a_1074_, v___x_1110_);
v___x_1113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1111_);
lean_ctor_set(v___x_1113_, 1, v___x_1112_);
return v___x_1113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_readTraceFile___boxed(lean_object* v_path_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lake_readTraceFile(v_path_1114_, v_a_1115_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile(lean_object* v_path_1118_, lean_object* v_data_1119_){
_start:
{
lean_object* v___x_1121_; 
lean_inc_ref(v_path_1118_);
v___x_1121_ = l_Lake_createParentDirs(v_path_1118_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
lean_dec_ref(v___x_1121_);
v___x_1122_ = l_Lake_BuildMetadata_toJson(v_data_1119_);
v___x_1123_ = lean_unsigned_to_nat(80u);
v___x_1124_ = l_Lean_Json_pretty(v___x_1122_, v___x_1123_);
v___x_1125_ = l_IO_FS_writeFile(v_path_1118_, v___x_1124_);
lean_dec_ref(v___x_1124_);
lean_dec_ref(v_path_1118_);
return v___x_1125_;
}
else
{
lean_dec_ref(v_data_1119_);
lean_dec_ref(v_path_1118_);
return v___x_1121_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile___boxed(lean_object* v_path_1126_, lean_object* v_data_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lake_BuildMetadata_writeFile(v_path_1126_, v_data_1127_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace(lean_object* v_path_1130_, uint64_t v_inputHash_1131_, lean_object* v_outputs_1132_){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = l_Lake_BuildMetadata_ofFetch(v_inputHash_1131_, v_outputs_1132_);
v___x_1135_ = l_Lake_BuildMetadata_writeFile(v_path_1130_, v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace___boxed(lean_object* v_path_1136_, lean_object* v_inputHash_1137_, lean_object* v_outputs_1138_, lean_object* v_a_1139_){
_start:
{
uint64_t v_inputHash_boxed_1140_; lean_object* v_res_1141_; 
v_inputHash_boxed_1140_ = lean_unbox_uint64(v_inputHash_1137_);
lean_dec_ref(v_inputHash_1137_);
v_res_1141_ = l_Lake_writeFetchTrace(v_path_1136_, v_inputHash_boxed_1140_, v_outputs_1138_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg(lean_object* v_inst_1142_, lean_object* v_path_1143_, lean_object* v_depTrace_1144_, lean_object* v_outputs_1145_, lean_object* v_log_1146_){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1148_ = lean_apply_1(v_inst_1142_, v_outputs_1145_);
v___x_1149_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1144_, v___x_1148_, v_log_1146_);
v___x_1150_ = l_Lake_BuildMetadata_writeFile(v_path_1143_, v___x_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg___boxed(lean_object* v_inst_1151_, lean_object* v_path_1152_, lean_object* v_depTrace_1153_, lean_object* v_outputs_1154_, lean_object* v_log_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lake_writeBuildTrace___redArg(v_inst_1151_, v_path_1152_, v_depTrace_1153_, v_outputs_1154_, v_log_1155_);
lean_dec_ref(v_depTrace_1153_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace(lean_object* v_00_u03b1_1158_, lean_object* v_inst_1159_, lean_object* v_path_1160_, lean_object* v_depTrace_1161_, lean_object* v_outputs_1162_, lean_object* v_log_1163_){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = lean_apply_1(v_inst_1159_, v_outputs_1162_);
v___x_1166_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1161_, v___x_1165_, v_log_1163_);
v___x_1167_ = l_Lake_BuildMetadata_writeFile(v_path_1160_, v___x_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___boxed(lean_object* v_00_u03b1_1168_, lean_object* v_inst_1169_, lean_object* v_path_1170_, lean_object* v_depTrace_1171_, lean_object* v_outputs_1172_, lean_object* v_log_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lake_writeBuildTrace(v_00_u03b1_1168_, v_inst_1169_, v_path_1170_, v_depTrace_1171_, v_outputs_1172_, v_log_1173_);
lean_dec_ref(v_depTrace_1171_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorIdx(uint8_t v_x_1176_){
_start:
{
switch(v_x_1176_)
{
case 0:
{
lean_object* v___x_1177_; 
v___x_1177_ = lean_unsigned_to_nat(0u);
return v___x_1177_;
}
case 1:
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_unsigned_to_nat(1u);
return v___x_1178_;
}
default: 
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_unsigned_to_nat(2u);
return v___x_1179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorIdx___boxed(lean_object* v_x_1180_){
_start:
{
uint8_t v_x_boxed_1181_; lean_object* v_res_1182_; 
v_x_boxed_1181_ = lean_unbox(v_x_1180_);
v_res_1182_ = l_Lake_OutputStatus_ctorIdx(v_x_boxed_1181_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_toCtorIdx(uint8_t v_x_1183_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lake_OutputStatus_ctorIdx(v_x_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_toCtorIdx___boxed(lean_object* v_x_1185_){
_start:
{
uint8_t v_x_4__boxed_1186_; lean_object* v_res_1187_; 
v_x_4__boxed_1186_ = lean_unbox(v_x_1185_);
v_res_1187_ = l_Lake_OutputStatus_toCtorIdx(v_x_4__boxed_1186_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg(lean_object* v_k_1188_){
_start:
{
lean_inc(v_k_1188_);
return v_k_1188_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg___boxed(lean_object* v_k_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lake_OutputStatus_ctorElim___redArg(v_k_1189_);
lean_dec(v_k_1189_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim(lean_object* v_motive_1191_, lean_object* v_ctorIdx_1192_, uint8_t v_t_1193_, lean_object* v_h_1194_, lean_object* v_k_1195_){
_start:
{
lean_inc(v_k_1195_);
return v_k_1195_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___boxed(lean_object* v_motive_1196_, lean_object* v_ctorIdx_1197_, lean_object* v_t_1198_, lean_object* v_h_1199_, lean_object* v_k_1200_){
_start:
{
uint8_t v_t_boxed_1201_; lean_object* v_res_1202_; 
v_t_boxed_1201_ = lean_unbox(v_t_1198_);
v_res_1202_ = l_Lake_OutputStatus_ctorElim(v_motive_1196_, v_ctorIdx_1197_, v_t_boxed_1201_, v_h_1199_, v_k_1200_);
lean_dec(v_k_1200_);
lean_dec(v_ctorIdx_1197_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg(lean_object* v_outOfDate_1203_){
_start:
{
lean_inc(v_outOfDate_1203_);
return v_outOfDate_1203_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg___boxed(lean_object* v_outOfDate_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lake_OutputStatus_outOfDate_elim___redArg(v_outOfDate_1204_);
lean_dec(v_outOfDate_1204_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim(lean_object* v_motive_1206_, uint8_t v_t_1207_, lean_object* v_h_1208_, lean_object* v_outOfDate_1209_){
_start:
{
lean_inc(v_outOfDate_1209_);
return v_outOfDate_1209_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___boxed(lean_object* v_motive_1210_, lean_object* v_t_1211_, lean_object* v_h_1212_, lean_object* v_outOfDate_1213_){
_start:
{
uint8_t v_t_boxed_1214_; lean_object* v_res_1215_; 
v_t_boxed_1214_ = lean_unbox(v_t_1211_);
v_res_1215_ = l_Lake_OutputStatus_outOfDate_elim(v_motive_1210_, v_t_boxed_1214_, v_h_1212_, v_outOfDate_1213_);
lean_dec(v_outOfDate_1213_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg(lean_object* v_mtimeUpToDate_1216_){
_start:
{
lean_inc(v_mtimeUpToDate_1216_);
return v_mtimeUpToDate_1216_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg___boxed(lean_object* v_mtimeUpToDate_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lake_OutputStatus_mtimeUpToDate_elim___redArg(v_mtimeUpToDate_1217_);
lean_dec(v_mtimeUpToDate_1217_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim(lean_object* v_motive_1219_, uint8_t v_t_1220_, lean_object* v_h_1221_, lean_object* v_mtimeUpToDate_1222_){
_start:
{
lean_inc(v_mtimeUpToDate_1222_);
return v_mtimeUpToDate_1222_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___boxed(lean_object* v_motive_1223_, lean_object* v_t_1224_, lean_object* v_h_1225_, lean_object* v_mtimeUpToDate_1226_){
_start:
{
uint8_t v_t_boxed_1227_; lean_object* v_res_1228_; 
v_t_boxed_1227_ = lean_unbox(v_t_1224_);
v_res_1228_ = l_Lake_OutputStatus_mtimeUpToDate_elim(v_motive_1223_, v_t_boxed_1227_, v_h_1225_, v_mtimeUpToDate_1226_);
lean_dec(v_mtimeUpToDate_1226_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg(lean_object* v_hashUpToDate_1229_){
_start:
{
lean_inc(v_hashUpToDate_1229_);
return v_hashUpToDate_1229_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg___boxed(lean_object* v_hashUpToDate_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lake_OutputStatus_hashUpToDate_elim___redArg(v_hashUpToDate_1230_);
lean_dec(v_hashUpToDate_1230_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim(lean_object* v_motive_1232_, uint8_t v_t_1233_, lean_object* v_h_1234_, lean_object* v_hashUpToDate_1235_){
_start:
{
lean_inc(v_hashUpToDate_1235_);
return v_hashUpToDate_1235_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___boxed(lean_object* v_motive_1236_, lean_object* v_t_1237_, lean_object* v_h_1238_, lean_object* v_hashUpToDate_1239_){
_start:
{
uint8_t v_t_boxed_1240_; lean_object* v_res_1241_; 
v_t_boxed_1240_ = lean_unbox(v_t_1237_);
v_res_1241_ = l_Lake_OutputStatus_hashUpToDate_elim(v_motive_1236_, v_t_boxed_1240_, v_h_1238_, v_hashUpToDate_1239_);
lean_dec(v_hashUpToDate_1239_);
return v_res_1241_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofNat(lean_object* v_n_1242_){
_start:
{
lean_object* v___x_1243_; uint8_t v___x_1244_; 
v___x_1243_ = lean_unsigned_to_nat(0u);
v___x_1244_ = lean_nat_dec_le(v_n_1242_, v___x_1243_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1245_ = lean_unsigned_to_nat(1u);
v___x_1246_ = lean_nat_dec_le(v_n_1242_, v___x_1245_);
if (v___x_1246_ == 0)
{
uint8_t v___x_1247_; 
v___x_1247_ = 2;
return v___x_1247_;
}
else
{
uint8_t v___x_1248_; 
v___x_1248_ = 1;
return v___x_1248_;
}
}
else
{
uint8_t v___x_1249_; 
v___x_1249_ = 0;
return v___x_1249_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofNat___boxed(lean_object* v_n_1250_){
_start:
{
uint8_t v_res_1251_; lean_object* v_r_1252_; 
v_res_1251_ = l_Lake_OutputStatus_ofNat(v_n_1250_);
lean_dec(v_n_1250_);
v_r_1252_ = lean_box(v_res_1251_);
return v_r_1252_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqOutputStatus(uint8_t v_x_1253_, uint8_t v_y_1254_){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; 
v___x_1255_ = l_Lake_OutputStatus_ctorIdx(v_x_1253_);
v___x_1256_ = l_Lake_OutputStatus_ctorIdx(v_y_1254_);
v___x_1257_ = lean_nat_dec_eq(v___x_1255_, v___x_1256_);
lean_dec(v___x_1256_);
lean_dec(v___x_1255_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqOutputStatus___boxed(lean_object* v_x_1258_, lean_object* v_y_1259_){
_start:
{
uint8_t v_x_13__boxed_1260_; uint8_t v_y_14__boxed_1261_; uint8_t v_res_1262_; lean_object* v_r_1263_; 
v_x_13__boxed_1260_ = lean_unbox(v_x_1258_);
v_y_14__boxed_1261_ = lean_unbox(v_y_1259_);
v_res_1262_ = l_Lake_instDecidableEqOutputStatus(v_x_13__boxed_1260_, v_y_14__boxed_1261_);
v_r_1263_ = lean_box(v_res_1262_);
return v_r_1263_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofHashCheck(uint8_t v_upToDate_1264_){
_start:
{
if (v_upToDate_1264_ == 0)
{
uint8_t v___x_1265_; 
v___x_1265_ = 0;
return v___x_1265_;
}
else
{
uint8_t v___x_1266_; 
v___x_1266_ = 2;
return v___x_1266_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofHashCheck___boxed(lean_object* v_upToDate_1267_){
_start:
{
uint8_t v_upToDate_boxed_1268_; uint8_t v_res_1269_; lean_object* v_r_1270_; 
v_upToDate_boxed_1268_ = lean_unbox(v_upToDate_1267_);
v_res_1269_ = l_Lake_OutputStatus_ofHashCheck(v_upToDate_boxed_1268_);
v_r_1270_ = lean_box(v_res_1269_);
return v_r_1270_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofMTimeCheck(uint8_t v_upToDate_1271_){
_start:
{
if (v_upToDate_1271_ == 0)
{
uint8_t v___x_1272_; 
v___x_1272_ = 0;
return v___x_1272_;
}
else
{
uint8_t v___x_1273_; 
v___x_1273_ = 1;
return v___x_1273_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofMTimeCheck___boxed(lean_object* v_upToDate_1274_){
_start:
{
uint8_t v_upToDate_boxed_1275_; uint8_t v_res_1276_; lean_object* v_r_1277_; 
v_upToDate_boxed_1275_ = lean_unbox(v_upToDate_1274_);
v_res_1276_ = l_Lake_OutputStatus_ofMTimeCheck(v_upToDate_boxed_1275_);
v_r_1277_ = lean_box(v_res_1276_);
return v_r_1277_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isUpToDate(uint8_t v_status_1278_){
_start:
{
uint8_t v___x_1279_; uint8_t v___x_1280_; 
v___x_1279_ = 0;
v___x_1280_ = l_Lake_instDecidableEqOutputStatus(v_status_1278_, v___x_1279_);
if (v___x_1280_ == 0)
{
uint8_t v___x_1281_; 
v___x_1281_ = 1;
return v___x_1281_;
}
else
{
uint8_t v___x_1282_; 
v___x_1282_ = 0;
return v___x_1282_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isUpToDate___boxed(lean_object* v_status_1283_){
_start:
{
uint8_t v_status_boxed_1284_; uint8_t v_res_1285_; lean_object* v_r_1286_; 
v_status_boxed_1284_ = lean_unbox(v_status_1283_);
v_res_1285_ = l_Lake_OutputStatus_isUpToDate(v_status_boxed_1284_);
v_r_1286_ = lean_box(v_res_1285_);
return v_r_1286_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isCacheable(uint8_t v_status_1287_){
_start:
{
uint8_t v___x_1288_; uint8_t v___x_1289_; 
v___x_1288_ = 1;
v___x_1289_ = l_Lake_instDecidableEqOutputStatus(v_status_1287_, v___x_1288_);
if (v___x_1289_ == 0)
{
uint8_t v___x_1290_; 
v___x_1290_ = 1;
return v___x_1290_;
}
else
{
uint8_t v___x_1291_; 
v___x_1291_ = 0;
return v___x_1291_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isCacheable___boxed(lean_object* v_status_1292_){
_start:
{
uint8_t v_status_boxed_1293_; uint8_t v_res_1294_; lean_object* v_r_1295_; 
v_status_boxed_1293_ = lean_unbox(v_status_1292_);
v_res_1294_ = l_Lake_OutputStatus_isCacheable(v_status_boxed_1293_);
v_r_1295_ = lean_box(v_res_1294_);
return v_r_1295_;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___f_1297_; 
v___x_1296_ = lean_alloc_closure((void*)(l_Lake_instDecidableEqHash___boxed), 2, 0);
v___f_1297_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1297_, 0, v___x_1296_);
return v___f_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(lean_object* v_inst_1298_, lean_object* v_inst_1299_, lean_object* v_info_1300_, lean_object* v_depTrace_1301_, lean_object* v_depHash_1302_, lean_object* v_oldTrace_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
uint64_t v_hash_1307_; lean_object* v___f_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v_hash_1307_ = lean_ctor_get_uint64(v_depTrace_1301_, sizeof(void*)*3);
v___f_1308_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0);
v___x_1309_ = lean_box_uint64(v_hash_1307_);
v___x_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
v___x_1311_ = l_Option_instBEq_beq___redArg(v___f_1308_, v___x_1310_, v_depHash_1302_);
if (v___x_1311_ == 0)
{
lean_object* v_toBuildConfig_1312_; uint8_t v_oldMode_1313_; 
lean_dec_ref(v_inst_1298_);
v_toBuildConfig_1312_ = lean_ctor_get(v_a_1304_, 0);
v_oldMode_1313_ = lean_ctor_get_uint8(v_toBuildConfig_1312_, sizeof(void*)*2);
if (v_oldMode_1313_ == 0)
{
uint8_t v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_dec(v_info_1300_);
lean_dec_ref(v_inst_1299_);
v___x_1314_ = 0;
v___x_1315_ = lean_box(v___x_1314_);
v___x_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
lean_ctor_set(v___x_1316_, 1, v_a_1305_);
return v___x_1316_;
}
else
{
uint8_t v___x_1317_; 
v___x_1317_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1299_, v_info_1300_, v_oldTrace_1303_);
if (v___x_1317_ == 0)
{
uint8_t v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1318_ = 0;
v___x_1319_ = lean_box(v___x_1318_);
v___x_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
lean_ctor_set(v___x_1320_, 1, v_a_1305_);
return v___x_1320_;
}
else
{
uint8_t v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1321_ = 1;
v___x_1322_ = lean_box(v___x_1321_);
v___x_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
lean_ctor_set(v___x_1323_, 1, v_a_1305_);
return v___x_1323_;
}
}
}
else
{
lean_object* v___x_1324_; uint8_t v___x_1325_; 
lean_dec_ref(v_inst_1299_);
v___x_1324_ = lean_apply_2(v_inst_1298_, v_info_1300_, lean_box(0));
v___x_1325_ = lean_unbox(v___x_1324_);
if (v___x_1325_ == 0)
{
uint8_t v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1326_ = 0;
v___x_1327_ = lean_box(v___x_1326_);
v___x_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
lean_ctor_set(v___x_1328_, 1, v_a_1305_);
return v___x_1328_;
}
else
{
uint8_t v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1329_ = 2;
v___x_1330_ = lean_box(v___x_1329_);
v___x_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
lean_ctor_set(v___x_1331_, 1, v_a_1305_);
return v___x_1331_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___boxed(lean_object* v_inst_1332_, lean_object* v_inst_1333_, lean_object* v_info_1334_, lean_object* v_depTrace_1335_, lean_object* v_depHash_1336_, lean_object* v_oldTrace_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1332_, v_inst_1333_, v_info_1334_, v_depTrace_1335_, v_depHash_1336_, v_oldTrace_1337_, v_a_1338_, v_a_1339_);
lean_dec_ref(v_a_1338_);
lean_dec_ref(v_oldTrace_1337_);
lean_dec_ref(v_depTrace_1335_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27(lean_object* v_00_u03b9_1342_, lean_object* v_inst_1343_, lean_object* v_inst_1344_, lean_object* v_info_1345_, lean_object* v_depTrace_1346_, lean_object* v_depHash_1347_, lean_object* v_oldTrace_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1343_, v_inst_1344_, v_info_1345_, v_depTrace_1346_, v_depHash_1347_, v_oldTrace_1348_, v_a_1353_, v_a_1354_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___boxed(lean_object* v_00_u03b9_1357_, lean_object* v_inst_1358_, lean_object* v_inst_1359_, lean_object* v_info_1360_, lean_object* v_depTrace_1361_, lean_object* v_depHash_1362_, lean_object* v_oldTrace_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27(v_00_u03b9_1357_, v_inst_1358_, v_inst_1359_, v_info_1360_, v_depTrace_1361_, v_depHash_1362_, v_oldTrace_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
lean_dec_ref(v_a_1368_);
lean_dec(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec_ref(v_oldTrace_1363_);
lean_dec_ref(v_depTrace_1361_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg(lean_object* v_inst_1372_, lean_object* v_inst_1373_, lean_object* v_info_1374_, lean_object* v_depTrace_1375_, lean_object* v_depHash_1376_, lean_object* v_oldTrace_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_){
_start:
{
lean_object* v___x_1381_; lean_object* v_a_1382_; lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1400_; 
v___x_1381_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1372_, v_inst_1373_, v_info_1374_, v_depTrace_1375_, v_depHash_1376_, v_oldTrace_1377_, v_a_1378_, v_a_1379_);
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
v_a_1383_ = lean_ctor_get(v___x_1381_, 1);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1385_ = v___x_1381_;
v_isShared_1386_ = v_isSharedCheck_1400_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_inc(v_a_1382_);
lean_dec(v___x_1381_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1400_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
uint8_t v___x_1387_; uint8_t v___x_1388_; uint8_t v___x_1389_; 
v___x_1387_ = 0;
v___x_1388_ = lean_unbox(v_a_1382_);
lean_dec(v_a_1382_);
v___x_1389_ = l_Lake_instDecidableEqOutputStatus(v___x_1388_, v___x_1387_);
if (v___x_1389_ == 0)
{
uint8_t v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1390_ = 1;
v___x_1391_ = lean_box(v___x_1390_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1391_);
v___x_1393_ = v___x_1385_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_a_1383_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
else
{
uint8_t v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1395_ = 0;
v___x_1396_ = lean_box(v___x_1395_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1396_);
v___x_1398_ = v___x_1385_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_a_1383_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg___boxed(lean_object* v_inst_1401_, lean_object* v_inst_1402_, lean_object* v_info_1403_, lean_object* v_depTrace_1404_, lean_object* v_depHash_1405_, lean_object* v_oldTrace_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lake_checkHashUpToDate___redArg(v_inst_1401_, v_inst_1402_, v_info_1403_, v_depTrace_1404_, v_depHash_1405_, v_oldTrace_1406_, v_a_1407_, v_a_1408_);
lean_dec_ref(v_a_1407_);
lean_dec_ref(v_oldTrace_1406_);
lean_dec_ref(v_depTrace_1404_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate(lean_object* v_00_u03b9_1411_, lean_object* v_inst_1412_, lean_object* v_inst_1413_, lean_object* v_info_1414_, lean_object* v_depTrace_1415_, lean_object* v_depHash_1416_, lean_object* v_oldTrace_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v___x_1425_; lean_object* v_a_1426_; lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1444_; 
v___x_1425_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1412_, v_inst_1413_, v_info_1414_, v_depTrace_1415_, v_depHash_1416_, v_oldTrace_1417_, v_a_1422_, v_a_1423_);
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
v_a_1427_ = lean_ctor_get(v___x_1425_, 1);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1429_ = v___x_1425_;
v_isShared_1430_ = v_isSharedCheck_1444_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_inc(v_a_1426_);
lean_dec(v___x_1425_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1444_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
uint8_t v___x_1431_; uint8_t v___x_1432_; uint8_t v___x_1433_; 
v___x_1431_ = 0;
v___x_1432_ = lean_unbox(v_a_1426_);
lean_dec(v_a_1426_);
v___x_1433_ = l_Lake_instDecidableEqOutputStatus(v___x_1432_, v___x_1431_);
if (v___x_1433_ == 0)
{
uint8_t v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1434_ = 1;
v___x_1435_ = lean_box(v___x_1434_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 0, v___x_1435_);
v___x_1437_ = v___x_1429_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_a_1427_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
else
{
uint8_t v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1439_ = 0;
v___x_1440_ = lean_box(v___x_1439_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 0, v___x_1440_);
v___x_1442_ = v___x_1429_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_a_1427_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___boxed(lean_object* v_00_u03b9_1445_, lean_object* v_inst_1446_, lean_object* v_inst_1447_, lean_object* v_info_1448_, lean_object* v_depTrace_1449_, lean_object* v_depHash_1450_, lean_object* v_oldTrace_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lake_checkHashUpToDate(v_00_u03b9_1445_, v_inst_1446_, v_inst_1447_, v_info_1448_, v_depTrace_1449_, v_depHash_1450_, v_oldTrace_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_);
lean_dec_ref(v_a_1456_);
lean_dec(v_a_1455_);
lean_dec(v_a_1454_);
lean_dec(v_a_1453_);
lean_dec_ref(v_a_1452_);
lean_dec_ref(v_oldTrace_1451_);
lean_dec_ref(v_depTrace_1449_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(lean_object* v_as_1460_, size_t v_i_1461_, size_t v_stop_1462_, lean_object* v_b_1463_, lean_object* v___y_1464_){
_start:
{
uint8_t v___x_1466_; 
v___x_1466_ = lean_usize_dec_eq(v_i_1461_, v_stop_1462_);
if (v___x_1466_ == 0)
{
lean_object* v_log_1467_; uint8_t v_action_1468_; uint8_t v_wantsRebuild_1469_; lean_object* v_trace_1470_; lean_object* v_buildTime_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1484_; 
v_log_1467_ = lean_ctor_get(v___y_1464_, 0);
v_action_1468_ = lean_ctor_get_uint8(v___y_1464_, sizeof(void*)*3);
v_wantsRebuild_1469_ = lean_ctor_get_uint8(v___y_1464_, sizeof(void*)*3 + 1);
v_trace_1470_ = lean_ctor_get(v___y_1464_, 1);
v_buildTime_1471_ = lean_ctor_get(v___y_1464_, 2);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___y_1464_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1473_ = v___y_1464_;
v_isShared_1474_ = v_isSharedCheck_1484_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_buildTime_1471_);
lean_inc(v_trace_1470_);
lean_inc(v_log_1467_);
lean_dec(v___y_1464_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1484_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1479_; 
v___x_1475_ = lean_array_uget_borrowed(v_as_1460_, v_i_1461_);
v___x_1476_ = lean_box(0);
lean_inc(v___x_1475_);
v___x_1477_ = lean_array_push(v_log_1467_, v___x_1475_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1477_);
v___x_1479_ = v___x_1473_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_trace_1470_);
lean_ctor_set(v_reuseFailAlloc_1483_, 2, v_buildTime_1471_);
lean_ctor_set_uint8(v_reuseFailAlloc_1483_, sizeof(void*)*3, v_action_1468_);
lean_ctor_set_uint8(v_reuseFailAlloc_1483_, sizeof(void*)*3 + 1, v_wantsRebuild_1469_);
v___x_1479_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
size_t v___x_1480_; size_t v___x_1481_; 
v___x_1480_ = ((size_t)1ULL);
v___x_1481_ = lean_usize_add(v_i_1461_, v___x_1480_);
v_i_1461_ = v___x_1481_;
v_b_1463_ = v___x_1476_;
v___y_1464_ = v___x_1479_;
goto _start;
}
}
}
else
{
lean_object* v___x_1485_; 
v___x_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1485_, 0, v_b_1463_);
lean_ctor_set(v___x_1485_, 1, v___y_1464_);
return v___x_1485_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg___boxed(lean_object* v_as_1486_, lean_object* v_i_1487_, lean_object* v_stop_1488_, lean_object* v_b_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
size_t v_i_boxed_1492_; size_t v_stop_boxed_1493_; lean_object* v_res_1494_; 
v_i_boxed_1492_ = lean_unbox_usize(v_i_1487_);
lean_dec(v_i_1487_);
v_stop_boxed_1493_ = lean_unbox_usize(v_stop_1488_);
lean_dec(v_stop_1488_);
v_res_1494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_as_1486_, v_i_boxed_1492_, v_stop_boxed_1493_, v_b_1489_, v___y_1490_);
lean_dec_ref(v_as_1486_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(lean_object* v_log_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; 
v___x_1503_ = lean_unsigned_to_nat(0u);
v___x_1504_ = lean_array_get_size(v_log_1495_);
v___x_1505_ = lean_box(0);
v___x_1506_ = lean_nat_dec_lt(v___x_1503_, v___x_1504_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1505_);
lean_ctor_set(v___x_1507_, 1, v_a_1501_);
return v___x_1507_;
}
else
{
uint8_t v___x_1508_; 
v___x_1508_ = lean_nat_dec_le(v___x_1504_, v___x_1504_);
if (v___x_1508_ == 0)
{
if (v___x_1506_ == 0)
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1505_);
lean_ctor_set(v___x_1509_, 1, v_a_1501_);
return v___x_1509_;
}
else
{
size_t v___x_1510_; size_t v___x_1511_; lean_object* v___x_1512_; 
v___x_1510_ = ((size_t)0ULL);
v___x_1511_ = lean_usize_of_nat(v___x_1504_);
v___x_1512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1495_, v___x_1510_, v___x_1511_, v___x_1505_, v_a_1501_);
return v___x_1512_;
}
}
else
{
size_t v___x_1513_; size_t v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = ((size_t)0ULL);
v___x_1514_ = lean_usize_of_nat(v___x_1504_);
v___x_1515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1495_, v___x_1513_, v___x_1514_, v___x_1505_, v_a_1501_);
return v___x_1515_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay___boxed(lean_object* v_log_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
lean_dec_ref(v_a_1521_);
lean_dec(v_a_1520_);
lean_dec(v_a_1519_);
lean_dec(v_a_1518_);
lean_dec_ref(v_a_1517_);
lean_dec_ref(v_log_1516_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(lean_object* v_as_1525_, size_t v_i_1526_, size_t v_stop_1527_, lean_object* v_b_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_as_1525_, v_i_1526_, v_stop_1527_, v_b_1528_, v___y_1534_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___boxed(lean_object* v_as_1537_, lean_object* v_i_1538_, lean_object* v_stop_1539_, lean_object* v_b_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
size_t v_i_boxed_1548_; size_t v_stop_boxed_1549_; lean_object* v_res_1550_; 
v_i_boxed_1548_ = lean_unbox_usize(v_i_1538_);
lean_dec(v_i_1538_);
v_stop_boxed_1549_ = lean_unbox_usize(v_stop_1539_);
lean_dec(v_stop_1539_);
v_res_1550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(v_as_1537_, v_i_boxed_1548_, v_stop_boxed_1549_, v_b_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec_ref(v_as_1537_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(lean_object* v_inst_1551_, lean_object* v_inst_1552_, lean_object* v_info_1553_, lean_object* v_depTrace_1554_, lean_object* v_savedTrace_1555_, lean_object* v_oldTrace_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_){
_start:
{
if (lean_obj_tag(v_savedTrace_1555_) == 2)
{
lean_object* v_data_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1614_; 
v_data_1564_ = lean_ctor_get(v_savedTrace_1555_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v_savedTrace_1555_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1566_ = v_savedTrace_1555_;
v_isShared_1567_ = v_isSharedCheck_1614_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_data_1564_);
lean_dec(v_savedTrace_1555_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1614_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
uint64_t v_depHash_1568_; lean_object* v_log_1569_; lean_object* v___x_1570_; lean_object* v___x_1572_; 
v_depHash_1568_ = lean_ctor_get_uint64(v_data_1564_, sizeof(void*)*3);
v_log_1569_ = lean_ctor_get(v_data_1564_, 2);
lean_inc_ref(v_log_1569_);
lean_dec_ref(v_data_1564_);
v___x_1570_ = lean_box_uint64(v_depHash_1568_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set_tag(v___x_1566_, 1);
lean_ctor_set(v___x_1566_, 0, v___x_1570_);
v___x_1572_ = v___x_1566_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
lean_object* v___x_1573_; lean_object* v_a_1574_; lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1612_; 
v___x_1573_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1551_, v_inst_1552_, v_info_1553_, v_depTrace_1554_, v___x_1572_, v_oldTrace_1556_, v_a_1561_, v_a_1562_);
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
v_a_1575_ = lean_ctor_get(v___x_1573_, 1);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1577_ = v___x_1573_;
v_isShared_1578_ = v_isSharedCheck_1612_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_inc(v_a_1574_);
lean_dec(v___x_1573_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1612_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___y_1580_; uint8_t v___x_1584_; uint8_t v___x_1585_; uint8_t v___x_1586_; 
v___x_1584_ = 0;
v___x_1585_ = lean_unbox(v_a_1574_);
v___x_1586_ = l_Lake_instDecidableEqOutputStatus(v___x_1585_, v___x_1584_);
if (v___x_1586_ == 0)
{
lean_object* v_log_1587_; uint8_t v_action_1588_; uint8_t v_wantsRebuild_1589_; lean_object* v_trace_1590_; lean_object* v_buildTime_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1611_; 
v_log_1587_ = lean_ctor_get(v_a_1575_, 0);
v_action_1588_ = lean_ctor_get_uint8(v_a_1575_, sizeof(void*)*3);
v_wantsRebuild_1589_ = lean_ctor_get_uint8(v_a_1575_, sizeof(void*)*3 + 1);
v_trace_1590_ = lean_ctor_get(v_a_1575_, 1);
v_buildTime_1591_ = lean_ctor_get(v_a_1575_, 2);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_a_1575_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1593_ = v_a_1575_;
v_isShared_1594_ = v_isSharedCheck_1611_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_buildTime_1591_);
lean_inc(v_trace_1590_);
lean_inc(v_log_1587_);
lean_dec(v_a_1575_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1611_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
uint8_t v___x_1595_; uint8_t v___x_1596_; lean_object* v___x_1598_; 
v___x_1595_ = 1;
v___x_1596_ = l_Lake_JobAction_merge(v_action_1588_, v___x_1595_);
if (v_isShared_1594_ == 0)
{
v___x_1598_ = v___x_1593_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_log_1587_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_trace_1590_);
lean_ctor_set(v_reuseFailAlloc_1610_, 2, v_buildTime_1591_);
lean_ctor_set_uint8(v_reuseFailAlloc_1610_, sizeof(void*)*3 + 1, v_wantsRebuild_1589_);
v___x_1598_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1599_; 
lean_ctor_set_uint8(v___x_1598_, sizeof(void*)*3, v___x_1596_);
v___x_1599_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_1569_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v___x_1598_);
lean_dec_ref(v_log_1569_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 1);
lean_inc(v_a_1600_);
lean_dec_ref(v___x_1599_);
v___y_1580_ = v_a_1600_;
goto v___jp_1579_;
}
else
{
lean_object* v_a_1601_; lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_del_object(v___x_1577_);
lean_dec(v_a_1574_);
v_a_1601_ = lean_ctor_get(v___x_1599_, 0);
v_a_1602_ = lean_ctor_get(v___x_1599_, 1);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1599_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_inc(v_a_1601_);
lean_dec(v___x_1599_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1601_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_log_1569_);
v___y_1580_ = v_a_1575_;
goto v___jp_1579_;
}
v___jp_1579_:
{
lean_object* v___x_1582_; 
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 1, v___y_1580_);
v___x_1582_ = v___x_1577_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1574_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v___y_1580_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
}
}
else
{
lean_object* v_toBuildConfig_1615_; uint8_t v_oldMode_1616_; 
lean_dec(v_savedTrace_1555_);
lean_dec_ref(v_inst_1551_);
v_toBuildConfig_1615_ = lean_ctor_get(v_a_1561_, 0);
v_oldMode_1616_ = lean_ctor_get_uint8(v_toBuildConfig_1615_, sizeof(void*)*2);
if (v_oldMode_1616_ == 0)
{
uint8_t v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
lean_dec(v_info_1553_);
lean_dec_ref(v_inst_1552_);
v___x_1617_ = 0;
v___x_1618_ = lean_box(v___x_1617_);
v___x_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
lean_ctor_set(v___x_1619_, 1, v_a_1562_);
return v___x_1619_;
}
else
{
uint8_t v___x_1620_; 
v___x_1620_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1552_, v_info_1553_, v_oldTrace_1556_);
if (v___x_1620_ == 0)
{
uint8_t v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1621_ = 0;
v___x_1622_ = lean_box(v___x_1621_);
v___x_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
lean_ctor_set(v___x_1623_, 1, v_a_1562_);
return v___x_1623_;
}
else
{
uint8_t v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1624_ = 1;
v___x_1625_ = lean_box(v___x_1624_);
v___x_1626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
lean_ctor_set(v___x_1626_, 1, v_a_1562_);
return v___x_1626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg___boxed(lean_object* v_inst_1627_, lean_object* v_inst_1628_, lean_object* v_info_1629_, lean_object* v_depTrace_1630_, lean_object* v_savedTrace_1631_, lean_object* v_oldTrace_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1627_, v_inst_1628_, v_info_1629_, v_depTrace_1630_, v_savedTrace_1631_, v_oldTrace_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
lean_dec_ref(v_a_1637_);
lean_dec(v_a_1636_);
lean_dec(v_a_1635_);
lean_dec(v_a_1634_);
lean_dec_ref(v_a_1633_);
lean_dec_ref(v_oldTrace_1632_);
lean_dec_ref(v_depTrace_1630_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27(lean_object* v_00_u03b9_1641_, lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_info_1644_, lean_object* v_depTrace_1645_, lean_object* v_savedTrace_1646_, lean_object* v_oldTrace_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1642_, v_inst_1643_, v_info_1644_, v_depTrace_1645_, v_savedTrace_1646_, v_oldTrace_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___boxed(lean_object* v_00_u03b9_1656_, lean_object* v_inst_1657_, lean_object* v_inst_1658_, lean_object* v_info_1659_, lean_object* v_depTrace_1660_, lean_object* v_savedTrace_1661_, lean_object* v_oldTrace_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lake_SavedTrace_replayIfUpToDate_x27(v_00_u03b9_1656_, v_inst_1657_, v_inst_1658_, v_info_1659_, v_depTrace_1660_, v_savedTrace_1661_, v_oldTrace_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_);
lean_dec_ref(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec(v_a_1665_);
lean_dec(v_a_1664_);
lean_dec_ref(v_a_1663_);
lean_dec_ref(v_oldTrace_1662_);
lean_dec_ref(v_depTrace_1660_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg(lean_object* v_inst_1671_, lean_object* v_inst_1672_, lean_object* v_info_1673_, lean_object* v_depTrace_1674_, lean_object* v_savedTrace_1675_, lean_object* v_oldTrace_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1671_, v_inst_1672_, v_info_1673_, v_depTrace_1674_, v_savedTrace_1675_, v_oldTrace_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_a_1685_; lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1703_; 
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
v_a_1686_ = lean_ctor_get(v___x_1684_, 1);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1688_ = v___x_1684_;
v_isShared_1689_ = v_isSharedCheck_1703_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_inc(v_a_1685_);
lean_dec(v___x_1684_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1703_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
uint8_t v___x_1690_; uint8_t v___x_1691_; uint8_t v___x_1692_; 
v___x_1690_ = 0;
v___x_1691_ = lean_unbox(v_a_1685_);
lean_dec(v_a_1685_);
v___x_1692_ = l_Lake_instDecidableEqOutputStatus(v___x_1691_, v___x_1690_);
if (v___x_1692_ == 0)
{
uint8_t v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1696_; 
v___x_1693_ = 1;
v___x_1694_ = lean_box(v___x_1693_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 0, v___x_1694_);
v___x_1696_ = v___x_1688_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1694_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v_a_1686_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
else
{
uint8_t v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1701_; 
v___x_1698_ = 0;
v___x_1699_ = lean_box(v___x_1698_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 0, v___x_1699_);
v___x_1701_ = v___x_1688_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_a_1686_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
else
{
lean_object* v_a_1704_; lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
v_a_1704_ = lean_ctor_get(v___x_1684_, 0);
v_a_1705_ = lean_ctor_get(v___x_1684_, 1);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1684_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_inc(v_a_1704_);
lean_dec(v___x_1684_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1704_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg___boxed(lean_object* v_inst_1713_, lean_object* v_inst_1714_, lean_object* v_info_1715_, lean_object* v_depTrace_1716_, lean_object* v_savedTrace_1717_, lean_object* v_oldTrace_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lake_SavedTrace_replayIfUpToDate___redArg(v_inst_1713_, v_inst_1714_, v_info_1715_, v_depTrace_1716_, v_savedTrace_1717_, v_oldTrace_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_);
lean_dec_ref(v_a_1723_);
lean_dec(v_a_1722_);
lean_dec(v_a_1721_);
lean_dec(v_a_1720_);
lean_dec_ref(v_a_1719_);
lean_dec_ref(v_oldTrace_1718_);
lean_dec_ref(v_depTrace_1716_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate(lean_object* v_00_u03b9_1727_, lean_object* v_inst_1728_, lean_object* v_inst_1729_, lean_object* v_info_1730_, lean_object* v_depTrace_1731_, lean_object* v_savedTrace_1732_, lean_object* v_oldTrace_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1728_, v_inst_1729_, v_info_1730_, v_depTrace_1731_, v_savedTrace_1732_, v_oldTrace_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1760_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
v_a_1743_ = lean_ctor_get(v___x_1741_, 1);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1745_ = v___x_1741_;
v_isShared_1746_ = v_isSharedCheck_1760_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_inc(v_a_1742_);
lean_dec(v___x_1741_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1760_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
uint8_t v___x_1747_; uint8_t v___x_1748_; uint8_t v___x_1749_; 
v___x_1747_ = 0;
v___x_1748_ = lean_unbox(v_a_1742_);
lean_dec(v_a_1742_);
v___x_1749_ = l_Lake_instDecidableEqOutputStatus(v___x_1748_, v___x_1747_);
if (v___x_1749_ == 0)
{
uint8_t v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1753_; 
v___x_1750_ = 1;
v___x_1751_ = lean_box(v___x_1750_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1751_);
v___x_1753_ = v___x_1745_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v___x_1751_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v_a_1743_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
else
{
uint8_t v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1758_; 
v___x_1755_ = 0;
v___x_1756_ = lean_box(v___x_1755_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1756_);
v___x_1758_ = v___x_1745_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_a_1743_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
v_a_1761_ = lean_ctor_get(v___x_1741_, 0);
v_a_1762_ = lean_ctor_get(v___x_1741_, 1);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1741_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_inc(v_a_1761_);
lean_dec(v___x_1741_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1761_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___boxed(lean_object* v_00_u03b9_1770_, lean_object* v_inst_1771_, lean_object* v_inst_1772_, lean_object* v_info_1773_, lean_object* v_depTrace_1774_, lean_object* v_savedTrace_1775_, lean_object* v_oldTrace_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Lake_SavedTrace_replayIfUpToDate(v_00_u03b9_1770_, v_inst_1771_, v_inst_1772_, v_info_1773_, v_depTrace_1774_, v_savedTrace_1775_, v_oldTrace_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_);
lean_dec_ref(v_a_1781_);
lean_dec(v_a_1780_);
lean_dec(v_a_1779_);
lean_dec(v_a_1778_);
lean_dec_ref(v_a_1777_);
lean_dec_ref(v_oldTrace_1776_);
lean_dec_ref(v_depTrace_1774_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(uint64_t v_inputHash_1785_, lean_object* v_self_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v___y_1790_; 
if (lean_obj_tag(v_self_1786_) == 2)
{
lean_object* v_data_1808_; uint64_t v_depHash_1809_; lean_object* v_log_1810_; uint8_t v_synthetic_1811_; uint8_t v___x_1812_; lean_object* v___y_1814_; lean_object* v___y_1818_; 
v_data_1808_ = lean_ctor_get(v_self_1786_, 0);
v_depHash_1809_ = lean_ctor_get_uint64(v_data_1808_, sizeof(void*)*3);
v_log_1810_ = lean_ctor_get(v_data_1808_, 2);
v_synthetic_1811_ = lean_ctor_get_uint8(v_data_1808_, sizeof(void*)*3 + 8);
v___x_1812_ = lean_uint64_dec_eq(v_depHash_1809_, v_inputHash_1785_);
if (v___x_1812_ == 0)
{
v___y_1790_ = v_a_1787_;
goto v___jp_1789_;
}
else
{
if (v_synthetic_1811_ == 0)
{
goto v___jp_1829_;
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; uint8_t v___x_1857_; 
v___x_1855_ = lean_array_get_size(v_log_1810_);
v___x_1856_ = lean_unsigned_to_nat(0u);
v___x_1857_ = lean_nat_dec_eq(v___x_1855_, v___x_1856_);
if (v___x_1857_ == 0)
{
goto v___jp_1829_;
}
else
{
lean_object* v_log_1858_; uint8_t v_action_1859_; uint8_t v_wantsRebuild_1860_; lean_object* v_trace_1861_; lean_object* v_buildTime_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1871_; 
v_log_1858_ = lean_ctor_get(v_a_1787_, 0);
v_action_1859_ = lean_ctor_get_uint8(v_a_1787_, sizeof(void*)*3);
v_wantsRebuild_1860_ = lean_ctor_get_uint8(v_a_1787_, sizeof(void*)*3 + 1);
v_trace_1861_ = lean_ctor_get(v_a_1787_, 1);
v_buildTime_1862_ = lean_ctor_get(v_a_1787_, 2);
v_isSharedCheck_1871_ = !lean_is_exclusive(v_a_1787_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1864_ = v_a_1787_;
v_isShared_1865_ = v_isSharedCheck_1871_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_buildTime_1862_);
lean_inc(v_trace_1861_);
lean_inc(v_log_1858_);
lean_dec(v_a_1787_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1871_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
uint8_t v___x_1866_; uint8_t v___x_1867_; lean_object* v___x_1869_; 
v___x_1866_ = 2;
v___x_1867_ = l_Lake_JobAction_merge(v_action_1859_, v___x_1866_);
if (v_isShared_1865_ == 0)
{
v___x_1869_ = v___x_1864_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_log_1858_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v_trace_1861_);
lean_ctor_set(v_reuseFailAlloc_1870_, 2, v_buildTime_1862_);
lean_ctor_set_uint8(v_reuseFailAlloc_1870_, sizeof(void*)*3 + 1, v_wantsRebuild_1860_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_ctor_set_uint8(v___x_1869_, sizeof(void*)*3, v___x_1867_);
v___y_1814_ = v___x_1869_;
goto v___jp_1813_;
}
}
}
}
}
v___jp_1813_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = lean_box(v___x_1812_);
v___x_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
lean_ctor_set(v___x_1816_, 1, v___y_1814_);
return v___x_1816_;
}
v___jp_1817_:
{
if (lean_obj_tag(v___y_1818_) == 0)
{
lean_object* v_a_1819_; 
v_a_1819_ = lean_ctor_get(v___y_1818_, 1);
lean_inc(v_a_1819_);
lean_dec_ref(v___y_1818_);
v___y_1814_ = v_a_1819_;
goto v___jp_1813_;
}
else
{
lean_object* v_a_1820_; lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
v_a_1820_ = lean_ctor_get(v___y_1818_, 0);
v_a_1821_ = lean_ctor_get(v___y_1818_, 1);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___y_1818_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___y_1818_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_inc(v_a_1820_);
lean_dec(v___y_1818_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1820_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
v___jp_1829_:
{
lean_object* v_log_1830_; uint8_t v_action_1831_; uint8_t v_wantsRebuild_1832_; lean_object* v_trace_1833_; lean_object* v_buildTime_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1854_; 
v_log_1830_ = lean_ctor_get(v_a_1787_, 0);
v_action_1831_ = lean_ctor_get_uint8(v_a_1787_, sizeof(void*)*3);
v_wantsRebuild_1832_ = lean_ctor_get_uint8(v_a_1787_, sizeof(void*)*3 + 1);
v_trace_1833_ = lean_ctor_get(v_a_1787_, 1);
v_buildTime_1834_ = lean_ctor_get(v_a_1787_, 2);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_a_1787_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1836_ = v_a_1787_;
v_isShared_1837_ = v_isSharedCheck_1854_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_buildTime_1834_);
lean_inc(v_trace_1833_);
lean_inc(v_log_1830_);
lean_dec(v_a_1787_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1854_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
uint8_t v___x_1838_; uint8_t v___x_1839_; lean_object* v___x_1841_; 
v___x_1838_ = 1;
v___x_1839_ = l_Lake_JobAction_merge(v_action_1831_, v___x_1838_);
if (v_isShared_1837_ == 0)
{
v___x_1841_ = v___x_1836_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_log_1830_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_trace_1833_);
lean_ctor_set(v_reuseFailAlloc_1853_, 2, v_buildTime_1834_);
lean_ctor_set_uint8(v_reuseFailAlloc_1853_, sizeof(void*)*3 + 1, v_wantsRebuild_1832_);
v___x_1841_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; 
lean_ctor_set_uint8(v___x_1841_, sizeof(void*)*3, v___x_1839_);
v___x_1842_ = lean_unsigned_to_nat(0u);
v___x_1843_ = lean_array_get_size(v_log_1810_);
v___x_1844_ = lean_nat_dec_lt(v___x_1842_, v___x_1843_);
if (v___x_1844_ == 0)
{
v___y_1814_ = v___x_1841_;
goto v___jp_1813_;
}
else
{
lean_object* v___x_1845_; uint8_t v___x_1846_; 
v___x_1845_ = lean_box(0);
v___x_1846_ = lean_nat_dec_le(v___x_1843_, v___x_1843_);
if (v___x_1846_ == 0)
{
if (v___x_1844_ == 0)
{
v___y_1814_ = v___x_1841_;
goto v___jp_1813_;
}
else
{
size_t v___x_1847_; size_t v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = ((size_t)0ULL);
v___x_1848_ = lean_usize_of_nat(v___x_1843_);
v___x_1849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1810_, v___x_1847_, v___x_1848_, v___x_1845_, v___x_1841_);
v___y_1818_ = v___x_1849_;
goto v___jp_1817_;
}
}
else
{
size_t v___x_1850_; size_t v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = ((size_t)0ULL);
v___x_1851_ = lean_usize_of_nat(v___x_1843_);
v___x_1852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1810_, v___x_1850_, v___x_1851_, v___x_1845_, v___x_1841_);
v___y_1818_ = v___x_1852_;
goto v___jp_1817_;
}
}
}
}
}
}
else
{
v___y_1790_ = v_a_1787_;
goto v___jp_1789_;
}
v___jp_1789_:
{
lean_object* v_log_1791_; uint8_t v_action_1792_; uint8_t v_wantsRebuild_1793_; lean_object* v_trace_1794_; lean_object* v_buildTime_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1807_; 
v_log_1791_ = lean_ctor_get(v___y_1790_, 0);
v_action_1792_ = lean_ctor_get_uint8(v___y_1790_, sizeof(void*)*3);
v_wantsRebuild_1793_ = lean_ctor_get_uint8(v___y_1790_, sizeof(void*)*3 + 1);
v_trace_1794_ = lean_ctor_get(v___y_1790_, 1);
v_buildTime_1795_ = lean_ctor_get(v___y_1790_, 2);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___y_1790_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1797_ = v___y_1790_;
v_isShared_1798_ = v_isSharedCheck_1807_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_buildTime_1795_);
lean_inc(v_trace_1794_);
lean_inc(v_log_1791_);
lean_dec(v___y_1790_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1807_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
uint8_t v___x_1799_; uint8_t v___x_1800_; lean_object* v___x_1802_; 
v___x_1799_ = 2;
v___x_1800_ = l_Lake_JobAction_merge(v_action_1792_, v___x_1799_);
if (v_isShared_1798_ == 0)
{
v___x_1802_ = v___x_1797_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_log_1791_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v_trace_1794_);
lean_ctor_set(v_reuseFailAlloc_1806_, 2, v_buildTime_1795_);
lean_ctor_set_uint8(v_reuseFailAlloc_1806_, sizeof(void*)*3 + 1, v_wantsRebuild_1793_);
v___x_1802_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
uint8_t v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
lean_ctor_set_uint8(v___x_1802_, sizeof(void*)*3, v___x_1800_);
v___x_1803_ = 0;
v___x_1804_ = lean_box(v___x_1803_);
v___x_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
lean_ctor_set(v___x_1805_, 1, v___x_1802_);
return v___x_1805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg___boxed(lean_object* v_inputHash_1872_, lean_object* v_self_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_){
_start:
{
uint64_t v_inputHash_boxed_1876_; lean_object* v_res_1877_; 
v_inputHash_boxed_1876_ = lean_unbox_uint64(v_inputHash_1872_);
lean_dec_ref(v_inputHash_1872_);
v_res_1877_ = l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(v_inputHash_boxed_1876_, v_self_1873_, v_a_1874_);
lean_dec(v_self_1873_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate(uint64_t v_inputHash_1878_, lean_object* v_self_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(v_inputHash_1878_, v_self_1879_, v_a_1885_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___boxed(lean_object* v_inputHash_1888_, lean_object* v_self_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_){
_start:
{
uint64_t v_inputHash_boxed_1897_; lean_object* v_res_1898_; 
v_inputHash_boxed_1897_ = lean_unbox_uint64(v_inputHash_1888_);
lean_dec_ref(v_inputHash_1888_);
v_res_1898_ = l_Lake_SavedTrace_replayOrFetchIfUpToDate(v_inputHash_boxed_1897_, v_self_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
lean_dec_ref(v_a_1894_);
lean_dec(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1890_);
lean_dec(v_self_1889_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonPUnit___lam__0(lean_object* v_x_1899_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = lean_box(0);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0(lean_object* v_x_1904_){
_start:
{
lean_object* v_descr_1905_; uint64_t v_hash_1906_; lean_object* v_ext_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; uint8_t v___x_1910_; 
v_descr_1905_ = lean_ctor_get(v_x_1904_, 0);
v_hash_1906_ = lean_ctor_get_uint64(v_descr_1905_, sizeof(void*)*1);
v_ext_1907_ = lean_ctor_get(v_descr_1905_, 0);
v___x_1908_ = lean_string_utf8_byte_size(v_ext_1907_);
v___x_1909_ = lean_unsigned_to_nat(0u);
v___x_1910_ = lean_nat_dec_eq(v___x_1908_, v___x_1909_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1911_ = l_Lake_Hash_hex(v_hash_1906_);
v___x_1912_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_1913_ = lean_string_append(v___x_1911_, v___x_1912_);
v___x_1914_ = lean_string_append(v___x_1913_, v_ext_1907_);
v___x_1915_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
return v___x_1915_;
}
else
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = l_Lake_Hash_hex(v_hash_1906_);
v___x_1917_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1916_);
return v___x_1917_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0___boxed(lean_object* v_x_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Lake_instToOutputJsonArtifact___lam__0(v_x_1918_);
lean_dec_ref(v_x_1918_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0(lean_object* v_val_1922_, lean_object* v_a_x3f_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v___x_1926_; lean_object* v_log_1927_; uint8_t v_action_1928_; uint8_t v_wantsRebuild_1929_; lean_object* v_trace_1930_; lean_object* v_buildTime_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1942_; 
v___x_1926_ = lean_io_mono_ms_now();
v_log_1927_ = lean_ctor_get(v___y_1924_, 0);
v_action_1928_ = lean_ctor_get_uint8(v___y_1924_, sizeof(void*)*3);
v_wantsRebuild_1929_ = lean_ctor_get_uint8(v___y_1924_, sizeof(void*)*3 + 1);
v_trace_1930_ = lean_ctor_get(v___y_1924_, 1);
v_buildTime_1931_ = lean_ctor_get(v___y_1924_, 2);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___y_1924_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1933_ = v___y_1924_;
v_isShared_1934_ = v_isSharedCheck_1942_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_buildTime_1931_);
lean_inc(v_trace_1930_);
lean_inc(v_log_1927_);
lean_dec(v___y_1924_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1942_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1939_; 
v___x_1935_ = lean_nat_sub(v___x_1926_, v_val_1922_);
lean_dec(v___x_1926_);
v___x_1936_ = lean_box(0);
v___x_1937_ = lean_nat_add(v_buildTime_1931_, v___x_1935_);
lean_dec(v___x_1935_);
lean_dec(v_buildTime_1931_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 2, v___x_1937_);
v___x_1939_ = v___x_1933_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_log_1927_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v_trace_1930_);
lean_ctor_set(v_reuseFailAlloc_1941_, 2, v___x_1937_);
lean_ctor_set_uint8(v_reuseFailAlloc_1941_, sizeof(void*)*3, v_action_1928_);
lean_ctor_set_uint8(v_reuseFailAlloc_1941_, sizeof(void*)*3 + 1, v_wantsRebuild_1929_);
v___x_1939_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
lean_object* v___x_1940_; 
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1936_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
return v___x_1940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0___boxed(lean_object* v_val_1943_, lean_object* v_a_x3f_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lake_buildAction___redArg___lam__0(v_val_1943_, v_a_x3f_1944_, v___y_1945_);
lean_dec(v_a_x3f_1944_);
lean_dec(v_val_1943_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg(lean_object* v_inst_1953_, lean_object* v_depTrace_1954_, lean_object* v_traceFile_1955_, lean_object* v_build_1956_, uint8_t v_action_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v_a_1966_; lean_object* v_a_1967_; lean_object* v_log_1970_; uint8_t v_action_1971_; uint8_t v_wantsRebuild_1972_; lean_object* v_trace_1973_; lean_object* v_buildTime_1974_; lean_object* v_toBuildConfig_1980_; lean_object* v_log_1981_; uint8_t v_action_1982_; uint8_t v_wantsRebuild_1983_; lean_object* v_trace_1984_; lean_object* v_buildTime_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2091_; 
v_toBuildConfig_1980_ = lean_ctor_get(v_a_1962_, 0);
v_log_1981_ = lean_ctor_get(v_a_1963_, 0);
v_action_1982_ = lean_ctor_get_uint8(v_a_1963_, sizeof(void*)*3);
v_wantsRebuild_1983_ = lean_ctor_get_uint8(v_a_1963_, sizeof(void*)*3 + 1);
v_trace_1984_ = lean_ctor_get(v_a_1963_, 1);
v_buildTime_1985_ = lean_ctor_get(v_a_1963_, 2);
v_isSharedCheck_2091_ = !lean_is_exclusive(v_a_1963_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_1987_ = v_a_1963_;
v_isShared_1988_ = v_isSharedCheck_2091_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_buildTime_1985_);
lean_inc(v_trace_1984_);
lean_inc(v_log_1981_);
lean_dec(v_a_1963_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2091_;
goto v_resetjp_1986_;
}
v___jp_1965_:
{
lean_object* v___x_1968_; 
v___x_1968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1968_, 0, v_a_1966_);
lean_ctor_set(v___x_1968_, 1, v_a_1967_);
return v___x_1968_;
}
v___jp_1969_:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1975_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_1976_ = lean_array_get_size(v_log_1970_);
v___x_1977_ = lean_array_push(v_log_1970_, v___x_1975_);
v___x_1978_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
lean_ctor_set(v___x_1978_, 1, v_trace_1973_);
lean_ctor_set(v___x_1978_, 2, v_buildTime_1974_);
lean_ctor_set_uint8(v___x_1978_, sizeof(void*)*3, v_action_1971_);
lean_ctor_set_uint8(v___x_1978_, sizeof(void*)*3 + 1, v_wantsRebuild_1972_);
v___x_1979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1976_);
lean_ctor_set(v___x_1979_, 1, v___x_1978_);
return v___x_1979_;
}
v_resetjp_1986_:
{
uint8_t v_noBuild_1989_; uint8_t v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v_noBuild_1989_ = lean_ctor_get_uint8(v_toBuildConfig_1980_, sizeof(void*)*2 + 2);
v___x_1990_ = l_Lake_JobAction_merge(v_action_1982_, v_action_1957_);
v___x_1991_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_1955_);
v___x_1992_ = l_System_FilePath_addExtension(v_traceFile_1955_, v___x_1991_);
if (v_noBuild_1989_ == 0)
{
lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1993_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_1981_);
if (v_isShared_1988_ == 0)
{
v___x_1995_ = v___x_1987_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_log_1981_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_trace_1984_);
lean_ctor_set(v_reuseFailAlloc_2075_, 2, v_buildTime_1985_);
lean_ctor_set_uint8(v_reuseFailAlloc_2075_, sizeof(void*)*3 + 1, v_wantsRebuild_1983_);
v___x_1995_ = v_reuseFailAlloc_2075_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1996_; lean_object* v_a_1998_; lean_object* v_a_1999_; 
lean_ctor_set_uint8(v___x_1995_, sizeof(void*)*3, v___x_1990_);
lean_inc_ref(v_a_1962_);
lean_inc(v_a_1961_);
lean_inc(v_a_1960_);
lean_inc(v_a_1959_);
v___x_1996_ = lean_apply_7(v_build_1956_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v___x_1995_, lean_box(0));
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_2003_; lean_object* v_a_2004_; lean_object* v_log_2005_; uint8_t v_action_2006_; uint8_t v_wantsRebuild_2007_; lean_object* v_trace_2008_; lean_object* v_buildTime_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v_a_2003_ = lean_ctor_get(v___x_1996_, 1);
lean_inc(v_a_2003_);
v_a_2004_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_2004_);
lean_dec_ref(v___x_1996_);
v_log_2005_ = lean_ctor_get(v_a_2003_, 0);
v_action_2006_ = lean_ctor_get_uint8(v_a_2003_, sizeof(void*)*3);
v_wantsRebuild_2007_ = lean_ctor_get_uint8(v_a_2003_, sizeof(void*)*3 + 1);
v_trace_2008_ = lean_ctor_get(v_a_2003_, 1);
v_buildTime_2009_ = lean_ctor_get(v_a_2003_, 2);
v___x_2010_ = lean_array_get_size(v_log_1981_);
lean_dec_ref(v_log_1981_);
v___x_2011_ = lean_array_get_size(v_log_2005_);
v___x_2012_ = l_Array_extract___redArg(v_log_2005_, v___x_2010_, v___x_2011_);
lean_inc(v_a_2004_);
v___x_2013_ = lean_apply_1(v_inst_1953_, v_a_2004_);
v___x_2014_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1954_, v___x_2013_, v___x_2012_);
v___x_2015_ = l_Lake_BuildMetadata_writeFile(v_traceFile_1955_, v___x_2014_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2056_; 
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2056_ == 0)
{
lean_object* v_unused_2057_; 
v_unused_2057_ = lean_ctor_get(v___x_2015_, 0);
lean_dec(v_unused_2057_);
v___x_2017_ = v___x_2015_;
v_isShared_2018_ = v_isSharedCheck_2056_;
goto v_resetjp_2016_;
}
else
{
lean_dec(v___x_2015_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2056_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Lake_removeFileIfExists(v___x_1992_);
lean_dec_ref(v___x_1992_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2039_; 
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2039_ == 0)
{
lean_object* v_unused_2040_; 
v_unused_2040_ = lean_ctor_get(v___x_2019_, 0);
lean_dec(v_unused_2040_);
v___x_2021_ = v___x_2019_;
v_isShared_2022_ = v_isSharedCheck_2039_;
goto v_resetjp_2020_;
}
else
{
lean_dec(v___x_2019_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2039_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
lean_inc(v_a_2004_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v_a_2004_);
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2004_);
v___x_2024_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
lean_object* v___x_2026_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set_tag(v___x_2017_, 1);
lean_ctor_set(v___x_2017_, 0, v___x_2024_);
v___x_2026_ = v___x_2017_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
lean_object* v___x_2027_; lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
v___x_2027_ = l_Lake_buildAction___redArg___lam__0(v___x_1993_, v___x_2026_, v_a_2003_);
lean_dec_ref(v___x_2026_);
lean_dec(v___x_1993_);
v_a_2028_ = lean_ctor_get(v___x_2027_, 1);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2035_ == 0)
{
lean_object* v_unused_2036_; 
v_unused_2036_ = lean_ctor_get(v___x_2027_, 0);
lean_dec(v_unused_2036_);
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v_a_2004_);
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2004_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
}
else
{
lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2052_; 
lean_inc(v_buildTime_2009_);
lean_inc_ref(v_trace_2008_);
lean_inc_ref(v_log_2005_);
lean_del_object(v___x_2017_);
lean_dec(v_a_2004_);
v_isSharedCheck_2052_ = !lean_is_exclusive(v_a_2003_);
if (v_isSharedCheck_2052_ == 0)
{
lean_object* v_unused_2053_; lean_object* v_unused_2054_; lean_object* v_unused_2055_; 
v_unused_2053_ = lean_ctor_get(v_a_2003_, 2);
lean_dec(v_unused_2053_);
v_unused_2054_ = lean_ctor_get(v_a_2003_, 1);
lean_dec(v_unused_2054_);
v_unused_2055_ = lean_ctor_get(v_a_2003_, 0);
lean_dec(v_unused_2055_);
v___x_2042_ = v_a_2003_;
v_isShared_2043_ = v_isSharedCheck_2052_;
goto v_resetjp_2041_;
}
else
{
lean_dec(v_a_2003_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2052_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v_a_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2050_; 
v_a_2044_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2044_);
lean_dec_ref(v___x_2019_);
v___x_2045_ = lean_io_error_to_string(v_a_2044_);
v___x_2046_ = 3;
v___x_2047_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2047_, 0, v___x_2045_);
lean_ctor_set_uint8(v___x_2047_, sizeof(void*)*1, v___x_2046_);
v___x_2048_ = lean_array_push(v_log_2005_, v___x_2047_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2048_);
v___x_2050_ = v___x_2042_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2048_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_trace_2008_);
lean_ctor_set(v_reuseFailAlloc_2051_, 2, v_buildTime_2009_);
lean_ctor_set_uint8(v_reuseFailAlloc_2051_, sizeof(void*)*3, v_action_2006_);
lean_ctor_set_uint8(v_reuseFailAlloc_2051_, sizeof(void*)*3 + 1, v_wantsRebuild_2007_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
v_a_1998_ = v___x_2011_;
v_a_1999_ = v___x_2050_;
goto v___jp_1997_;
}
}
}
}
}
else
{
lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2069_; 
lean_inc(v_buildTime_2009_);
lean_inc_ref(v_trace_2008_);
lean_inc_ref(v_log_2005_);
lean_dec(v_a_2004_);
lean_dec_ref(v___x_1992_);
v_isSharedCheck_2069_ = !lean_is_exclusive(v_a_2003_);
if (v_isSharedCheck_2069_ == 0)
{
lean_object* v_unused_2070_; lean_object* v_unused_2071_; lean_object* v_unused_2072_; 
v_unused_2070_ = lean_ctor_get(v_a_2003_, 2);
lean_dec(v_unused_2070_);
v_unused_2071_ = lean_ctor_get(v_a_2003_, 1);
lean_dec(v_unused_2071_);
v_unused_2072_ = lean_ctor_get(v_a_2003_, 0);
lean_dec(v_unused_2072_);
v___x_2059_ = v_a_2003_;
v_isShared_2060_ = v_isSharedCheck_2069_;
goto v_resetjp_2058_;
}
else
{
lean_dec(v_a_2003_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2069_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v_a_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2067_; 
v_a_2061_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2061_);
lean_dec_ref(v___x_2015_);
v___x_2062_ = lean_io_error_to_string(v_a_2061_);
v___x_2063_ = 3;
v___x_2064_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2064_, 0, v___x_2062_);
lean_ctor_set_uint8(v___x_2064_, sizeof(void*)*1, v___x_2063_);
v___x_2065_ = lean_array_push(v_log_2005_, v___x_2064_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2065_);
v___x_2067_ = v___x_2059_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v_trace_2008_);
lean_ctor_set(v_reuseFailAlloc_2068_, 2, v_buildTime_2009_);
lean_ctor_set_uint8(v_reuseFailAlloc_2068_, sizeof(void*)*3, v_action_2006_);
lean_ctor_set_uint8(v_reuseFailAlloc_2068_, sizeof(void*)*3 + 1, v_wantsRebuild_2007_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
v_a_1998_ = v___x_2011_;
v_a_1999_ = v___x_2067_;
goto v___jp_1997_;
}
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v_a_2074_; 
lean_dec_ref(v___x_1992_);
lean_dec_ref(v_log_1981_);
lean_dec_ref(v_traceFile_1955_);
lean_dec_ref(v_inst_1953_);
v_a_2073_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_2073_);
v_a_2074_ = lean_ctor_get(v___x_1996_, 1);
lean_inc(v_a_2074_);
lean_dec_ref(v___x_1996_);
v_a_1998_ = v_a_2073_;
v_a_1999_ = v_a_2074_;
goto v___jp_1997_;
}
v___jp_1997_:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v_a_2002_; 
v___x_2000_ = lean_box(0);
v___x_2001_ = l_Lake_buildAction___redArg___lam__0(v___x_1993_, v___x_2000_, v_a_1999_);
lean_dec(v___x_1993_);
v_a_2002_ = lean_ctor_get(v___x_2001_, 1);
lean_inc(v_a_2002_);
lean_dec_ref(v___x_2001_);
v_a_1966_ = v_a_1998_;
v_a_1967_ = v_a_2002_;
goto v___jp_1965_;
}
}
}
else
{
uint8_t v___x_2076_; 
lean_dec_ref(v_a_1958_);
lean_dec_ref(v_build_1956_);
lean_dec_ref(v_inst_1953_);
v___x_2076_ = l_System_FilePath_pathExists(v_traceFile_1955_);
lean_dec_ref(v_traceFile_1955_);
if (v___x_2076_ == 0)
{
lean_dec_ref(v___x_1992_);
lean_del_object(v___x_1987_);
v_log_1970_ = v_log_1981_;
v_action_1971_ = v___x_1990_;
v_wantsRebuild_1972_ = v_noBuild_1989_;
v_trace_1973_ = v_trace_1984_;
v_buildTime_1974_ = v_buildTime_1985_;
goto v___jp_1969_;
}
else
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2077_ = lean_box(0);
v___x_2078_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_2079_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1954_, v___x_2077_, v___x_2078_);
v___x_2080_ = l_Lake_BuildMetadata_writeFile(v___x_1992_, v___x_2079_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_dec_ref(v___x_2080_);
lean_del_object(v___x_1987_);
v_log_1970_ = v_log_1981_;
v_action_1971_ = v___x_1990_;
v_wantsRebuild_1972_ = v_noBuild_1989_;
v_trace_1973_ = v_trace_1984_;
v_buildTime_1974_ = v_buildTime_1985_;
goto v___jp_1969_;
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2088_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_a_2081_);
lean_dec_ref(v___x_2080_);
v___x_2082_ = lean_io_error_to_string(v_a_2081_);
v___x_2083_ = 3;
v___x_2084_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2084_, 0, v___x_2082_);
lean_ctor_set_uint8(v___x_2084_, sizeof(void*)*1, v___x_2083_);
v___x_2085_ = lean_array_get_size(v_log_1981_);
v___x_2086_ = lean_array_push(v_log_1981_, v___x_2084_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 0, v___x_2086_);
v___x_2088_ = v___x_1987_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2086_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_trace_1984_);
lean_ctor_set(v_reuseFailAlloc_2090_, 2, v_buildTime_1985_);
v___x_2088_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
lean_object* v___x_2089_; 
lean_ctor_set_uint8(v___x_2088_, sizeof(void*)*3, v___x_1990_);
lean_ctor_set_uint8(v___x_2088_, sizeof(void*)*3 + 1, v_noBuild_1989_);
v___x_2089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2085_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
return v___x_2089_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___boxed(lean_object* v_inst_2092_, lean_object* v_depTrace_2093_, lean_object* v_traceFile_2094_, lean_object* v_build_2095_, lean_object* v_action_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_){
_start:
{
uint8_t v_action_boxed_2104_; lean_object* v_res_2105_; 
v_action_boxed_2104_ = lean_unbox(v_action_2096_);
v_res_2105_ = l_Lake_buildAction___redArg(v_inst_2092_, v_depTrace_2093_, v_traceFile_2094_, v_build_2095_, v_action_boxed_2104_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
lean_dec_ref(v_a_2101_);
lean_dec(v_a_2100_);
lean_dec(v_a_2099_);
lean_dec(v_a_2098_);
lean_dec_ref(v_depTrace_2093_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction(lean_object* v_00_u03b1_2106_, lean_object* v_inst_2107_, lean_object* v_depTrace_2108_, lean_object* v_traceFile_2109_, lean_object* v_build_2110_, uint8_t v_action_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_){
_start:
{
lean_object* v___x_2119_; 
v___x_2119_ = l_Lake_buildAction___redArg(v_inst_2107_, v_depTrace_2108_, v_traceFile_2109_, v_build_2110_, v_action_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___boxed(lean_object* v_00_u03b1_2120_, lean_object* v_inst_2121_, lean_object* v_depTrace_2122_, lean_object* v_traceFile_2123_, lean_object* v_build_2124_, lean_object* v_action_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_){
_start:
{
uint8_t v_action_boxed_2133_; lean_object* v_res_2134_; 
v_action_boxed_2133_ = lean_unbox(v_action_2125_);
v_res_2134_ = l_Lake_buildAction(v_00_u03b1_2120_, v_inst_2121_, v_depTrace_2122_, v_traceFile_2123_, v_build_2124_, v_action_boxed_2133_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_);
lean_dec_ref(v_a_2130_);
lean_dec(v_a_2129_);
lean_dec(v_a_2128_);
lean_dec(v_a_2127_);
lean_dec_ref(v_depTrace_2122_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg(lean_object* v_inst_2135_, lean_object* v_inst_2136_, lean_object* v_info_2137_, lean_object* v_depTrace_2138_, lean_object* v_traceFile_2139_, lean_object* v_build_2140_, uint8_t v_action_2141_, lean_object* v_oldTrace_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_){
_start:
{
lean_object* v_log_2150_; uint8_t v_action_2151_; uint8_t v_wantsRebuild_2152_; lean_object* v_trace_2153_; lean_object* v_buildTime_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2222_; 
v_log_2150_ = lean_ctor_get(v_a_2148_, 0);
v_action_2151_ = lean_ctor_get_uint8(v_a_2148_, sizeof(void*)*3);
v_wantsRebuild_2152_ = lean_ctor_get_uint8(v_a_2148_, sizeof(void*)*3 + 1);
v_trace_2153_ = lean_ctor_get(v_a_2148_, 1);
v_buildTime_2154_ = lean_ctor_get(v_a_2148_, 2);
v_isSharedCheck_2222_ = !lean_is_exclusive(v_a_2148_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2156_ = v_a_2148_;
v_isShared_2157_ = v_isSharedCheck_2222_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_buildTime_2154_);
lean_inc(v_trace_2153_);
lean_inc(v_log_2150_);
lean_dec(v_a_2148_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2222_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2158_; 
lean_inc_ref(v_traceFile_2139_);
v___x_2158_ = l_Lake_readTraceFile(v_traceFile_2139_, v_log_2150_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v_a_2160_; lean_object* v___x_2162_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2159_);
v_a_2160_ = lean_ctor_get(v___x_2158_, 1);
lean_inc(v_a_2160_);
lean_dec_ref(v___x_2158_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v_a_2160_);
v___x_2162_ = v___x_2156_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2160_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_trace_2153_);
lean_ctor_set(v_reuseFailAlloc_2209_, 2, v_buildTime_2154_);
lean_ctor_set_uint8(v_reuseFailAlloc_2209_, sizeof(void*)*3, v_action_2151_);
lean_ctor_set_uint8(v_reuseFailAlloc_2209_, sizeof(void*)*3 + 1, v_wantsRebuild_2152_);
v___x_2162_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
lean_object* v___x_2163_; 
v___x_2163_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2135_, v_inst_2136_, v_info_2137_, v_depTrace_2138_, v_a_2159_, v_oldTrace_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v___x_2162_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2199_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v_a_2165_ = lean_ctor_get(v___x_2163_, 1);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2167_ = v___x_2163_;
v_isShared_2168_ = v_isSharedCheck_2199_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2199_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
uint8_t v___x_2169_; uint8_t v___x_2170_; uint8_t v___x_2171_; 
v___x_2169_ = 0;
v___x_2170_ = lean_unbox(v_a_2164_);
lean_dec(v_a_2164_);
v___x_2171_ = l_Lake_instDecidableEqOutputStatus(v___x_2170_, v___x_2169_);
if (v___x_2171_ == 0)
{
uint8_t v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2175_; 
lean_dec_ref(v_a_2143_);
lean_dec_ref(v_build_2140_);
lean_dec_ref(v_traceFile_2139_);
v___x_2172_ = 1;
v___x_2173_ = lean_box(v___x_2172_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v___x_2173_);
v___x_2175_ = v___x_2167_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2173_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_a_2165_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
else
{
lean_object* v___f_2177_; lean_object* v___x_2178_; 
lean_del_object(v___x_2167_);
v___f_2177_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2178_ = l_Lake_buildAction___redArg(v___f_2177_, v_depTrace_2138_, v_traceFile_2139_, v_build_2140_, v_action_2141_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2165_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2188_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 1);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2188_ == 0)
{
lean_object* v_unused_2189_; 
v_unused_2189_ = lean_ctor_get(v___x_2178_, 0);
lean_dec(v_unused_2189_);
v___x_2181_ = v___x_2178_;
v_isShared_2182_ = v_isSharedCheck_2188_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2178_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2188_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
uint8_t v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2186_; 
v___x_2183_ = 0;
v___x_2184_ = lean_box(v___x_2183_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v___x_2184_);
v___x_2186_ = v___x_2181_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_a_2179_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
v_a_2190_ = lean_ctor_get(v___x_2178_, 0);
v_a_2191_ = lean_ctor_get(v___x_2178_, 1);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2178_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_inc(v_a_2190_);
lean_dec(v___x_2178_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2190_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
}
}
else
{
lean_object* v_a_2200_; lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_dec_ref(v_a_2143_);
lean_dec_ref(v_build_2140_);
lean_dec_ref(v_traceFile_2139_);
v_a_2200_ = lean_ctor_get(v___x_2163_, 0);
v_a_2201_ = lean_ctor_get(v___x_2163_, 1);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2163_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_inc(v_a_2200_);
lean_dec(v___x_2163_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2200_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
else
{
lean_object* v_a_2210_; lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2221_; 
lean_dec_ref(v_a_2143_);
lean_dec_ref(v_build_2140_);
lean_dec_ref(v_traceFile_2139_);
lean_dec(v_info_2137_);
lean_dec_ref(v_inst_2136_);
lean_dec_ref(v_inst_2135_);
v_a_2210_ = lean_ctor_get(v___x_2158_, 0);
v_a_2211_ = lean_ctor_get(v___x_2158_, 1);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2213_ = v___x_2158_;
v_isShared_2214_ = v_isSharedCheck_2221_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_inc(v_a_2210_);
lean_dec(v___x_2158_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2221_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v_a_2211_);
v___x_2216_ = v___x_2156_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2211_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v_trace_2153_);
lean_ctor_set(v_reuseFailAlloc_2220_, 2, v_buildTime_2154_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, sizeof(void*)*3, v_action_2151_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, sizeof(void*)*3 + 1, v_wantsRebuild_2152_);
v___x_2216_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
lean_object* v___x_2218_; 
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 1, v___x_2216_);
v___x_2218_ = v___x_2213_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2210_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v___x_2216_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg___boxed(lean_object* v_inst_2223_, lean_object* v_inst_2224_, lean_object* v_info_2225_, lean_object* v_depTrace_2226_, lean_object* v_traceFile_2227_, lean_object* v_build_2228_, lean_object* v_action_2229_, lean_object* v_oldTrace_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_){
_start:
{
uint8_t v_action_boxed_2238_; lean_object* v_res_2239_; 
v_action_boxed_2238_ = lean_unbox(v_action_2229_);
v_res_2239_ = l_Lake_buildUnlessUpToDate_x3f___redArg(v_inst_2223_, v_inst_2224_, v_info_2225_, v_depTrace_2226_, v_traceFile_2227_, v_build_2228_, v_action_boxed_2238_, v_oldTrace_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_);
lean_dec_ref(v_a_2235_);
lean_dec(v_a_2234_);
lean_dec(v_a_2233_);
lean_dec(v_a_2232_);
lean_dec_ref(v_oldTrace_2230_);
lean_dec_ref(v_depTrace_2226_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f(lean_object* v_00_u03b9_2240_, lean_object* v_inst_2241_, lean_object* v_inst_2242_, lean_object* v_info_2243_, lean_object* v_depTrace_2244_, lean_object* v_traceFile_2245_, lean_object* v_build_2246_, uint8_t v_action_2247_, lean_object* v_oldTrace_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_){
_start:
{
lean_object* v_log_2256_; uint8_t v_action_2257_; uint8_t v_wantsRebuild_2258_; lean_object* v_trace_2259_; lean_object* v_buildTime_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2328_; 
v_log_2256_ = lean_ctor_get(v_a_2254_, 0);
v_action_2257_ = lean_ctor_get_uint8(v_a_2254_, sizeof(void*)*3);
v_wantsRebuild_2258_ = lean_ctor_get_uint8(v_a_2254_, sizeof(void*)*3 + 1);
v_trace_2259_ = lean_ctor_get(v_a_2254_, 1);
v_buildTime_2260_ = lean_ctor_get(v_a_2254_, 2);
v_isSharedCheck_2328_ = !lean_is_exclusive(v_a_2254_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2262_ = v_a_2254_;
v_isShared_2263_ = v_isSharedCheck_2328_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_buildTime_2260_);
lean_inc(v_trace_2259_);
lean_inc(v_log_2256_);
lean_dec(v_a_2254_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2328_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2264_; 
lean_inc_ref(v_traceFile_2245_);
v___x_2264_ = l_Lake_readTraceFile(v_traceFile_2245_, v_log_2256_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v_a_2266_; lean_object* v___x_2268_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_a_2265_);
v_a_2266_ = lean_ctor_get(v___x_2264_, 1);
lean_inc(v_a_2266_);
lean_dec_ref(v___x_2264_);
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 0, v_a_2266_);
v___x_2268_ = v___x_2262_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2266_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v_trace_2259_);
lean_ctor_set(v_reuseFailAlloc_2315_, 2, v_buildTime_2260_);
lean_ctor_set_uint8(v_reuseFailAlloc_2315_, sizeof(void*)*3, v_action_2257_);
lean_ctor_set_uint8(v_reuseFailAlloc_2315_, sizeof(void*)*3 + 1, v_wantsRebuild_2258_);
v___x_2268_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
lean_object* v___x_2269_; 
v___x_2269_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2241_, v_inst_2242_, v_info_2243_, v_depTrace_2244_, v_a_2265_, v_oldTrace_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v___x_2268_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2305_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
v_a_2271_ = lean_ctor_get(v___x_2269_, 1);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2273_ = v___x_2269_;
v_isShared_2274_ = v_isSharedCheck_2305_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_inc(v_a_2270_);
lean_dec(v___x_2269_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2305_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
uint8_t v___x_2275_; uint8_t v___x_2276_; uint8_t v___x_2277_; 
v___x_2275_ = 0;
v___x_2276_ = lean_unbox(v_a_2270_);
lean_dec(v_a_2270_);
v___x_2277_ = l_Lake_instDecidableEqOutputStatus(v___x_2276_, v___x_2275_);
if (v___x_2277_ == 0)
{
uint8_t v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2281_; 
lean_dec_ref(v_a_2249_);
lean_dec_ref(v_build_2246_);
lean_dec_ref(v_traceFile_2245_);
v___x_2278_ = 1;
v___x_2279_ = lean_box(v___x_2278_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 0, v___x_2279_);
v___x_2281_ = v___x_2273_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2279_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v_a_2271_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
else
{
lean_object* v___f_2283_; lean_object* v___x_2284_; 
lean_del_object(v___x_2273_);
v___f_2283_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2284_ = l_Lake_buildAction___redArg(v___f_2283_, v_depTrace_2244_, v_traceFile_2245_, v_build_2246_, v_action_2247_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2271_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2294_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 1);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2294_ == 0)
{
lean_object* v_unused_2295_; 
v_unused_2295_ = lean_ctor_get(v___x_2284_, 0);
lean_dec(v_unused_2295_);
v___x_2287_ = v___x_2284_;
v_isShared_2288_ = v_isSharedCheck_2294_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2284_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2294_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
uint8_t v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2292_; 
v___x_2289_ = 0;
v___x_2290_ = lean_box(v___x_2289_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v___x_2290_);
v___x_2292_ = v___x_2287_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2290_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_a_2285_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
else
{
lean_object* v_a_2296_; lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
v_a_2296_ = lean_ctor_get(v___x_2284_, 0);
v_a_2297_ = lean_ctor_get(v___x_2284_, 1);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2284_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_inc(v_a_2296_);
lean_dec(v___x_2284_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2296_);
lean_ctor_set(v_reuseFailAlloc_2303_, 1, v_a_2297_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
}
}
else
{
lean_object* v_a_2306_; lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec_ref(v_a_2249_);
lean_dec_ref(v_build_2246_);
lean_dec_ref(v_traceFile_2245_);
v_a_2306_ = lean_ctor_get(v___x_2269_, 0);
v_a_2307_ = lean_ctor_get(v___x_2269_, 1);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2269_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_inc(v_a_2306_);
lean_dec(v___x_2269_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2306_);
lean_ctor_set(v_reuseFailAlloc_2313_, 1, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2327_; 
lean_dec_ref(v_a_2249_);
lean_dec_ref(v_build_2246_);
lean_dec_ref(v_traceFile_2245_);
lean_dec(v_info_2243_);
lean_dec_ref(v_inst_2242_);
lean_dec_ref(v_inst_2241_);
v_a_2316_ = lean_ctor_get(v___x_2264_, 0);
v_a_2317_ = lean_ctor_get(v___x_2264_, 1);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2319_ = v___x_2264_;
v_isShared_2320_ = v_isSharedCheck_2327_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_inc(v_a_2316_);
lean_dec(v___x_2264_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2327_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 0, v_a_2317_);
v___x_2322_ = v___x_2262_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2317_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v_trace_2259_);
lean_ctor_set(v_reuseFailAlloc_2326_, 2, v_buildTime_2260_);
lean_ctor_set_uint8(v_reuseFailAlloc_2326_, sizeof(void*)*3, v_action_2257_);
lean_ctor_set_uint8(v_reuseFailAlloc_2326_, sizeof(void*)*3 + 1, v_wantsRebuild_2258_);
v___x_2322_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
lean_object* v___x_2324_; 
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 1, v___x_2322_);
v___x_2324_ = v___x_2319_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2316_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v___x_2322_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___boxed(lean_object* v_00_u03b9_2329_, lean_object* v_inst_2330_, lean_object* v_inst_2331_, lean_object* v_info_2332_, lean_object* v_depTrace_2333_, lean_object* v_traceFile_2334_, lean_object* v_build_2335_, lean_object* v_action_2336_, lean_object* v_oldTrace_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
uint8_t v_action_boxed_2345_; lean_object* v_res_2346_; 
v_action_boxed_2345_ = lean_unbox(v_action_2336_);
v_res_2346_ = l_Lake_buildUnlessUpToDate_x3f(v_00_u03b9_2329_, v_inst_2330_, v_inst_2331_, v_info_2332_, v_depTrace_2333_, v_traceFile_2334_, v_build_2335_, v_action_boxed_2345_, v_oldTrace_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_);
lean_dec_ref(v_a_2342_);
lean_dec(v_a_2341_);
lean_dec(v_a_2340_);
lean_dec(v_a_2339_);
lean_dec_ref(v_oldTrace_2337_);
lean_dec_ref(v_depTrace_2333_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg(lean_object* v_inst_2347_, lean_object* v_inst_2348_, lean_object* v_info_2349_, lean_object* v_depTrace_2350_, lean_object* v_traceFile_2351_, lean_object* v_build_2352_, uint8_t v_action_2353_, lean_object* v_oldTrace_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v_a_2363_; lean_object* v_a_2364_; lean_object* v_log_2366_; uint8_t v_action_2367_; uint8_t v_wantsRebuild_2368_; lean_object* v_trace_2369_; lean_object* v_buildTime_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2408_; 
v_log_2366_ = lean_ctor_get(v_a_2360_, 0);
v_action_2367_ = lean_ctor_get_uint8(v_a_2360_, sizeof(void*)*3);
v_wantsRebuild_2368_ = lean_ctor_get_uint8(v_a_2360_, sizeof(void*)*3 + 1);
v_trace_2369_ = lean_ctor_get(v_a_2360_, 1);
v_buildTime_2370_ = lean_ctor_get(v_a_2360_, 2);
v_isSharedCheck_2408_ = !lean_is_exclusive(v_a_2360_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2372_ = v_a_2360_;
v_isShared_2373_ = v_isSharedCheck_2408_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_buildTime_2370_);
lean_inc(v_trace_2369_);
lean_inc(v_log_2366_);
lean_dec(v_a_2360_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2408_;
goto v_resetjp_2371_;
}
v___jp_2362_:
{
lean_object* v___x_2365_; 
v___x_2365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2365_, 0, v_a_2363_);
lean_ctor_set(v___x_2365_, 1, v_a_2364_);
return v___x_2365_;
}
v_resetjp_2371_:
{
lean_object* v___x_2374_; 
lean_inc_ref(v_traceFile_2351_);
v___x_2374_ = l_Lake_readTraceFile(v_traceFile_2351_, v_log_2366_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v_a_2376_; lean_object* v___x_2378_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
v_a_2376_ = lean_ctor_get(v___x_2374_, 1);
lean_inc(v_a_2376_);
lean_dec_ref(v___x_2374_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 0, v_a_2376_);
v___x_2378_ = v___x_2372_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2376_);
lean_ctor_set(v_reuseFailAlloc_2402_, 1, v_trace_2369_);
lean_ctor_set(v_reuseFailAlloc_2402_, 2, v_buildTime_2370_);
lean_ctor_set_uint8(v_reuseFailAlloc_2402_, sizeof(void*)*3, v_action_2367_);
lean_ctor_set_uint8(v_reuseFailAlloc_2402_, sizeof(void*)*3 + 1, v_wantsRebuild_2368_);
v___x_2378_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2347_, v_inst_2348_, v_info_2349_, v_depTrace_2350_, v_a_2375_, v_oldTrace_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v___x_2378_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2399_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
v_a_2381_ = lean_ctor_get(v___x_2379_, 1);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2383_ = v___x_2379_;
v_isShared_2384_ = v_isSharedCheck_2399_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_inc(v_a_2380_);
lean_dec(v___x_2379_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2399_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2385_; lean_object* v_a_2387_; uint8_t v___x_2391_; uint8_t v___x_2392_; uint8_t v___x_2393_; 
v___x_2385_ = lean_box(0);
v___x_2391_ = 0;
v___x_2392_ = lean_unbox(v_a_2380_);
lean_dec(v_a_2380_);
v___x_2393_ = l_Lake_instDecidableEqOutputStatus(v___x_2392_, v___x_2391_);
if (v___x_2393_ == 0)
{
lean_dec_ref(v_a_2355_);
lean_dec_ref(v_build_2352_);
lean_dec_ref(v_traceFile_2351_);
v_a_2387_ = v_a_2381_;
goto v___jp_2386_;
}
else
{
lean_object* v___f_2394_; lean_object* v___x_2395_; 
v___f_2394_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2395_ = l_Lake_buildAction___redArg(v___f_2394_, v_depTrace_2350_, v_traceFile_2351_, v_build_2352_, v_action_2353_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2381_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 1);
lean_inc(v_a_2396_);
lean_dec_ref(v___x_2395_);
v_a_2387_ = v_a_2396_;
goto v___jp_2386_;
}
else
{
lean_object* v_a_2397_; lean_object* v_a_2398_; 
lean_del_object(v___x_2383_);
v_a_2397_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_a_2397_);
v_a_2398_ = lean_ctor_get(v___x_2395_, 1);
lean_inc(v_a_2398_);
lean_dec_ref(v___x_2395_);
v_a_2363_ = v_a_2397_;
v_a_2364_ = v_a_2398_;
goto v___jp_2362_;
}
}
v___jp_2386_:
{
lean_object* v___x_2389_; 
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 1, v_a_2387_);
lean_ctor_set(v___x_2383_, 0, v___x_2385_);
v___x_2389_ = v___x_2383_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v___x_2385_);
lean_ctor_set(v_reuseFailAlloc_2390_, 1, v_a_2387_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
else
{
lean_object* v_a_2400_; lean_object* v_a_2401_; 
lean_dec_ref(v_a_2355_);
lean_dec_ref(v_build_2352_);
lean_dec_ref(v_traceFile_2351_);
v_a_2400_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_a_2400_);
v_a_2401_ = lean_ctor_get(v___x_2379_, 1);
lean_inc(v_a_2401_);
lean_dec_ref(v___x_2379_);
v_a_2363_ = v_a_2400_;
v_a_2364_ = v_a_2401_;
goto v___jp_2362_;
}
}
}
else
{
lean_object* v_a_2403_; lean_object* v_a_2404_; lean_object* v___x_2406_; 
lean_dec_ref(v_a_2355_);
lean_dec_ref(v_build_2352_);
lean_dec_ref(v_traceFile_2351_);
lean_dec(v_info_2349_);
lean_dec_ref(v_inst_2348_);
lean_dec_ref(v_inst_2347_);
v_a_2403_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2403_);
v_a_2404_ = lean_ctor_get(v___x_2374_, 1);
lean_inc(v_a_2404_);
lean_dec_ref(v___x_2374_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 0, v_a_2404_);
v___x_2406_ = v___x_2372_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2404_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v_trace_2369_);
lean_ctor_set(v_reuseFailAlloc_2407_, 2, v_buildTime_2370_);
lean_ctor_set_uint8(v_reuseFailAlloc_2407_, sizeof(void*)*3, v_action_2367_);
lean_ctor_set_uint8(v_reuseFailAlloc_2407_, sizeof(void*)*3 + 1, v_wantsRebuild_2368_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
v_a_2363_ = v_a_2403_;
v_a_2364_ = v___x_2406_;
goto v___jp_2362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg___boxed(lean_object* v_inst_2409_, lean_object* v_inst_2410_, lean_object* v_info_2411_, lean_object* v_depTrace_2412_, lean_object* v_traceFile_2413_, lean_object* v_build_2414_, lean_object* v_action_2415_, lean_object* v_oldTrace_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
uint8_t v_action_boxed_2424_; lean_object* v_res_2425_; 
v_action_boxed_2424_ = lean_unbox(v_action_2415_);
v_res_2425_ = l_Lake_buildUnlessUpToDate___redArg(v_inst_2409_, v_inst_2410_, v_info_2411_, v_depTrace_2412_, v_traceFile_2413_, v_build_2414_, v_action_boxed_2424_, v_oldTrace_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
lean_dec_ref(v_a_2421_);
lean_dec(v_a_2420_);
lean_dec(v_a_2419_);
lean_dec(v_a_2418_);
lean_dec_ref(v_oldTrace_2416_);
lean_dec_ref(v_depTrace_2412_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate(lean_object* v_00_u03b9_2426_, lean_object* v_inst_2427_, lean_object* v_inst_2428_, lean_object* v_info_2429_, lean_object* v_depTrace_2430_, lean_object* v_traceFile_2431_, lean_object* v_build_2432_, uint8_t v_action_2433_, lean_object* v_oldTrace_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v_a_2443_; lean_object* v_a_2444_; lean_object* v_log_2446_; uint8_t v_action_2447_; uint8_t v_wantsRebuild_2448_; lean_object* v_trace_2449_; lean_object* v_buildTime_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2488_; 
v_log_2446_ = lean_ctor_get(v_a_2440_, 0);
v_action_2447_ = lean_ctor_get_uint8(v_a_2440_, sizeof(void*)*3);
v_wantsRebuild_2448_ = lean_ctor_get_uint8(v_a_2440_, sizeof(void*)*3 + 1);
v_trace_2449_ = lean_ctor_get(v_a_2440_, 1);
v_buildTime_2450_ = lean_ctor_get(v_a_2440_, 2);
v_isSharedCheck_2488_ = !lean_is_exclusive(v_a_2440_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2452_ = v_a_2440_;
v_isShared_2453_ = v_isSharedCheck_2488_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_buildTime_2450_);
lean_inc(v_trace_2449_);
lean_inc(v_log_2446_);
lean_dec(v_a_2440_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2488_;
goto v_resetjp_2451_;
}
v___jp_2442_:
{
lean_object* v___x_2445_; 
v___x_2445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2445_, 0, v_a_2443_);
lean_ctor_set(v___x_2445_, 1, v_a_2444_);
return v___x_2445_;
}
v_resetjp_2451_:
{
lean_object* v___x_2454_; 
lean_inc_ref(v_traceFile_2431_);
v___x_2454_ = l_Lake_readTraceFile(v_traceFile_2431_, v_log_2446_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v_a_2456_; lean_object* v___x_2458_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2455_);
v_a_2456_ = lean_ctor_get(v___x_2454_, 1);
lean_inc(v_a_2456_);
lean_dec_ref(v___x_2454_);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 0, v_a_2456_);
v___x_2458_ = v___x_2452_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2456_);
lean_ctor_set(v_reuseFailAlloc_2482_, 1, v_trace_2449_);
lean_ctor_set(v_reuseFailAlloc_2482_, 2, v_buildTime_2450_);
lean_ctor_set_uint8(v_reuseFailAlloc_2482_, sizeof(void*)*3, v_action_2447_);
lean_ctor_set_uint8(v_reuseFailAlloc_2482_, sizeof(void*)*3 + 1, v_wantsRebuild_2448_);
v___x_2458_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2427_, v_inst_2428_, v_info_2429_, v_depTrace_2430_, v_a_2455_, v_oldTrace_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v___x_2458_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2479_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
v_a_2461_ = lean_ctor_get(v___x_2459_, 1);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2463_ = v___x_2459_;
v_isShared_2464_ = v_isSharedCheck_2479_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_inc(v_a_2460_);
lean_dec(v___x_2459_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2479_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; lean_object* v_a_2467_; uint8_t v___x_2471_; uint8_t v___x_2472_; uint8_t v___x_2473_; 
v___x_2465_ = lean_box(0);
v___x_2471_ = 0;
v___x_2472_ = lean_unbox(v_a_2460_);
lean_dec(v_a_2460_);
v___x_2473_ = l_Lake_instDecidableEqOutputStatus(v___x_2472_, v___x_2471_);
if (v___x_2473_ == 0)
{
lean_dec_ref(v_a_2435_);
lean_dec_ref(v_build_2432_);
lean_dec_ref(v_traceFile_2431_);
v_a_2467_ = v_a_2461_;
goto v___jp_2466_;
}
else
{
lean_object* v___f_2474_; lean_object* v___x_2475_; 
v___f_2474_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2475_ = l_Lake_buildAction___redArg(v___f_2474_, v_depTrace_2430_, v_traceFile_2431_, v_build_2432_, v_action_2433_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2461_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 1);
lean_inc(v_a_2476_);
lean_dec_ref(v___x_2475_);
v_a_2467_ = v_a_2476_;
goto v___jp_2466_;
}
else
{
lean_object* v_a_2477_; lean_object* v_a_2478_; 
lean_del_object(v___x_2463_);
v_a_2477_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_a_2477_);
v_a_2478_ = lean_ctor_get(v___x_2475_, 1);
lean_inc(v_a_2478_);
lean_dec_ref(v___x_2475_);
v_a_2443_ = v_a_2477_;
v_a_2444_ = v_a_2478_;
goto v___jp_2442_;
}
}
v___jp_2466_:
{
lean_object* v___x_2469_; 
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 1, v_a_2467_);
lean_ctor_set(v___x_2463_, 0, v___x_2465_);
v___x_2469_ = v___x_2463_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2465_);
lean_ctor_set(v_reuseFailAlloc_2470_, 1, v_a_2467_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
else
{
lean_object* v_a_2480_; lean_object* v_a_2481_; 
lean_dec_ref(v_a_2435_);
lean_dec_ref(v_build_2432_);
lean_dec_ref(v_traceFile_2431_);
v_a_2480_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_a_2480_);
v_a_2481_ = lean_ctor_get(v___x_2459_, 1);
lean_inc(v_a_2481_);
lean_dec_ref(v___x_2459_);
v_a_2443_ = v_a_2480_;
v_a_2444_ = v_a_2481_;
goto v___jp_2442_;
}
}
}
else
{
lean_object* v_a_2483_; lean_object* v_a_2484_; lean_object* v___x_2486_; 
lean_dec_ref(v_a_2435_);
lean_dec_ref(v_build_2432_);
lean_dec_ref(v_traceFile_2431_);
lean_dec(v_info_2429_);
lean_dec_ref(v_inst_2428_);
lean_dec_ref(v_inst_2427_);
v_a_2483_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2483_);
v_a_2484_ = lean_ctor_get(v___x_2454_, 1);
lean_inc(v_a_2484_);
lean_dec_ref(v___x_2454_);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 0, v_a_2484_);
v___x_2486_ = v___x_2452_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2484_);
lean_ctor_set(v_reuseFailAlloc_2487_, 1, v_trace_2449_);
lean_ctor_set(v_reuseFailAlloc_2487_, 2, v_buildTime_2450_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, sizeof(void*)*3, v_action_2447_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, sizeof(void*)*3 + 1, v_wantsRebuild_2448_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
v_a_2443_ = v_a_2483_;
v_a_2444_ = v___x_2486_;
goto v___jp_2442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___boxed(lean_object* v_00_u03b9_2489_, lean_object* v_inst_2490_, lean_object* v_inst_2491_, lean_object* v_info_2492_, lean_object* v_depTrace_2493_, lean_object* v_traceFile_2494_, lean_object* v_build_2495_, lean_object* v_action_2496_, lean_object* v_oldTrace_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_){
_start:
{
uint8_t v_action_boxed_2505_; lean_object* v_res_2506_; 
v_action_boxed_2505_ = lean_unbox(v_action_2496_);
v_res_2506_ = l_Lake_buildUnlessUpToDate(v_00_u03b9_2489_, v_inst_2490_, v_inst_2491_, v_info_2492_, v_depTrace_2493_, v_traceFile_2494_, v_build_2495_, v_action_boxed_2505_, v_oldTrace_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
lean_dec_ref(v_a_2502_);
lean_dec(v_a_2501_);
lean_dec(v_a_2500_);
lean_dec(v_a_2499_);
lean_dec_ref(v_oldTrace_2497_);
lean_dec_ref(v_depTrace_2493_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFileHash(lean_object* v_file_2508_, uint64_t v_hash_2509_){
_start:
{
lean_object* v___x_2511_; lean_object* v_hashFile_2512_; lean_object* v___x_2513_; 
v___x_2511_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
v_hashFile_2512_ = lean_string_append(v_file_2508_, v___x_2511_);
lean_inc_ref(v_hashFile_2512_);
v___x_2513_ = l_Lake_createParentDirs(v_hashFile_2512_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
lean_dec_ref(v___x_2513_);
v___x_2514_ = l_Lake_Hash_hex(v_hash_2509_);
v___x_2515_ = l_IO_FS_writeFile(v_hashFile_2512_, v___x_2514_);
lean_dec_ref(v___x_2514_);
lean_dec_ref(v_hashFile_2512_);
return v___x_2515_;
}
else
{
lean_dec_ref(v_hashFile_2512_);
return v___x_2513_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_writeFileHash___boxed(lean_object* v_file_2516_, lean_object* v_hash_2517_, lean_object* v_a_2518_){
_start:
{
uint64_t v_hash_boxed_2519_; lean_object* v_res_2520_; 
v_hash_boxed_2519_ = lean_unbox_uint64(v_hash_2517_);
lean_dec_ref(v_hash_2517_);
v_res_2520_ = l_Lake_writeFileHash(v_file_2516_, v_hash_boxed_2519_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object* v_file_2521_, uint8_t v_text_2522_){
_start:
{
lean_object* v___y_2525_; 
if (v_text_2522_ == 0)
{
lean_object* v___x_2537_; 
v___x_2537_ = l_Lake_computeBinFileHash(v_file_2521_);
v___y_2525_ = v___x_2537_;
goto v___jp_2524_;
}
else
{
lean_object* v___x_2538_; 
v___x_2538_ = l_Lake_computeTextFileHash(v_file_2521_);
v___y_2525_ = v___x_2538_;
goto v___jp_2524_;
}
v___jp_2524_:
{
if (lean_obj_tag(v___y_2525_) == 0)
{
lean_object* v_a_2526_; uint64_t v___x_2527_; lean_object* v___x_2528_; 
v_a_2526_ = lean_ctor_get(v___y_2525_, 0);
lean_inc(v_a_2526_);
lean_dec_ref(v___y_2525_);
v___x_2527_ = lean_unbox_uint64(v_a_2526_);
lean_dec(v_a_2526_);
v___x_2528_ = l_Lake_writeFileHash(v_file_2521_, v___x_2527_);
return v___x_2528_;
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
lean_dec_ref(v_file_2521_);
v_a_2529_ = lean_ctor_get(v___y_2525_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___y_2525_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2531_ = v___y_2525_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___y_2525_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2529_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash___boxed(lean_object* v_file_2539_, lean_object* v_text_2540_, lean_object* v_a_2541_){
_start:
{
uint8_t v_text_boxed_2542_; lean_object* v_res_2543_; 
v_text_boxed_2542_ = lean_unbox(v_text_2540_);
v_res_2543_ = l_Lake_cacheFileHash(v_file_2539_, v_text_boxed_2542_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l_Lake_clearFileHash(lean_object* v_file_2544_){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2546_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
v___x_2547_ = lean_string_append(v_file_2544_, v___x_2546_);
v___x_2548_ = l_Lake_removeFileIfExists(v___x_2547_);
lean_dec_ref(v___x_2547_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lake_clearFileHash___boxed(lean_object* v_file_2549_, lean_object* v_a_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_Lake_clearFileHash(v_file_2549_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg(lean_object* v_file_2552_, uint8_t v_text_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_){
_start:
{
lean_object* v_toBuildConfig_2557_; uint8_t v_trustHash_2558_; lean_object* v___x_2559_; lean_object* v_hashFile_2560_; lean_object* v___y_2562_; lean_object* v___y_2563_; uint8_t v___y_2564_; lean_object* v___y_2565_; uint8_t v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2600_; 
v_toBuildConfig_2557_ = lean_ctor_get(v_a_2554_, 0);
v_trustHash_2558_ = lean_ctor_get_uint8(v_toBuildConfig_2557_, sizeof(void*)*2 + 1);
v___x_2559_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
lean_inc_ref(v_file_2552_);
v_hashFile_2560_ = lean_string_append(v_file_2552_, v___x_2559_);
if (v_trustHash_2558_ == 0)
{
v___y_2600_ = v_a_2555_;
goto v___jp_2599_;
}
else
{
lean_object* v___x_2613_; 
v___x_2613_ = l_Lake_Hash_load_x3f(v_hashFile_2560_);
if (lean_obj_tag(v___x_2613_) == 1)
{
lean_object* v_val_2614_; lean_object* v___x_2615_; 
lean_dec_ref(v_hashFile_2560_);
lean_dec_ref(v_file_2552_);
v_val_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_val_2614_);
lean_dec_ref(v___x_2613_);
v___x_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2615_, 0, v_val_2614_);
lean_ctor_set(v___x_2615_, 1, v_a_2555_);
return v___x_2615_;
}
else
{
lean_dec(v___x_2613_);
v___y_2600_ = v_a_2555_;
goto v___jp_2599_;
}
}
v___jp_2561_:
{
if (lean_obj_tag(v___y_2567_) == 0)
{
lean_object* v_a_2568_; lean_object* v___x_2569_; 
v_a_2568_ = lean_ctor_get(v___y_2567_, 0);
lean_inc(v_a_2568_);
lean_dec_ref(v___y_2567_);
lean_inc_ref(v_hashFile_2560_);
v___x_2569_ = l_Lake_createParentDirs(v_hashFile_2560_);
if (lean_obj_tag(v___x_2569_) == 0)
{
uint64_t v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
lean_dec_ref(v___x_2569_);
v___x_2570_ = lean_unbox_uint64(v_a_2568_);
v___x_2571_ = l_Lake_Hash_hex(v___x_2570_);
v___x_2572_ = l_IO_FS_writeFile(v_hashFile_2560_, v___x_2571_);
lean_dec_ref(v___x_2571_);
lean_dec_ref(v_hashFile_2560_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
lean_dec_ref(v___x_2572_);
v___x_2573_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2573_, 0, v___y_2563_);
lean_ctor_set(v___x_2573_, 1, v___y_2562_);
lean_ctor_set(v___x_2573_, 2, v___y_2565_);
lean_ctor_set_uint8(v___x_2573_, sizeof(void*)*3, v___y_2564_);
lean_ctor_set_uint8(v___x_2573_, sizeof(void*)*3 + 1, v___y_2566_);
v___x_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2574_, 0, v_a_2568_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
return v___x_2574_;
}
else
{
lean_object* v_a_2575_; lean_object* v___x_2576_; uint8_t v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
lean_dec(v_a_2568_);
v_a_2575_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_a_2575_);
lean_dec_ref(v___x_2572_);
v___x_2576_ = lean_io_error_to_string(v_a_2575_);
v___x_2577_ = 3;
v___x_2578_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2578_, 0, v___x_2576_);
lean_ctor_set_uint8(v___x_2578_, sizeof(void*)*1, v___x_2577_);
v___x_2579_ = lean_array_get_size(v___y_2563_);
v___x_2580_ = lean_array_push(v___y_2563_, v___x_2578_);
v___x_2581_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2581_, 0, v___x_2580_);
lean_ctor_set(v___x_2581_, 1, v___y_2562_);
lean_ctor_set(v___x_2581_, 2, v___y_2565_);
lean_ctor_set_uint8(v___x_2581_, sizeof(void*)*3, v___y_2564_);
lean_ctor_set_uint8(v___x_2581_, sizeof(void*)*3 + 1, v___y_2566_);
v___x_2582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2579_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
return v___x_2582_;
}
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2584_; uint8_t v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
lean_dec(v_a_2568_);
lean_dec_ref(v_hashFile_2560_);
v_a_2583_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_a_2583_);
lean_dec_ref(v___x_2569_);
v___x_2584_ = lean_io_error_to_string(v_a_2583_);
v___x_2585_ = 3;
v___x_2586_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2586_, 0, v___x_2584_);
lean_ctor_set_uint8(v___x_2586_, sizeof(void*)*1, v___x_2585_);
v___x_2587_ = lean_array_get_size(v___y_2563_);
v___x_2588_ = lean_array_push(v___y_2563_, v___x_2586_);
v___x_2589_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2589_, 0, v___x_2588_);
lean_ctor_set(v___x_2589_, 1, v___y_2562_);
lean_ctor_set(v___x_2589_, 2, v___y_2565_);
lean_ctor_set_uint8(v___x_2589_, sizeof(void*)*3, v___y_2564_);
lean_ctor_set_uint8(v___x_2589_, sizeof(void*)*3 + 1, v___y_2566_);
v___x_2590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2587_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
return v___x_2590_;
}
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
lean_dec_ref(v_hashFile_2560_);
v_a_2591_ = lean_ctor_get(v___y_2567_, 0);
lean_inc(v_a_2591_);
lean_dec_ref(v___y_2567_);
v___x_2592_ = lean_io_error_to_string(v_a_2591_);
v___x_2593_ = 3;
v___x_2594_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2594_, 0, v___x_2592_);
lean_ctor_set_uint8(v___x_2594_, sizeof(void*)*1, v___x_2593_);
v___x_2595_ = lean_array_get_size(v___y_2563_);
v___x_2596_ = lean_array_push(v___y_2563_, v___x_2594_);
v___x_2597_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2597_, 0, v___x_2596_);
lean_ctor_set(v___x_2597_, 1, v___y_2562_);
lean_ctor_set(v___x_2597_, 2, v___y_2565_);
lean_ctor_set_uint8(v___x_2597_, sizeof(void*)*3, v___y_2564_);
lean_ctor_set_uint8(v___x_2597_, sizeof(void*)*3 + 1, v___y_2566_);
v___x_2598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2595_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
return v___x_2598_;
}
}
v___jp_2599_:
{
if (v_text_2553_ == 0)
{
lean_object* v_log_2601_; uint8_t v_action_2602_; uint8_t v_wantsRebuild_2603_; lean_object* v_trace_2604_; lean_object* v_buildTime_2605_; lean_object* v___x_2606_; 
v_log_2601_ = lean_ctor_get(v___y_2600_, 0);
lean_inc_ref(v_log_2601_);
v_action_2602_ = lean_ctor_get_uint8(v___y_2600_, sizeof(void*)*3);
v_wantsRebuild_2603_ = lean_ctor_get_uint8(v___y_2600_, sizeof(void*)*3 + 1);
v_trace_2604_ = lean_ctor_get(v___y_2600_, 1);
lean_inc_ref(v_trace_2604_);
v_buildTime_2605_ = lean_ctor_get(v___y_2600_, 2);
lean_inc(v_buildTime_2605_);
lean_dec_ref(v___y_2600_);
v___x_2606_ = l_Lake_computeBinFileHash(v_file_2552_);
lean_dec_ref(v_file_2552_);
v___y_2562_ = v_trace_2604_;
v___y_2563_ = v_log_2601_;
v___y_2564_ = v_action_2602_;
v___y_2565_ = v_buildTime_2605_;
v___y_2566_ = v_wantsRebuild_2603_;
v___y_2567_ = v___x_2606_;
goto v___jp_2561_;
}
else
{
lean_object* v_log_2607_; uint8_t v_action_2608_; uint8_t v_wantsRebuild_2609_; lean_object* v_trace_2610_; lean_object* v_buildTime_2611_; lean_object* v___x_2612_; 
v_log_2607_ = lean_ctor_get(v___y_2600_, 0);
lean_inc_ref(v_log_2607_);
v_action_2608_ = lean_ctor_get_uint8(v___y_2600_, sizeof(void*)*3);
v_wantsRebuild_2609_ = lean_ctor_get_uint8(v___y_2600_, sizeof(void*)*3 + 1);
v_trace_2610_ = lean_ctor_get(v___y_2600_, 1);
lean_inc_ref(v_trace_2610_);
v_buildTime_2611_ = lean_ctor_get(v___y_2600_, 2);
lean_inc(v_buildTime_2611_);
lean_dec_ref(v___y_2600_);
v___x_2612_ = l_Lake_computeTextFileHash(v_file_2552_);
lean_dec_ref(v_file_2552_);
v___y_2562_ = v_trace_2610_;
v___y_2563_ = v_log_2607_;
v___y_2564_ = v_action_2608_;
v___y_2565_ = v_buildTime_2611_;
v___y_2566_ = v_wantsRebuild_2609_;
v___y_2567_ = v___x_2612_;
goto v___jp_2561_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg___boxed(lean_object* v_file_2616_, lean_object* v_text_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_){
_start:
{
uint8_t v_text_boxed_2621_; lean_object* v_res_2622_; 
v_text_boxed_2621_ = lean_unbox(v_text_2617_);
v_res_2622_ = l_Lake_fetchFileHash___redArg(v_file_2616_, v_text_boxed_2621_, v_a_2618_, v_a_2619_);
lean_dec_ref(v_a_2618_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash(lean_object* v_file_2623_, uint8_t v_text_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = l_Lake_fetchFileHash___redArg(v_file_2623_, v_text_2624_, v_a_2629_, v_a_2630_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___boxed(lean_object* v_file_2633_, lean_object* v_text_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_){
_start:
{
uint8_t v_text_boxed_2642_; lean_object* v_res_2643_; 
v_text_boxed_2642_ = lean_unbox(v_text_2634_);
v_res_2643_ = l_Lake_fetchFileHash(v_file_2633_, v_text_boxed_2642_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_);
lean_dec_ref(v_a_2639_);
lean_dec(v_a_2638_);
lean_dec(v_a_2637_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg(lean_object* v_file_2644_, uint8_t v_text_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_){
_start:
{
lean_object* v___x_2649_; 
lean_inc_ref(v_file_2644_);
v___x_2649_ = l_Lake_fetchFileHash___redArg(v_file_2644_, v_text_2645_, v_a_2646_, v_a_2647_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2688_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 1);
v_a_2651_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2653_ = v___x_2649_;
v_isShared_2654_ = v_isSharedCheck_2688_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2650_);
lean_inc(v_a_2651_);
lean_dec(v___x_2649_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2688_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v_log_2655_; uint8_t v_action_2656_; uint8_t v_wantsRebuild_2657_; lean_object* v_trace_2658_; lean_object* v_buildTime_2659_; lean_object* v___x_2660_; 
v_log_2655_ = lean_ctor_get(v_a_2650_, 0);
v_action_2656_ = lean_ctor_get_uint8(v_a_2650_, sizeof(void*)*3);
v_wantsRebuild_2657_ = lean_ctor_get_uint8(v_a_2650_, sizeof(void*)*3 + 1);
v_trace_2658_ = lean_ctor_get(v_a_2650_, 1);
v_buildTime_2659_ = lean_ctor_get(v_a_2650_, 2);
v___x_2660_ = lean_io_metadata(v_file_2644_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v_a_2661_; lean_object* v_modified_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; uint64_t v___x_2665_; lean_object* v___x_2667_; 
v_a_2661_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_a_2661_);
lean_dec_ref(v___x_2660_);
v_modified_2662_ = lean_ctor_get(v_a_2661_, 1);
lean_inc_ref(v_modified_2662_);
lean_dec(v_a_2661_);
v___x_2663_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_2664_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_2664_, 0, v_file_2644_);
lean_ctor_set(v___x_2664_, 1, v___x_2663_);
lean_ctor_set(v___x_2664_, 2, v_modified_2662_);
v___x_2665_ = lean_unbox_uint64(v_a_2651_);
lean_dec(v_a_2651_);
lean_ctor_set_uint64(v___x_2664_, sizeof(void*)*3, v___x_2665_);
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 0, v___x_2664_);
v___x_2667_ = v___x_2653_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2668_, 1, v_a_2650_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
else
{
lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2684_; 
lean_inc(v_buildTime_2659_);
lean_inc_ref(v_trace_2658_);
lean_inc_ref(v_log_2655_);
lean_dec(v_a_2651_);
lean_dec_ref(v_file_2644_);
v_isSharedCheck_2684_ = !lean_is_exclusive(v_a_2650_);
if (v_isSharedCheck_2684_ == 0)
{
lean_object* v_unused_2685_; lean_object* v_unused_2686_; lean_object* v_unused_2687_; 
v_unused_2685_ = lean_ctor_get(v_a_2650_, 2);
lean_dec(v_unused_2685_);
v_unused_2686_ = lean_ctor_get(v_a_2650_, 1);
lean_dec(v_unused_2686_);
v_unused_2687_ = lean_ctor_get(v_a_2650_, 0);
lean_dec(v_unused_2687_);
v___x_2670_ = v_a_2650_;
v_isShared_2671_ = v_isSharedCheck_2684_;
goto v_resetjp_2669_;
}
else
{
lean_dec(v_a_2650_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2684_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v_a_2672_; lean_object* v___x_2673_; uint8_t v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2679_; 
v_a_2672_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_a_2672_);
lean_dec_ref(v___x_2660_);
v___x_2673_ = lean_io_error_to_string(v_a_2672_);
v___x_2674_ = 3;
v___x_2675_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2675_, 0, v___x_2673_);
lean_ctor_set_uint8(v___x_2675_, sizeof(void*)*1, v___x_2674_);
v___x_2676_ = lean_array_get_size(v_log_2655_);
v___x_2677_ = lean_array_push(v_log_2655_, v___x_2675_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v___x_2677_);
v___x_2679_ = v___x_2670_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2677_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v_trace_2658_);
lean_ctor_set(v_reuseFailAlloc_2683_, 2, v_buildTime_2659_);
lean_ctor_set_uint8(v_reuseFailAlloc_2683_, sizeof(void*)*3, v_action_2656_);
lean_ctor_set_uint8(v_reuseFailAlloc_2683_, sizeof(void*)*3 + 1, v_wantsRebuild_2657_);
v___x_2679_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
lean_object* v___x_2681_; 
if (v_isShared_2654_ == 0)
{
lean_ctor_set_tag(v___x_2653_, 1);
lean_ctor_set(v___x_2653_, 1, v___x_2679_);
lean_ctor_set(v___x_2653_, 0, v___x_2676_);
v___x_2681_ = v___x_2653_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2676_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v___x_2679_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
}
}
else
{
lean_object* v_a_2689_; lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
lean_dec_ref(v_file_2644_);
v_a_2689_ = lean_ctor_get(v___x_2649_, 0);
v_a_2690_ = lean_ctor_get(v___x_2649_, 1);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2649_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_inc(v_a_2689_);
lean_dec(v___x_2649_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2689_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v_a_2690_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg___boxed(lean_object* v_file_2698_, lean_object* v_text_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_){
_start:
{
uint8_t v_text_boxed_2703_; lean_object* v_res_2704_; 
v_text_boxed_2703_ = lean_unbox(v_text_2699_);
v_res_2704_ = l_Lake_fetchFileTrace___redArg(v_file_2698_, v_text_boxed_2703_, v_a_2700_, v_a_2701_);
lean_dec_ref(v_a_2700_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object* v_file_2705_, uint8_t v_text_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l_Lake_fetchFileTrace___redArg(v_file_2705_, v_text_2706_, v_a_2711_, v_a_2712_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object* v_file_2715_, lean_object* v_text_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_){
_start:
{
uint8_t v_text_boxed_2724_; lean_object* v_res_2725_; 
v_text_boxed_2724_ = lean_unbox(v_text_2716_);
v_res_2725_ = l_Lake_fetchFileTrace(v_file_2715_, v_text_boxed_2724_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_);
lean_dec_ref(v_a_2721_);
lean_dec(v_a_2720_);
lean_dec(v_a_2719_);
lean_dec(v_a_2718_);
lean_dec_ref(v_a_2717_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(lean_object* v_val_2726_, lean_object* v_a_x3f_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v___x_2730_; lean_object* v_log_2731_; uint8_t v_action_2732_; uint8_t v_wantsRebuild_2733_; lean_object* v_trace_2734_; lean_object* v_buildTime_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2746_; 
v___x_2730_ = lean_io_mono_ms_now();
v_log_2731_ = lean_ctor_get(v___y_2728_, 0);
v_action_2732_ = lean_ctor_get_uint8(v___y_2728_, sizeof(void*)*3);
v_wantsRebuild_2733_ = lean_ctor_get_uint8(v___y_2728_, sizeof(void*)*3 + 1);
v_trace_2734_ = lean_ctor_get(v___y_2728_, 1);
v_buildTime_2735_ = lean_ctor_get(v___y_2728_, 2);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___y_2728_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2737_ = v___y_2728_;
v_isShared_2738_ = v_isSharedCheck_2746_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_buildTime_2735_);
lean_inc(v_trace_2734_);
lean_inc(v_log_2731_);
lean_dec(v___y_2728_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2746_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2743_; 
v___x_2739_ = lean_nat_sub(v___x_2730_, v_val_2726_);
lean_dec(v___x_2730_);
v___x_2740_ = lean_box(0);
v___x_2741_ = lean_nat_add(v_buildTime_2735_, v___x_2739_);
lean_dec(v___x_2739_);
lean_dec(v_buildTime_2735_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 2, v___x_2741_);
v___x_2743_ = v___x_2737_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_log_2731_);
lean_ctor_set(v_reuseFailAlloc_2745_, 1, v_trace_2734_);
lean_ctor_set(v_reuseFailAlloc_2745_, 2, v___x_2741_);
lean_ctor_set_uint8(v_reuseFailAlloc_2745_, sizeof(void*)*3, v_action_2732_);
lean_ctor_set_uint8(v_reuseFailAlloc_2745_, sizeof(void*)*3 + 1, v_wantsRebuild_2733_);
v___x_2743_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
lean_object* v___x_2744_; 
v___x_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2740_);
lean_ctor_set(v___x_2744_, 1, v___x_2743_);
return v___x_2744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0___boxed(lean_object* v_val_2747_, lean_object* v_a_x3f_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v_val_2747_, v_a_x3f_2748_, v___y_2749_);
lean_dec(v_a_x3f_2748_);
lean_dec(v_val_2747_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(lean_object* v_build_2752_, lean_object* v_file_2753_, lean_object* v_a_2754_, lean_object* v_depTrace_2755_, lean_object* v_traceFile_2756_, uint8_t v_action_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_){
_start:
{
lean_object* v_a_2765_; lean_object* v_a_2766_; lean_object* v_log_2769_; uint8_t v_action_2770_; uint8_t v_wantsRebuild_2771_; lean_object* v_trace_2772_; lean_object* v_buildTime_2773_; lean_object* v_toBuildConfig_2779_; lean_object* v_log_2780_; uint8_t v_action_2781_; uint8_t v_wantsRebuild_2782_; lean_object* v_trace_2783_; lean_object* v_buildTime_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2907_; 
v_toBuildConfig_2779_ = lean_ctor_get(v_a_2761_, 0);
v_log_2780_ = lean_ctor_get(v_a_2762_, 0);
v_action_2781_ = lean_ctor_get_uint8(v_a_2762_, sizeof(void*)*3);
v_wantsRebuild_2782_ = lean_ctor_get_uint8(v_a_2762_, sizeof(void*)*3 + 1);
v_trace_2783_ = lean_ctor_get(v_a_2762_, 1);
v_buildTime_2784_ = lean_ctor_get(v_a_2762_, 2);
v_isSharedCheck_2907_ = !lean_is_exclusive(v_a_2762_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2786_ = v_a_2762_;
v_isShared_2787_ = v_isSharedCheck_2907_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_buildTime_2784_);
lean_inc(v_trace_2783_);
lean_inc(v_log_2780_);
lean_dec(v_a_2762_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2907_;
goto v_resetjp_2785_;
}
v___jp_2764_:
{
lean_object* v___x_2767_; 
v___x_2767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2767_, 0, v_a_2765_);
lean_ctor_set(v___x_2767_, 1, v_a_2766_);
return v___x_2767_;
}
v___jp_2768_:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2774_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_2775_ = lean_array_get_size(v_log_2769_);
v___x_2776_ = lean_array_push(v_log_2769_, v___x_2774_);
v___x_2777_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2777_, 0, v___x_2776_);
lean_ctor_set(v___x_2777_, 1, v_trace_2772_);
lean_ctor_set(v___x_2777_, 2, v_buildTime_2773_);
lean_ctor_set_uint8(v___x_2777_, sizeof(void*)*3, v_action_2770_);
lean_ctor_set_uint8(v___x_2777_, sizeof(void*)*3 + 1, v_wantsRebuild_2771_);
v___x_2778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2775_);
lean_ctor_set(v___x_2778_, 1, v___x_2777_);
return v___x_2778_;
}
v_resetjp_2785_:
{
uint8_t v_noBuild_2788_; uint8_t v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v_noBuild_2788_ = lean_ctor_get_uint8(v_toBuildConfig_2779_, sizeof(void*)*2 + 2);
v___x_2789_ = l_Lake_JobAction_merge(v_action_2781_, v_action_2757_);
v___x_2790_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_2756_);
v___x_2791_ = l_System_FilePath_addExtension(v_traceFile_2756_, v___x_2790_);
if (v_noBuild_2788_ == 0)
{
lean_object* v___x_2792_; lean_object* v___x_2794_; 
v___x_2792_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_2780_);
if (v_isShared_2787_ == 0)
{
v___x_2794_ = v___x_2786_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_log_2780_);
lean_ctor_set(v_reuseFailAlloc_2891_, 1, v_trace_2783_);
lean_ctor_set(v_reuseFailAlloc_2891_, 2, v_buildTime_2784_);
lean_ctor_set_uint8(v_reuseFailAlloc_2891_, sizeof(void*)*3 + 1, v_wantsRebuild_2782_);
v___x_2794_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
lean_object* v___x_2795_; lean_object* v_a_2797_; lean_object* v_a_2798_; 
lean_ctor_set_uint8(v___x_2794_, sizeof(void*)*3, v___x_2789_);
lean_inc_ref(v_a_2761_);
lean_inc(v_a_2760_);
lean_inc(v_a_2759_);
lean_inc(v_a_2758_);
v___x_2795_ = lean_apply_7(v_build_2752_, v_a_2754_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v___x_2794_, lean_box(0));
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2802_; lean_object* v_log_2803_; uint8_t v_action_2804_; uint8_t v_wantsRebuild_2805_; lean_object* v_trace_2806_; lean_object* v_buildTime_2807_; lean_object* v___x_2808_; 
v_a_2802_ = lean_ctor_get(v___x_2795_, 1);
lean_inc(v_a_2802_);
lean_dec_ref(v___x_2795_);
v_log_2803_ = lean_ctor_get(v_a_2802_, 0);
v_action_2804_ = lean_ctor_get_uint8(v_a_2802_, sizeof(void*)*3);
v_wantsRebuild_2805_ = lean_ctor_get_uint8(v_a_2802_, sizeof(void*)*3 + 1);
v_trace_2806_ = lean_ctor_get(v_a_2802_, 1);
v_buildTime_2807_ = lean_ctor_get(v_a_2802_, 2);
v___x_2808_ = l_Lake_clearFileHash(v_file_2753_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_a_2809_);
lean_dec_ref(v___x_2808_);
v___x_2810_ = lean_array_get_size(v_log_2780_);
lean_dec_ref(v_log_2780_);
v___x_2811_ = lean_array_get_size(v_log_2803_);
v___x_2812_ = l_Array_extract___redArg(v_log_2803_, v___x_2810_, v___x_2811_);
v___x_2813_ = lean_box(0);
v___x_2814_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_2755_, v___x_2813_, v___x_2812_);
v___x_2815_ = l_Lake_BuildMetadata_writeFile(v_traceFile_2756_, v___x_2814_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2856_; 
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2856_ == 0)
{
lean_object* v_unused_2857_; 
v_unused_2857_ = lean_ctor_get(v___x_2815_, 0);
lean_dec(v_unused_2857_);
v___x_2817_ = v___x_2815_;
v_isShared_2818_ = v_isSharedCheck_2856_;
goto v_resetjp_2816_;
}
else
{
lean_dec(v___x_2815_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2856_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2819_; 
v___x_2819_ = l_Lake_removeFileIfExists(v___x_2791_);
lean_dec_ref(v___x_2791_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2839_; 
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2839_ == 0)
{
lean_object* v_unused_2840_; 
v_unused_2840_ = lean_ctor_get(v___x_2819_, 0);
lean_dec(v_unused_2840_);
v___x_2821_ = v___x_2819_;
v_isShared_2822_ = v_isSharedCheck_2839_;
goto v_resetjp_2820_;
}
else
{
lean_dec(v___x_2819_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2839_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
lean_inc(v_a_2809_);
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 0, v_a_2809_);
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2809_);
v___x_2824_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
lean_object* v___x_2826_; 
if (v_isShared_2818_ == 0)
{
lean_ctor_set_tag(v___x_2817_, 1);
lean_ctor_set(v___x_2817_, 0, v___x_2824_);
v___x_2826_ = v___x_2817_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v___x_2824_);
v___x_2826_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
lean_object* v___x_2827_; lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
v___x_2827_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v___x_2792_, v___x_2826_, v_a_2802_);
lean_dec_ref(v___x_2826_);
lean_dec(v___x_2792_);
v_a_2828_ = lean_ctor_get(v___x_2827_, 1);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2835_ == 0)
{
lean_object* v_unused_2836_; 
v_unused_2836_ = lean_ctor_get(v___x_2827_, 0);
lean_dec(v_unused_2836_);
v___x_2830_ = v___x_2827_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2827_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 0, v_a_2809_);
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2809_);
lean_ctor_set(v_reuseFailAlloc_2834_, 1, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
}
}
else
{
lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2852_; 
lean_inc(v_buildTime_2807_);
lean_inc_ref(v_trace_2806_);
lean_inc_ref(v_log_2803_);
lean_del_object(v___x_2817_);
lean_dec(v_a_2809_);
v_isSharedCheck_2852_ = !lean_is_exclusive(v_a_2802_);
if (v_isSharedCheck_2852_ == 0)
{
lean_object* v_unused_2853_; lean_object* v_unused_2854_; lean_object* v_unused_2855_; 
v_unused_2853_ = lean_ctor_get(v_a_2802_, 2);
lean_dec(v_unused_2853_);
v_unused_2854_ = lean_ctor_get(v_a_2802_, 1);
lean_dec(v_unused_2854_);
v_unused_2855_ = lean_ctor_get(v_a_2802_, 0);
lean_dec(v_unused_2855_);
v___x_2842_ = v_a_2802_;
v_isShared_2843_ = v_isSharedCheck_2852_;
goto v_resetjp_2841_;
}
else
{
lean_dec(v_a_2802_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2852_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v_a_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2850_; 
v_a_2844_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2844_);
lean_dec_ref(v___x_2819_);
v___x_2845_ = lean_io_error_to_string(v_a_2844_);
v___x_2846_ = 3;
v___x_2847_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2847_, 0, v___x_2845_);
lean_ctor_set_uint8(v___x_2847_, sizeof(void*)*1, v___x_2846_);
v___x_2848_ = lean_array_push(v_log_2803_, v___x_2847_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v___x_2848_);
v___x_2850_ = v___x_2842_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2848_);
lean_ctor_set(v_reuseFailAlloc_2851_, 1, v_trace_2806_);
lean_ctor_set(v_reuseFailAlloc_2851_, 2, v_buildTime_2807_);
lean_ctor_set_uint8(v_reuseFailAlloc_2851_, sizeof(void*)*3, v_action_2804_);
lean_ctor_set_uint8(v_reuseFailAlloc_2851_, sizeof(void*)*3 + 1, v_wantsRebuild_2805_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
v_a_2797_ = v___x_2811_;
v_a_2798_ = v___x_2850_;
goto v___jp_2796_;
}
}
}
}
}
else
{
lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2869_; 
lean_inc(v_buildTime_2807_);
lean_inc_ref(v_trace_2806_);
lean_inc_ref(v_log_2803_);
lean_dec(v_a_2809_);
lean_dec_ref(v___x_2791_);
v_isSharedCheck_2869_ = !lean_is_exclusive(v_a_2802_);
if (v_isSharedCheck_2869_ == 0)
{
lean_object* v_unused_2870_; lean_object* v_unused_2871_; lean_object* v_unused_2872_; 
v_unused_2870_ = lean_ctor_get(v_a_2802_, 2);
lean_dec(v_unused_2870_);
v_unused_2871_ = lean_ctor_get(v_a_2802_, 1);
lean_dec(v_unused_2871_);
v_unused_2872_ = lean_ctor_get(v_a_2802_, 0);
lean_dec(v_unused_2872_);
v___x_2859_ = v_a_2802_;
v_isShared_2860_ = v_isSharedCheck_2869_;
goto v_resetjp_2858_;
}
else
{
lean_dec(v_a_2802_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2869_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v_a_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2867_; 
v_a_2861_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2861_);
lean_dec_ref(v___x_2815_);
v___x_2862_ = lean_io_error_to_string(v_a_2861_);
v___x_2863_ = 3;
v___x_2864_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2864_, 0, v___x_2862_);
lean_ctor_set_uint8(v___x_2864_, sizeof(void*)*1, v___x_2863_);
v___x_2865_ = lean_array_push(v_log_2803_, v___x_2864_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v___x_2865_);
v___x_2867_ = v___x_2859_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2865_);
lean_ctor_set(v_reuseFailAlloc_2868_, 1, v_trace_2806_);
lean_ctor_set(v_reuseFailAlloc_2868_, 2, v_buildTime_2807_);
lean_ctor_set_uint8(v_reuseFailAlloc_2868_, sizeof(void*)*3, v_action_2804_);
lean_ctor_set_uint8(v_reuseFailAlloc_2868_, sizeof(void*)*3 + 1, v_wantsRebuild_2805_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
v_a_2797_ = v___x_2811_;
v_a_2798_ = v___x_2867_;
goto v___jp_2796_;
}
}
}
}
else
{
lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2885_; 
lean_inc(v_buildTime_2807_);
lean_inc_ref(v_trace_2806_);
lean_inc_ref(v_log_2803_);
lean_dec_ref(v___x_2791_);
lean_dec_ref(v_log_2780_);
lean_dec_ref(v_traceFile_2756_);
v_isSharedCheck_2885_ = !lean_is_exclusive(v_a_2802_);
if (v_isSharedCheck_2885_ == 0)
{
lean_object* v_unused_2886_; lean_object* v_unused_2887_; lean_object* v_unused_2888_; 
v_unused_2886_ = lean_ctor_get(v_a_2802_, 2);
lean_dec(v_unused_2886_);
v_unused_2887_ = lean_ctor_get(v_a_2802_, 1);
lean_dec(v_unused_2887_);
v_unused_2888_ = lean_ctor_get(v_a_2802_, 0);
lean_dec(v_unused_2888_);
v___x_2874_ = v_a_2802_;
v_isShared_2875_ = v_isSharedCheck_2885_;
goto v_resetjp_2873_;
}
else
{
lean_dec(v_a_2802_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2885_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v_a_2876_; lean_object* v___x_2877_; uint8_t v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2883_; 
v_a_2876_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_a_2876_);
lean_dec_ref(v___x_2808_);
v___x_2877_ = lean_io_error_to_string(v_a_2876_);
v___x_2878_ = 3;
v___x_2879_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2879_, 0, v___x_2877_);
lean_ctor_set_uint8(v___x_2879_, sizeof(void*)*1, v___x_2878_);
v___x_2880_ = lean_array_get_size(v_log_2803_);
v___x_2881_ = lean_array_push(v_log_2803_, v___x_2879_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 0, v___x_2881_);
v___x_2883_ = v___x_2874_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2881_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v_trace_2806_);
lean_ctor_set(v_reuseFailAlloc_2884_, 2, v_buildTime_2807_);
lean_ctor_set_uint8(v_reuseFailAlloc_2884_, sizeof(void*)*3, v_action_2804_);
lean_ctor_set_uint8(v_reuseFailAlloc_2884_, sizeof(void*)*3 + 1, v_wantsRebuild_2805_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
v_a_2797_ = v___x_2880_;
v_a_2798_ = v___x_2883_;
goto v___jp_2796_;
}
}
}
}
else
{
lean_object* v_a_2889_; lean_object* v_a_2890_; 
lean_dec_ref(v___x_2791_);
lean_dec_ref(v_log_2780_);
lean_dec_ref(v_traceFile_2756_);
lean_dec_ref(v_file_2753_);
v_a_2889_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_a_2889_);
v_a_2890_ = lean_ctor_get(v___x_2795_, 1);
lean_inc(v_a_2890_);
lean_dec_ref(v___x_2795_);
v_a_2797_ = v_a_2889_;
v_a_2798_ = v_a_2890_;
goto v___jp_2796_;
}
v___jp_2796_:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v_a_2801_; 
v___x_2799_ = lean_box(0);
v___x_2800_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v___x_2792_, v___x_2799_, v_a_2798_);
lean_dec(v___x_2792_);
v_a_2801_ = lean_ctor_get(v___x_2800_, 1);
lean_inc(v_a_2801_);
lean_dec_ref(v___x_2800_);
v_a_2765_ = v_a_2797_;
v_a_2766_ = v_a_2801_;
goto v___jp_2764_;
}
}
}
else
{
uint8_t v___x_2892_; 
lean_dec_ref(v_a_2754_);
lean_dec_ref(v_file_2753_);
lean_dec_ref(v_build_2752_);
v___x_2892_ = l_System_FilePath_pathExists(v_traceFile_2756_);
lean_dec_ref(v_traceFile_2756_);
if (v___x_2892_ == 0)
{
lean_dec_ref(v___x_2791_);
lean_del_object(v___x_2786_);
v_log_2769_ = v_log_2780_;
v_action_2770_ = v___x_2789_;
v_wantsRebuild_2771_ = v_noBuild_2788_;
v_trace_2772_ = v_trace_2783_;
v_buildTime_2773_ = v_buildTime_2784_;
goto v___jp_2768_;
}
else
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2893_ = lean_box(0);
v___x_2894_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_2895_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_2755_, v___x_2893_, v___x_2894_);
v___x_2896_ = l_Lake_BuildMetadata_writeFile(v___x_2791_, v___x_2895_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_dec_ref(v___x_2896_);
lean_del_object(v___x_2786_);
v_log_2769_ = v_log_2780_;
v_action_2770_ = v___x_2789_;
v_wantsRebuild_2771_ = v_noBuild_2788_;
v_trace_2772_ = v_trace_2783_;
v_buildTime_2773_ = v_buildTime_2784_;
goto v___jp_2768_;
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2898_; uint8_t v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2904_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc(v_a_2897_);
lean_dec_ref(v___x_2896_);
v___x_2898_ = lean_io_error_to_string(v_a_2897_);
v___x_2899_ = 3;
v___x_2900_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2900_, 0, v___x_2898_);
lean_ctor_set_uint8(v___x_2900_, sizeof(void*)*1, v___x_2899_);
v___x_2901_ = lean_array_get_size(v_log_2780_);
v___x_2902_ = lean_array_push(v_log_2780_, v___x_2900_);
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 0, v___x_2902_);
v___x_2904_ = v___x_2786_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2902_);
lean_ctor_set(v_reuseFailAlloc_2906_, 1, v_trace_2783_);
lean_ctor_set(v_reuseFailAlloc_2906_, 2, v_buildTime_2784_);
v___x_2904_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
lean_object* v___x_2905_; 
lean_ctor_set_uint8(v___x_2904_, sizeof(void*)*3, v___x_2789_);
lean_ctor_set_uint8(v___x_2904_, sizeof(void*)*3 + 1, v_noBuild_2788_);
v___x_2905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2901_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
return v___x_2905_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___boxed(lean_object* v_build_2908_, lean_object* v_file_2909_, lean_object* v_a_2910_, lean_object* v_depTrace_2911_, lean_object* v_traceFile_2912_, lean_object* v_action_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_){
_start:
{
uint8_t v_action_boxed_2920_; lean_object* v_res_2921_; 
v_action_boxed_2920_ = lean_unbox(v_action_2913_);
v_res_2921_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(v_build_2908_, v_file_2909_, v_a_2910_, v_depTrace_2911_, v_traceFile_2912_, v_action_boxed_2920_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_);
lean_dec_ref(v_a_2917_);
lean_dec(v_a_2916_);
lean_dec(v_a_2915_);
lean_dec(v_a_2914_);
lean_dec_ref(v_depTrace_2911_);
return v_res_2921_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(lean_object* v_info_2922_, lean_object* v_self_2923_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = lean_io_metadata(v_info_2922_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; lean_object* v_modified_2927_; uint8_t v___x_2928_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_a_2926_);
lean_dec_ref(v___x_2925_);
v_modified_2927_ = lean_ctor_get(v_a_2926_, 1);
lean_inc_ref(v_modified_2927_);
lean_dec(v_a_2926_);
v___x_2928_ = l_IO_FS_instOrdSystemTime_ord(v_self_2923_, v_modified_2927_);
lean_dec_ref(v_modified_2927_);
if (v___x_2928_ == 0)
{
uint8_t v___x_2929_; 
v___x_2929_ = 1;
return v___x_2929_;
}
else
{
uint8_t v___x_2930_; 
v___x_2930_ = 0;
return v___x_2930_;
}
}
else
{
uint8_t v___x_2931_; 
lean_dec_ref(v___x_2925_);
v___x_2931_ = 0;
return v___x_2931_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___boxed(lean_object* v_info_2932_, lean_object* v_self_2933_, lean_object* v_a_2934_){
_start:
{
uint8_t v_res_2935_; lean_object* v_r_2936_; 
v_res_2935_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_2932_, v_self_2933_);
lean_dec_ref(v_self_2933_);
lean_dec_ref(v_info_2932_);
v_r_2936_ = lean_box(v_res_2935_);
return v_r_2936_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(lean_object* v_x_2937_, lean_object* v_x_2938_){
_start:
{
if (lean_obj_tag(v_x_2937_) == 0)
{
if (lean_obj_tag(v_x_2938_) == 0)
{
uint8_t v___x_2939_; 
v___x_2939_ = 1;
return v___x_2939_;
}
else
{
uint8_t v___x_2940_; 
v___x_2940_ = 0;
return v___x_2940_;
}
}
else
{
if (lean_obj_tag(v_x_2938_) == 0)
{
uint8_t v___x_2941_; 
v___x_2941_ = 0;
return v___x_2941_;
}
else
{
lean_object* v_val_2942_; lean_object* v_val_2943_; uint64_t v___x_2944_; uint64_t v___x_2945_; uint8_t v___x_2946_; 
v_val_2942_ = lean_ctor_get(v_x_2937_, 0);
v_val_2943_ = lean_ctor_get(v_x_2938_, 0);
v___x_2944_ = lean_unbox_uint64(v_val_2942_);
v___x_2945_ = lean_unbox_uint64(v_val_2943_);
v___x_2946_ = lean_uint64_dec_eq(v___x_2944_, v___x_2945_);
return v___x_2946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2947_, lean_object* v_x_2948_){
_start:
{
uint8_t v_res_2949_; lean_object* v_r_2950_; 
v_res_2949_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(v_x_2947_, v_x_2948_);
lean_dec(v_x_2948_);
lean_dec(v_x_2947_);
v_r_2950_ = lean_box(v_res_2949_);
return v_r_2950_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(lean_object* v_info_2951_, lean_object* v_depTrace_2952_, lean_object* v_depHash_2953_, lean_object* v_oldTrace_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_){
_start:
{
uint64_t v_hash_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; uint8_t v___x_2961_; 
v_hash_2958_ = lean_ctor_get_uint64(v_depTrace_2952_, sizeof(void*)*3);
v___x_2959_ = lean_box_uint64(v_hash_2958_);
v___x_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
v___x_2961_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(v___x_2960_, v_depHash_2953_);
lean_dec_ref(v___x_2960_);
if (v___x_2961_ == 0)
{
lean_object* v_toBuildConfig_2962_; uint8_t v_oldMode_2963_; 
v_toBuildConfig_2962_ = lean_ctor_get(v_a_2955_, 0);
v_oldMode_2963_ = lean_ctor_get_uint8(v_toBuildConfig_2962_, sizeof(void*)*2);
if (v_oldMode_2963_ == 0)
{
uint8_t v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2964_ = 0;
v___x_2965_ = lean_box(v___x_2964_);
v___x_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2965_);
lean_ctor_set(v___x_2966_, 1, v_a_2956_);
return v___x_2966_;
}
else
{
uint8_t v___x_2967_; 
v___x_2967_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_2951_, v_oldTrace_2954_);
if (v___x_2967_ == 0)
{
uint8_t v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2968_ = 0;
v___x_2969_ = lean_box(v___x_2968_);
v___x_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
lean_ctor_set(v___x_2970_, 1, v_a_2956_);
return v___x_2970_;
}
else
{
uint8_t v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2971_ = 1;
v___x_2972_ = lean_box(v___x_2971_);
v___x_2973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2972_);
lean_ctor_set(v___x_2973_, 1, v_a_2956_);
return v___x_2973_;
}
}
}
else
{
uint8_t v___x_2974_; 
v___x_2974_ = l_System_FilePath_pathExists(v_info_2951_);
if (v___x_2974_ == 0)
{
uint8_t v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2975_ = 0;
v___x_2976_ = lean_box(v___x_2975_);
v___x_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
lean_ctor_set(v___x_2977_, 1, v_a_2956_);
return v___x_2977_;
}
else
{
uint8_t v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2978_ = 2;
v___x_2979_ = lean_box(v___x_2978_);
v___x_2980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
lean_ctor_set(v___x_2980_, 1, v_a_2956_);
return v___x_2980_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg___boxed(lean_object* v_info_2981_, lean_object* v_depTrace_2982_, lean_object* v_depHash_2983_, lean_object* v_oldTrace_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_){
_start:
{
lean_object* v_res_2988_; 
v_res_2988_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_2981_, v_depTrace_2982_, v_depHash_2983_, v_oldTrace_2984_, v_a_2985_, v_a_2986_);
lean_dec_ref(v_a_2985_);
lean_dec_ref(v_oldTrace_2984_);
lean_dec(v_depHash_2983_);
lean_dec_ref(v_depTrace_2982_);
lean_dec_ref(v_info_2981_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(lean_object* v_a_2989_, lean_object* v_info_2990_, lean_object* v_depTrace_2991_, lean_object* v_savedTrace_2992_, lean_object* v_oldTrace_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_){
_start:
{
if (lean_obj_tag(v_savedTrace_2992_) == 2)
{
lean_object* v_data_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3050_; 
v_data_3000_ = lean_ctor_get(v_savedTrace_2992_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v_savedTrace_2992_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3002_ = v_savedTrace_2992_;
v_isShared_3003_ = v_isSharedCheck_3050_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_data_3000_);
lean_dec(v_savedTrace_2992_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3050_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
uint64_t v_depHash_3004_; lean_object* v_log_3005_; lean_object* v___x_3006_; lean_object* v___x_3008_; 
v_depHash_3004_ = lean_ctor_get_uint64(v_data_3000_, sizeof(void*)*3);
v_log_3005_ = lean_ctor_get(v_data_3000_, 2);
lean_inc_ref(v_log_3005_);
lean_dec_ref(v_data_3000_);
v___x_3006_ = lean_box_uint64(v_depHash_3004_);
if (v_isShared_3003_ == 0)
{
lean_ctor_set_tag(v___x_3002_, 1);
lean_ctor_set(v___x_3002_, 0, v___x_3006_);
v___x_3008_ = v___x_3002_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3006_);
v___x_3008_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
lean_object* v___x_3009_; lean_object* v_a_3010_; lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3048_; 
v___x_3009_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_2990_, v_depTrace_2991_, v___x_3008_, v_oldTrace_2993_, v_a_2997_, v_a_2998_);
lean_dec_ref(v___x_3008_);
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
v_a_3011_ = lean_ctor_get(v___x_3009_, 1);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3013_ = v___x_3009_;
v_isShared_3014_ = v_isSharedCheck_3048_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_inc(v_a_3010_);
lean_dec(v___x_3009_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3048_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___y_3016_; uint8_t v___x_3020_; uint8_t v___x_3021_; uint8_t v___x_3022_; 
v___x_3020_ = 0;
v___x_3021_ = lean_unbox(v_a_3010_);
v___x_3022_ = l_Lake_instDecidableEqOutputStatus(v___x_3021_, v___x_3020_);
if (v___x_3022_ == 0)
{
lean_object* v_log_3023_; uint8_t v_action_3024_; uint8_t v_wantsRebuild_3025_; lean_object* v_trace_3026_; lean_object* v_buildTime_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3047_; 
v_log_3023_ = lean_ctor_get(v_a_3011_, 0);
v_action_3024_ = lean_ctor_get_uint8(v_a_3011_, sizeof(void*)*3);
v_wantsRebuild_3025_ = lean_ctor_get_uint8(v_a_3011_, sizeof(void*)*3 + 1);
v_trace_3026_ = lean_ctor_get(v_a_3011_, 1);
v_buildTime_3027_ = lean_ctor_get(v_a_3011_, 2);
v_isSharedCheck_3047_ = !lean_is_exclusive(v_a_3011_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3029_ = v_a_3011_;
v_isShared_3030_ = v_isSharedCheck_3047_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_buildTime_3027_);
lean_inc(v_trace_3026_);
lean_inc(v_log_3023_);
lean_dec(v_a_3011_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3047_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
uint8_t v___x_3031_; uint8_t v___x_3032_; lean_object* v___x_3034_; 
v___x_3031_ = 1;
v___x_3032_ = l_Lake_JobAction_merge(v_action_3024_, v___x_3031_);
if (v_isShared_3030_ == 0)
{
v___x_3034_ = v___x_3029_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_log_3023_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v_trace_3026_);
lean_ctor_set(v_reuseFailAlloc_3046_, 2, v_buildTime_3027_);
lean_ctor_set_uint8(v_reuseFailAlloc_3046_, sizeof(void*)*3 + 1, v_wantsRebuild_3025_);
v___x_3034_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
lean_object* v___x_3035_; 
lean_ctor_set_uint8(v___x_3034_, sizeof(void*)*3, v___x_3032_);
v___x_3035_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_3005_, v_a_2989_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v___x_3034_);
lean_dec_ref(v_log_3005_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 1);
lean_inc(v_a_3036_);
lean_dec_ref(v___x_3035_);
v___y_3016_ = v_a_3036_;
goto v___jp_3015_;
}
else
{
lean_object* v_a_3037_; lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_del_object(v___x_3013_);
lean_dec(v_a_3010_);
v_a_3037_ = lean_ctor_get(v___x_3035_, 0);
v_a_3038_ = lean_ctor_get(v___x_3035_, 1);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3035_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_inc(v_a_3037_);
lean_dec(v___x_3035_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3037_);
lean_ctor_set(v_reuseFailAlloc_3044_, 1, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_log_3005_);
v___y_3016_ = v_a_3011_;
goto v___jp_3015_;
}
v___jp_3015_:
{
lean_object* v___x_3018_; 
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 1, v___y_3016_);
v___x_3018_ = v___x_3013_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_3010_);
lean_ctor_set(v_reuseFailAlloc_3019_, 1, v___y_3016_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
}
}
else
{
lean_object* v_toBuildConfig_3051_; uint8_t v_oldMode_3052_; 
lean_dec(v_savedTrace_2992_);
v_toBuildConfig_3051_ = lean_ctor_get(v_a_2997_, 0);
v_oldMode_3052_ = lean_ctor_get_uint8(v_toBuildConfig_3051_, sizeof(void*)*2);
if (v_oldMode_3052_ == 0)
{
uint8_t v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3053_ = 0;
v___x_3054_ = lean_box(v___x_3053_);
v___x_3055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
lean_ctor_set(v___x_3055_, 1, v_a_2998_);
return v___x_3055_;
}
else
{
uint8_t v___x_3056_; 
v___x_3056_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_2990_, v_oldTrace_2993_);
if (v___x_3056_ == 0)
{
uint8_t v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3057_ = 0;
v___x_3058_ = lean_box(v___x_3057_);
v___x_3059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3058_);
lean_ctor_set(v___x_3059_, 1, v_a_2998_);
return v___x_3059_;
}
else
{
uint8_t v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3060_ = 1;
v___x_3061_ = lean_box(v___x_3060_);
v___x_3062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3061_);
lean_ctor_set(v___x_3062_, 1, v_a_2998_);
return v___x_3062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0___boxed(lean_object* v_a_3063_, lean_object* v_info_3064_, lean_object* v_depTrace_3065_, lean_object* v_savedTrace_3066_, lean_object* v_oldTrace_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_3063_, v_info_3064_, v_depTrace_3065_, v_savedTrace_3066_, v_oldTrace_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec_ref(v_oldTrace_3067_);
lean_dec_ref(v_depTrace_3065_);
lean_dec_ref(v_info_3064_);
lean_dec_ref(v_a_3063_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27(lean_object* v_file_3076_, lean_object* v_build_3077_, uint8_t v_text_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_){
_start:
{
lean_object* v_a_3087_; lean_object* v_a_3088_; lean_object* v_a_3091_; lean_object* v_log_3124_; uint8_t v_action_3125_; uint8_t v_wantsRebuild_3126_; lean_object* v_trace_3127_; lean_object* v_buildTime_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3159_; 
v_log_3124_ = lean_ctor_get(v_a_3084_, 0);
v_action_3125_ = lean_ctor_get_uint8(v_a_3084_, sizeof(void*)*3);
v_wantsRebuild_3126_ = lean_ctor_get_uint8(v_a_3084_, sizeof(void*)*3 + 1);
v_trace_3127_ = lean_ctor_get(v_a_3084_, 1);
v_buildTime_3128_ = lean_ctor_get(v_a_3084_, 2);
v_isSharedCheck_3159_ = !lean_is_exclusive(v_a_3084_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3130_ = v_a_3084_;
v_isShared_3131_ = v_isSharedCheck_3159_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_buildTime_3128_);
lean_inc(v_trace_3127_);
lean_inc(v_log_3124_);
lean_dec(v_a_3084_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3159_;
goto v_resetjp_3129_;
}
v___jp_3086_:
{
lean_object* v___x_3089_; 
v___x_3089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3089_, 0, v_a_3087_);
lean_ctor_set(v___x_3089_, 1, v_a_3088_);
return v___x_3089_;
}
v___jp_3090_:
{
lean_object* v___x_3092_; 
v___x_3092_ = l_Lake_fetchFileTrace___redArg(v_file_3076_, v_text_3078_, v_a_3083_, v_a_3091_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_object* v_a_3093_; lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3114_; 
v_a_3093_ = lean_ctor_get(v___x_3092_, 1);
v_a_3094_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3096_ = v___x_3092_;
v_isShared_3097_ = v_isSharedCheck_3114_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3093_);
lean_inc(v_a_3094_);
lean_dec(v___x_3092_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3114_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v_log_3098_; uint8_t v_action_3099_; uint8_t v_wantsRebuild_3100_; lean_object* v_buildTime_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3112_; 
v_log_3098_ = lean_ctor_get(v_a_3093_, 0);
v_action_3099_ = lean_ctor_get_uint8(v_a_3093_, sizeof(void*)*3);
v_wantsRebuild_3100_ = lean_ctor_get_uint8(v_a_3093_, sizeof(void*)*3 + 1);
v_buildTime_3101_ = lean_ctor_get(v_a_3093_, 2);
v_isSharedCheck_3112_ = !lean_is_exclusive(v_a_3093_);
if (v_isSharedCheck_3112_ == 0)
{
lean_object* v_unused_3113_; 
v_unused_3113_ = lean_ctor_get(v_a_3093_, 1);
lean_dec(v_unused_3113_);
v___x_3103_ = v_a_3093_;
v_isShared_3104_ = v_isSharedCheck_3112_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_buildTime_3101_);
lean_inc(v_log_3098_);
lean_dec(v_a_3093_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3112_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3105_; lean_object* v___x_3107_; 
v___x_3105_ = lean_box(0);
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 1, v_a_3094_);
v___x_3107_ = v___x_3103_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_log_3098_);
lean_ctor_set(v_reuseFailAlloc_3111_, 1, v_a_3094_);
lean_ctor_set(v_reuseFailAlloc_3111_, 2, v_buildTime_3101_);
lean_ctor_set_uint8(v_reuseFailAlloc_3111_, sizeof(void*)*3, v_action_3099_);
lean_ctor_set_uint8(v_reuseFailAlloc_3111_, sizeof(void*)*3 + 1, v_wantsRebuild_3100_);
v___x_3107_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
lean_object* v___x_3109_; 
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 1, v___x_3107_);
lean_ctor_set(v___x_3096_, 0, v___x_3105_);
v___x_3109_ = v___x_3096_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3105_);
lean_ctor_set(v_reuseFailAlloc_3110_, 1, v___x_3107_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
}
else
{
lean_object* v_a_3115_; lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
v_a_3115_ = lean_ctor_get(v___x_3092_, 0);
v_a_3116_ = lean_ctor_get(v___x_3092_, 1);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3118_ = v___x_3092_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_inc(v_a_3115_);
lean_dec(v___x_3092_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3115_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v_a_3116_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
v_resetjp_3129_:
{
lean_object* v___x_3132_; lean_object* v_traceFile_3133_; lean_object* v___x_3134_; 
v___x_3132_ = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(v_file_3076_);
v_traceFile_3133_ = lean_string_append(v_file_3076_, v___x_3132_);
lean_inc_ref(v_traceFile_3133_);
v___x_3134_ = l_Lake_readTraceFile(v_traceFile_3133_, v_log_3124_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_a_3135_; lean_object* v_a_3136_; lean_object* v_mtime_3137_; lean_object* v___x_3139_; 
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
lean_inc(v_a_3135_);
v_a_3136_ = lean_ctor_get(v___x_3134_, 1);
lean_inc(v_a_3136_);
lean_dec_ref(v___x_3134_);
v_mtime_3137_ = lean_ctor_get(v_trace_3127_, 2);
lean_inc_ref(v_trace_3127_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v_a_3136_);
v___x_3139_ = v___x_3130_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3136_);
lean_ctor_set(v_reuseFailAlloc_3153_, 1, v_trace_3127_);
lean_ctor_set(v_reuseFailAlloc_3153_, 2, v_buildTime_3128_);
lean_ctor_set_uint8(v_reuseFailAlloc_3153_, sizeof(void*)*3, v_action_3125_);
lean_ctor_set_uint8(v_reuseFailAlloc_3153_, sizeof(void*)*3 + 1, v_wantsRebuild_3126_);
v___x_3139_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
lean_object* v___x_3140_; 
v___x_3140_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_3079_, v_file_3076_, v_trace_3127_, v_a_3135_, v_mtime_3137_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v___x_3139_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; lean_object* v_a_3142_; uint8_t v___x_3143_; uint8_t v___x_3144_; uint8_t v___x_3145_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3141_);
v_a_3142_ = lean_ctor_get(v___x_3140_, 1);
lean_inc(v_a_3142_);
lean_dec_ref(v___x_3140_);
v___x_3143_ = 0;
v___x_3144_ = lean_unbox(v_a_3141_);
lean_dec(v_a_3141_);
v___x_3145_ = l_Lake_instDecidableEqOutputStatus(v___x_3144_, v___x_3143_);
if (v___x_3145_ == 0)
{
lean_dec_ref(v_traceFile_3133_);
lean_dec_ref(v_trace_3127_);
lean_dec_ref(v_a_3079_);
lean_dec_ref(v_build_3077_);
v_a_3091_ = v_a_3142_;
goto v___jp_3090_;
}
else
{
uint8_t v___x_3146_; lean_object* v___x_3147_; 
v___x_3146_ = 3;
lean_inc_ref(v_file_3076_);
v___x_3147_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(v_build_3077_, v_file_3076_, v_a_3079_, v_trace_3127_, v_traceFile_3133_, v___x_3146_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3142_);
lean_dec_ref(v_trace_3127_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v_a_3148_; 
v_a_3148_ = lean_ctor_get(v___x_3147_, 1);
lean_inc(v_a_3148_);
lean_dec_ref(v___x_3147_);
v_a_3091_ = v_a_3148_;
goto v___jp_3090_;
}
else
{
lean_object* v_a_3149_; lean_object* v_a_3150_; 
lean_dec_ref(v_file_3076_);
v_a_3149_ = lean_ctor_get(v___x_3147_, 0);
lean_inc(v_a_3149_);
v_a_3150_ = lean_ctor_get(v___x_3147_, 1);
lean_inc(v_a_3150_);
lean_dec_ref(v___x_3147_);
v_a_3087_ = v_a_3149_;
v_a_3088_ = v_a_3150_;
goto v___jp_3086_;
}
}
}
else
{
lean_object* v_a_3151_; lean_object* v_a_3152_; 
lean_dec_ref(v_traceFile_3133_);
lean_dec_ref(v_trace_3127_);
lean_dec_ref(v_a_3079_);
lean_dec_ref(v_build_3077_);
lean_dec_ref(v_file_3076_);
v_a_3151_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3151_);
v_a_3152_ = lean_ctor_get(v___x_3140_, 1);
lean_inc(v_a_3152_);
lean_dec_ref(v___x_3140_);
v_a_3087_ = v_a_3151_;
v_a_3088_ = v_a_3152_;
goto v___jp_3086_;
}
}
}
else
{
lean_object* v_a_3154_; lean_object* v_a_3155_; lean_object* v___x_3157_; 
lean_dec_ref(v_traceFile_3133_);
lean_dec_ref(v_a_3079_);
lean_dec_ref(v_build_3077_);
lean_dec_ref(v_file_3076_);
v_a_3154_ = lean_ctor_get(v___x_3134_, 0);
lean_inc(v_a_3154_);
v_a_3155_ = lean_ctor_get(v___x_3134_, 1);
lean_inc(v_a_3155_);
lean_dec_ref(v___x_3134_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v_a_3155_);
v___x_3157_ = v___x_3130_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3155_);
lean_ctor_set(v_reuseFailAlloc_3158_, 1, v_trace_3127_);
lean_ctor_set(v_reuseFailAlloc_3158_, 2, v_buildTime_3128_);
lean_ctor_set_uint8(v_reuseFailAlloc_3158_, sizeof(void*)*3, v_action_3125_);
lean_ctor_set_uint8(v_reuseFailAlloc_3158_, sizeof(void*)*3 + 1, v_wantsRebuild_3126_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
v_a_3087_ = v_a_3154_;
v_a_3088_ = v___x_3157_;
goto v___jp_3086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27___boxed(lean_object* v_file_3160_, lean_object* v_build_3161_, lean_object* v_text_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_){
_start:
{
uint8_t v_text_boxed_3170_; lean_object* v_res_3171_; 
v_text_boxed_3170_ = lean_unbox(v_text_3162_);
v_res_3171_ = l_Lake_buildFileUnlessUpToDate_x27(v_file_3160_, v_build_3161_, v_text_boxed_3170_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_);
lean_dec_ref(v_a_3167_);
lean_dec(v_a_3166_);
lean_dec(v_a_3165_);
lean_dec(v_a_3164_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(lean_object* v_a_3172_, lean_object* v_info_3173_, lean_object* v_depTrace_3174_, lean_object* v_depHash_3175_, lean_object* v_oldTrace_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_){
_start:
{
lean_object* v___x_3183_; 
v___x_3183_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_3173_, v_depTrace_3174_, v_depHash_3175_, v_oldTrace_3176_, v_a_3180_, v_a_3181_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___boxed(lean_object* v_a_3184_, lean_object* v_info_3185_, lean_object* v_depTrace_3186_, lean_object* v_depHash_3187_, lean_object* v_oldTrace_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(v_a_3184_, v_info_3185_, v_depTrace_3186_, v_depHash_3187_, v_oldTrace_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_);
lean_dec_ref(v_a_3192_);
lean_dec(v_a_3191_);
lean_dec(v_a_3190_);
lean_dec(v_a_3189_);
lean_dec_ref(v_oldTrace_3188_);
lean_dec(v_depHash_3187_);
lean_dec_ref(v_depTrace_3186_);
lean_dec_ref(v_info_3185_);
lean_dec_ref(v_a_3184_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0(lean_object* v_file_3196_, uint64_t v___x_3197_, lean_object* v___x_3198_, uint8_t v_useLocalFile_3199_, lean_object* v___x_3200_, lean_object* v_____r_3201_){
_start:
{
lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3210_; lean_object* v___x_3211_; 
lean_inc_ref(v_file_3196_);
v___x_3211_ = l_Lake_writeFileHash(v_file_3196_, v___x_3197_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v___x_3212_; 
lean_dec_ref(v___x_3211_);
v___x_3212_ = lean_io_metadata(v___x_3200_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v_a_3213_; lean_object* v_modified_3214_; 
v_a_3213_ = lean_ctor_get(v___x_3212_, 0);
lean_inc(v_a_3213_);
lean_dec_ref(v___x_3212_);
v_modified_3214_ = lean_ctor_get(v_a_3213_, 1);
lean_inc_ref(v_modified_3214_);
lean_dec(v_a_3213_);
v___y_3210_ = v_modified_3214_;
goto v___jp_3209_;
}
else
{
lean_object* v___x_3215_; 
lean_dec_ref(v___x_3212_);
v___x_3215_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___y_3210_ = v___x_3215_;
goto v___jp_3209_;
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_dec_ref(v___x_3200_);
lean_dec_ref(v___x_3198_);
lean_dec_ref(v_file_3196_);
v_a_3216_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3211_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3211_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
v___jp_3203_:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3206_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3198_);
lean_ctor_set(v___x_3206_, 1, v___y_3205_);
lean_ctor_set(v___x_3206_, 2, v_file_3196_);
lean_ctor_set(v___x_3206_, 3, v___y_3204_);
v___x_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3206_);
v___x_3208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3207_);
return v___x_3208_;
}
v___jp_3209_:
{
if (v_useLocalFile_3199_ == 0)
{
v___y_3204_ = v___y_3210_;
v___y_3205_ = v___x_3200_;
goto v___jp_3203_;
}
else
{
lean_dec_ref(v___x_3200_);
lean_inc_ref(v_file_3196_);
v___y_3204_ = v___y_3210_;
v___y_3205_ = v_file_3196_;
goto v___jp_3203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0___boxed(lean_object* v_file_3224_, lean_object* v___x_3225_, lean_object* v___x_3226_, lean_object* v_useLocalFile_3227_, lean_object* v___x_3228_, lean_object* v_____r_3229_, lean_object* v___y_3230_){
_start:
{
uint64_t v___x_3426__boxed_3231_; uint8_t v_useLocalFile_boxed_3232_; lean_object* v_res_3233_; 
v___x_3426__boxed_3231_ = lean_unbox_uint64(v___x_3225_);
lean_dec_ref(v___x_3225_);
v_useLocalFile_boxed_3232_ = lean_unbox(v_useLocalFile_3227_);
v_res_3233_ = l_Lake_Cache_saveArtifact___lam__0(v_file_3224_, v___x_3426__boxed_3231_, v___x_3226_, v_useLocalFile_boxed_3232_, v___x_3228_, v_____r_3229_);
return v_res_3233_;
}
}
static lean_object* _init_l_Lake_Cache_saveArtifact___closed__3(void){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3239_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__2));
v___x_3240_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3239_);
lean_ctor_set(v___x_3240_, 1, v___x_3239_);
lean_ctor_set(v___x_3240_, 2, v___x_3239_);
return v___x_3240_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact(lean_object* v_cache_3241_, lean_object* v_file_3242_, lean_object* v_ext_3243_, uint8_t v_text_3244_, uint8_t v_exe_3245_, uint8_t v_useLocalFile_3246_){
_start:
{
lean_object* v_a_3249_; lean_object* v___y_3256_; uint8_t v___x_3267_; 
v___x_3267_ = 1;
if (v_text_3244_ == 0)
{
lean_object* v___x_3268_; 
v___x_3268_ = l_IO_FS_readBinFile(v_file_3242_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; uint64_t v___x_3270_; uint64_t v___x_3271_; uint64_t v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___y_3277_; lean_object* v___x_3297_; lean_object* v___x_3298_; uint8_t v___x_3299_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3269_);
lean_dec_ref(v___x_3268_);
v___x_3270_ = l_Lake_Hash_nil;
v___x_3271_ = lean_byte_array_hash(v_a_3269_);
v___x_3272_ = lean_uint64_mix_hash(v___x_3270_, v___x_3271_);
lean_inc_ref(v_ext_3243_);
v___x_3273_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3273_, 0, v_ext_3243_);
lean_ctor_set_uint64(v___x_3273_, sizeof(void*)*1, v___x_3272_);
v___x_3274_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
v___x_3275_ = l_System_FilePath_join(v_cache_3241_, v___x_3274_);
v___x_3297_ = lean_string_utf8_byte_size(v_ext_3243_);
v___x_3298_ = lean_unsigned_to_nat(0u);
v___x_3299_ = lean_nat_dec_eq(v___x_3297_, v___x_3298_);
if (v___x_3299_ == 0)
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3300_ = l_Lake_Hash_hex(v___x_3272_);
v___x_3301_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_3302_ = lean_string_append(v___x_3300_, v___x_3301_);
v___x_3303_ = lean_string_append(v___x_3302_, v_ext_3243_);
lean_dec_ref(v_ext_3243_);
v___y_3277_ = v___x_3303_;
goto v___jp_3276_;
}
else
{
lean_object* v___x_3304_; 
lean_dec_ref(v_ext_3243_);
v___x_3304_ = l_Lake_Hash_hex(v___x_3272_);
v___y_3277_ = v___x_3304_;
goto v___jp_3276_;
}
v___jp_3276_:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3278_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_3278_, 0, v___x_3267_);
lean_ctor_set_uint8(v___x_3278_, 1, v_text_3244_);
lean_ctor_set_uint8(v___x_3278_, 2, v_exe_3245_);
lean_inc_ref_n(v___x_3278_, 2);
v___x_3279_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
lean_ctor_set(v___x_3279_, 1, v___x_3278_);
lean_ctor_set(v___x_3279_, 2, v___x_3278_);
v___x_3280_ = l_IO_setAccessRights(v_file_3242_, v___x_3279_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v___x_3281_; uint8_t v___x_3282_; 
lean_dec_ref(v___x_3280_);
v___x_3281_ = l_Lake_joinRelative(v___x_3275_, v___y_3277_);
v___x_3282_ = l_System_FilePath_pathExists(v___x_3281_);
if (v___x_3282_ == 0)
{
lean_object* v___x_3283_; 
lean_inc_ref(v___x_3281_);
v___x_3283_ = l_Lake_createParentDirs(v___x_3281_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v___x_3284_; 
lean_dec_ref(v___x_3283_);
v___x_3284_ = lean_io_hard_link(v_file_3242_, v___x_3281_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
lean_dec_ref(v___x_3284_);
lean_dec_ref(v___x_3279_);
lean_dec(v_a_3269_);
v___x_3285_ = lean_box(0);
v___x_3286_ = l_Lake_Cache_saveArtifact___lam__0(v_file_3242_, v___x_3272_, v___x_3273_, v_useLocalFile_3246_, v___x_3281_, v___x_3285_);
v___y_3256_ = v___x_3286_;
goto v___jp_3255_;
}
else
{
lean_object* v___x_3287_; 
lean_dec_ref(v___x_3284_);
v___x_3287_ = l_IO_FS_writeBinFile(v___x_3281_, v_a_3269_);
lean_dec(v_a_3269_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v___x_3288_; 
lean_dec_ref(v___x_3287_);
v___x_3288_ = l_IO_setAccessRights(v___x_3281_, v___x_3279_);
lean_dec_ref(v___x_3279_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; lean_object* v___x_3290_; 
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_a_3289_);
lean_dec_ref(v___x_3288_);
v___x_3290_ = l_Lake_Cache_saveArtifact___lam__0(v_file_3242_, v___x_3272_, v___x_3273_, v_useLocalFile_3246_, v___x_3281_, v_a_3289_);
v___y_3256_ = v___x_3290_;
goto v___jp_3255_;
}
else
{
lean_object* v_a_3291_; 
lean_dec_ref(v___x_3281_);
lean_dec_ref(v___x_3273_);
lean_dec_ref(v_file_3242_);
v_a_3291_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_a_3291_);
lean_dec_ref(v___x_3288_);
v_a_3249_ = v_a_3291_;
goto v___jp_3248_;
}
}
else
{
lean_object* v_a_3292_; 
lean_dec_ref(v___x_3281_);
lean_dec_ref(v___x_3279_);
lean_dec_ref(v___x_3273_);
lean_dec_ref(v_file_3242_);
v_a_3292_ = lean_ctor_get(v___x_3287_, 0);
lean_inc(v_a_3292_);
lean_dec_ref(v___x_3287_);
v_a_3249_ = v_a_3292_;
goto v___jp_3248_;
}
}
}
else
{
lean_object* v_a_3293_; 
lean_dec_ref(v___x_3281_);
lean_dec_ref(v___x_3279_);
lean_dec_ref(v___x_3273_);
lean_dec(v_a_3269_);
lean_dec_ref(v_file_3242_);
v_a_3293_ = lean_ctor_get(v___x_3283_, 0);
lean_inc(v_a_3293_);
lean_dec_ref(v___x_3283_);
v_a_3249_ = v_a_3293_;
goto v___jp_3248_;
}
}
else
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
lean_dec_ref(v___x_3279_);
lean_dec(v_a_3269_);
v___x_3294_ = lean_box(0);
v___x_3295_ = l_Lake_Cache_saveArtifact___lam__0(v_file_3242_, v___x_3272_, v___x_3273_, v_useLocalFile_3246_, v___x_3281_, v___x_3294_);
v___y_3256_ = v___x_3295_;
goto v___jp_3255_;
}
}
else
{
lean_object* v_a_3296_; 
lean_dec_ref(v___x_3279_);
lean_dec_ref(v___y_3277_);
lean_dec_ref(v___x_3275_);
lean_dec_ref(v___x_3273_);
lean_dec(v_a_3269_);
lean_dec_ref(v_file_3242_);
v_a_3296_ = lean_ctor_get(v___x_3280_, 0);
lean_inc(v_a_3296_);
lean_dec_ref(v___x_3280_);
v_a_3249_ = v_a_3296_;
goto v___jp_3248_;
}
}
}
else
{
lean_object* v_a_3305_; 
lean_dec_ref(v_ext_3243_);
lean_dec_ref(v_file_3242_);
lean_dec_ref(v_cache_3241_);
v_a_3305_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3305_);
lean_dec_ref(v___x_3268_);
v_a_3249_ = v_a_3305_;
goto v___jp_3248_;
}
}
else
{
lean_object* v___x_3306_; 
v___x_3306_ = l_IO_FS_readFile(v_file_3242_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; lean_object* v___x_3308_; uint64_t v___x_3309_; uint64_t v___x_3310_; uint64_t v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___y_3316_; lean_object* v___x_3332_; lean_object* v___x_3333_; uint8_t v___x_3334_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_a_3307_);
lean_dec_ref(v___x_3306_);
v___x_3308_ = l_String_crlfToLf(v_a_3307_);
lean_dec(v_a_3307_);
v___x_3309_ = l_Lake_Hash_nil;
v___x_3310_ = lean_string_hash(v___x_3308_);
v___x_3311_ = lean_uint64_mix_hash(v___x_3309_, v___x_3310_);
lean_inc_ref(v_ext_3243_);
v___x_3312_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3312_, 0, v_ext_3243_);
lean_ctor_set_uint64(v___x_3312_, sizeof(void*)*1, v___x_3311_);
v___x_3313_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
v___x_3314_ = l_System_FilePath_join(v_cache_3241_, v___x_3313_);
v___x_3332_ = lean_string_utf8_byte_size(v_ext_3243_);
v___x_3333_ = lean_unsigned_to_nat(0u);
v___x_3334_ = lean_nat_dec_eq(v___x_3332_, v___x_3333_);
if (v___x_3334_ == 0)
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3335_ = l_Lake_Hash_hex(v___x_3311_);
v___x_3336_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_3337_ = lean_string_append(v___x_3335_, v___x_3336_);
v___x_3338_ = lean_string_append(v___x_3337_, v_ext_3243_);
lean_dec_ref(v_ext_3243_);
v___y_3316_ = v___x_3338_;
goto v___jp_3315_;
}
else
{
lean_object* v___x_3339_; 
lean_dec_ref(v_ext_3243_);
v___x_3339_ = l_Lake_Hash_hex(v___x_3311_);
v___y_3316_ = v___x_3339_;
goto v___jp_3315_;
}
v___jp_3315_:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3317_ = lean_obj_once(&l_Lake_Cache_saveArtifact___closed__3, &l_Lake_Cache_saveArtifact___closed__3_once, _init_l_Lake_Cache_saveArtifact___closed__3);
v___x_3318_ = l_IO_setAccessRights(v_file_3242_, v___x_3317_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v___x_3319_; uint8_t v___x_3320_; 
lean_dec_ref(v___x_3318_);
v___x_3319_ = l_Lake_joinRelative(v___x_3314_, v___y_3316_);
v___x_3320_ = l_System_FilePath_pathExists(v___x_3319_);
if (v___x_3320_ == 0)
{
lean_object* v___x_3321_; 
lean_inc_ref(v___x_3319_);
v___x_3321_ = l_Lake_createParentDirs(v___x_3319_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v___x_3322_; 
lean_dec_ref(v___x_3321_);
v___x_3322_ = l_IO_FS_writeFile(v___x_3319_, v___x_3308_);
lean_dec_ref(v___x_3308_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v___x_3323_; 
lean_dec_ref(v___x_3322_);
v___x_3323_ = l_IO_setAccessRights(v___x_3319_, v___x_3317_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3324_; lean_object* v___x_3325_; 
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3324_);
lean_dec_ref(v___x_3323_);
v___x_3325_ = l_Lake_Cache_saveArtifact___lam__0(v_file_3242_, v___x_3311_, v___x_3312_, v_useLocalFile_3246_, v___x_3319_, v_a_3324_);
v___y_3256_ = v___x_3325_;
goto v___jp_3255_;
}
else
{
lean_object* v_a_3326_; 
lean_dec_ref(v___x_3319_);
lean_dec_ref(v___x_3312_);
lean_dec_ref(v_file_3242_);
v_a_3326_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3326_);
lean_dec_ref(v___x_3323_);
v_a_3249_ = v_a_3326_;
goto v___jp_3248_;
}
}
else
{
lean_object* v_a_3327_; 
lean_dec_ref(v___x_3319_);
lean_dec_ref(v___x_3312_);
lean_dec_ref(v_file_3242_);
v_a_3327_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3327_);
lean_dec_ref(v___x_3322_);
v_a_3249_ = v_a_3327_;
goto v___jp_3248_;
}
}
else
{
lean_object* v_a_3328_; 
lean_dec_ref(v___x_3319_);
lean_dec_ref(v___x_3312_);
lean_dec_ref(v___x_3308_);
lean_dec_ref(v_file_3242_);
v_a_3328_ = lean_ctor_get(v___x_3321_, 0);
lean_inc(v_a_3328_);
lean_dec_ref(v___x_3321_);
v_a_3249_ = v_a_3328_;
goto v___jp_3248_;
}
}
else
{
lean_object* v___x_3329_; lean_object* v___x_3330_; 
lean_dec_ref(v___x_3308_);
v___x_3329_ = lean_box(0);
v___x_3330_ = l_Lake_Cache_saveArtifact___lam__0(v_file_3242_, v___x_3311_, v___x_3312_, v_useLocalFile_3246_, v___x_3319_, v___x_3329_);
v___y_3256_ = v___x_3330_;
goto v___jp_3255_;
}
}
else
{
lean_object* v_a_3331_; 
lean_dec_ref(v___y_3316_);
lean_dec_ref(v___x_3314_);
lean_dec_ref(v___x_3312_);
lean_dec_ref(v___x_3308_);
lean_dec_ref(v_file_3242_);
v_a_3331_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3331_);
lean_dec_ref(v___x_3318_);
v_a_3249_ = v_a_3331_;
goto v___jp_3248_;
}
}
}
else
{
lean_object* v_a_3340_; 
lean_dec_ref(v_ext_3243_);
lean_dec_ref(v_file_3242_);
lean_dec_ref(v_cache_3241_);
v_a_3340_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_a_3340_);
lean_dec_ref(v___x_3306_);
v_a_3249_ = v_a_3340_;
goto v___jp_3248_;
}
}
v___jp_3248_:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3250_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__0));
v___x_3251_ = lean_io_error_to_string(v_a_3249_);
v___x_3252_ = lean_string_append(v___x_3250_, v___x_3251_);
lean_dec_ref(v___x_3251_);
v___x_3253_ = lean_mk_io_user_error(v___x_3252_);
v___x_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3253_);
return v___x_3254_;
}
v___jp_3255_:
{
if (lean_obj_tag(v___y_3256_) == 0)
{
lean_object* v_a_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3265_; 
v_a_3257_ = lean_ctor_get(v___y_3256_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___y_3256_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3259_ = v___y_3256_;
v_isShared_3260_ = v_isSharedCheck_3265_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_a_3257_);
lean_dec(v___y_3256_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3265_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v_a_3261_; lean_object* v___x_3263_; 
v_a_3261_ = lean_ctor_get(v_a_3257_, 0);
lean_inc(v_a_3261_);
lean_dec(v_a_3257_);
if (v_isShared_3260_ == 0)
{
lean_ctor_set(v___x_3259_, 0, v_a_3261_);
v___x_3263_ = v___x_3259_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3261_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
else
{
lean_object* v_a_3266_; 
v_a_3266_ = lean_ctor_get(v___y_3256_, 0);
lean_inc(v_a_3266_);
lean_dec_ref(v___y_3256_);
v_a_3249_ = v_a_3266_;
goto v___jp_3248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___boxed(lean_object* v_cache_3341_, lean_object* v_file_3342_, lean_object* v_ext_3343_, lean_object* v_text_3344_, lean_object* v_exe_3345_, lean_object* v_useLocalFile_3346_, lean_object* v_a_3347_){
_start:
{
uint8_t v_text_boxed_3348_; uint8_t v_exe_boxed_3349_; uint8_t v_useLocalFile_boxed_3350_; lean_object* v_res_3351_; 
v_text_boxed_3348_ = lean_unbox(v_text_3344_);
v_exe_boxed_3349_ = lean_unbox(v_exe_3345_);
v_useLocalFile_boxed_3350_ = lean_unbox(v_useLocalFile_3346_);
v_res_3351_ = l_Lake_Cache_saveArtifact(v_cache_3341_, v_file_3342_, v_ext_3343_, v_text_boxed_3348_, v_exe_boxed_3349_, v_useLocalFile_boxed_3350_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0(lean_object* v_x_3352_){
_start:
{
lean_object* v_lakeCache_3353_; 
v_lakeCache_3353_ = lean_ctor_get(v_x_3352_, 3);
lean_inc_ref(v_lakeCache_3353_);
return v_lakeCache_3353_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0___boxed(lean_object* v_x_3354_){
_start:
{
lean_object* v_res_3355_; 
v_res_3355_ = l_Lake_cacheArtifact___redArg___lam__0(v_x_3354_);
lean_dec_ref(v_x_3354_);
return v_res_3355_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1(lean_object* v_file_3356_, lean_object* v_ext_3357_, uint8_t v_text_3358_, uint8_t v_exe_3359_, uint8_t v_useLocalFile_3360_, lean_object* v_inst_3361_, lean_object* v_____do__lift_3362_){
_start:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3363_ = lean_box(v_text_3358_);
v___x_3364_ = lean_box(v_exe_3359_);
v___x_3365_ = lean_box(v_useLocalFile_3360_);
v___x_3366_ = lean_alloc_closure((void*)(l_Lake_Cache_saveArtifact___boxed), 7, 6);
lean_closure_set(v___x_3366_, 0, v_____do__lift_3362_);
lean_closure_set(v___x_3366_, 1, v_file_3356_);
lean_closure_set(v___x_3366_, 2, v_ext_3357_);
lean_closure_set(v___x_3366_, 3, v___x_3363_);
lean_closure_set(v___x_3366_, 4, v___x_3364_);
lean_closure_set(v___x_3366_, 5, v___x_3365_);
v___x_3367_ = lean_apply_2(v_inst_3361_, lean_box(0), v___x_3366_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1___boxed(lean_object* v_file_3368_, lean_object* v_ext_3369_, lean_object* v_text_3370_, lean_object* v_exe_3371_, lean_object* v_useLocalFile_3372_, lean_object* v_inst_3373_, lean_object* v_____do__lift_3374_){
_start:
{
uint8_t v_text_boxed_3375_; uint8_t v_exe_boxed_3376_; uint8_t v_useLocalFile_boxed_3377_; lean_object* v_res_3378_; 
v_text_boxed_3375_ = lean_unbox(v_text_3370_);
v_exe_boxed_3376_ = lean_unbox(v_exe_3371_);
v_useLocalFile_boxed_3377_ = lean_unbox(v_useLocalFile_3372_);
v_res_3378_ = l_Lake_cacheArtifact___redArg___lam__1(v_file_3368_, v_ext_3369_, v_text_boxed_3375_, v_exe_boxed_3376_, v_useLocalFile_boxed_3377_, v_inst_3373_, v_____do__lift_3374_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg(lean_object* v_inst_3380_, lean_object* v_inst_3381_, lean_object* v_inst_3382_, lean_object* v_file_3383_, lean_object* v_ext_3384_, uint8_t v_text_3385_, uint8_t v_exe_3386_, uint8_t v_useLocalFile_3387_){
_start:
{
lean_object* v_toApplicative_3388_; lean_object* v_toFunctor_3389_; lean_object* v_toBind_3390_; lean_object* v_map_3391_; lean_object* v___f_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___f_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v_toApplicative_3388_ = lean_ctor_get(v_inst_3382_, 0);
v_toFunctor_3389_ = lean_ctor_get(v_toApplicative_3388_, 0);
lean_inc_ref(v_toFunctor_3389_);
v_toBind_3390_ = lean_ctor_get(v_inst_3382_, 1);
lean_inc(v_toBind_3390_);
lean_dec_ref(v_inst_3382_);
v_map_3391_ = lean_ctor_get(v_toFunctor_3389_, 0);
lean_inc(v_map_3391_);
lean_dec_ref(v_toFunctor_3389_);
v___f_3392_ = ((lean_object*)(l_Lake_cacheArtifact___redArg___closed__0));
v___x_3393_ = lean_box(v_text_3385_);
v___x_3394_ = lean_box(v_exe_3386_);
v___x_3395_ = lean_box(v_useLocalFile_3387_);
v___f_3396_ = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_3396_, 0, v_file_3383_);
lean_closure_set(v___f_3396_, 1, v_ext_3384_);
lean_closure_set(v___f_3396_, 2, v___x_3393_);
lean_closure_set(v___f_3396_, 3, v___x_3394_);
lean_closure_set(v___f_3396_, 4, v___x_3395_);
lean_closure_set(v___f_3396_, 5, v_inst_3381_);
v___x_3397_ = lean_apply_4(v_map_3391_, lean_box(0), lean_box(0), v___f_3392_, v_inst_3380_);
v___x_3398_ = lean_apply_4(v_toBind_3390_, lean_box(0), lean_box(0), v___x_3397_, v___f_3396_);
return v___x_3398_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___boxed(lean_object* v_inst_3399_, lean_object* v_inst_3400_, lean_object* v_inst_3401_, lean_object* v_file_3402_, lean_object* v_ext_3403_, lean_object* v_text_3404_, lean_object* v_exe_3405_, lean_object* v_useLocalFile_3406_){
_start:
{
uint8_t v_text_boxed_3407_; uint8_t v_exe_boxed_3408_; uint8_t v_useLocalFile_boxed_3409_; lean_object* v_res_3410_; 
v_text_boxed_3407_ = lean_unbox(v_text_3404_);
v_exe_boxed_3408_ = lean_unbox(v_exe_3405_);
v_useLocalFile_boxed_3409_ = lean_unbox(v_useLocalFile_3406_);
v_res_3410_ = l_Lake_cacheArtifact___redArg(v_inst_3399_, v_inst_3400_, v_inst_3401_, v_file_3402_, v_ext_3403_, v_text_boxed_3407_, v_exe_boxed_3408_, v_useLocalFile_boxed_3409_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact(lean_object* v_m_3411_, lean_object* v_inst_3412_, lean_object* v_inst_3413_, lean_object* v_inst_3414_, lean_object* v_file_3415_, lean_object* v_ext_3416_, uint8_t v_text_3417_, uint8_t v_exe_3418_, uint8_t v_useLocalFile_3419_){
_start:
{
lean_object* v_toApplicative_3420_; lean_object* v_toFunctor_3421_; lean_object* v_toBind_3422_; lean_object* v_map_3423_; lean_object* v___f_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___f_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
v_toApplicative_3420_ = lean_ctor_get(v_inst_3414_, 0);
v_toFunctor_3421_ = lean_ctor_get(v_toApplicative_3420_, 0);
lean_inc_ref(v_toFunctor_3421_);
v_toBind_3422_ = lean_ctor_get(v_inst_3414_, 1);
lean_inc(v_toBind_3422_);
lean_dec_ref(v_inst_3414_);
v_map_3423_ = lean_ctor_get(v_toFunctor_3421_, 0);
lean_inc(v_map_3423_);
lean_dec_ref(v_toFunctor_3421_);
v___f_3424_ = ((lean_object*)(l_Lake_cacheArtifact___redArg___closed__0));
v___x_3425_ = lean_box(v_text_3417_);
v___x_3426_ = lean_box(v_exe_3418_);
v___x_3427_ = lean_box(v_useLocalFile_3419_);
v___f_3428_ = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_3428_, 0, v_file_3415_);
lean_closure_set(v___f_3428_, 1, v_ext_3416_);
lean_closure_set(v___f_3428_, 2, v___x_3425_);
lean_closure_set(v___f_3428_, 3, v___x_3426_);
lean_closure_set(v___f_3428_, 4, v___x_3427_);
lean_closure_set(v___f_3428_, 5, v_inst_3413_);
v___x_3429_ = lean_apply_4(v_map_3423_, lean_box(0), lean_box(0), v___f_3424_, v_inst_3412_);
v___x_3430_ = lean_apply_4(v_toBind_3422_, lean_box(0), lean_box(0), v___x_3429_, v___f_3428_);
return v___x_3430_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___boxed(lean_object* v_m_3431_, lean_object* v_inst_3432_, lean_object* v_inst_3433_, lean_object* v_inst_3434_, lean_object* v_file_3435_, lean_object* v_ext_3436_, lean_object* v_text_3437_, lean_object* v_exe_3438_, lean_object* v_useLocalFile_3439_){
_start:
{
uint8_t v_text_boxed_3440_; uint8_t v_exe_boxed_3441_; uint8_t v_useLocalFile_boxed_3442_; lean_object* v_res_3443_; 
v_text_boxed_3440_ = lean_unbox(v_text_3437_);
v_exe_boxed_3441_ = lean_unbox(v_exe_3438_);
v_useLocalFile_boxed_3442_ = lean_unbox(v_useLocalFile_3439_);
v_res_3443_ = l_Lake_cacheArtifact(v_m_3431_, v_inst_3432_, v_inst_3433_, v_inst_3434_, v_file_3435_, v_ext_3436_, v_text_boxed_3440_, v_exe_boxed_3441_, v_useLocalFile_boxed_3442_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0(lean_object* v_x1_3445_, lean_object* v_x2_3446_){
_start:
{
lean_object* v_message_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
v_message_3447_ = lean_ctor_get(v_x2_3446_, 0);
v___x_3448_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0));
v___x_3449_ = lean_string_append(v_x1_3445_, v___x_3448_);
v___x_3450_ = lean_string_append(v___x_3449_, v_message_3447_);
return v___x_3450_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___boxed(lean_object* v_x1_3451_, lean_object* v_x2_3452_){
_start:
{
lean_object* v_res_3453_; 
v_res_3453_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0(v_x1_3451_, v_x2_3452_);
lean_dec_ref(v_x2_3452_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(lean_object* v_inst_3457_, uint64_t v_inputHash_3458_, lean_object* v_pkg_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_){
_start:
{
lean_object* v_toContext_3467_; lean_object* v_log_3468_; uint8_t v_action_3469_; uint8_t v_wantsRebuild_3470_; lean_object* v_trace_3471_; lean_object* v_buildTime_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3567_; 
v_toContext_3467_ = lean_ctor_get(v_a_3464_, 1);
v_log_3468_ = lean_ctor_get(v_a_3465_, 0);
v_action_3469_ = lean_ctor_get_uint8(v_a_3465_, sizeof(void*)*3);
v_wantsRebuild_3470_ = lean_ctor_get_uint8(v_a_3465_, sizeof(void*)*3 + 1);
v_trace_3471_ = lean_ctor_get(v_a_3465_, 1);
v_buildTime_3472_ = lean_ctor_get(v_a_3465_, 2);
v_isSharedCheck_3567_ = !lean_is_exclusive(v_a_3465_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3474_ = v_a_3465_;
v_isShared_3475_ = v_isSharedCheck_3567_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_buildTime_3472_);
lean_inc(v_trace_3471_);
lean_inc(v_log_3468_);
lean_dec(v_a_3465_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3567_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v_lakeCache_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; 
v_lakeCache_3476_ = lean_ctor_get(v_toContext_3467_, 3);
v___x_3477_ = l_Lake_Package_cacheScope(v_pkg_3459_);
lean_inc_ref(v_lakeCache_3476_);
v___x_3478_ = l_Lake_Cache_readOutputs_x3f(v_lakeCache_3476_, v___x_3477_, v_inputHash_3458_, v_log_3468_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v_a_3479_; lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3554_; 
v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
v_a_3480_ = lean_ctor_get(v___x_3478_, 1);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3482_ = v___x_3478_;
v_isShared_3483_ = v_isSharedCheck_3554_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_inc(v_a_3479_);
lean_dec(v___x_3478_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3554_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3485_; 
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 0, v_a_3480_);
v___x_3485_ = v___x_3474_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_a_3480_);
lean_ctor_set(v_reuseFailAlloc_3553_, 1, v_trace_3471_);
lean_ctor_set(v_reuseFailAlloc_3553_, 2, v_buildTime_3472_);
lean_ctor_set_uint8(v_reuseFailAlloc_3553_, sizeof(void*)*3, v_action_3469_);
lean_ctor_set_uint8(v_reuseFailAlloc_3553_, sizeof(void*)*3 + 1, v_wantsRebuild_3470_);
v___x_3485_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
if (lean_obj_tag(v_a_3479_) == 1)
{
lean_object* v_val_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3548_; 
v_val_3486_ = lean_ctor_get(v_a_3479_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v_a_3479_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3488_ = v_a_3479_;
v_isShared_3489_ = v_isSharedCheck_3548_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_val_3486_);
lean_dec(v_a_3479_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3548_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3490_; lean_object* v_r_3492_; lean_object* v___y_3493_; 
lean_inc(v_a_3463_);
lean_inc(v_a_3462_);
lean_inc(v_a_3461_);
v___x_3490_ = lean_apply_8(v_inst_3457_, v_val_3486_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v___x_3485_, lean_box(0));
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v_a_3497_; lean_object* v_a_3498_; lean_object* v___x_3500_; 
v_a_3497_ = lean_ctor_get(v___x_3490_, 0);
lean_inc(v_a_3497_);
v_a_3498_ = lean_ctor_get(v___x_3490_, 1);
lean_inc(v_a_3498_);
lean_dec_ref(v___x_3490_);
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 0, v_a_3497_);
v___x_3500_ = v___x_3488_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3497_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
v_r_3492_ = v___x_3500_;
v___y_3493_ = v_a_3498_;
goto v___jp_3491_;
}
}
else
{
lean_object* v_a_3502_; lean_object* v_a_3503_; lean_object* v_log_3504_; uint8_t v_action_3505_; uint8_t v_wantsRebuild_3506_; lean_object* v_trace_3507_; lean_object* v_buildTime_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3547_; 
lean_del_object(v___x_3488_);
v_a_3502_ = lean_ctor_get(v___x_3490_, 1);
lean_inc(v_a_3502_);
v_a_3503_ = lean_ctor_get(v___x_3490_, 0);
lean_inc(v_a_3503_);
lean_dec_ref(v___x_3490_);
v_log_3504_ = lean_ctor_get(v_a_3502_, 0);
v_action_3505_ = lean_ctor_get_uint8(v_a_3502_, sizeof(void*)*3);
v_wantsRebuild_3506_ = lean_ctor_get_uint8(v_a_3502_, sizeof(void*)*3 + 1);
v_trace_3507_ = lean_ctor_get(v_a_3502_, 1);
v_buildTime_3508_ = lean_ctor_get(v_a_3502_, 2);
v_isSharedCheck_3547_ = !lean_is_exclusive(v_a_3502_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3510_ = v_a_3502_;
v_isShared_3511_ = v_isSharedCheck_3547_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_buildTime_3508_);
lean_inc(v_trace_3507_);
lean_inc(v_log_3504_);
lean_dec(v_a_3502_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3547_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___y_3516_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; uint8_t v___x_3538_; 
v___x_3512_ = lean_array_get_size(v_log_3504_);
lean_inc(v_a_3503_);
v___x_3513_ = l_Array_extract___redArg(v_log_3504_, v_a_3503_, v___x_3512_);
v___x_3514_ = l_Array_shrink___redArg(v_log_3504_, v_a_3503_);
lean_dec(v_a_3503_);
v___x_3524_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0));
v___x_3525_ = l_Lake_Hash_hex(v_inputHash_3458_);
v___x_3526_ = lean_unsigned_to_nat(7u);
v___x_3527_ = lean_unsigned_to_nat(0u);
v___x_3528_ = lean_string_utf8_byte_size(v___x_3525_);
lean_inc_ref(v___x_3525_);
v___x_3529_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3525_);
lean_ctor_set(v___x_3529_, 1, v___x_3527_);
lean_ctor_set(v___x_3529_, 2, v___x_3528_);
v___x_3530_ = l_String_Slice_Pos_nextn(v___x_3529_, v___x_3527_, v___x_3526_);
lean_dec_ref(v___x_3529_);
v___x_3531_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3525_);
lean_ctor_set(v___x_3531_, 1, v___x_3527_);
lean_ctor_set(v___x_3531_, 2, v___x_3530_);
v___x_3532_ = l_String_Slice_toString(v___x_3531_);
lean_dec_ref(v___x_3531_);
v___x_3533_ = lean_string_append(v___x_3524_, v___x_3532_);
lean_dec_ref(v___x_3532_);
v___x_3534_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1));
v___x_3535_ = lean_string_append(v___x_3533_, v___x_3534_);
v___x_3536_ = lean_array_get_size(v___x_3513_);
v___x_3537_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__9));
v___x_3538_ = lean_nat_dec_lt(v___x_3527_, v___x_3536_);
if (v___x_3538_ == 0)
{
lean_dec_ref(v___x_3513_);
v___y_3516_ = v___x_3535_;
goto v___jp_3515_;
}
else
{
lean_object* v___f_3539_; uint8_t v___x_3540_; 
v___f_3539_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__2));
v___x_3540_ = lean_nat_dec_le(v___x_3536_, v___x_3536_);
if (v___x_3540_ == 0)
{
if (v___x_3538_ == 0)
{
lean_dec_ref(v___x_3513_);
v___y_3516_ = v___x_3535_;
goto v___jp_3515_;
}
else
{
size_t v___x_3541_; size_t v___x_3542_; lean_object* v___x_3543_; 
v___x_3541_ = ((size_t)0ULL);
v___x_3542_ = lean_usize_of_nat(v___x_3536_);
v___x_3543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3537_, v___f_3539_, v___x_3513_, v___x_3541_, v___x_3542_, v___x_3535_);
v___y_3516_ = v___x_3543_;
goto v___jp_3515_;
}
}
else
{
size_t v___x_3544_; size_t v___x_3545_; lean_object* v___x_3546_; 
v___x_3544_ = ((size_t)0ULL);
v___x_3545_ = lean_usize_of_nat(v___x_3536_);
v___x_3546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3537_, v___f_3539_, v___x_3513_, v___x_3544_, v___x_3545_, v___x_3535_);
v___y_3516_ = v___x_3546_;
goto v___jp_3515_;
}
}
v___jp_3515_:
{
uint8_t v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3521_; 
v___x_3517_ = 2;
v___x_3518_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3518_, 0, v___y_3516_);
lean_ctor_set_uint8(v___x_3518_, sizeof(void*)*1, v___x_3517_);
v___x_3519_ = lean_array_push(v___x_3514_, v___x_3518_);
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 0, v___x_3519_);
v___x_3521_ = v___x_3510_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3519_);
lean_ctor_set(v_reuseFailAlloc_3523_, 1, v_trace_3507_);
lean_ctor_set(v_reuseFailAlloc_3523_, 2, v_buildTime_3508_);
lean_ctor_set_uint8(v_reuseFailAlloc_3523_, sizeof(void*)*3, v_action_3505_);
lean_ctor_set_uint8(v_reuseFailAlloc_3523_, sizeof(void*)*3 + 1, v_wantsRebuild_3506_);
v___x_3521_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
lean_object* v___x_3522_; 
v___x_3522_ = lean_box(0);
v_r_3492_ = v___x_3522_;
v___y_3493_ = v___x_3521_;
goto v___jp_3491_;
}
}
}
}
v___jp_3491_:
{
lean_object* v___x_3495_; 
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 1, v___y_3493_);
lean_ctor_set(v___x_3482_, 0, v_r_3492_);
v___x_3495_ = v___x_3482_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_r_3492_);
lean_ctor_set(v_reuseFailAlloc_3496_, 1, v___y_3493_);
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
lean_object* v___x_3549_; lean_object* v___x_3551_; 
lean_dec(v_a_3479_);
lean_dec_ref(v_a_3464_);
lean_dec_ref(v_a_3460_);
lean_dec_ref(v_inst_3457_);
v___x_3549_ = lean_box(0);
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 1, v___x_3485_);
lean_ctor_set(v___x_3482_, 0, v___x_3549_);
v___x_3551_ = v___x_3482_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_3549_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v___x_3485_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
}
else
{
lean_object* v_a_3555_; lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3566_; 
lean_dec_ref(v_a_3464_);
lean_dec_ref(v_a_3460_);
lean_dec_ref(v_inst_3457_);
v_a_3555_ = lean_ctor_get(v___x_3478_, 0);
v_a_3556_ = lean_ctor_get(v___x_3478_, 1);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3558_ = v___x_3478_;
v_isShared_3559_ = v_isSharedCheck_3566_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_inc(v_a_3555_);
lean_dec(v___x_3478_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3566_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 0, v_a_3556_);
v___x_3561_ = v___x_3474_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3556_);
lean_ctor_set(v_reuseFailAlloc_3565_, 1, v_trace_3471_);
lean_ctor_set(v_reuseFailAlloc_3565_, 2, v_buildTime_3472_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, sizeof(void*)*3, v_action_3469_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, sizeof(void*)*3 + 1, v_wantsRebuild_3470_);
v___x_3561_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
lean_object* v___x_3563_; 
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 1, v___x_3561_);
v___x_3563_ = v___x_3558_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3555_);
lean_ctor_set(v_reuseFailAlloc_3564_, 1, v___x_3561_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___boxed(lean_object* v_inst_3568_, lean_object* v_inputHash_3569_, lean_object* v_pkg_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_){
_start:
{
uint64_t v_inputHash_boxed_3578_; lean_object* v_res_3579_; 
v_inputHash_boxed_3578_ = lean_unbox_uint64(v_inputHash_3569_);
lean_dec_ref(v_inputHash_3569_);
v_res_3579_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3568_, v_inputHash_boxed_3578_, v_pkg_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_);
lean_dec(v_a_3574_);
lean_dec(v_a_3573_);
lean_dec(v_a_3572_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f(lean_object* v_00_u03b1_3580_, lean_object* v_inst_3581_, uint64_t v_inputHash_3582_, lean_object* v_pkg_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_){
_start:
{
lean_object* v___x_3591_; 
lean_inc_ref(v_a_3588_);
v___x_3591_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3581_, v_inputHash_3582_, v_pkg_3583_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___boxed(lean_object* v_00_u03b1_3592_, lean_object* v_inst_3593_, lean_object* v_inputHash_3594_, lean_object* v_pkg_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_){
_start:
{
uint64_t v_inputHash_boxed_3603_; lean_object* v_res_3604_; 
v_inputHash_boxed_3603_ = lean_unbox_uint64(v_inputHash_3594_);
lean_dec_ref(v_inputHash_3594_);
v_res_3604_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f(v_00_u03b1_3592_, v_inst_3593_, v_inputHash_boxed_3603_, v_pkg_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_);
lean_dec_ref(v_a_3600_);
lean_dec(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec(v_a_3597_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(lean_object* v_a_3605_, lean_object* v_____r_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3614_, 0, v_a_3605_);
v___x_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3614_);
v___x_3616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3615_);
lean_ctor_set(v___x_3616_, 1, v___y_3612_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0___boxed(lean_object* v_a_3617_, lean_object* v_____r_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
lean_object* v_res_3626_; 
v_res_3626_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3617_, v_____r_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec(v___y_3622_);
lean_dec(v___y_3621_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg(lean_object* v_inst_3628_, uint64_t v_inputHash_3629_, lean_object* v_savedTrace_3630_, lean_object* v_pkg_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_){
_start:
{
lean_object* v___y_3640_; lean_object* v_a_3644_; lean_object* v_a_3645_; lean_object* v___y_3660_; 
if (lean_obj_tag(v_savedTrace_3630_) == 2)
{
lean_object* v_data_3675_; uint64_t v_depHash_3676_; lean_object* v_outputs_x3f_3677_; uint8_t v___x_3678_; 
v_data_3675_ = lean_ctor_get(v_savedTrace_3630_, 0);
lean_inc_ref(v_data_3675_);
lean_dec_ref(v_savedTrace_3630_);
v_depHash_3676_ = lean_ctor_get_uint64(v_data_3675_, sizeof(void*)*3);
v_outputs_x3f_3677_ = lean_ctor_get(v_data_3675_, 1);
lean_inc(v_outputs_x3f_3677_);
lean_dec_ref(v_data_3675_);
v___x_3678_ = lean_uint64_dec_eq(v_depHash_3676_, v_inputHash_3629_);
if (v___x_3678_ == 0)
{
lean_dec(v_outputs_x3f_3677_);
lean_dec_ref(v_a_3636_);
lean_dec_ref(v_a_3632_);
lean_dec_ref(v_pkg_3631_);
lean_dec_ref(v_inst_3628_);
v___y_3640_ = v_a_3637_;
goto v___jp_3639_;
}
else
{
if (lean_obj_tag(v_outputs_x3f_3677_) == 1)
{
lean_object* v_val_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
v_val_3679_ = lean_ctor_get(v_outputs_x3f_3677_, 0);
lean_inc(v_val_3679_);
lean_dec_ref(v_outputs_x3f_3677_);
v___x_3680_ = lean_box(0);
lean_inc(v_val_3679_);
v___x_3681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3681_, 0, v_val_3679_);
lean_ctor_set(v___x_3681_, 1, v___x_3680_);
lean_ctor_set(v___x_3681_, 2, v___x_3680_);
lean_inc_ref(v_a_3636_);
lean_inc(v_a_3635_);
lean_inc(v_a_3634_);
lean_inc(v_a_3633_);
lean_inc_ref(v_a_3632_);
v___x_3682_ = lean_apply_8(v_inst_3628_, v___x_3681_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_, lean_box(0));
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_config_3683_; lean_object* v_a_3684_; lean_object* v_a_3685_; lean_object* v_enableArtifactCache_x3f_3686_; lean_object* v_a_3688_; uint8_t v_a_3692_; lean_object* v_a_3693_; 
v_config_3683_ = lean_ctor_get(v_pkg_3631_, 6);
v_a_3684_ = lean_ctor_get(v___x_3682_, 0);
lean_inc(v_a_3684_);
v_a_3685_ = lean_ctor_get(v___x_3682_, 1);
lean_inc(v_a_3685_);
lean_dec_ref(v___x_3682_);
v_enableArtifactCache_x3f_3686_ = lean_ctor_get(v_config_3683_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_3686_) == 0)
{
lean_object* v_toContext_3724_; lean_object* v_lakeEnv_3725_; lean_object* v_enableArtifactCache_x3f_3726_; 
v_toContext_3724_ = lean_ctor_get(v_a_3636_, 1);
v_lakeEnv_3725_ = lean_ctor_get(v_toContext_3724_, 1);
v_enableArtifactCache_x3f_3726_ = lean_ctor_get(v_lakeEnv_3725_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_3726_) == 0)
{
lean_object* v_root_3727_; lean_object* v_config_3728_; lean_object* v_enableArtifactCache_x3f_3729_; 
v_root_3727_ = lean_ctor_get(v_toContext_3724_, 0);
v_config_3728_ = lean_ctor_get(v_root_3727_, 6);
v_enableArtifactCache_x3f_3729_ = lean_ctor_get(v_config_3728_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_3729_) == 0)
{
lean_dec(v_val_3679_);
lean_dec_ref(v_pkg_3631_);
v_a_3688_ = v_a_3685_;
goto v___jp_3687_;
}
else
{
lean_object* v_val_3730_; uint8_t v___x_3731_; 
v_val_3730_ = lean_ctor_get(v_enableArtifactCache_x3f_3729_, 0);
v___x_3731_ = lean_unbox(v_val_3730_);
v_a_3692_ = v___x_3731_;
v_a_3693_ = v_a_3685_;
goto v___jp_3691_;
}
}
else
{
lean_object* v_val_3732_; uint8_t v___x_3733_; 
v_val_3732_ = lean_ctor_get(v_enableArtifactCache_x3f_3726_, 0);
v___x_3733_ = lean_unbox(v_val_3732_);
v_a_3692_ = v___x_3733_;
v_a_3693_ = v_a_3685_;
goto v___jp_3691_;
}
}
else
{
lean_object* v_val_3734_; uint8_t v___x_3735_; 
v_val_3734_ = lean_ctor_get(v_enableArtifactCache_x3f_3686_, 0);
v___x_3735_ = lean_unbox(v_val_3734_);
v_a_3692_ = v___x_3735_;
v_a_3693_ = v_a_3685_;
goto v___jp_3691_;
}
v___jp_3687_:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3689_ = lean_box(0);
v___x_3690_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3684_, v___x_3689_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3688_);
lean_dec_ref(v_a_3636_);
lean_dec_ref(v_a_3632_);
v___y_3660_ = v___x_3690_;
goto v___jp_3659_;
}
v___jp_3691_:
{
if (v_a_3692_ == 0)
{
lean_dec(v_val_3679_);
lean_dec_ref(v_pkg_3631_);
v_a_3688_ = v_a_3693_;
goto v___jp_3687_;
}
else
{
lean_object* v_toContext_3694_; lean_object* v_log_3695_; uint8_t v_action_3696_; uint8_t v_wantsRebuild_3697_; lean_object* v_trace_3698_; lean_object* v_buildTime_3699_; lean_object* v_lakeCache_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
v_toContext_3694_ = lean_ctor_get(v_a_3636_, 1);
v_log_3695_ = lean_ctor_get(v_a_3693_, 0);
v_action_3696_ = lean_ctor_get_uint8(v_a_3693_, sizeof(void*)*3);
v_wantsRebuild_3697_ = lean_ctor_get_uint8(v_a_3693_, sizeof(void*)*3 + 1);
v_trace_3698_ = lean_ctor_get(v_a_3693_, 1);
v_buildTime_3699_ = lean_ctor_get(v_a_3693_, 2);
v_lakeCache_3700_ = lean_ctor_get(v_toContext_3694_, 3);
v___x_3701_ = l_Lake_Package_cacheScope(v_pkg_3631_);
lean_inc_ref(v_lakeCache_3700_);
v___x_3702_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_3700_, v___x_3701_, v_inputHash_3629_, v_val_3679_, v___x_3680_, v___x_3680_);
if (lean_obj_tag(v___x_3702_) == 0)
{
lean_object* v___x_3703_; lean_object* v___x_3704_; 
lean_dec_ref(v___x_3702_);
v___x_3703_ = lean_box(0);
v___x_3704_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3684_, v___x_3703_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3693_);
lean_dec_ref(v_a_3636_);
lean_dec_ref(v_a_3632_);
v___y_3660_ = v___x_3704_;
goto v___jp_3659_;
}
else
{
lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3720_; 
lean_inc(v_buildTime_3699_);
lean_inc_ref(v_trace_3698_);
lean_inc_ref(v_log_3695_);
v_isSharedCheck_3720_ = !lean_is_exclusive(v_a_3693_);
if (v_isSharedCheck_3720_ == 0)
{
lean_object* v_unused_3721_; lean_object* v_unused_3722_; lean_object* v_unused_3723_; 
v_unused_3721_ = lean_ctor_get(v_a_3693_, 2);
lean_dec(v_unused_3721_);
v_unused_3722_ = lean_ctor_get(v_a_3693_, 1);
lean_dec(v_unused_3722_);
v_unused_3723_ = lean_ctor_get(v_a_3693_, 0);
lean_dec(v_unused_3723_);
v___x_3706_ = v_a_3693_;
v_isShared_3707_ = v_isSharedCheck_3720_;
goto v_resetjp_3705_;
}
else
{
lean_dec(v_a_3693_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3720_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v_a_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; uint8_t v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3717_; 
v_a_3708_ = lean_ctor_get(v___x_3702_, 0);
lean_inc(v_a_3708_);
lean_dec_ref(v___x_3702_);
v___x_3709_ = ((lean_object*)(l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0));
v___x_3710_ = lean_io_error_to_string(v_a_3708_);
v___x_3711_ = lean_string_append(v___x_3709_, v___x_3710_);
lean_dec_ref(v___x_3710_);
v___x_3712_ = 2;
v___x_3713_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3713_, 0, v___x_3711_);
lean_ctor_set_uint8(v___x_3713_, sizeof(void*)*1, v___x_3712_);
v___x_3714_ = lean_box(0);
v___x_3715_ = lean_array_push(v_log_3695_, v___x_3713_);
if (v_isShared_3707_ == 0)
{
lean_ctor_set(v___x_3706_, 0, v___x_3715_);
v___x_3717_ = v___x_3706_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3715_);
lean_ctor_set(v_reuseFailAlloc_3719_, 1, v_trace_3698_);
lean_ctor_set(v_reuseFailAlloc_3719_, 2, v_buildTime_3699_);
lean_ctor_set_uint8(v_reuseFailAlloc_3719_, sizeof(void*)*3, v_action_3696_);
lean_ctor_set_uint8(v_reuseFailAlloc_3719_, sizeof(void*)*3 + 1, v_wantsRebuild_3697_);
v___x_3717_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
lean_object* v___x_3718_; 
v___x_3718_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3684_, v___x_3714_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v___x_3717_);
lean_dec_ref(v_a_3636_);
lean_dec_ref(v_a_3632_);
v___y_3660_ = v___x_3718_;
goto v___jp_3659_;
}
}
}
}
}
}
else
{
lean_object* v_a_3736_; lean_object* v_a_3737_; 
lean_dec(v_val_3679_);
lean_dec_ref(v_a_3636_);
lean_dec_ref(v_a_3632_);
lean_dec_ref(v_pkg_3631_);
v_a_3736_ = lean_ctor_get(v___x_3682_, 0);
lean_inc(v_a_3736_);
v_a_3737_ = lean_ctor_get(v___x_3682_, 1);
lean_inc(v_a_3737_);
lean_dec_ref(v___x_3682_);
v_a_3644_ = v_a_3736_;
v_a_3645_ = v_a_3737_;
goto v___jp_3643_;
}
}
else
{
lean_dec(v_outputs_x3f_3677_);
lean_dec_ref(v_a_3636_);
lean_dec_ref(v_a_3632_);
lean_dec_ref(v_pkg_3631_);
lean_dec_ref(v_inst_3628_);
v___y_3640_ = v_a_3637_;
goto v___jp_3639_;
}
}
}
else
{
lean_dec_ref(v_a_3636_);
lean_dec_ref(v_a_3632_);
lean_dec_ref(v_pkg_3631_);
lean_dec(v_savedTrace_3630_);
lean_dec_ref(v_inst_3628_);
v___y_3640_ = v_a_3637_;
goto v___jp_3639_;
}
v___jp_3639_:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3641_ = lean_box(0);
v___x_3642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3641_);
lean_ctor_set(v___x_3642_, 1, v___y_3640_);
return v___x_3642_;
}
v___jp_3643_:
{
lean_object* v_log_3646_; uint8_t v_action_3647_; uint8_t v_wantsRebuild_3648_; lean_object* v_trace_3649_; lean_object* v_buildTime_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3658_; 
v_log_3646_ = lean_ctor_get(v_a_3645_, 0);
v_action_3647_ = lean_ctor_get_uint8(v_a_3645_, sizeof(void*)*3);
v_wantsRebuild_3648_ = lean_ctor_get_uint8(v_a_3645_, sizeof(void*)*3 + 1);
v_trace_3649_ = lean_ctor_get(v_a_3645_, 1);
v_buildTime_3650_ = lean_ctor_get(v_a_3645_, 2);
v_isSharedCheck_3658_ = !lean_is_exclusive(v_a_3645_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3652_ = v_a_3645_;
v_isShared_3653_ = v_isSharedCheck_3658_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_buildTime_3650_);
lean_inc(v_trace_3649_);
lean_inc(v_log_3646_);
lean_dec(v_a_3645_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3658_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3654_; lean_object* v___x_3656_; 
v___x_3654_ = l_Array_shrink___redArg(v_log_3646_, v_a_3644_);
lean_dec(v_a_3644_);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v___x_3654_);
v___x_3656_ = v___x_3652_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3654_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v_trace_3649_);
lean_ctor_set(v_reuseFailAlloc_3657_, 2, v_buildTime_3650_);
lean_ctor_set_uint8(v_reuseFailAlloc_3657_, sizeof(void*)*3, v_action_3647_);
lean_ctor_set_uint8(v_reuseFailAlloc_3657_, sizeof(void*)*3 + 1, v_wantsRebuild_3648_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
v___y_3640_ = v___x_3656_;
goto v___jp_3639_;
}
}
}
v___jp_3659_:
{
if (lean_obj_tag(v___y_3660_) == 0)
{
lean_object* v_a_3661_; 
v_a_3661_ = lean_ctor_get(v___y_3660_, 0);
if (lean_obj_tag(v_a_3661_) == 0)
{
lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3670_; 
lean_inc_ref(v_a_3661_);
v_a_3662_ = lean_ctor_get(v___y_3660_, 1);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___y_3660_);
if (v_isSharedCheck_3670_ == 0)
{
lean_object* v_unused_3671_; 
v_unused_3671_ = lean_ctor_get(v___y_3660_, 0);
lean_dec(v_unused_3671_);
v___x_3664_ = v___y_3660_;
v_isShared_3665_ = v_isSharedCheck_3670_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v___y_3660_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3670_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v_a_3666_; lean_object* v___x_3668_; 
v_a_3666_ = lean_ctor_get(v_a_3661_, 0);
lean_inc(v_a_3666_);
lean_dec_ref(v_a_3661_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 0, v_a_3666_);
v___x_3668_ = v___x_3664_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3666_);
lean_ctor_set(v_reuseFailAlloc_3669_, 1, v_a_3662_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
else
{
lean_object* v_a_3672_; 
v_a_3672_ = lean_ctor_get(v___y_3660_, 1);
lean_inc(v_a_3672_);
lean_dec_ref(v___y_3660_);
v___y_3640_ = v_a_3672_;
goto v___jp_3639_;
}
}
else
{
lean_object* v_a_3673_; lean_object* v_a_3674_; 
v_a_3673_ = lean_ctor_get(v___y_3660_, 0);
lean_inc(v_a_3673_);
v_a_3674_ = lean_ctor_get(v___y_3660_, 1);
lean_inc(v_a_3674_);
lean_dec_ref(v___y_3660_);
v_a_3644_ = v_a_3673_;
v_a_3645_ = v_a_3674_;
goto v___jp_3643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___boxed(lean_object* v_inst_3738_, lean_object* v_inputHash_3739_, lean_object* v_savedTrace_3740_, lean_object* v_pkg_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_){
_start:
{
uint64_t v_inputHash_boxed_3749_; lean_object* v_res_3750_; 
v_inputHash_boxed_3749_ = lean_unbox_uint64(v_inputHash_3739_);
lean_dec_ref(v_inputHash_3739_);
v_res_3750_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3738_, v_inputHash_boxed_3749_, v_savedTrace_3740_, v_pkg_3741_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_);
lean_dec(v_a_3745_);
lean_dec(v_a_3744_);
lean_dec(v_a_3743_);
return v_res_3750_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f(lean_object* v_00_u03b1_3751_, lean_object* v_inst_3752_, uint64_t v_inputHash_3753_, lean_object* v_savedTrace_3754_, lean_object* v_pkg_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_){
_start:
{
lean_object* v___x_3763_; 
lean_inc_ref(v_a_3760_);
v___x_3763_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3752_, v_inputHash_3753_, v_savedTrace_3754_, v_pkg_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_);
return v___x_3763_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___boxed(lean_object* v_00_u03b1_3764_, lean_object* v_inst_3765_, lean_object* v_inputHash_3766_, lean_object* v_savedTrace_3767_, lean_object* v_pkg_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_){
_start:
{
uint64_t v_inputHash_boxed_3776_; lean_object* v_res_3777_; 
v_inputHash_boxed_3776_ = lean_unbox_uint64(v_inputHash_3766_);
lean_dec_ref(v_inputHash_3766_);
v_res_3777_ = l_Lake_getArtifactsUsingTrace_x3f(v_00_u03b1_3764_, v_inst_3765_, v_inputHash_boxed_3776_, v_savedTrace_3767_, v_pkg_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_);
lean_dec_ref(v_a_3773_);
lean_dec(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec(v_a_3770_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg(lean_object* v_inst_3778_, uint64_t v_inputHash_3779_, lean_object* v_savedTrace_3780_, lean_object* v_pkg_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_){
_start:
{
lean_object* v___x_3789_; 
lean_inc_ref(v_a_3786_);
lean_inc_ref(v_a_3782_);
lean_inc_ref(v_pkg_3781_);
lean_inc_ref(v_inst_3778_);
v___x_3789_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3778_, v_inputHash_3779_, v_pkg_3781_, v_a_3782_, v_a_3783_, v_a_3784_, v_a_3785_, v_a_3786_, v_a_3787_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v_a_3790_; 
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_a_3790_);
if (lean_obj_tag(v_a_3790_) == 1)
{
lean_dec_ref(v_a_3790_);
lean_dec_ref(v_a_3782_);
lean_dec_ref(v_pkg_3781_);
lean_dec(v_savedTrace_3780_);
lean_dec_ref(v_inst_3778_);
return v___x_3789_;
}
else
{
lean_object* v_a_3791_; lean_object* v___x_3792_; lean_object* v_a_3793_; 
lean_dec(v_a_3790_);
v_a_3791_ = lean_ctor_get(v___x_3789_, 1);
lean_inc(v_a_3791_);
lean_dec_ref(v___x_3789_);
lean_inc_ref(v_a_3786_);
v___x_3792_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3778_, v_inputHash_3779_, v_savedTrace_3780_, v_pkg_3781_, v_a_3782_, v_a_3783_, v_a_3784_, v_a_3785_, v_a_3786_, v_a_3791_);
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3793_);
if (lean_obj_tag(v_a_3793_) == 1)
{
lean_dec_ref(v_a_3793_);
return v___x_3792_;
}
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3802_; 
lean_dec(v_a_3793_);
v_a_3794_ = lean_ctor_get(v___x_3792_, 1);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3802_ == 0)
{
lean_object* v_unused_3803_; 
v_unused_3803_ = lean_ctor_get(v___x_3792_, 0);
lean_dec(v_unused_3803_);
v___x_3796_ = v___x_3792_;
v_isShared_3797_ = v_isSharedCheck_3802_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3792_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3802_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3798_; lean_object* v___x_3800_; 
v___x_3798_ = lean_box(0);
if (v_isShared_3797_ == 0)
{
lean_ctor_set(v___x_3796_, 0, v___x_3798_);
v___x_3800_ = v___x_3796_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3798_);
lean_ctor_set(v_reuseFailAlloc_3801_, 1, v_a_3794_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_3782_);
lean_dec_ref(v_pkg_3781_);
lean_dec(v_savedTrace_3780_);
lean_dec_ref(v_inst_3778_);
return v___x_3789_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___boxed(lean_object* v_inst_3804_, lean_object* v_inputHash_3805_, lean_object* v_savedTrace_3806_, lean_object* v_pkg_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_){
_start:
{
uint64_t v_inputHash_boxed_3815_; lean_object* v_res_3816_; 
v_inputHash_boxed_3815_ = lean_unbox_uint64(v_inputHash_3805_);
lean_dec_ref(v_inputHash_3805_);
v_res_3816_ = l_Lake_getArtifacts_x3f___redArg(v_inst_3804_, v_inputHash_boxed_3815_, v_savedTrace_3806_, v_pkg_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_);
lean_dec_ref(v_a_3812_);
lean_dec(v_a_3811_);
lean_dec(v_a_3810_);
lean_dec(v_a_3809_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f(lean_object* v_00_u03b1_3817_, lean_object* v_inst_3818_, uint64_t v_inputHash_3819_, lean_object* v_savedTrace_3820_, lean_object* v_pkg_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_){
_start:
{
lean_object* v___x_3829_; 
lean_inc_ref(v_a_3826_);
lean_inc_ref(v_a_3822_);
lean_inc_ref(v_pkg_3821_);
lean_inc_ref(v_inst_3818_);
v___x_3829_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3818_, v_inputHash_3819_, v_pkg_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_);
if (lean_obj_tag(v___x_3829_) == 0)
{
lean_object* v_a_3830_; 
v_a_3830_ = lean_ctor_get(v___x_3829_, 0);
lean_inc(v_a_3830_);
if (lean_obj_tag(v_a_3830_) == 1)
{
lean_dec_ref(v_a_3830_);
lean_dec_ref(v_a_3822_);
lean_dec_ref(v_pkg_3821_);
lean_dec(v_savedTrace_3820_);
lean_dec_ref(v_inst_3818_);
return v___x_3829_;
}
else
{
lean_object* v_a_3831_; lean_object* v___x_3832_; lean_object* v_a_3833_; 
lean_dec(v_a_3830_);
v_a_3831_ = lean_ctor_get(v___x_3829_, 1);
lean_inc(v_a_3831_);
lean_dec_ref(v___x_3829_);
lean_inc_ref(v_a_3826_);
v___x_3832_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3818_, v_inputHash_3819_, v_savedTrace_3820_, v_pkg_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3831_);
v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
lean_inc(v_a_3833_);
if (lean_obj_tag(v_a_3833_) == 1)
{
lean_dec_ref(v_a_3833_);
return v___x_3832_;
}
else
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3842_; 
lean_dec(v_a_3833_);
v_a_3834_ = lean_ctor_get(v___x_3832_, 1);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3842_ == 0)
{
lean_object* v_unused_3843_; 
v_unused_3843_ = lean_ctor_get(v___x_3832_, 0);
lean_dec(v_unused_3843_);
v___x_3836_ = v___x_3832_;
v_isShared_3837_ = v_isSharedCheck_3842_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3832_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3842_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3838_; lean_object* v___x_3840_; 
v___x_3838_ = lean_box(0);
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 0, v___x_3838_);
v___x_3840_ = v___x_3836_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v___x_3838_);
lean_ctor_set(v_reuseFailAlloc_3841_, 1, v_a_3834_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_3822_);
lean_dec_ref(v_pkg_3821_);
lean_dec(v_savedTrace_3820_);
lean_dec_ref(v_inst_3818_);
return v___x_3829_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___boxed(lean_object* v_00_u03b1_3844_, lean_object* v_inst_3845_, lean_object* v_inputHash_3846_, lean_object* v_savedTrace_3847_, lean_object* v_pkg_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_){
_start:
{
uint64_t v_inputHash_boxed_3856_; lean_object* v_res_3857_; 
v_inputHash_boxed_3856_ = lean_unbox_uint64(v_inputHash_3846_);
lean_dec_ref(v_inputHash_3846_);
v_res_3857_ = l_Lake_getArtifacts_x3f(v_00_u03b1_3844_, v_inst_3845_, v_inputHash_boxed_3856_, v_savedTrace_3847_, v_pkg_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_);
lean_dec_ref(v_a_3853_);
lean_dec(v_a_3852_);
lean_dec(v_a_3851_);
lean_dec(v_a_3850_);
return v_res_3857_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__0(lean_object* v_descr_3858_, lean_object* v___x_3859_, lean_object* v_mtime_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
lean_inc_ref(v___x_3859_);
v___x_3868_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3868_, 0, v_descr_3858_);
lean_ctor_set(v___x_3868_, 1, v___x_3859_);
lean_ctor_set(v___x_3868_, 2, v___x_3859_);
lean_ctor_set(v___x_3868_, 3, v_mtime_3860_);
v___x_3869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3868_);
lean_ctor_set(v___x_3869_, 1, v___y_3866_);
return v___x_3869_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__0___boxed(lean_object* v_descr_3870_, lean_object* v___x_3871_, lean_object* v_mtime_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_){
_start:
{
lean_object* v_res_3880_; 
v_res_3880_ = l_Lake_resolveArtifact___lam__0(v_descr_3870_, v___x_3871_, v_mtime_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_);
lean_dec_ref(v___y_3877_);
lean_dec(v___y_3876_);
lean_dec(v___y_3875_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__1(lean_object* v___x_3882_, lean_object* v___f_3883_, lean_object* v_____r_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_){
_start:
{
lean_object* v_log_3892_; uint8_t v_action_3893_; uint8_t v_wantsRebuild_3894_; lean_object* v_trace_3895_; lean_object* v_buildTime_3896_; lean_object* v___x_3897_; 
v_log_3892_ = lean_ctor_get(v___y_3890_, 0);
v_action_3893_ = lean_ctor_get_uint8(v___y_3890_, sizeof(void*)*3);
v_wantsRebuild_3894_ = lean_ctor_get_uint8(v___y_3890_, sizeof(void*)*3 + 1);
v_trace_3895_ = lean_ctor_get(v___y_3890_, 1);
v_buildTime_3896_ = lean_ctor_get(v___y_3890_, 2);
v___x_3897_ = lean_io_metadata(v___x_3882_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; lean_object* v_modified_3899_; lean_object* v___x_3900_; 
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_a_3898_);
lean_dec_ref(v___x_3897_);
v_modified_3899_ = lean_ctor_get(v_a_3898_, 1);
lean_inc_ref(v_modified_3899_);
lean_dec(v_a_3898_);
lean_inc_ref(v___y_3889_);
lean_inc(v___y_3888_);
lean_inc(v___y_3887_);
lean_inc(v___y_3886_);
v___x_3900_ = lean_apply_8(v___f_3883_, v_modified_3899_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_, lean_box(0));
return v___x_3900_;
}
else
{
lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3916_; 
lean_inc(v_buildTime_3896_);
lean_inc_ref(v_trace_3895_);
lean_inc_ref(v_log_3892_);
lean_dec_ref(v___y_3885_);
lean_dec_ref(v___f_3883_);
v_isSharedCheck_3916_ = !lean_is_exclusive(v___y_3890_);
if (v_isSharedCheck_3916_ == 0)
{
lean_object* v_unused_3917_; lean_object* v_unused_3918_; lean_object* v_unused_3919_; 
v_unused_3917_ = lean_ctor_get(v___y_3890_, 2);
lean_dec(v_unused_3917_);
v_unused_3918_ = lean_ctor_get(v___y_3890_, 1);
lean_dec(v_unused_3918_);
v_unused_3919_ = lean_ctor_get(v___y_3890_, 0);
lean_dec(v_unused_3919_);
v___x_3902_ = v___y_3890_;
v_isShared_3903_ = v_isSharedCheck_3916_;
goto v_resetjp_3901_;
}
else
{
lean_dec(v___y_3890_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3916_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v_a_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; uint8_t v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3913_; 
v_a_3904_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_a_3904_);
lean_dec_ref(v___x_3897_);
v___x_3905_ = ((lean_object*)(l_Lake_resolveArtifact___lam__1___closed__0));
v___x_3906_ = lean_io_error_to_string(v_a_3904_);
v___x_3907_ = lean_string_append(v___x_3905_, v___x_3906_);
lean_dec_ref(v___x_3906_);
v___x_3908_ = 3;
v___x_3909_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3909_, 0, v___x_3907_);
lean_ctor_set_uint8(v___x_3909_, sizeof(void*)*1, v___x_3908_);
v___x_3910_ = lean_array_get_size(v_log_3892_);
v___x_3911_ = lean_array_push(v_log_3892_, v___x_3909_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 0, v___x_3911_);
v___x_3913_ = v___x_3902_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v___x_3911_);
lean_ctor_set(v_reuseFailAlloc_3915_, 1, v_trace_3895_);
lean_ctor_set(v_reuseFailAlloc_3915_, 2, v_buildTime_3896_);
lean_ctor_set_uint8(v_reuseFailAlloc_3915_, sizeof(void*)*3, v_action_3893_);
lean_ctor_set_uint8(v_reuseFailAlloc_3915_, sizeof(void*)*3 + 1, v_wantsRebuild_3894_);
v___x_3913_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
lean_object* v___x_3914_; 
v___x_3914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3910_);
lean_ctor_set(v___x_3914_, 1, v___x_3913_);
return v___x_3914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__1___boxed(lean_object* v___x_3920_, lean_object* v___f_3921_, lean_object* v_____r_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_){
_start:
{
lean_object* v_res_3930_; 
v_res_3930_ = l_Lake_resolveArtifact___lam__1(v___x_3920_, v___f_3921_, v_____r_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_);
lean_dec_ref(v___y_3927_);
lean_dec(v___y_3926_);
lean_dec(v___y_3925_);
lean_dec(v___y_3924_);
lean_dec_ref(v___x_3920_);
return v_res_3930_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact(lean_object* v_descr_3942_, lean_object* v_service_x3f_3943_, lean_object* v_scope_x3f_3944_, uint8_t v_exe_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_){
_start:
{
lean_object* v___y_3954_; lean_object* v_a_3955_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v_toContext_3961_; lean_object* v_log_3962_; uint8_t v_action_3963_; uint8_t v_wantsRebuild_3964_; lean_object* v_trace_3965_; lean_object* v_buildTime_3966_; lean_object* v_lakeConfig_3967_; lean_object* v_lakeCache_3968_; uint64_t v_hash_3969_; lean_object* v_ext_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___y_3974_; lean_object* v___x_4072_; lean_object* v___x_4073_; uint8_t v___x_4074_; 
v_toContext_3961_ = lean_ctor_get(v_a_3950_, 1);
v_log_3962_ = lean_ctor_get(v_a_3951_, 0);
v_action_3963_ = lean_ctor_get_uint8(v_a_3951_, sizeof(void*)*3);
v_wantsRebuild_3964_ = lean_ctor_get_uint8(v_a_3951_, sizeof(void*)*3 + 1);
v_trace_3965_ = lean_ctor_get(v_a_3951_, 1);
v_buildTime_3966_ = lean_ctor_get(v_a_3951_, 2);
v_lakeConfig_3967_ = lean_ctor_get(v_toContext_3961_, 2);
v_lakeCache_3968_ = lean_ctor_get(v_toContext_3961_, 3);
v_hash_3969_ = lean_ctor_get_uint64(v_descr_3942_, sizeof(void*)*1);
v_ext_3970_ = lean_ctor_get(v_descr_3942_, 0);
v___x_3971_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
lean_inc_ref(v_lakeCache_3968_);
v___x_3972_ = l_System_FilePath_join(v_lakeCache_3968_, v___x_3971_);
v___x_4072_ = lean_string_utf8_byte_size(v_ext_3970_);
v___x_4073_ = lean_unsigned_to_nat(0u);
v___x_4074_ = lean_nat_dec_eq(v___x_4072_, v___x_4073_);
if (v___x_4074_ == 0)
{
lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4075_ = l_Lake_Hash_hex(v_hash_3969_);
v___x_4076_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_4077_ = lean_string_append(v___x_4075_, v___x_4076_);
v___x_4078_ = lean_string_append(v___x_4077_, v_ext_3970_);
v___y_3974_ = v___x_4078_;
goto v___jp_3973_;
}
else
{
lean_object* v___x_4079_; 
v___x_4079_ = l_Lake_Hash_hex(v_hash_3969_);
v___y_3974_ = v___x_4079_;
goto v___jp_3973_;
}
v___jp_3953_:
{
lean_object* v___x_3956_; 
v___x_3956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3956_, 0, v___y_3954_);
lean_ctor_set(v___x_3956_, 1, v_a_3955_);
return v___x_3956_;
}
v___jp_3957_:
{
if (lean_obj_tag(v___y_3959_) == 0)
{
lean_dec(v___y_3958_);
return v___y_3959_;
}
else
{
lean_object* v_a_3960_; 
v_a_3960_ = lean_ctor_get(v___y_3959_, 1);
lean_inc(v_a_3960_);
lean_dec_ref(v___y_3959_);
v___y_3954_ = v___y_3958_;
v_a_3955_ = v_a_3960_;
goto v___jp_3953_;
}
}
v___jp_3973_:
{
lean_object* v___x_3975_; lean_object* v___f_3976_; lean_object* v___x_3977_; 
v___x_3975_ = l_Lake_joinRelative(v___x_3972_, v___y_3974_);
lean_inc_ref(v___x_3975_);
lean_inc_ref(v_descr_3942_);
v___f_3976_ = lean_alloc_closure((void*)(l_Lake_resolveArtifact___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3976_, 0, v_descr_3942_);
lean_closure_set(v___f_3976_, 1, v___x_3975_);
v___x_3977_ = lean_io_metadata(v___x_3975_);
if (lean_obj_tag(v___x_3977_) == 0)
{
lean_object* v_a_3978_; lean_object* v_modified_3979_; lean_object* v___x_3980_; 
lean_dec_ref(v___f_3976_);
lean_dec(v_scope_x3f_3944_);
lean_dec(v_service_x3f_3943_);
v_a_3978_ = lean_ctor_get(v___x_3977_, 0);
lean_inc(v_a_3978_);
lean_dec_ref(v___x_3977_);
v_modified_3979_ = lean_ctor_get(v_a_3978_, 1);
lean_inc_ref(v_modified_3979_);
lean_dec(v_a_3978_);
v___x_3980_ = l_Lake_resolveArtifact___lam__0(v_descr_3942_, v___x_3975_, v_modified_3979_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
lean_dec_ref(v_a_3950_);
lean_dec_ref(v_a_3946_);
return v___x_3980_;
}
else
{
lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_4068_; 
lean_inc(v_buildTime_3966_);
lean_inc_ref(v_trace_3965_);
lean_inc_ref(v_log_3962_);
lean_dec_ref(v_descr_3942_);
v_isSharedCheck_4068_ = !lean_is_exclusive(v_a_3951_);
if (v_isSharedCheck_4068_ == 0)
{
lean_object* v_unused_4069_; lean_object* v_unused_4070_; lean_object* v_unused_4071_; 
v_unused_4069_ = lean_ctor_get(v_a_3951_, 2);
lean_dec(v_unused_4069_);
v_unused_4070_ = lean_ctor_get(v_a_3951_, 1);
lean_dec(v_unused_4070_);
v_unused_4071_ = lean_ctor_get(v_a_3951_, 0);
lean_dec(v_unused_4071_);
v___x_3982_ = v_a_3951_;
v_isShared_3983_ = v_isSharedCheck_4068_;
goto v_resetjp_3981_;
}
else
{
lean_dec(v_a_3951_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_4068_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v_a_3984_; 
v_a_3984_ = lean_ctor_get(v___x_3977_, 0);
lean_inc(v_a_3984_);
lean_dec_ref(v___x_3977_);
if (lean_obj_tag(v_a_3984_) == 11)
{
lean_object* v___x_3985_; 
lean_dec_ref(v_a_3984_);
v___x_3985_ = lean_array_get_size(v_log_3962_);
if (lean_obj_tag(v_service_x3f_3943_) == 1)
{
lean_object* v_val_3986_; lean_object* v_cacheServices_3987_; uint8_t v___x_3988_; uint8_t v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; 
v_val_3986_ = lean_ctor_get(v_service_x3f_3943_, 0);
lean_inc(v_val_3986_);
lean_dec_ref(v_service_x3f_3943_);
v_cacheServices_3987_ = lean_ctor_get(v_lakeConfig_3967_, 3);
v___x_3988_ = 2;
v___x_3989_ = l_Lake_JobAction_merge(v_action_3963_, v___x_3988_);
v___x_3990_ = lean_box(0);
lean_inc(v_val_3986_);
v___x_3991_ = l_Lean_Name_str___override(v___x_3990_, v_val_3986_);
v___x_3992_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_cacheServices_3987_, v___x_3991_);
lean_dec(v___x_3991_);
if (lean_obj_tag(v___x_3992_) == 1)
{
lean_dec(v_val_3986_);
if (lean_obj_tag(v_scope_x3f_3944_) == 1)
{
lean_object* v_val_3993_; lean_object* v_val_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; uint8_t v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v_val_3993_ = lean_ctor_get(v___x_3992_, 0);
lean_inc(v_val_3993_);
lean_dec_ref(v___x_3992_);
v_val_3994_ = lean_ctor_get(v_scope_x3f_3944_, 0);
lean_inc(v_val_3994_);
lean_dec_ref(v_scope_x3f_3944_);
v___x_3995_ = l_Lake_CacheService_artifactUrl(v_hash_3969_, v_val_3993_, v_val_3994_);
v___x_3996_ = ((lean_object*)(l_Lake_resolveArtifact___closed__0));
v___x_3997_ = l_Lake_Hash_hex(v_hash_3969_);
v___x_3998_ = lean_string_append(v___x_3996_, v___x_3997_);
lean_dec_ref(v___x_3997_);
v___x_3999_ = ((lean_object*)(l_Lake_resolveArtifact___closed__1));
v___x_4000_ = lean_string_append(v___x_3998_, v___x_3999_);
v___x_4001_ = lean_string_append(v___x_4000_, v___x_3975_);
v___x_4002_ = ((lean_object*)(l_Lake_resolveArtifact___closed__2));
v___x_4003_ = lean_string_append(v___x_4001_, v___x_4002_);
v___x_4004_ = lean_string_append(v___x_4003_, v___x_3995_);
v___x_4005_ = 0;
v___x_4006_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4006_, 0, v___x_4004_);
lean_ctor_set_uint8(v___x_4006_, sizeof(void*)*1, v___x_4005_);
v___x_4007_ = lean_array_push(v_log_3962_, v___x_4006_);
lean_inc_ref(v___x_3975_);
v___x_4008_ = l_Lake_downloadArtifactCore(v_hash_3969_, v___x_3995_, v___x_3975_, v___x_4007_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v_a_4009_; uint8_t v___x_4010_; uint8_t v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; 
v_a_4009_ = lean_ctor_get(v___x_4008_, 1);
lean_inc(v_a_4009_);
lean_dec_ref(v___x_4008_);
v___x_4010_ = 1;
v___x_4011_ = 0;
v___x_4012_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4012_, 0, v___x_4010_);
lean_ctor_set_uint8(v___x_4012_, 1, v___x_4011_);
lean_ctor_set_uint8(v___x_4012_, 2, v_exe_3945_);
lean_inc_ref_n(v___x_4012_, 2);
v___x_4013_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4013_, 0, v___x_4012_);
lean_ctor_set(v___x_4013_, 1, v___x_4012_);
lean_ctor_set(v___x_4013_, 2, v___x_4012_);
v___x_4014_ = l_IO_setAccessRights(v___x_3975_, v___x_4013_);
lean_dec_ref(v___x_4013_);
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_object* v___x_4016_; 
lean_dec_ref(v___x_4014_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 0, v_a_4009_);
v___x_4016_ = v___x_3982_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4009_);
lean_ctor_set(v_reuseFailAlloc_4019_, 1, v_trace_3965_);
lean_ctor_set(v_reuseFailAlloc_4019_, 2, v_buildTime_3966_);
lean_ctor_set_uint8(v_reuseFailAlloc_4019_, sizeof(void*)*3 + 1, v_wantsRebuild_3964_);
v___x_4016_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
lean_object* v___x_4017_; lean_object* v___x_4018_; 
lean_ctor_set_uint8(v___x_4016_, sizeof(void*)*3, v___x_3989_);
v___x_4017_ = lean_box(0);
v___x_4018_ = l_Lake_resolveArtifact___lam__1(v___x_3975_, v___f_3976_, v___x_4017_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v___x_4016_);
lean_dec_ref(v_a_3950_);
lean_dec_ref(v___x_3975_);
v___y_3958_ = v___x_3985_;
v___y_3959_ = v___x_4018_;
goto v___jp_3957_;
}
}
else
{
lean_object* v_a_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; uint8_t v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4029_; 
v_a_4020_ = lean_ctor_get(v___x_4014_, 0);
lean_inc(v_a_4020_);
lean_dec_ref(v___x_4014_);
v___x_4021_ = ((lean_object*)(l_Lake_resolveArtifact___closed__3));
v___x_4022_ = lean_io_error_to_string(v_a_4020_);
v___x_4023_ = lean_string_append(v___x_4021_, v___x_4022_);
lean_dec_ref(v___x_4022_);
v___x_4024_ = 2;
v___x_4025_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4025_, 0, v___x_4023_);
lean_ctor_set_uint8(v___x_4025_, sizeof(void*)*1, v___x_4024_);
v___x_4026_ = lean_box(0);
v___x_4027_ = lean_array_push(v_a_4009_, v___x_4025_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 0, v___x_4027_);
v___x_4029_ = v___x_3982_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4027_);
lean_ctor_set(v_reuseFailAlloc_4031_, 1, v_trace_3965_);
lean_ctor_set(v_reuseFailAlloc_4031_, 2, v_buildTime_3966_);
lean_ctor_set_uint8(v_reuseFailAlloc_4031_, sizeof(void*)*3 + 1, v_wantsRebuild_3964_);
v___x_4029_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
lean_object* v___x_4030_; 
lean_ctor_set_uint8(v___x_4029_, sizeof(void*)*3, v___x_3989_);
v___x_4030_ = l_Lake_resolveArtifact___lam__1(v___x_3975_, v___f_3976_, v___x_4026_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v___x_4029_);
lean_dec_ref(v_a_3950_);
lean_dec_ref(v___x_3975_);
v___y_3958_ = v___x_3985_;
v___y_3959_ = v___x_4030_;
goto v___jp_3957_;
}
}
}
else
{
lean_object* v_a_4032_; lean_object* v___x_4034_; 
lean_dec_ref(v___f_3976_);
lean_dec_ref(v___x_3975_);
lean_dec_ref(v_a_3950_);
lean_dec_ref(v_a_3946_);
v_a_4032_ = lean_ctor_get(v___x_4008_, 1);
lean_inc(v_a_4032_);
lean_dec_ref(v___x_4008_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 0, v_a_4032_);
v___x_4034_ = v___x_3982_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4032_);
lean_ctor_set(v_reuseFailAlloc_4035_, 1, v_trace_3965_);
lean_ctor_set(v_reuseFailAlloc_4035_, 2, v_buildTime_3966_);
lean_ctor_set_uint8(v_reuseFailAlloc_4035_, sizeof(void*)*3 + 1, v_wantsRebuild_3964_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
lean_ctor_set_uint8(v___x_4034_, sizeof(void*)*3, v___x_3989_);
v___y_3954_ = v___x_3985_;
v_a_3955_ = v___x_4034_;
goto v___jp_3953_;
}
}
}
else
{
lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4039_; 
lean_dec_ref(v___x_3992_);
lean_dec_ref(v___f_3976_);
lean_dec_ref(v___x_3975_);
lean_dec_ref(v_a_3950_);
lean_dec_ref(v_a_3946_);
lean_dec(v_scope_x3f_3944_);
v___x_4036_ = ((lean_object*)(l_Lake_resolveArtifact___closed__5));
v___x_4037_ = lean_array_push(v_log_3962_, v___x_4036_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 0, v___x_4037_);
v___x_4039_ = v___x_3982_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4037_);
lean_ctor_set(v_reuseFailAlloc_4040_, 1, v_trace_3965_);
lean_ctor_set(v_reuseFailAlloc_4040_, 2, v_buildTime_3966_);
lean_ctor_set_uint8(v_reuseFailAlloc_4040_, sizeof(void*)*3 + 1, v_wantsRebuild_3964_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
lean_ctor_set_uint8(v___x_4039_, sizeof(void*)*3, v___x_3989_);
v___y_3954_ = v___x_3985_;
v_a_3955_ = v___x_4039_;
goto v___jp_3953_;
}
}
}
else
{
lean_object* v___x_4041_; lean_object* v___x_4042_; uint8_t v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4047_; 
lean_dec(v___x_3992_);
lean_dec_ref(v___f_3976_);
lean_dec_ref(v___x_3975_);
lean_dec_ref(v_a_3950_);
lean_dec_ref(v_a_3946_);
lean_dec(v_scope_x3f_3944_);
v___x_4041_ = ((lean_object*)(l_Lake_resolveArtifact___closed__6));
v___x_4042_ = lean_string_append(v___x_4041_, v_val_3986_);
lean_dec(v_val_3986_);
v___x_4043_ = 3;
v___x_4044_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4044_, 0, v___x_4042_);
lean_ctor_set_uint8(v___x_4044_, sizeof(void*)*1, v___x_4043_);
v___x_4045_ = lean_array_push(v_log_3962_, v___x_4044_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 0, v___x_4045_);
v___x_4047_ = v___x_3982_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v___x_4045_);
lean_ctor_set(v_reuseFailAlloc_4048_, 1, v_trace_3965_);
lean_ctor_set(v_reuseFailAlloc_4048_, 2, v_buildTime_3966_);
lean_ctor_set_uint8(v_reuseFailAlloc_4048_, sizeof(void*)*3 + 1, v_wantsRebuild_3964_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
lean_ctor_set_uint8(v___x_4047_, sizeof(void*)*3, v___x_3989_);
v___y_3954_ = v___x_3985_;
v_a_3955_ = v___x_4047_;
goto v___jp_3953_;
}
}
}
else
{
lean_object* v___x_4049_; lean_object* v___x_4050_; uint8_t v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4055_; 
lean_dec_ref(v___f_3976_);
lean_dec_ref(v_a_3950_);
lean_dec_ref(v_a_3946_);
lean_dec(v_scope_x3f_3944_);
lean_dec(v_service_x3f_3943_);
v___x_4049_ = ((lean_object*)(l_Lake_resolveArtifact___closed__7));
v___x_4050_ = lean_string_append(v___x_4049_, v___x_3975_);
lean_dec_ref(v___x_3975_);
v___x_4051_ = 3;
v___x_4052_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4052_, 0, v___x_4050_);
lean_ctor_set_uint8(v___x_4052_, sizeof(void*)*1, v___x_4051_);
v___x_4053_ = lean_array_push(v_log_3962_, v___x_4052_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 0, v___x_4053_);
v___x_4055_ = v___x_3982_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___x_4053_);
lean_ctor_set(v_reuseFailAlloc_4056_, 1, v_trace_3965_);
lean_ctor_set(v_reuseFailAlloc_4056_, 2, v_buildTime_3966_);
lean_ctor_set_uint8(v_reuseFailAlloc_4056_, sizeof(void*)*3, v_action_3963_);
lean_ctor_set_uint8(v_reuseFailAlloc_4056_, sizeof(void*)*3 + 1, v_wantsRebuild_3964_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
v___y_3954_ = v___x_3985_;
v_a_3955_ = v___x_4055_;
goto v___jp_3953_;
}
}
}
else
{
lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; uint8_t v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4065_; 
lean_dec_ref(v___f_3976_);
lean_dec_ref(v___x_3975_);
lean_dec_ref(v_a_3950_);
lean_dec_ref(v_a_3946_);
lean_dec(v_scope_x3f_3944_);
lean_dec(v_service_x3f_3943_);
v___x_4057_ = ((lean_object*)(l_Lake_resolveArtifact___closed__8));
v___x_4058_ = lean_io_error_to_string(v_a_3984_);
v___x_4059_ = lean_string_append(v___x_4057_, v___x_4058_);
lean_dec_ref(v___x_4058_);
v___x_4060_ = 3;
v___x_4061_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4061_, 0, v___x_4059_);
lean_ctor_set_uint8(v___x_4061_, sizeof(void*)*1, v___x_4060_);
v___x_4062_ = lean_array_get_size(v_log_3962_);
v___x_4063_ = lean_array_push(v_log_3962_, v___x_4061_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 0, v___x_4063_);
v___x_4065_ = v___x_3982_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v___x_4063_);
lean_ctor_set(v_reuseFailAlloc_4067_, 1, v_trace_3965_);
lean_ctor_set(v_reuseFailAlloc_4067_, 2, v_buildTime_3966_);
lean_ctor_set_uint8(v_reuseFailAlloc_4067_, sizeof(void*)*3, v_action_3963_);
lean_ctor_set_uint8(v_reuseFailAlloc_4067_, sizeof(void*)*3 + 1, v_wantsRebuild_3964_);
v___x_4065_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
lean_object* v___x_4066_; 
v___x_4066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4062_);
lean_ctor_set(v___x_4066_, 1, v___x_4065_);
return v___x_4066_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___boxed(lean_object* v_descr_4080_, lean_object* v_service_x3f_4081_, lean_object* v_scope_x3f_4082_, lean_object* v_exe_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_){
_start:
{
uint8_t v_exe_boxed_4091_; lean_object* v_res_4092_; 
v_exe_boxed_4091_ = lean_unbox(v_exe_4083_);
v_res_4092_ = l_Lake_resolveArtifact(v_descr_4080_, v_service_x3f_4081_, v_scope_x3f_4082_, v_exe_boxed_4091_, v_a_4084_, v_a_4085_, v_a_4086_, v_a_4087_, v_a_4088_, v_a_4089_);
lean_dec(v_a_4087_);
lean_dec(v_a_4086_);
lean_dec(v_a_4085_);
return v_res_4092_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput(lean_object* v_out_4095_, uint8_t v_exe_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_){
_start:
{
lean_object* v_data_4104_; lean_object* v_service_x3f_4105_; lean_object* v_scope_x3f_4106_; lean_object* v___x_4107_; 
v_data_4104_ = lean_ctor_get(v_out_4095_, 0);
lean_inc(v_data_4104_);
v_service_x3f_4105_ = lean_ctor_get(v_out_4095_, 1);
lean_inc(v_service_x3f_4105_);
v_scope_x3f_4106_ = lean_ctor_get(v_out_4095_, 2);
lean_inc(v_scope_x3f_4106_);
lean_dec_ref(v_out_4095_);
lean_inc(v_data_4104_);
v___x_4107_ = l_Lake_ArtifactDescr_fromJson_x3f(v_data_4104_);
if (lean_obj_tag(v___x_4107_) == 0)
{
lean_object* v_a_4108_; lean_object* v_log_4109_; uint8_t v_action_4110_; uint8_t v_wantsRebuild_4111_; lean_object* v_trace_4112_; lean_object* v_buildTime_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4135_; 
lean_dec(v_scope_x3f_4106_);
lean_dec(v_service_x3f_4105_);
lean_dec_ref(v_a_4097_);
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
v___x_4117_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__0));
v___x_4118_ = l_Lean_Json_render(v_data_4104_);
v___x_4119_ = lean_unsigned_to_nat(80u);
v___x_4120_ = lean_unsigned_to_nat(2u);
v___x_4121_ = lean_unsigned_to_nat(0u);
v___x_4122_ = l_Std_Format_pretty(v___x_4118_, v___x_4119_, v___x_4120_, v___x_4121_);
v___x_4123_ = lean_string_append(v___x_4117_, v___x_4122_);
lean_dec_ref(v___x_4122_);
v___x_4124_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__1));
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
lean_inc_ref(v_a_4101_);
v___x_4137_ = l_Lake_resolveArtifact(v_a_4136_, v_service_x3f_4105_, v_scope_x3f_4106_, v_exe_4096_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
return v___x_4137_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput___boxed(lean_object* v_out_4138_, lean_object* v_exe_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_){
_start:
{
uint8_t v_exe_boxed_4147_; lean_object* v_res_4148_; 
v_exe_boxed_4147_ = lean_unbox(v_exe_4139_);
v_res_4148_ = l_Lake_resolveArtifactOutput(v_out_4138_, v_exe_boxed_4147_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_);
lean_dec_ref(v_a_4144_);
lean_dec(v_a_4143_);
lean_dec(v_a_4142_);
lean_dec(v_a_4141_);
return v_res_4148_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(uint8_t v_exe_4149_, lean_object* v_out_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
lean_object* v___x_4158_; 
v___x_4158_ = l_Lake_resolveArtifactOutput(v_out_4150_, v_exe_4149_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
return v___x_4158_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed(lean_object* v_exe_4159_, lean_object* v_out_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_){
_start:
{
uint8_t v_exe_boxed_4168_; lean_object* v_res_4169_; 
v_exe_boxed_4168_ = lean_unbox(v_exe_4159_);
v_res_4169_ = l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(v_exe_boxed_4168_, v_out_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_);
lean_dec_ref(v___y_4165_);
lean_dec(v___y_4164_);
lean_dec(v___y_4163_);
lean_dec(v___y_4162_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(uint8_t v_exe_4170_){
_start:
{
lean_object* v___x_4171_; lean_object* v___f_4172_; 
v___x_4171_ = lean_box(v_exe_4170_);
v___f_4172_ = lean_alloc_closure((void*)(l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4172_, 0, v___x_4171_);
return v___f_4172_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___boxed(lean_object* v_exe_4173_){
_start:
{
uint8_t v_exe_boxed_4174_; lean_object* v_res_4175_; 
v_exe_boxed_4174_ = lean_unbox(v_exe_4173_);
v_res_4175_ = l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(v_exe_boxed_4174_);
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg(lean_object* v_path_4176_, lean_object* v_ext_4177_, uint8_t v_text_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_){
_start:
{
lean_object* v___x_4182_; 
lean_inc_ref(v_path_4176_);
v___x_4182_ = l_Lake_fetchFileHash___redArg(v_path_4176_, v_text_4178_, v_a_4179_, v_a_4180_);
if (lean_obj_tag(v___x_4182_) == 0)
{
lean_object* v_a_4183_; lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4201_; 
v_a_4183_ = lean_ctor_get(v___x_4182_, 0);
v_a_4184_ = lean_ctor_get(v___x_4182_, 1);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4182_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4186_ = v___x_4182_;
v_isShared_4187_ = v_isSharedCheck_4201_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_inc(v_a_4183_);
lean_dec(v___x_4182_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4201_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___x_4197_; 
v___x_4197_ = lean_io_metadata(v_path_4176_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_object* v_a_4198_; lean_object* v_modified_4199_; 
v_a_4198_ = lean_ctor_get(v___x_4197_, 0);
lean_inc(v_a_4198_);
lean_dec_ref(v___x_4197_);
v_modified_4199_ = lean_ctor_get(v_a_4198_, 1);
lean_inc_ref(v_modified_4199_);
lean_dec(v_a_4198_);
v___y_4189_ = v_a_4184_;
v___y_4190_ = v_modified_4199_;
goto v___jp_4188_;
}
else
{
lean_object* v___x_4200_; 
lean_dec_ref(v___x_4197_);
v___x_4200_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___y_4189_ = v_a_4184_;
v___y_4190_ = v___x_4200_;
goto v___jp_4188_;
}
v___jp_4188_:
{
lean_object* v___x_4191_; uint64_t v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4195_; 
v___x_4191_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4191_, 0, v_ext_4177_);
v___x_4192_ = lean_unbox_uint64(v_a_4183_);
lean_dec(v_a_4183_);
lean_ctor_set_uint64(v___x_4191_, sizeof(void*)*1, v___x_4192_);
lean_inc_ref(v_path_4176_);
v___x_4193_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4193_, 0, v___x_4191_);
lean_ctor_set(v___x_4193_, 1, v_path_4176_);
lean_ctor_set(v___x_4193_, 2, v_path_4176_);
lean_ctor_set(v___x_4193_, 3, v___y_4190_);
if (v_isShared_4187_ == 0)
{
lean_ctor_set(v___x_4186_, 1, v___y_4189_);
lean_ctor_set(v___x_4186_, 0, v___x_4193_);
v___x_4195_ = v___x_4186_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v___x_4193_);
lean_ctor_set(v_reuseFailAlloc_4196_, 1, v___y_4189_);
v___x_4195_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
return v___x_4195_;
}
}
}
}
else
{
lean_object* v_a_4202_; lean_object* v_a_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4210_; 
lean_dec_ref(v_ext_4177_);
lean_dec_ref(v_path_4176_);
v_a_4202_ = lean_ctor_get(v___x_4182_, 0);
v_a_4203_ = lean_ctor_get(v___x_4182_, 1);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_4182_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4205_ = v___x_4182_;
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_a_4203_);
lean_inc(v_a_4202_);
lean_dec(v___x_4182_);
v___x_4205_ = lean_box(0);
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
v_resetjp_4204_:
{
lean_object* v___x_4208_; 
if (v_isShared_4206_ == 0)
{
v___x_4208_ = v___x_4205_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_a_4202_);
lean_ctor_set(v_reuseFailAlloc_4209_, 1, v_a_4203_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg___boxed(lean_object* v_path_4211_, lean_object* v_ext_4212_, lean_object* v_text_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_){
_start:
{
uint8_t v_text_boxed_4217_; lean_object* v_res_4218_; 
v_text_boxed_4217_ = lean_unbox(v_text_4213_);
v_res_4218_ = l_Lake_computeArtifact___redArg(v_path_4211_, v_ext_4212_, v_text_boxed_4217_, v_a_4214_, v_a_4215_);
lean_dec_ref(v_a_4214_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact(lean_object* v_path_4219_, lean_object* v_ext_4220_, uint8_t v_text_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_, lean_object* v_a_4224_, lean_object* v_a_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_){
_start:
{
lean_object* v___x_4229_; 
v___x_4229_ = l_Lake_computeArtifact___redArg(v_path_4219_, v_ext_4220_, v_text_4221_, v_a_4226_, v_a_4227_);
return v___x_4229_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___boxed(lean_object* v_path_4230_, lean_object* v_ext_4231_, lean_object* v_text_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_){
_start:
{
uint8_t v_text_boxed_4240_; lean_object* v_res_4241_; 
v_text_boxed_4240_ = lean_unbox(v_text_4232_);
v_res_4241_ = l_Lake_computeArtifact(v_path_4230_, v_ext_4231_, v_text_boxed_4240_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_);
lean_dec_ref(v_a_4237_);
lean_dec(v_a_4236_);
lean_dec(v_a_4235_);
lean_dec(v_a_4234_);
lean_dec_ref(v_a_4233_);
return v_res_4241_;
}
}
LEAN_EXPORT lean_object* l_Lake_restoreArtifact(lean_object* v_file_4245_, lean_object* v_art_4246_, uint8_t v_exe_4247_, lean_object* v_a_4248_){
_start:
{
lean_object* v___y_4251_; uint8_t v___x_4264_; 
v___x_4264_ = l_System_FilePath_pathExists(v_file_4245_);
if (v___x_4264_ == 0)
{
lean_object* v_descr_4265_; lean_object* v_path_4266_; lean_object* v___y_4268_; lean_object* v___x_4283_; lean_object* v___x_4284_; uint8_t v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; 
v_descr_4265_ = lean_ctor_get(v_art_4246_, 0);
v_path_4266_ = lean_ctor_get(v_art_4246_, 1);
v___x_4283_ = ((lean_object*)(l_Lake_restoreArtifact___closed__1));
v___x_4284_ = lean_string_append(v___x_4283_, v_path_4266_);
v___x_4285_ = 0;
v___x_4286_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4286_, 0, v___x_4284_);
lean_ctor_set_uint8(v___x_4286_, sizeof(void*)*1, v___x_4285_);
v___x_4287_ = lean_array_push(v_a_4248_, v___x_4286_);
lean_inc_ref(v_file_4245_);
v___x_4288_ = l_Lake_createParentDirs(v_file_4245_);
if (lean_obj_tag(v___x_4288_) == 0)
{
lean_object* v___x_4289_; 
lean_dec_ref(v___x_4288_);
v___x_4289_ = lean_io_hard_link(v_path_4266_, v_file_4245_);
if (lean_obj_tag(v___x_4289_) == 0)
{
lean_dec_ref(v___x_4289_);
v___y_4268_ = v___x_4287_;
goto v___jp_4267_;
}
else
{
lean_object* v_a_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
v_a_4290_ = lean_ctor_get(v___x_4289_, 0);
lean_inc(v_a_4290_);
lean_dec_ref(v___x_4289_);
v___x_4291_ = ((lean_object*)(l_Lake_restoreArtifact___closed__2));
v___x_4292_ = lean_io_error_to_string(v_a_4290_);
v___x_4293_ = lean_string_append(v___x_4291_, v___x_4292_);
lean_dec_ref(v___x_4292_);
v___x_4294_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4294_, 0, v___x_4293_);
lean_ctor_set_uint8(v___x_4294_, sizeof(void*)*1, v___x_4285_);
v___x_4295_ = lean_array_push(v___x_4287_, v___x_4294_);
v___x_4296_ = l_Lake_copyFile(v_path_4266_, v_file_4245_);
if (lean_obj_tag(v___x_4296_) == 0)
{
uint8_t v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; 
lean_dec_ref(v___x_4296_);
v___x_4297_ = 1;
v___x_4298_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4298_, 0, v___x_4297_);
lean_ctor_set_uint8(v___x_4298_, 1, v___x_4264_);
lean_ctor_set_uint8(v___x_4298_, 2, v_exe_4247_);
lean_inc_ref_n(v___x_4298_, 2);
v___x_4299_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4299_, 0, v___x_4298_);
lean_ctor_set(v___x_4299_, 1, v___x_4298_);
lean_ctor_set(v___x_4299_, 2, v___x_4298_);
v___x_4300_ = l_IO_setAccessRights(v_file_4245_, v___x_4299_);
lean_dec_ref(v___x_4299_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_dec_ref(v___x_4300_);
v___y_4268_ = v___x_4295_;
goto v___jp_4267_;
}
else
{
lean_object* v_a_4301_; lean_object* v___x_4302_; uint8_t v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; 
lean_dec_ref(v_art_4246_);
lean_dec_ref(v_file_4245_);
v_a_4301_ = lean_ctor_get(v___x_4300_, 0);
lean_inc(v_a_4301_);
lean_dec_ref(v___x_4300_);
v___x_4302_ = lean_io_error_to_string(v_a_4301_);
v___x_4303_ = 3;
v___x_4304_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4304_, 0, v___x_4302_);
lean_ctor_set_uint8(v___x_4304_, sizeof(void*)*1, v___x_4303_);
v___x_4305_ = lean_array_get_size(v___x_4295_);
v___x_4306_ = lean_array_push(v___x_4295_, v___x_4304_);
v___x_4307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4305_);
lean_ctor_set(v___x_4307_, 1, v___x_4306_);
return v___x_4307_;
}
}
else
{
lean_object* v_a_4308_; lean_object* v___x_4309_; uint8_t v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
lean_dec_ref(v_art_4246_);
lean_dec_ref(v_file_4245_);
v_a_4308_ = lean_ctor_get(v___x_4296_, 0);
lean_inc(v_a_4308_);
lean_dec_ref(v___x_4296_);
v___x_4309_ = lean_io_error_to_string(v_a_4308_);
v___x_4310_ = 3;
v___x_4311_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4311_, 0, v___x_4309_);
lean_ctor_set_uint8(v___x_4311_, sizeof(void*)*1, v___x_4310_);
v___x_4312_ = lean_array_get_size(v___x_4295_);
v___x_4313_ = lean_array_push(v___x_4295_, v___x_4311_);
v___x_4314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4312_);
lean_ctor_set(v___x_4314_, 1, v___x_4313_);
return v___x_4314_;
}
}
}
else
{
lean_object* v_a_4315_; lean_object* v___x_4316_; uint8_t v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; 
lean_dec_ref(v_art_4246_);
lean_dec_ref(v_file_4245_);
v_a_4315_ = lean_ctor_get(v___x_4288_, 0);
lean_inc(v_a_4315_);
lean_dec_ref(v___x_4288_);
v___x_4316_ = lean_io_error_to_string(v_a_4315_);
v___x_4317_ = 3;
v___x_4318_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4318_, 0, v___x_4316_);
lean_ctor_set_uint8(v___x_4318_, sizeof(void*)*1, v___x_4317_);
v___x_4319_ = lean_array_get_size(v___x_4287_);
v___x_4320_ = lean_array_push(v___x_4287_, v___x_4318_);
v___x_4321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4321_, 0, v___x_4319_);
lean_ctor_set(v___x_4321_, 1, v___x_4320_);
return v___x_4321_;
}
v___jp_4267_:
{
uint64_t v_hash_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; uint8_t v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v_hash_4269_ = lean_ctor_get_uint64(v_descr_4265_, sizeof(void*)*1);
v___x_4270_ = ((lean_object*)(l_Lake_restoreArtifact___closed__0));
v___x_4271_ = lean_string_append(v___x_4270_, v_file_4245_);
v___x_4272_ = 0;
v___x_4273_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4273_, 0, v___x_4271_);
lean_ctor_set_uint8(v___x_4273_, sizeof(void*)*1, v___x_4272_);
v___x_4274_ = lean_array_push(v___y_4268_, v___x_4273_);
lean_inc_ref(v_file_4245_);
v___x_4275_ = l_Lake_writeFileHash(v_file_4245_, v_hash_4269_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_dec_ref(v___x_4275_);
v___y_4251_ = v___x_4274_;
goto v___jp_4250_;
}
else
{
lean_object* v_a_4276_; lean_object* v___x_4277_; uint8_t v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; 
lean_dec_ref(v_art_4246_);
lean_dec_ref(v_file_4245_);
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
lean_inc(v_a_4276_);
lean_dec_ref(v___x_4275_);
v___x_4277_ = lean_io_error_to_string(v_a_4276_);
v___x_4278_ = 3;
v___x_4279_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4279_, 0, v___x_4277_);
lean_ctor_set_uint8(v___x_4279_, sizeof(void*)*1, v___x_4278_);
v___x_4280_ = lean_array_get_size(v___x_4274_);
v___x_4281_ = lean_array_push(v___x_4274_, v___x_4279_);
v___x_4282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4282_, 0, v___x_4280_);
lean_ctor_set(v___x_4282_, 1, v___x_4281_);
return v___x_4282_;
}
}
}
else
{
v___y_4251_ = v_a_4248_;
goto v___jp_4250_;
}
v___jp_4250_:
{
lean_object* v_descr_4252_; lean_object* v_mtime_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4261_; 
v_descr_4252_ = lean_ctor_get(v_art_4246_, 0);
v_mtime_4253_ = lean_ctor_get(v_art_4246_, 3);
v_isSharedCheck_4261_ = !lean_is_exclusive(v_art_4246_);
if (v_isSharedCheck_4261_ == 0)
{
lean_object* v_unused_4262_; lean_object* v_unused_4263_; 
v_unused_4262_ = lean_ctor_get(v_art_4246_, 2);
lean_dec(v_unused_4262_);
v_unused_4263_ = lean_ctor_get(v_art_4246_, 1);
lean_dec(v_unused_4263_);
v___x_4255_ = v_art_4246_;
v_isShared_4256_ = v_isSharedCheck_4261_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_mtime_4253_);
lean_inc(v_descr_4252_);
lean_dec(v_art_4246_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4261_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4258_; 
lean_inc_ref(v_file_4245_);
if (v_isShared_4256_ == 0)
{
lean_ctor_set(v___x_4255_, 2, v_file_4245_);
lean_ctor_set(v___x_4255_, 1, v_file_4245_);
v___x_4258_ = v___x_4255_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4260_; 
v_reuseFailAlloc_4260_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4260_, 0, v_descr_4252_);
lean_ctor_set(v_reuseFailAlloc_4260_, 1, v_file_4245_);
lean_ctor_set(v_reuseFailAlloc_4260_, 2, v_file_4245_);
lean_ctor_set(v_reuseFailAlloc_4260_, 3, v_mtime_4253_);
v___x_4258_ = v_reuseFailAlloc_4260_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
lean_object* v___x_4259_; 
v___x_4259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4259_, 0, v___x_4258_);
lean_ctor_set(v___x_4259_, 1, v___y_4251_);
return v___x_4259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_restoreArtifact___boxed(lean_object* v_file_4322_, lean_object* v_art_4323_, lean_object* v_exe_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_){
_start:
{
uint8_t v_exe_boxed_4327_; lean_object* v_res_4328_; 
v_exe_boxed_4327_ = lean_unbox(v_exe_4324_);
v_res_4328_ = l_Lake_restoreArtifact(v_file_4322_, v_art_4323_, v_exe_boxed_4327_, v_a_4325_);
return v_res_4328_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(lean_object* v_val_4329_, lean_object* v_a_x3f_4330_, lean_object* v___y_4331_){
_start:
{
lean_object* v___x_4333_; lean_object* v_log_4334_; uint8_t v_action_4335_; uint8_t v_wantsRebuild_4336_; lean_object* v_trace_4337_; lean_object* v_buildTime_4338_; lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4349_; 
v___x_4333_ = lean_io_mono_ms_now();
v_log_4334_ = lean_ctor_get(v___y_4331_, 0);
v_action_4335_ = lean_ctor_get_uint8(v___y_4331_, sizeof(void*)*3);
v_wantsRebuild_4336_ = lean_ctor_get_uint8(v___y_4331_, sizeof(void*)*3 + 1);
v_trace_4337_ = lean_ctor_get(v___y_4331_, 1);
v_buildTime_4338_ = lean_ctor_get(v___y_4331_, 2);
v_isSharedCheck_4349_ = !lean_is_exclusive(v___y_4331_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4340_ = v___y_4331_;
v_isShared_4341_ = v_isSharedCheck_4349_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_buildTime_4338_);
lean_inc(v_trace_4337_);
lean_inc(v_log_4334_);
lean_dec(v___y_4331_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4349_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4346_; 
v___x_4342_ = lean_nat_sub(v___x_4333_, v_val_4329_);
lean_dec(v___x_4333_);
v___x_4343_ = lean_box(0);
v___x_4344_ = lean_nat_add(v_buildTime_4338_, v___x_4342_);
lean_dec(v___x_4342_);
lean_dec(v_buildTime_4338_);
if (v_isShared_4341_ == 0)
{
lean_ctor_set(v___x_4340_, 2, v___x_4344_);
v___x_4346_ = v___x_4340_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_log_4334_);
lean_ctor_set(v_reuseFailAlloc_4348_, 1, v_trace_4337_);
lean_ctor_set(v_reuseFailAlloc_4348_, 2, v___x_4344_);
lean_ctor_set_uint8(v_reuseFailAlloc_4348_, sizeof(void*)*3, v_action_4335_);
lean_ctor_set_uint8(v_reuseFailAlloc_4348_, sizeof(void*)*3 + 1, v_wantsRebuild_4336_);
v___x_4346_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
lean_object* v___x_4347_; 
v___x_4347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4347_, 0, v___x_4343_);
lean_ctor_set(v___x_4347_, 1, v___x_4346_);
return v___x_4347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0___boxed(lean_object* v_val_4350_, lean_object* v_a_x3f_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_){
_start:
{
lean_object* v_res_4354_; 
v_res_4354_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v_val_4350_, v_a_x3f_4351_, v___y_4352_);
lean_dec(v_a_x3f_4351_);
lean_dec(v_val_4350_);
return v_res_4354_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(lean_object* v_file_4355_, lean_object* v_build_4356_, lean_object* v_traceFile_4357_, lean_object* v_ext_4358_, uint8_t v_text_4359_, lean_object* v_a_4360_, lean_object* v_depTrace_4361_, lean_object* v_traceFile_4362_, uint8_t v_action_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_){
_start:
{
lean_object* v_a_4371_; lean_object* v_a_4372_; lean_object* v_log_4375_; uint8_t v_action_4376_; uint8_t v_wantsRebuild_4377_; lean_object* v_trace_4378_; lean_object* v_buildTime_4379_; lean_object* v_toBuildConfig_4385_; lean_object* v_log_4386_; uint8_t v_action_4387_; uint8_t v_wantsRebuild_4388_; lean_object* v_trace_4389_; lean_object* v_buildTime_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4569_; 
v_toBuildConfig_4385_ = lean_ctor_get(v_a_4367_, 0);
v_log_4386_ = lean_ctor_get(v_a_4368_, 0);
v_action_4387_ = lean_ctor_get_uint8(v_a_4368_, sizeof(void*)*3);
v_wantsRebuild_4388_ = lean_ctor_get_uint8(v_a_4368_, sizeof(void*)*3 + 1);
v_trace_4389_ = lean_ctor_get(v_a_4368_, 1);
v_buildTime_4390_ = lean_ctor_get(v_a_4368_, 2);
v_isSharedCheck_4569_ = !lean_is_exclusive(v_a_4368_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4392_ = v_a_4368_;
v_isShared_4393_ = v_isSharedCheck_4569_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_buildTime_4390_);
lean_inc(v_trace_4389_);
lean_inc(v_log_4386_);
lean_dec(v_a_4368_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4569_;
goto v_resetjp_4391_;
}
v___jp_4370_:
{
lean_object* v___x_4373_; 
v___x_4373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4373_, 0, v_a_4371_);
lean_ctor_set(v___x_4373_, 1, v_a_4372_);
return v___x_4373_;
}
v___jp_4374_:
{
lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; 
v___x_4380_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_4381_ = lean_array_get_size(v_log_4375_);
v___x_4382_ = lean_array_push(v_log_4375_, v___x_4380_);
v___x_4383_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4383_, 0, v___x_4382_);
lean_ctor_set(v___x_4383_, 1, v_trace_4378_);
lean_ctor_set(v___x_4383_, 2, v_buildTime_4379_);
lean_ctor_set_uint8(v___x_4383_, sizeof(void*)*3, v_action_4376_);
lean_ctor_set_uint8(v___x_4383_, sizeof(void*)*3 + 1, v_wantsRebuild_4377_);
v___x_4384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4384_, 0, v___x_4381_);
lean_ctor_set(v___x_4384_, 1, v___x_4383_);
return v___x_4384_;
}
v_resetjp_4391_:
{
uint8_t v_noBuild_4394_; uint8_t v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; 
v_noBuild_4394_ = lean_ctor_get_uint8(v_toBuildConfig_4385_, sizeof(void*)*2 + 2);
v___x_4395_ = l_Lake_JobAction_merge(v_action_4387_, v_action_4363_);
v___x_4396_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_4362_);
v___x_4397_ = l_System_FilePath_addExtension(v_traceFile_4362_, v___x_4396_);
if (v_noBuild_4394_ == 0)
{
lean_object* v___x_4398_; lean_object* v_a_4400_; lean_object* v_a_4401_; lean_object* v___x_4405_; 
v___x_4398_ = lean_io_mono_ms_now();
v___x_4405_ = l_Lake_removeFileIfExists(v_file_4355_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v___x_4407_; 
lean_dec_ref(v___x_4405_);
lean_inc_ref(v_log_4386_);
if (v_isShared_4393_ == 0)
{
v___x_4407_ = v___x_4392_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_log_4386_);
lean_ctor_set(v_reuseFailAlloc_4544_, 1, v_trace_4389_);
lean_ctor_set(v_reuseFailAlloc_4544_, 2, v_buildTime_4390_);
lean_ctor_set_uint8(v_reuseFailAlloc_4544_, sizeof(void*)*3 + 1, v_wantsRebuild_4388_);
v___x_4407_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
lean_object* v___x_4408_; 
lean_ctor_set_uint8(v___x_4407_, sizeof(void*)*3, v___x_4395_);
lean_inc_ref(v_a_4367_);
lean_inc(v_a_4366_);
lean_inc(v_a_4365_);
lean_inc(v_a_4364_);
v___x_4408_ = lean_apply_7(v_build_4356_, v_a_4360_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_, v___x_4407_, lean_box(0));
if (lean_obj_tag(v___x_4408_) == 0)
{
lean_object* v_a_4409_; lean_object* v_log_4410_; uint8_t v_action_4411_; uint8_t v_wantsRebuild_4412_; lean_object* v_trace_4413_; lean_object* v_buildTime_4414_; lean_object* v___x_4415_; 
v_a_4409_ = lean_ctor_get(v___x_4408_, 1);
lean_inc(v_a_4409_);
lean_dec_ref(v___x_4408_);
v_log_4410_ = lean_ctor_get(v_a_4409_, 0);
v_action_4411_ = lean_ctor_get_uint8(v_a_4409_, sizeof(void*)*3);
v_wantsRebuild_4412_ = lean_ctor_get_uint8(v_a_4409_, sizeof(void*)*3 + 1);
v_trace_4413_ = lean_ctor_get(v_a_4409_, 1);
v_buildTime_4414_ = lean_ctor_get(v_a_4409_, 2);
lean_inc_ref(v_file_4355_);
v___x_4415_ = l_Lake_clearFileHash(v_file_4355_);
if (lean_obj_tag(v___x_4415_) == 0)
{
lean_object* v___x_4416_; 
lean_dec_ref(v___x_4415_);
v___x_4416_ = l_Lake_removeFileIfExists(v_traceFile_4357_);
if (lean_obj_tag(v___x_4416_) == 0)
{
lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4508_; 
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4416_);
if (v_isSharedCheck_4508_ == 0)
{
lean_object* v_unused_4509_; 
v_unused_4509_ = lean_ctor_get(v___x_4416_, 0);
lean_dec(v_unused_4509_);
v___x_4418_ = v___x_4416_;
v_isShared_4419_ = v_isSharedCheck_4508_;
goto v_resetjp_4417_;
}
else
{
lean_dec(v___x_4416_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4508_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v___x_4420_; 
v___x_4420_ = l_Lake_computeArtifact___redArg(v_file_4355_, v_ext_4358_, v_text_4359_, v_a_4367_, v_a_4409_);
if (lean_obj_tag(v___x_4420_) == 0)
{
lean_object* v_a_4421_; lean_object* v_a_4422_; lean_object* v_descr_4423_; lean_object* v_log_4424_; uint8_t v_action_4425_; uint8_t v_wantsRebuild_4426_; lean_object* v_trace_4427_; lean_object* v_buildTime_4428_; uint64_t v_hash_4429_; lean_object* v_ext_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___y_4435_; lean_object* v___x_4498_; lean_object* v___x_4499_; uint8_t v___x_4500_; 
v_a_4421_ = lean_ctor_get(v___x_4420_, 1);
lean_inc(v_a_4421_);
v_a_4422_ = lean_ctor_get(v___x_4420_, 0);
lean_inc(v_a_4422_);
lean_dec_ref(v___x_4420_);
v_descr_4423_ = lean_ctor_get(v_a_4422_, 0);
v_log_4424_ = lean_ctor_get(v_a_4421_, 0);
v_action_4425_ = lean_ctor_get_uint8(v_a_4421_, sizeof(void*)*3);
v_wantsRebuild_4426_ = lean_ctor_get_uint8(v_a_4421_, sizeof(void*)*3 + 1);
v_trace_4427_ = lean_ctor_get(v_a_4421_, 1);
v_buildTime_4428_ = lean_ctor_get(v_a_4421_, 2);
v_hash_4429_ = lean_ctor_get_uint64(v_descr_4423_, sizeof(void*)*1);
v_ext_4430_ = lean_ctor_get(v_descr_4423_, 0);
v___x_4431_ = lean_array_get_size(v_log_4386_);
lean_dec_ref(v_log_4386_);
v___x_4432_ = lean_array_get_size(v_log_4424_);
v___x_4433_ = l_Array_extract___redArg(v_log_4424_, v___x_4431_, v___x_4432_);
v___x_4498_ = lean_string_utf8_byte_size(v_ext_4430_);
v___x_4499_ = lean_unsigned_to_nat(0u);
v___x_4500_ = lean_nat_dec_eq(v___x_4498_, v___x_4499_);
if (v___x_4500_ == 0)
{
lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; 
v___x_4501_ = l_Lake_Hash_hex(v_hash_4429_);
v___x_4502_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_4503_ = lean_string_append(v___x_4501_, v___x_4502_);
v___x_4504_ = lean_string_append(v___x_4503_, v_ext_4430_);
v___y_4435_ = v___x_4504_;
goto v___jp_4434_;
}
else
{
lean_object* v___x_4505_; 
v___x_4505_ = l_Lake_Hash_hex(v_hash_4429_);
v___y_4435_ = v___x_4505_;
goto v___jp_4434_;
}
v___jp_4434_:
{
lean_object* v___x_4437_; 
if (v_isShared_4419_ == 0)
{
lean_ctor_set_tag(v___x_4418_, 3);
lean_ctor_set(v___x_4418_, 0, v___y_4435_);
v___x_4437_ = v___x_4418_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v___y_4435_);
v___x_4437_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
lean_object* v___x_4438_; lean_object* v___x_4439_; 
v___x_4438_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_4361_, v___x_4437_, v___x_4433_);
v___x_4439_ = l_Lake_BuildMetadata_writeFile(v_traceFile_4362_, v___x_4438_);
if (lean_obj_tag(v___x_4439_) == 0)
{
lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4480_; 
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4439_);
if (v_isSharedCheck_4480_ == 0)
{
lean_object* v_unused_4481_; 
v_unused_4481_ = lean_ctor_get(v___x_4439_, 0);
lean_dec(v_unused_4481_);
v___x_4441_ = v___x_4439_;
v_isShared_4442_ = v_isSharedCheck_4480_;
goto v_resetjp_4440_;
}
else
{
lean_dec(v___x_4439_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4480_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v___x_4443_; 
v___x_4443_ = l_Lake_removeFileIfExists(v___x_4397_);
lean_dec_ref(v___x_4397_);
if (lean_obj_tag(v___x_4443_) == 0)
{
lean_object* v___x_4445_; uint8_t v_isShared_4446_; uint8_t v_isSharedCheck_4463_; 
v_isSharedCheck_4463_ = !lean_is_exclusive(v___x_4443_);
if (v_isSharedCheck_4463_ == 0)
{
lean_object* v_unused_4464_; 
v_unused_4464_ = lean_ctor_get(v___x_4443_, 0);
lean_dec(v_unused_4464_);
v___x_4445_ = v___x_4443_;
v_isShared_4446_ = v_isSharedCheck_4463_;
goto v_resetjp_4444_;
}
else
{
lean_dec(v___x_4443_);
v___x_4445_ = lean_box(0);
v_isShared_4446_ = v_isSharedCheck_4463_;
goto v_resetjp_4444_;
}
v_resetjp_4444_:
{
lean_object* v___x_4448_; 
lean_inc(v_a_4422_);
if (v_isShared_4446_ == 0)
{
lean_ctor_set(v___x_4445_, 0, v_a_4422_);
v___x_4448_ = v___x_4445_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v_a_4422_);
v___x_4448_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
lean_object* v___x_4450_; 
if (v_isShared_4442_ == 0)
{
lean_ctor_set_tag(v___x_4441_, 1);
lean_ctor_set(v___x_4441_, 0, v___x_4448_);
v___x_4450_ = v___x_4441_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v___x_4448_);
v___x_4450_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
lean_object* v___x_4451_; lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4459_; 
v___x_4451_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v___x_4398_, v___x_4450_, v_a_4421_);
lean_dec_ref(v___x_4450_);
lean_dec(v___x_4398_);
v_a_4452_ = lean_ctor_get(v___x_4451_, 1);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4451_);
if (v_isSharedCheck_4459_ == 0)
{
lean_object* v_unused_4460_; 
v_unused_4460_ = lean_ctor_get(v___x_4451_, 0);
lean_dec(v_unused_4460_);
v___x_4454_ = v___x_4451_;
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4451_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4457_; 
if (v_isShared_4455_ == 0)
{
lean_ctor_set(v___x_4454_, 0, v_a_4422_);
v___x_4457_ = v___x_4454_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v_a_4422_);
lean_ctor_set(v_reuseFailAlloc_4458_, 1, v_a_4452_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
return v___x_4457_;
}
}
}
}
}
}
else
{
lean_object* v___x_4466_; uint8_t v_isShared_4467_; uint8_t v_isSharedCheck_4476_; 
lean_inc(v_buildTime_4428_);
lean_inc_ref(v_trace_4427_);
lean_inc_ref(v_log_4424_);
lean_del_object(v___x_4441_);
lean_dec(v_a_4422_);
v_isSharedCheck_4476_ = !lean_is_exclusive(v_a_4421_);
if (v_isSharedCheck_4476_ == 0)
{
lean_object* v_unused_4477_; lean_object* v_unused_4478_; lean_object* v_unused_4479_; 
v_unused_4477_ = lean_ctor_get(v_a_4421_, 2);
lean_dec(v_unused_4477_);
v_unused_4478_ = lean_ctor_get(v_a_4421_, 1);
lean_dec(v_unused_4478_);
v_unused_4479_ = lean_ctor_get(v_a_4421_, 0);
lean_dec(v_unused_4479_);
v___x_4466_ = v_a_4421_;
v_isShared_4467_ = v_isSharedCheck_4476_;
goto v_resetjp_4465_;
}
else
{
lean_dec(v_a_4421_);
v___x_4466_ = lean_box(0);
v_isShared_4467_ = v_isSharedCheck_4476_;
goto v_resetjp_4465_;
}
v_resetjp_4465_:
{
lean_object* v_a_4468_; lean_object* v___x_4469_; uint8_t v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4474_; 
v_a_4468_ = lean_ctor_get(v___x_4443_, 0);
lean_inc(v_a_4468_);
lean_dec_ref(v___x_4443_);
v___x_4469_ = lean_io_error_to_string(v_a_4468_);
v___x_4470_ = 3;
v___x_4471_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4471_, 0, v___x_4469_);
lean_ctor_set_uint8(v___x_4471_, sizeof(void*)*1, v___x_4470_);
v___x_4472_ = lean_array_push(v_log_4424_, v___x_4471_);
if (v_isShared_4467_ == 0)
{
lean_ctor_set(v___x_4466_, 0, v___x_4472_);
v___x_4474_ = v___x_4466_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v___x_4472_);
lean_ctor_set(v_reuseFailAlloc_4475_, 1, v_trace_4427_);
lean_ctor_set(v_reuseFailAlloc_4475_, 2, v_buildTime_4428_);
lean_ctor_set_uint8(v_reuseFailAlloc_4475_, sizeof(void*)*3, v_action_4425_);
lean_ctor_set_uint8(v_reuseFailAlloc_4475_, sizeof(void*)*3 + 1, v_wantsRebuild_4426_);
v___x_4474_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
v_a_4400_ = v___x_4432_;
v_a_4401_ = v___x_4474_;
goto v___jp_4399_;
}
}
}
}
}
else
{
lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4493_; 
lean_inc(v_buildTime_4428_);
lean_inc_ref(v_trace_4427_);
lean_inc_ref(v_log_4424_);
lean_dec(v_a_4422_);
lean_dec_ref(v___x_4397_);
v_isSharedCheck_4493_ = !lean_is_exclusive(v_a_4421_);
if (v_isSharedCheck_4493_ == 0)
{
lean_object* v_unused_4494_; lean_object* v_unused_4495_; lean_object* v_unused_4496_; 
v_unused_4494_ = lean_ctor_get(v_a_4421_, 2);
lean_dec(v_unused_4494_);
v_unused_4495_ = lean_ctor_get(v_a_4421_, 1);
lean_dec(v_unused_4495_);
v_unused_4496_ = lean_ctor_get(v_a_4421_, 0);
lean_dec(v_unused_4496_);
v___x_4483_ = v_a_4421_;
v_isShared_4484_ = v_isSharedCheck_4493_;
goto v_resetjp_4482_;
}
else
{
lean_dec(v_a_4421_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4493_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v_a_4485_; lean_object* v___x_4486_; uint8_t v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4491_; 
v_a_4485_ = lean_ctor_get(v___x_4439_, 0);
lean_inc(v_a_4485_);
lean_dec_ref(v___x_4439_);
v___x_4486_ = lean_io_error_to_string(v_a_4485_);
v___x_4487_ = 3;
v___x_4488_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4488_, 0, v___x_4486_);
lean_ctor_set_uint8(v___x_4488_, sizeof(void*)*1, v___x_4487_);
v___x_4489_ = lean_array_push(v_log_4424_, v___x_4488_);
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
lean_ctor_set(v_reuseFailAlloc_4492_, 1, v_trace_4427_);
lean_ctor_set(v_reuseFailAlloc_4492_, 2, v_buildTime_4428_);
lean_ctor_set_uint8(v_reuseFailAlloc_4492_, sizeof(void*)*3, v_action_4425_);
lean_ctor_set_uint8(v_reuseFailAlloc_4492_, sizeof(void*)*3 + 1, v_wantsRebuild_4426_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
v_a_4400_ = v___x_4432_;
v_a_4401_ = v___x_4491_;
goto v___jp_4399_;
}
}
}
}
}
}
else
{
lean_object* v_a_4506_; lean_object* v_a_4507_; 
lean_del_object(v___x_4418_);
lean_dec_ref(v___x_4397_);
lean_dec_ref(v_log_4386_);
lean_dec_ref(v_traceFile_4362_);
v_a_4506_ = lean_ctor_get(v___x_4420_, 0);
lean_inc(v_a_4506_);
v_a_4507_ = lean_ctor_get(v___x_4420_, 1);
lean_inc(v_a_4507_);
lean_dec_ref(v___x_4420_);
v_a_4400_ = v_a_4506_;
v_a_4401_ = v_a_4507_;
goto v___jp_4399_;
}
}
}
else
{
lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4522_; 
lean_inc(v_buildTime_4414_);
lean_inc_ref(v_trace_4413_);
lean_inc_ref(v_log_4410_);
lean_dec_ref(v___x_4397_);
lean_dec_ref(v_log_4386_);
lean_dec_ref(v_traceFile_4362_);
lean_dec_ref(v_ext_4358_);
lean_dec_ref(v_file_4355_);
v_isSharedCheck_4522_ = !lean_is_exclusive(v_a_4409_);
if (v_isSharedCheck_4522_ == 0)
{
lean_object* v_unused_4523_; lean_object* v_unused_4524_; lean_object* v_unused_4525_; 
v_unused_4523_ = lean_ctor_get(v_a_4409_, 2);
lean_dec(v_unused_4523_);
v_unused_4524_ = lean_ctor_get(v_a_4409_, 1);
lean_dec(v_unused_4524_);
v_unused_4525_ = lean_ctor_get(v_a_4409_, 0);
lean_dec(v_unused_4525_);
v___x_4511_ = v_a_4409_;
v_isShared_4512_ = v_isSharedCheck_4522_;
goto v_resetjp_4510_;
}
else
{
lean_dec(v_a_4409_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4522_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v_a_4513_; lean_object* v___x_4514_; uint8_t v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4520_; 
v_a_4513_ = lean_ctor_get(v___x_4416_, 0);
lean_inc(v_a_4513_);
lean_dec_ref(v___x_4416_);
v___x_4514_ = lean_io_error_to_string(v_a_4513_);
v___x_4515_ = 3;
v___x_4516_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4516_, 0, v___x_4514_);
lean_ctor_set_uint8(v___x_4516_, sizeof(void*)*1, v___x_4515_);
v___x_4517_ = lean_array_get_size(v_log_4410_);
v___x_4518_ = lean_array_push(v_log_4410_, v___x_4516_);
if (v_isShared_4512_ == 0)
{
lean_ctor_set(v___x_4511_, 0, v___x_4518_);
v___x_4520_ = v___x_4511_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v___x_4518_);
lean_ctor_set(v_reuseFailAlloc_4521_, 1, v_trace_4413_);
lean_ctor_set(v_reuseFailAlloc_4521_, 2, v_buildTime_4414_);
lean_ctor_set_uint8(v_reuseFailAlloc_4521_, sizeof(void*)*3, v_action_4411_);
lean_ctor_set_uint8(v_reuseFailAlloc_4521_, sizeof(void*)*3 + 1, v_wantsRebuild_4412_);
v___x_4520_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
v_a_4400_ = v___x_4517_;
v_a_4401_ = v___x_4520_;
goto v___jp_4399_;
}
}
}
}
else
{
lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4538_; 
lean_inc(v_buildTime_4414_);
lean_inc_ref(v_trace_4413_);
lean_inc_ref(v_log_4410_);
lean_dec_ref(v___x_4397_);
lean_dec_ref(v_log_4386_);
lean_dec_ref(v_traceFile_4362_);
lean_dec_ref(v_ext_4358_);
lean_dec_ref(v_file_4355_);
v_isSharedCheck_4538_ = !lean_is_exclusive(v_a_4409_);
if (v_isSharedCheck_4538_ == 0)
{
lean_object* v_unused_4539_; lean_object* v_unused_4540_; lean_object* v_unused_4541_; 
v_unused_4539_ = lean_ctor_get(v_a_4409_, 2);
lean_dec(v_unused_4539_);
v_unused_4540_ = lean_ctor_get(v_a_4409_, 1);
lean_dec(v_unused_4540_);
v_unused_4541_ = lean_ctor_get(v_a_4409_, 0);
lean_dec(v_unused_4541_);
v___x_4527_ = v_a_4409_;
v_isShared_4528_ = v_isSharedCheck_4538_;
goto v_resetjp_4526_;
}
else
{
lean_dec(v_a_4409_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4538_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v_a_4529_; lean_object* v___x_4530_; uint8_t v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4536_; 
v_a_4529_ = lean_ctor_get(v___x_4415_, 0);
lean_inc(v_a_4529_);
lean_dec_ref(v___x_4415_);
v___x_4530_ = lean_io_error_to_string(v_a_4529_);
v___x_4531_ = 3;
v___x_4532_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4532_, 0, v___x_4530_);
lean_ctor_set_uint8(v___x_4532_, sizeof(void*)*1, v___x_4531_);
v___x_4533_ = lean_array_get_size(v_log_4410_);
v___x_4534_ = lean_array_push(v_log_4410_, v___x_4532_);
if (v_isShared_4528_ == 0)
{
lean_ctor_set(v___x_4527_, 0, v___x_4534_);
v___x_4536_ = v___x_4527_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v___x_4534_);
lean_ctor_set(v_reuseFailAlloc_4537_, 1, v_trace_4413_);
lean_ctor_set(v_reuseFailAlloc_4537_, 2, v_buildTime_4414_);
lean_ctor_set_uint8(v_reuseFailAlloc_4537_, sizeof(void*)*3, v_action_4411_);
lean_ctor_set_uint8(v_reuseFailAlloc_4537_, sizeof(void*)*3 + 1, v_wantsRebuild_4412_);
v___x_4536_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
v_a_4400_ = v___x_4533_;
v_a_4401_ = v___x_4536_;
goto v___jp_4399_;
}
}
}
}
else
{
lean_object* v_a_4542_; lean_object* v_a_4543_; 
lean_dec_ref(v___x_4397_);
lean_dec_ref(v_log_4386_);
lean_dec_ref(v_traceFile_4362_);
lean_dec_ref(v_ext_4358_);
lean_dec_ref(v_file_4355_);
v_a_4542_ = lean_ctor_get(v___x_4408_, 0);
lean_inc(v_a_4542_);
v_a_4543_ = lean_ctor_get(v___x_4408_, 1);
lean_inc(v_a_4543_);
lean_dec_ref(v___x_4408_);
v_a_4400_ = v_a_4542_;
v_a_4401_ = v_a_4543_;
goto v___jp_4399_;
}
}
}
else
{
lean_object* v_a_4545_; lean_object* v___x_4546_; uint8_t v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4552_; 
lean_dec_ref(v___x_4397_);
lean_dec_ref(v_traceFile_4362_);
lean_dec_ref(v_a_4360_);
lean_dec_ref(v_ext_4358_);
lean_dec_ref(v_build_4356_);
lean_dec_ref(v_file_4355_);
v_a_4545_ = lean_ctor_get(v___x_4405_, 0);
lean_inc(v_a_4545_);
lean_dec_ref(v___x_4405_);
v___x_4546_ = lean_io_error_to_string(v_a_4545_);
v___x_4547_ = 3;
v___x_4548_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4548_, 0, v___x_4546_);
lean_ctor_set_uint8(v___x_4548_, sizeof(void*)*1, v___x_4547_);
v___x_4549_ = lean_array_get_size(v_log_4386_);
v___x_4550_ = lean_array_push(v_log_4386_, v___x_4548_);
if (v_isShared_4393_ == 0)
{
lean_ctor_set(v___x_4392_, 0, v___x_4550_);
v___x_4552_ = v___x_4392_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v___x_4550_);
lean_ctor_set(v_reuseFailAlloc_4553_, 1, v_trace_4389_);
lean_ctor_set(v_reuseFailAlloc_4553_, 2, v_buildTime_4390_);
lean_ctor_set_uint8(v_reuseFailAlloc_4553_, sizeof(void*)*3 + 1, v_wantsRebuild_4388_);
v___x_4552_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
lean_ctor_set_uint8(v___x_4552_, sizeof(void*)*3, v___x_4395_);
v_a_4400_ = v___x_4549_;
v_a_4401_ = v___x_4552_;
goto v___jp_4399_;
}
}
v___jp_4399_:
{
lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v_a_4404_; 
v___x_4402_ = lean_box(0);
v___x_4403_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v___x_4398_, v___x_4402_, v_a_4401_);
lean_dec(v___x_4398_);
v_a_4404_ = lean_ctor_get(v___x_4403_, 1);
lean_inc(v_a_4404_);
lean_dec_ref(v___x_4403_);
v_a_4371_ = v_a_4400_;
v_a_4372_ = v_a_4404_;
goto v___jp_4370_;
}
}
else
{
uint8_t v___x_4554_; 
lean_dec_ref(v_a_4360_);
lean_dec_ref(v_ext_4358_);
lean_dec_ref(v_build_4356_);
lean_dec_ref(v_file_4355_);
v___x_4554_ = l_System_FilePath_pathExists(v_traceFile_4362_);
lean_dec_ref(v_traceFile_4362_);
if (v___x_4554_ == 0)
{
lean_dec_ref(v___x_4397_);
lean_del_object(v___x_4392_);
v_log_4375_ = v_log_4386_;
v_action_4376_ = v___x_4395_;
v_wantsRebuild_4377_ = v_noBuild_4394_;
v_trace_4378_ = v_trace_4389_;
v_buildTime_4379_ = v_buildTime_4390_;
goto v___jp_4374_;
}
else
{
lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; 
v___x_4555_ = lean_box(0);
v___x_4556_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_4557_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_4361_, v___x_4555_, v___x_4556_);
v___x_4558_ = l_Lake_BuildMetadata_writeFile(v___x_4397_, v___x_4557_);
if (lean_obj_tag(v___x_4558_) == 0)
{
lean_dec_ref(v___x_4558_);
lean_del_object(v___x_4392_);
v_log_4375_ = v_log_4386_;
v_action_4376_ = v___x_4395_;
v_wantsRebuild_4377_ = v_noBuild_4394_;
v_trace_4378_ = v_trace_4389_;
v_buildTime_4379_ = v_buildTime_4390_;
goto v___jp_4374_;
}
else
{
lean_object* v_a_4559_; lean_object* v___x_4560_; uint8_t v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4566_; 
v_a_4559_ = lean_ctor_get(v___x_4558_, 0);
lean_inc(v_a_4559_);
lean_dec_ref(v___x_4558_);
v___x_4560_ = lean_io_error_to_string(v_a_4559_);
v___x_4561_ = 3;
v___x_4562_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4562_, 0, v___x_4560_);
lean_ctor_set_uint8(v___x_4562_, sizeof(void*)*1, v___x_4561_);
v___x_4563_ = lean_array_get_size(v_log_4386_);
v___x_4564_ = lean_array_push(v_log_4386_, v___x_4562_);
if (v_isShared_4393_ == 0)
{
lean_ctor_set(v___x_4392_, 0, v___x_4564_);
v___x_4566_ = v___x_4392_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v___x_4564_);
lean_ctor_set(v_reuseFailAlloc_4568_, 1, v_trace_4389_);
lean_ctor_set(v_reuseFailAlloc_4568_, 2, v_buildTime_4390_);
v___x_4566_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
lean_object* v___x_4567_; 
lean_ctor_set_uint8(v___x_4566_, sizeof(void*)*3, v___x_4395_);
lean_ctor_set_uint8(v___x_4566_, sizeof(void*)*3 + 1, v_noBuild_4394_);
v___x_4567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4567_, 0, v___x_4563_);
lean_ctor_set(v___x_4567_, 1, v___x_4566_);
return v___x_4567_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___boxed(lean_object* v_file_4570_, lean_object* v_build_4571_, lean_object* v_traceFile_4572_, lean_object* v_ext_4573_, lean_object* v_text_4574_, lean_object* v_a_4575_, lean_object* v_depTrace_4576_, lean_object* v_traceFile_4577_, lean_object* v_action_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_){
_start:
{
uint8_t v_text_boxed_4585_; uint8_t v_action_boxed_4586_; lean_object* v_res_4587_; 
v_text_boxed_4585_ = lean_unbox(v_text_4574_);
v_action_boxed_4586_ = lean_unbox(v_action_4578_);
v_res_4587_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(v_file_4570_, v_build_4571_, v_traceFile_4572_, v_ext_4573_, v_text_boxed_4585_, v_a_4575_, v_depTrace_4576_, v_traceFile_4577_, v_action_boxed_4586_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_);
lean_dec_ref(v_a_4582_);
lean_dec(v_a_4581_);
lean_dec(v_a_4580_);
lean_dec(v_a_4579_);
lean_dec_ref(v_depTrace_4576_);
lean_dec_ref(v_traceFile_4572_);
return v_res_4587_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(lean_object* v_file_4588_, lean_object* v_build_4589_, uint8_t v_text_4590_, lean_object* v_ext_4591_, lean_object* v_depTrace_4592_, lean_object* v_traceFile_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_){
_start:
{
uint8_t v___x_4601_; lean_object* v___x_4602_; 
v___x_4601_ = 3;
lean_inc_ref(v_traceFile_4593_);
v___x_4602_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(v_file_4588_, v_build_4589_, v_traceFile_4593_, v_ext_4591_, v_text_4590_, v_a_4594_, v_depTrace_4592_, v_traceFile_4593_, v___x_4601_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_);
lean_dec_ref(v_traceFile_4593_);
return v___x_4602_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild___boxed(lean_object* v_file_4603_, lean_object* v_build_4604_, lean_object* v_text_4605_, lean_object* v_ext_4606_, lean_object* v_depTrace_4607_, lean_object* v_traceFile_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_){
_start:
{
uint8_t v_text_boxed_4616_; lean_object* v_res_4617_; 
v_text_boxed_4616_ = lean_unbox(v_text_4605_);
v_res_4617_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_4603_, v_build_4604_, v_text_boxed_4616_, v_ext_4606_, v_depTrace_4607_, v_traceFile_4608_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_);
lean_dec_ref(v_a_4613_);
lean_dec(v_a_4612_);
lean_dec(v_a_4611_);
lean_dec(v_a_4610_);
lean_dec_ref(v_depTrace_4607_);
return v_res_4617_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(lean_object* v_art_4619_, lean_object* v_traceFile_4620_, lean_object* v_a_4621_){
_start:
{
lean_object* v_log_4623_; uint8_t v_action_4624_; uint8_t v_wantsRebuild_4625_; lean_object* v_trace_4626_; lean_object* v_buildTime_4627_; lean_object* v___x_4628_; 
v_log_4623_ = lean_ctor_get(v_a_4621_, 0);
v_action_4624_ = lean_ctor_get_uint8(v_a_4621_, sizeof(void*)*3);
v_wantsRebuild_4625_ = lean_ctor_get_uint8(v_a_4621_, sizeof(void*)*3 + 1);
v_trace_4626_ = lean_ctor_get(v_a_4621_, 1);
v_buildTime_4627_ = lean_ctor_get(v_a_4621_, 2);
v___x_4628_ = lean_io_metadata(v_traceFile_4620_);
if (lean_obj_tag(v___x_4628_) == 0)
{
lean_object* v_a_4629_; lean_object* v_modified_4630_; lean_object* v_descr_4631_; lean_object* v_path_4632_; lean_object* v_name_4633_; lean_object* v___x_4635_; uint8_t v_isShared_4636_; uint8_t v_isSharedCheck_4641_; 
v_a_4629_ = lean_ctor_get(v___x_4628_, 0);
lean_inc(v_a_4629_);
lean_dec_ref(v___x_4628_);
v_modified_4630_ = lean_ctor_get(v_a_4629_, 1);
lean_inc_ref(v_modified_4630_);
lean_dec(v_a_4629_);
v_descr_4631_ = lean_ctor_get(v_art_4619_, 0);
v_path_4632_ = lean_ctor_get(v_art_4619_, 1);
v_name_4633_ = lean_ctor_get(v_art_4619_, 2);
v_isSharedCheck_4641_ = !lean_is_exclusive(v_art_4619_);
if (v_isSharedCheck_4641_ == 0)
{
lean_object* v_unused_4642_; 
v_unused_4642_ = lean_ctor_get(v_art_4619_, 3);
lean_dec(v_unused_4642_);
v___x_4635_ = v_art_4619_;
v_isShared_4636_ = v_isSharedCheck_4641_;
goto v_resetjp_4634_;
}
else
{
lean_inc(v_name_4633_);
lean_inc(v_path_4632_);
lean_inc(v_descr_4631_);
lean_dec(v_art_4619_);
v___x_4635_ = lean_box(0);
v_isShared_4636_ = v_isSharedCheck_4641_;
goto v_resetjp_4634_;
}
v_resetjp_4634_:
{
lean_object* v___x_4638_; 
if (v_isShared_4636_ == 0)
{
lean_ctor_set(v___x_4635_, 3, v_modified_4630_);
v___x_4638_ = v___x_4635_;
goto v_reusejp_4637_;
}
else
{
lean_object* v_reuseFailAlloc_4640_; 
v_reuseFailAlloc_4640_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4640_, 0, v_descr_4631_);
lean_ctor_set(v_reuseFailAlloc_4640_, 1, v_path_4632_);
lean_ctor_set(v_reuseFailAlloc_4640_, 2, v_name_4633_);
lean_ctor_set(v_reuseFailAlloc_4640_, 3, v_modified_4630_);
v___x_4638_ = v_reuseFailAlloc_4640_;
goto v_reusejp_4637_;
}
v_reusejp_4637_:
{
lean_object* v___x_4639_; 
v___x_4639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4639_, 0, v___x_4638_);
lean_ctor_set(v___x_4639_, 1, v_a_4621_);
return v___x_4639_;
}
}
}
else
{
lean_object* v_a_4643_; 
v_a_4643_ = lean_ctor_get(v___x_4628_, 0);
lean_inc(v_a_4643_);
lean_dec_ref(v___x_4628_);
if (lean_obj_tag(v_a_4643_) == 11)
{
lean_object* v___x_4644_; 
lean_dec_ref(v_a_4643_);
v___x_4644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4644_, 0, v_art_4619_);
lean_ctor_set(v___x_4644_, 1, v_a_4621_);
return v___x_4644_;
}
else
{
lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4659_; 
lean_inc(v_buildTime_4627_);
lean_inc_ref(v_trace_4626_);
lean_inc_ref(v_log_4623_);
lean_dec_ref(v_art_4619_);
v_isSharedCheck_4659_ = !lean_is_exclusive(v_a_4621_);
if (v_isSharedCheck_4659_ == 0)
{
lean_object* v_unused_4660_; lean_object* v_unused_4661_; lean_object* v_unused_4662_; 
v_unused_4660_ = lean_ctor_get(v_a_4621_, 2);
lean_dec(v_unused_4660_);
v_unused_4661_ = lean_ctor_get(v_a_4621_, 1);
lean_dec(v_unused_4661_);
v_unused_4662_ = lean_ctor_get(v_a_4621_, 0);
lean_dec(v_unused_4662_);
v___x_4646_ = v_a_4621_;
v_isShared_4647_ = v_isSharedCheck_4659_;
goto v_resetjp_4645_;
}
else
{
lean_dec(v_a_4621_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4659_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; uint8_t v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4656_; 
v___x_4648_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___closed__0));
v___x_4649_ = lean_io_error_to_string(v_a_4643_);
v___x_4650_ = lean_string_append(v___x_4648_, v___x_4649_);
lean_dec_ref(v___x_4649_);
v___x_4651_ = 3;
v___x_4652_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4652_, 0, v___x_4650_);
lean_ctor_set_uint8(v___x_4652_, sizeof(void*)*1, v___x_4651_);
v___x_4653_ = lean_array_get_size(v_log_4623_);
v___x_4654_ = lean_array_push(v_log_4623_, v___x_4652_);
if (v_isShared_4647_ == 0)
{
lean_ctor_set(v___x_4646_, 0, v___x_4654_);
v___x_4656_ = v___x_4646_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v___x_4654_);
lean_ctor_set(v_reuseFailAlloc_4658_, 1, v_trace_4626_);
lean_ctor_set(v_reuseFailAlloc_4658_, 2, v_buildTime_4627_);
lean_ctor_set_uint8(v_reuseFailAlloc_4658_, sizeof(void*)*3, v_action_4624_);
lean_ctor_set_uint8(v_reuseFailAlloc_4658_, sizeof(void*)*3 + 1, v_wantsRebuild_4625_);
v___x_4656_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
lean_object* v___x_4657_; 
v___x_4657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4657_, 0, v___x_4653_);
lean_ctor_set(v___x_4657_, 1, v___x_4656_);
return v___x_4657_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___boxed(lean_object* v_art_4663_, lean_object* v_traceFile_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_){
_start:
{
lean_object* v_res_4667_; 
v_res_4667_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_4663_, v_traceFile_4664_, v_a_4665_);
lean_dec_ref(v_traceFile_4664_);
return v_res_4667_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(lean_object* v_art_4668_, lean_object* v_traceFile_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_){
_start:
{
lean_object* v___x_4677_; 
v___x_4677_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_4668_, v_traceFile_4669_, v_a_4675_);
return v___x_4677_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___boxed(lean_object* v_art_4678_, lean_object* v_traceFile_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_){
_start:
{
lean_object* v_res_4687_; 
v_res_4687_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(v_art_4678_, v_traceFile_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_);
lean_dec_ref(v_a_4684_);
lean_dec(v_a_4683_);
lean_dec(v_a_4682_);
lean_dec(v_a_4681_);
lean_dec_ref(v_a_4680_);
lean_dec_ref(v_traceFile_4679_);
return v_res_4687_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0(lean_object* v_a_4688_, lean_object* v_____r_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_){
_start:
{
lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; 
v___x_4697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4697_, 0, v_a_4688_);
v___x_4698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4698_, 0, v___x_4697_);
v___x_4699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4699_, 0, v___x_4698_);
lean_ctor_set(v___x_4699_, 1, v___y_4695_);
return v___x_4699_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0___boxed(lean_object* v_a_4700_, lean_object* v_____r_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_){
_start:
{
lean_object* v_res_4709_; 
v_res_4709_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0(v_a_4700_, v_____r_4701_, v___y_4702_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_);
lean_dec_ref(v___y_4706_);
lean_dec(v___y_4705_);
lean_dec(v___y_4704_);
lean_dec(v___y_4703_);
lean_dec_ref(v___y_4702_);
return v_res_4709_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(uint8_t v_exe_4710_, lean_object* v___y_4711_, uint64_t v_inputHash_4712_, lean_object* v_savedTrace_4713_, lean_object* v_pkg_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_){
_start:
{
lean_object* v___y_4722_; lean_object* v_a_4726_; lean_object* v_a_4727_; lean_object* v___y_4742_; 
if (lean_obj_tag(v_savedTrace_4713_) == 2)
{
lean_object* v_data_4757_; uint64_t v_depHash_4758_; lean_object* v_outputs_x3f_4759_; uint8_t v___x_4760_; 
v_data_4757_ = lean_ctor_get(v_savedTrace_4713_, 0);
lean_inc_ref(v_data_4757_);
lean_dec_ref(v_savedTrace_4713_);
v_depHash_4758_ = lean_ctor_get_uint64(v_data_4757_, sizeof(void*)*3);
v_outputs_x3f_4759_ = lean_ctor_get(v_data_4757_, 1);
lean_inc(v_outputs_x3f_4759_);
lean_dec_ref(v_data_4757_);
v___x_4760_ = lean_uint64_dec_eq(v_depHash_4758_, v_inputHash_4712_);
if (v___x_4760_ == 0)
{
lean_dec(v_outputs_x3f_4759_);
lean_dec_ref(v_a_4718_);
lean_dec_ref(v_pkg_4714_);
lean_dec_ref(v___y_4711_);
v___y_4722_ = v_a_4719_;
goto v___jp_4721_;
}
else
{
if (lean_obj_tag(v_outputs_x3f_4759_) == 1)
{
lean_object* v_val_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; 
v_val_4761_ = lean_ctor_get(v_outputs_x3f_4759_, 0);
lean_inc(v_val_4761_);
lean_dec_ref(v_outputs_x3f_4759_);
v___x_4762_ = lean_box(0);
lean_inc(v_val_4761_);
v___x_4763_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4763_, 0, v_val_4761_);
lean_ctor_set(v___x_4763_, 1, v___x_4762_);
lean_ctor_set(v___x_4763_, 2, v___x_4762_);
lean_inc_ref(v___y_4711_);
v___x_4764_ = l_Lake_resolveArtifactOutput(v___x_4763_, v_exe_4710_, v___y_4711_, v_a_4715_, v_a_4716_, v_a_4717_, v_a_4718_, v_a_4719_);
if (lean_obj_tag(v___x_4764_) == 0)
{
lean_object* v_config_4765_; lean_object* v_a_4766_; lean_object* v_a_4767_; lean_object* v_enableArtifactCache_x3f_4768_; lean_object* v_a_4770_; uint8_t v_a_4774_; lean_object* v_a_4775_; 
v_config_4765_ = lean_ctor_get(v_pkg_4714_, 6);
v_a_4766_ = lean_ctor_get(v___x_4764_, 0);
lean_inc(v_a_4766_);
v_a_4767_ = lean_ctor_get(v___x_4764_, 1);
lean_inc(v_a_4767_);
lean_dec_ref(v___x_4764_);
v_enableArtifactCache_x3f_4768_ = lean_ctor_get(v_config_4765_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_4768_) == 0)
{
lean_object* v_toContext_4806_; lean_object* v_lakeEnv_4807_; lean_object* v_enableArtifactCache_x3f_4808_; 
v_toContext_4806_ = lean_ctor_get(v_a_4718_, 1);
v_lakeEnv_4807_ = lean_ctor_get(v_toContext_4806_, 1);
v_enableArtifactCache_x3f_4808_ = lean_ctor_get(v_lakeEnv_4807_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_4808_) == 0)
{
lean_object* v_root_4809_; lean_object* v_config_4810_; lean_object* v_enableArtifactCache_x3f_4811_; 
v_root_4809_ = lean_ctor_get(v_toContext_4806_, 0);
v_config_4810_ = lean_ctor_get(v_root_4809_, 6);
v_enableArtifactCache_x3f_4811_ = lean_ctor_get(v_config_4810_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_4811_) == 0)
{
lean_dec(v_val_4761_);
lean_dec_ref(v_pkg_4714_);
v_a_4770_ = v_a_4767_;
goto v___jp_4769_;
}
else
{
lean_object* v_val_4812_; uint8_t v___x_4813_; 
v_val_4812_ = lean_ctor_get(v_enableArtifactCache_x3f_4811_, 0);
v___x_4813_ = lean_unbox(v_val_4812_);
v_a_4774_ = v___x_4813_;
v_a_4775_ = v_a_4767_;
goto v___jp_4773_;
}
}
else
{
lean_object* v_val_4814_; uint8_t v___x_4815_; 
v_val_4814_ = lean_ctor_get(v_enableArtifactCache_x3f_4808_, 0);
v___x_4815_ = lean_unbox(v_val_4814_);
v_a_4774_ = v___x_4815_;
v_a_4775_ = v_a_4767_;
goto v___jp_4773_;
}
}
else
{
lean_object* v_val_4816_; uint8_t v___x_4817_; 
v_val_4816_ = lean_ctor_get(v_enableArtifactCache_x3f_4768_, 0);
v___x_4817_ = lean_unbox(v_val_4816_);
v_a_4774_ = v___x_4817_;
v_a_4775_ = v_a_4767_;
goto v___jp_4773_;
}
v___jp_4769_:
{
lean_object* v___x_4771_; lean_object* v___x_4772_; 
v___x_4771_ = lean_box(0);
v___x_4772_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0(v_a_4766_, v___x_4771_, v___y_4711_, v_a_4715_, v_a_4716_, v_a_4717_, v_a_4718_, v_a_4770_);
lean_dec_ref(v_a_4718_);
lean_dec_ref(v___y_4711_);
v___y_4742_ = v___x_4772_;
goto v___jp_4741_;
}
v___jp_4773_:
{
if (v_a_4774_ == 0)
{
lean_dec(v_val_4761_);
lean_dec_ref(v_pkg_4714_);
v_a_4770_ = v_a_4775_;
goto v___jp_4769_;
}
else
{
lean_object* v_toContext_4776_; lean_object* v_log_4777_; uint8_t v_action_4778_; uint8_t v_wantsRebuild_4779_; lean_object* v_trace_4780_; lean_object* v_buildTime_4781_; lean_object* v_lakeCache_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; 
v_toContext_4776_ = lean_ctor_get(v_a_4718_, 1);
v_log_4777_ = lean_ctor_get(v_a_4775_, 0);
v_action_4778_ = lean_ctor_get_uint8(v_a_4775_, sizeof(void*)*3);
v_wantsRebuild_4779_ = lean_ctor_get_uint8(v_a_4775_, sizeof(void*)*3 + 1);
v_trace_4780_ = lean_ctor_get(v_a_4775_, 1);
v_buildTime_4781_ = lean_ctor_get(v_a_4775_, 2);
v_lakeCache_4782_ = lean_ctor_get(v_toContext_4776_, 3);
v___x_4783_ = l_Lake_Package_cacheScope(v_pkg_4714_);
lean_inc_ref(v_lakeCache_4782_);
v___x_4784_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_4782_, v___x_4783_, v_inputHash_4712_, v_val_4761_, v___x_4762_, v___x_4762_);
if (lean_obj_tag(v___x_4784_) == 0)
{
lean_object* v___x_4785_; lean_object* v___x_4786_; 
lean_dec_ref(v___x_4784_);
v___x_4785_ = lean_box(0);
v___x_4786_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0(v_a_4766_, v___x_4785_, v___y_4711_, v_a_4715_, v_a_4716_, v_a_4717_, v_a_4718_, v_a_4775_);
lean_dec_ref(v_a_4718_);
lean_dec_ref(v___y_4711_);
v___y_4742_ = v___x_4786_;
goto v___jp_4741_;
}
else
{
lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4802_; 
lean_inc(v_buildTime_4781_);
lean_inc_ref(v_trace_4780_);
lean_inc_ref(v_log_4777_);
v_isSharedCheck_4802_ = !lean_is_exclusive(v_a_4775_);
if (v_isSharedCheck_4802_ == 0)
{
lean_object* v_unused_4803_; lean_object* v_unused_4804_; lean_object* v_unused_4805_; 
v_unused_4803_ = lean_ctor_get(v_a_4775_, 2);
lean_dec(v_unused_4803_);
v_unused_4804_ = lean_ctor_get(v_a_4775_, 1);
lean_dec(v_unused_4804_);
v_unused_4805_ = lean_ctor_get(v_a_4775_, 0);
lean_dec(v_unused_4805_);
v___x_4788_ = v_a_4775_;
v_isShared_4789_ = v_isSharedCheck_4802_;
goto v_resetjp_4787_;
}
else
{
lean_dec(v_a_4775_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4802_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
lean_object* v_a_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; uint8_t v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4799_; 
v_a_4790_ = lean_ctor_get(v___x_4784_, 0);
lean_inc(v_a_4790_);
lean_dec_ref(v___x_4784_);
v___x_4791_ = ((lean_object*)(l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0));
v___x_4792_ = lean_io_error_to_string(v_a_4790_);
v___x_4793_ = lean_string_append(v___x_4791_, v___x_4792_);
lean_dec_ref(v___x_4792_);
v___x_4794_ = 2;
v___x_4795_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4795_, 0, v___x_4793_);
lean_ctor_set_uint8(v___x_4795_, sizeof(void*)*1, v___x_4794_);
v___x_4796_ = lean_box(0);
v___x_4797_ = lean_array_push(v_log_4777_, v___x_4795_);
if (v_isShared_4789_ == 0)
{
lean_ctor_set(v___x_4788_, 0, v___x_4797_);
v___x_4799_ = v___x_4788_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v___x_4797_);
lean_ctor_set(v_reuseFailAlloc_4801_, 1, v_trace_4780_);
lean_ctor_set(v_reuseFailAlloc_4801_, 2, v_buildTime_4781_);
lean_ctor_set_uint8(v_reuseFailAlloc_4801_, sizeof(void*)*3, v_action_4778_);
lean_ctor_set_uint8(v_reuseFailAlloc_4801_, sizeof(void*)*3 + 1, v_wantsRebuild_4779_);
v___x_4799_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
lean_object* v___x_4800_; 
v___x_4800_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0(v_a_4766_, v___x_4796_, v___y_4711_, v_a_4715_, v_a_4716_, v_a_4717_, v_a_4718_, v___x_4799_);
lean_dec_ref(v_a_4718_);
lean_dec_ref(v___y_4711_);
v___y_4742_ = v___x_4800_;
goto v___jp_4741_;
}
}
}
}
}
}
else
{
lean_object* v_a_4818_; lean_object* v_a_4819_; 
lean_dec(v_val_4761_);
lean_dec_ref(v_a_4718_);
lean_dec_ref(v_pkg_4714_);
lean_dec_ref(v___y_4711_);
v_a_4818_ = lean_ctor_get(v___x_4764_, 0);
lean_inc(v_a_4818_);
v_a_4819_ = lean_ctor_get(v___x_4764_, 1);
lean_inc(v_a_4819_);
lean_dec_ref(v___x_4764_);
v_a_4726_ = v_a_4818_;
v_a_4727_ = v_a_4819_;
goto v___jp_4725_;
}
}
else
{
lean_dec(v_outputs_x3f_4759_);
lean_dec_ref(v_a_4718_);
lean_dec_ref(v_pkg_4714_);
lean_dec_ref(v___y_4711_);
v___y_4722_ = v_a_4719_;
goto v___jp_4721_;
}
}
}
else
{
lean_dec_ref(v_a_4718_);
lean_dec_ref(v_pkg_4714_);
lean_dec(v_savedTrace_4713_);
lean_dec_ref(v___y_4711_);
v___y_4722_ = v_a_4719_;
goto v___jp_4721_;
}
v___jp_4721_:
{
lean_object* v___x_4723_; lean_object* v___x_4724_; 
v___x_4723_ = lean_box(0);
v___x_4724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4724_, 0, v___x_4723_);
lean_ctor_set(v___x_4724_, 1, v___y_4722_);
return v___x_4724_;
}
v___jp_4725_:
{
lean_object* v_log_4728_; uint8_t v_action_4729_; uint8_t v_wantsRebuild_4730_; lean_object* v_trace_4731_; lean_object* v_buildTime_4732_; lean_object* v___x_4734_; uint8_t v_isShared_4735_; uint8_t v_isSharedCheck_4740_; 
v_log_4728_ = lean_ctor_get(v_a_4727_, 0);
v_action_4729_ = lean_ctor_get_uint8(v_a_4727_, sizeof(void*)*3);
v_wantsRebuild_4730_ = lean_ctor_get_uint8(v_a_4727_, sizeof(void*)*3 + 1);
v_trace_4731_ = lean_ctor_get(v_a_4727_, 1);
v_buildTime_4732_ = lean_ctor_get(v_a_4727_, 2);
v_isSharedCheck_4740_ = !lean_is_exclusive(v_a_4727_);
if (v_isSharedCheck_4740_ == 0)
{
v___x_4734_ = v_a_4727_;
v_isShared_4735_ = v_isSharedCheck_4740_;
goto v_resetjp_4733_;
}
else
{
lean_inc(v_buildTime_4732_);
lean_inc(v_trace_4731_);
lean_inc(v_log_4728_);
lean_dec(v_a_4727_);
v___x_4734_ = lean_box(0);
v_isShared_4735_ = v_isSharedCheck_4740_;
goto v_resetjp_4733_;
}
v_resetjp_4733_:
{
lean_object* v___x_4736_; lean_object* v___x_4738_; 
v___x_4736_ = l_Array_shrink___redArg(v_log_4728_, v_a_4726_);
lean_dec(v_a_4726_);
if (v_isShared_4735_ == 0)
{
lean_ctor_set(v___x_4734_, 0, v___x_4736_);
v___x_4738_ = v___x_4734_;
goto v_reusejp_4737_;
}
else
{
lean_object* v_reuseFailAlloc_4739_; 
v_reuseFailAlloc_4739_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4739_, 0, v___x_4736_);
lean_ctor_set(v_reuseFailAlloc_4739_, 1, v_trace_4731_);
lean_ctor_set(v_reuseFailAlloc_4739_, 2, v_buildTime_4732_);
lean_ctor_set_uint8(v_reuseFailAlloc_4739_, sizeof(void*)*3, v_action_4729_);
lean_ctor_set_uint8(v_reuseFailAlloc_4739_, sizeof(void*)*3 + 1, v_wantsRebuild_4730_);
v___x_4738_ = v_reuseFailAlloc_4739_;
goto v_reusejp_4737_;
}
v_reusejp_4737_:
{
v___y_4722_ = v___x_4738_;
goto v___jp_4721_;
}
}
}
v___jp_4741_:
{
if (lean_obj_tag(v___y_4742_) == 0)
{
lean_object* v_a_4743_; 
v_a_4743_ = lean_ctor_get(v___y_4742_, 0);
if (lean_obj_tag(v_a_4743_) == 0)
{
lean_object* v_a_4744_; lean_object* v___x_4746_; uint8_t v_isShared_4747_; uint8_t v_isSharedCheck_4752_; 
lean_inc_ref(v_a_4743_);
v_a_4744_ = lean_ctor_get(v___y_4742_, 1);
v_isSharedCheck_4752_ = !lean_is_exclusive(v___y_4742_);
if (v_isSharedCheck_4752_ == 0)
{
lean_object* v_unused_4753_; 
v_unused_4753_ = lean_ctor_get(v___y_4742_, 0);
lean_dec(v_unused_4753_);
v___x_4746_ = v___y_4742_;
v_isShared_4747_ = v_isSharedCheck_4752_;
goto v_resetjp_4745_;
}
else
{
lean_inc(v_a_4744_);
lean_dec(v___y_4742_);
v___x_4746_ = lean_box(0);
v_isShared_4747_ = v_isSharedCheck_4752_;
goto v_resetjp_4745_;
}
v_resetjp_4745_:
{
lean_object* v_a_4748_; lean_object* v___x_4750_; 
v_a_4748_ = lean_ctor_get(v_a_4743_, 0);
lean_inc(v_a_4748_);
lean_dec_ref(v_a_4743_);
if (v_isShared_4747_ == 0)
{
lean_ctor_set(v___x_4746_, 0, v_a_4748_);
v___x_4750_ = v___x_4746_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v_a_4748_);
lean_ctor_set(v_reuseFailAlloc_4751_, 1, v_a_4744_);
v___x_4750_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
return v___x_4750_;
}
}
}
else
{
lean_object* v_a_4754_; 
v_a_4754_ = lean_ctor_get(v___y_4742_, 1);
lean_inc(v_a_4754_);
lean_dec_ref(v___y_4742_);
v___y_4722_ = v_a_4754_;
goto v___jp_4721_;
}
}
else
{
lean_object* v_a_4755_; lean_object* v_a_4756_; 
v_a_4755_ = lean_ctor_get(v___y_4742_, 0);
lean_inc(v_a_4755_);
v_a_4756_ = lean_ctor_get(v___y_4742_, 1);
lean_inc(v_a_4756_);
lean_dec_ref(v___y_4742_);
v_a_4726_ = v_a_4755_;
v_a_4727_ = v_a_4756_;
goto v___jp_4725_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___boxed(lean_object* v_exe_4820_, lean_object* v___y_4821_, lean_object* v_inputHash_4822_, lean_object* v_savedTrace_4823_, lean_object* v_pkg_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_){
_start:
{
uint8_t v_exe_boxed_4831_; uint64_t v_inputHash_boxed_4832_; lean_object* v_res_4833_; 
v_exe_boxed_4831_ = lean_unbox(v_exe_4820_);
v_inputHash_boxed_4832_ = lean_unbox_uint64(v_inputHash_4822_);
lean_dec_ref(v_inputHash_4822_);
v_res_4833_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(v_exe_boxed_4831_, v___y_4821_, v_inputHash_boxed_4832_, v_savedTrace_4823_, v_pkg_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_);
lean_dec(v_a_4827_);
lean_dec(v_a_4826_);
lean_dec(v_a_4825_);
return v_res_4833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(lean_object* v_as_4834_, size_t v_i_4835_, size_t v_stop_4836_, lean_object* v_b_4837_){
_start:
{
uint8_t v___x_4838_; 
v___x_4838_ = lean_usize_dec_eq(v_i_4835_, v_stop_4836_);
if (v___x_4838_ == 0)
{
lean_object* v___x_4839_; lean_object* v_message_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; size_t v___x_4844_; size_t v___x_4845_; 
v___x_4839_ = lean_array_uget_borrowed(v_as_4834_, v_i_4835_);
v_message_4840_ = lean_ctor_get(v___x_4839_, 0);
v___x_4841_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0));
v___x_4842_ = lean_string_append(v_b_4837_, v___x_4841_);
v___x_4843_ = lean_string_append(v___x_4842_, v_message_4840_);
v___x_4844_ = ((size_t)1ULL);
v___x_4845_ = lean_usize_add(v_i_4835_, v___x_4844_);
v_i_4835_ = v___x_4845_;
v_b_4837_ = v___x_4843_;
goto _start;
}
else
{
return v_b_4837_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0___boxed(lean_object* v_as_4847_, lean_object* v_i_4848_, lean_object* v_stop_4849_, lean_object* v_b_4850_){
_start:
{
size_t v_i_boxed_4851_; size_t v_stop_boxed_4852_; lean_object* v_res_4853_; 
v_i_boxed_4851_ = lean_unbox_usize(v_i_4848_);
lean_dec(v_i_4848_);
v_stop_boxed_4852_ = lean_unbox_usize(v_stop_4849_);
lean_dec(v_stop_4849_);
v_res_4853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(v_as_4847_, v_i_boxed_4851_, v_stop_boxed_4852_, v_b_4850_);
lean_dec_ref(v_as_4847_);
return v_res_4853_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(uint8_t v_exe_4854_, lean_object* v___y_4855_, uint64_t v_inputHash_4856_, lean_object* v_pkg_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_){
_start:
{
lean_object* v_toContext_4864_; lean_object* v_log_4865_; uint8_t v_action_4866_; uint8_t v_wantsRebuild_4867_; lean_object* v_trace_4868_; lean_object* v_buildTime_4869_; lean_object* v___x_4871_; uint8_t v_isShared_4872_; uint8_t v_isSharedCheck_4962_; 
v_toContext_4864_ = lean_ctor_get(v_a_4861_, 1);
v_log_4865_ = lean_ctor_get(v_a_4862_, 0);
v_action_4866_ = lean_ctor_get_uint8(v_a_4862_, sizeof(void*)*3);
v_wantsRebuild_4867_ = lean_ctor_get_uint8(v_a_4862_, sizeof(void*)*3 + 1);
v_trace_4868_ = lean_ctor_get(v_a_4862_, 1);
v_buildTime_4869_ = lean_ctor_get(v_a_4862_, 2);
v_isSharedCheck_4962_ = !lean_is_exclusive(v_a_4862_);
if (v_isSharedCheck_4962_ == 0)
{
v___x_4871_ = v_a_4862_;
v_isShared_4872_ = v_isSharedCheck_4962_;
goto v_resetjp_4870_;
}
else
{
lean_inc(v_buildTime_4869_);
lean_inc(v_trace_4868_);
lean_inc(v_log_4865_);
lean_dec(v_a_4862_);
v___x_4871_ = lean_box(0);
v_isShared_4872_ = v_isSharedCheck_4962_;
goto v_resetjp_4870_;
}
v_resetjp_4870_:
{
lean_object* v_lakeCache_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; 
v_lakeCache_4873_ = lean_ctor_get(v_toContext_4864_, 3);
v___x_4874_ = l_Lake_Package_cacheScope(v_pkg_4857_);
lean_inc_ref(v_lakeCache_4873_);
v___x_4875_ = l_Lake_Cache_readOutputs_x3f(v_lakeCache_4873_, v___x_4874_, v_inputHash_4856_, v_log_4865_);
if (lean_obj_tag(v___x_4875_) == 0)
{
lean_object* v_a_4876_; lean_object* v_a_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4949_; 
v_a_4876_ = lean_ctor_get(v___x_4875_, 0);
v_a_4877_ = lean_ctor_get(v___x_4875_, 1);
v_isSharedCheck_4949_ = !lean_is_exclusive(v___x_4875_);
if (v_isSharedCheck_4949_ == 0)
{
v___x_4879_ = v___x_4875_;
v_isShared_4880_ = v_isSharedCheck_4949_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_a_4877_);
lean_inc(v_a_4876_);
lean_dec(v___x_4875_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4949_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
lean_object* v___x_4882_; 
if (v_isShared_4872_ == 0)
{
lean_ctor_set(v___x_4871_, 0, v_a_4877_);
v___x_4882_ = v___x_4871_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4948_; 
v_reuseFailAlloc_4948_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4948_, 0, v_a_4877_);
lean_ctor_set(v_reuseFailAlloc_4948_, 1, v_trace_4868_);
lean_ctor_set(v_reuseFailAlloc_4948_, 2, v_buildTime_4869_);
lean_ctor_set_uint8(v_reuseFailAlloc_4948_, sizeof(void*)*3, v_action_4866_);
lean_ctor_set_uint8(v_reuseFailAlloc_4948_, sizeof(void*)*3 + 1, v_wantsRebuild_4867_);
v___x_4882_ = v_reuseFailAlloc_4948_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
if (lean_obj_tag(v_a_4876_) == 1)
{
lean_object* v_val_4883_; lean_object* v___x_4885_; uint8_t v_isShared_4886_; uint8_t v_isSharedCheck_4943_; 
v_val_4883_ = lean_ctor_get(v_a_4876_, 0);
v_isSharedCheck_4943_ = !lean_is_exclusive(v_a_4876_);
if (v_isSharedCheck_4943_ == 0)
{
v___x_4885_ = v_a_4876_;
v_isShared_4886_ = v_isSharedCheck_4943_;
goto v_resetjp_4884_;
}
else
{
lean_inc(v_val_4883_);
lean_dec(v_a_4876_);
v___x_4885_ = lean_box(0);
v_isShared_4886_ = v_isSharedCheck_4943_;
goto v_resetjp_4884_;
}
v_resetjp_4884_:
{
lean_object* v___x_4887_; lean_object* v_r_4889_; lean_object* v___y_4890_; 
v___x_4887_ = l_Lake_resolveArtifactOutput(v_val_4883_, v_exe_4854_, v___y_4855_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v___x_4882_);
lean_dec_ref(v_a_4861_);
if (lean_obj_tag(v___x_4887_) == 0)
{
lean_object* v_a_4894_; lean_object* v_a_4895_; lean_object* v___x_4897_; 
v_a_4894_ = lean_ctor_get(v___x_4887_, 0);
lean_inc(v_a_4894_);
v_a_4895_ = lean_ctor_get(v___x_4887_, 1);
lean_inc(v_a_4895_);
lean_dec_ref(v___x_4887_);
if (v_isShared_4886_ == 0)
{
lean_ctor_set(v___x_4885_, 0, v_a_4894_);
v___x_4897_ = v___x_4885_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_a_4894_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
v_r_4889_ = v___x_4897_;
v___y_4890_ = v_a_4895_;
goto v___jp_4888_;
}
}
else
{
lean_object* v_a_4899_; lean_object* v_a_4900_; lean_object* v_log_4901_; uint8_t v_action_4902_; uint8_t v_wantsRebuild_4903_; lean_object* v_trace_4904_; lean_object* v_buildTime_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4942_; 
lean_del_object(v___x_4885_);
v_a_4899_ = lean_ctor_get(v___x_4887_, 1);
lean_inc(v_a_4899_);
v_a_4900_ = lean_ctor_get(v___x_4887_, 0);
lean_inc(v_a_4900_);
lean_dec_ref(v___x_4887_);
v_log_4901_ = lean_ctor_get(v_a_4899_, 0);
v_action_4902_ = lean_ctor_get_uint8(v_a_4899_, sizeof(void*)*3);
v_wantsRebuild_4903_ = lean_ctor_get_uint8(v_a_4899_, sizeof(void*)*3 + 1);
v_trace_4904_ = lean_ctor_get(v_a_4899_, 1);
v_buildTime_4905_ = lean_ctor_get(v_a_4899_, 2);
v_isSharedCheck_4942_ = !lean_is_exclusive(v_a_4899_);
if (v_isSharedCheck_4942_ == 0)
{
v___x_4907_ = v_a_4899_;
v_isShared_4908_ = v_isSharedCheck_4942_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_buildTime_4905_);
lean_inc(v_trace_4904_);
lean_inc(v_log_4901_);
lean_dec(v_a_4899_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4942_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___y_4913_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; uint8_t v___x_4934_; 
v___x_4909_ = lean_array_get_size(v_log_4901_);
lean_inc(v_a_4900_);
v___x_4910_ = l_Array_extract___redArg(v_log_4901_, v_a_4900_, v___x_4909_);
v___x_4911_ = l_Array_shrink___redArg(v_log_4901_, v_a_4900_);
lean_dec(v_a_4900_);
v___x_4921_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0));
v___x_4922_ = l_Lake_Hash_hex(v_inputHash_4856_);
v___x_4923_ = lean_unsigned_to_nat(7u);
v___x_4924_ = lean_unsigned_to_nat(0u);
v___x_4925_ = lean_string_utf8_byte_size(v___x_4922_);
lean_inc_ref(v___x_4922_);
v___x_4926_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4926_, 0, v___x_4922_);
lean_ctor_set(v___x_4926_, 1, v___x_4924_);
lean_ctor_set(v___x_4926_, 2, v___x_4925_);
v___x_4927_ = l_String_Slice_Pos_nextn(v___x_4926_, v___x_4924_, v___x_4923_);
lean_dec_ref(v___x_4926_);
v___x_4928_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4928_, 0, v___x_4922_);
lean_ctor_set(v___x_4928_, 1, v___x_4924_);
lean_ctor_set(v___x_4928_, 2, v___x_4927_);
v___x_4929_ = l_String_Slice_toString(v___x_4928_);
lean_dec_ref(v___x_4928_);
v___x_4930_ = lean_string_append(v___x_4921_, v___x_4929_);
lean_dec_ref(v___x_4929_);
v___x_4931_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1));
v___x_4932_ = lean_string_append(v___x_4930_, v___x_4931_);
v___x_4933_ = lean_array_get_size(v___x_4910_);
v___x_4934_ = lean_nat_dec_lt(v___x_4924_, v___x_4933_);
if (v___x_4934_ == 0)
{
lean_dec_ref(v___x_4910_);
v___y_4913_ = v___x_4932_;
goto v___jp_4912_;
}
else
{
uint8_t v___x_4935_; 
v___x_4935_ = lean_nat_dec_le(v___x_4933_, v___x_4933_);
if (v___x_4935_ == 0)
{
if (v___x_4934_ == 0)
{
lean_dec_ref(v___x_4910_);
v___y_4913_ = v___x_4932_;
goto v___jp_4912_;
}
else
{
size_t v___x_4936_; size_t v___x_4937_; lean_object* v___x_4938_; 
v___x_4936_ = ((size_t)0ULL);
v___x_4937_ = lean_usize_of_nat(v___x_4933_);
v___x_4938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(v___x_4910_, v___x_4936_, v___x_4937_, v___x_4932_);
lean_dec_ref(v___x_4910_);
v___y_4913_ = v___x_4938_;
goto v___jp_4912_;
}
}
else
{
size_t v___x_4939_; size_t v___x_4940_; lean_object* v___x_4941_; 
v___x_4939_ = ((size_t)0ULL);
v___x_4940_ = lean_usize_of_nat(v___x_4933_);
v___x_4941_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(v___x_4910_, v___x_4939_, v___x_4940_, v___x_4932_);
lean_dec_ref(v___x_4910_);
v___y_4913_ = v___x_4941_;
goto v___jp_4912_;
}
}
v___jp_4912_:
{
uint8_t v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4918_; 
v___x_4914_ = 2;
v___x_4915_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4915_, 0, v___y_4913_);
lean_ctor_set_uint8(v___x_4915_, sizeof(void*)*1, v___x_4914_);
v___x_4916_ = lean_array_push(v___x_4911_, v___x_4915_);
if (v_isShared_4908_ == 0)
{
lean_ctor_set(v___x_4907_, 0, v___x_4916_);
v___x_4918_ = v___x_4907_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v___x_4916_);
lean_ctor_set(v_reuseFailAlloc_4920_, 1, v_trace_4904_);
lean_ctor_set(v_reuseFailAlloc_4920_, 2, v_buildTime_4905_);
lean_ctor_set_uint8(v_reuseFailAlloc_4920_, sizeof(void*)*3, v_action_4902_);
lean_ctor_set_uint8(v_reuseFailAlloc_4920_, sizeof(void*)*3 + 1, v_wantsRebuild_4903_);
v___x_4918_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
lean_object* v___x_4919_; 
v___x_4919_ = lean_box(0);
v_r_4889_ = v___x_4919_;
v___y_4890_ = v___x_4918_;
goto v___jp_4888_;
}
}
}
}
v___jp_4888_:
{
lean_object* v___x_4892_; 
if (v_isShared_4880_ == 0)
{
lean_ctor_set(v___x_4879_, 1, v___y_4890_);
lean_ctor_set(v___x_4879_, 0, v_r_4889_);
v___x_4892_ = v___x_4879_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v_r_4889_);
lean_ctor_set(v_reuseFailAlloc_4893_, 1, v___y_4890_);
v___x_4892_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
return v___x_4892_;
}
}
}
}
else
{
lean_object* v___x_4944_; lean_object* v___x_4946_; 
lean_dec(v_a_4876_);
lean_dec_ref(v_a_4861_);
lean_dec_ref(v___y_4855_);
v___x_4944_ = lean_box(0);
if (v_isShared_4880_ == 0)
{
lean_ctor_set(v___x_4879_, 1, v___x_4882_);
lean_ctor_set(v___x_4879_, 0, v___x_4944_);
v___x_4946_ = v___x_4879_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v___x_4944_);
lean_ctor_set(v_reuseFailAlloc_4947_, 1, v___x_4882_);
v___x_4946_ = v_reuseFailAlloc_4947_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
return v___x_4946_;
}
}
}
}
}
else
{
lean_object* v_a_4950_; lean_object* v_a_4951_; lean_object* v___x_4953_; uint8_t v_isShared_4954_; uint8_t v_isSharedCheck_4961_; 
lean_dec_ref(v_a_4861_);
lean_dec_ref(v___y_4855_);
v_a_4950_ = lean_ctor_get(v___x_4875_, 0);
v_a_4951_ = lean_ctor_get(v___x_4875_, 1);
v_isSharedCheck_4961_ = !lean_is_exclusive(v___x_4875_);
if (v_isSharedCheck_4961_ == 0)
{
v___x_4953_ = v___x_4875_;
v_isShared_4954_ = v_isSharedCheck_4961_;
goto v_resetjp_4952_;
}
else
{
lean_inc(v_a_4951_);
lean_inc(v_a_4950_);
lean_dec(v___x_4875_);
v___x_4953_ = lean_box(0);
v_isShared_4954_ = v_isSharedCheck_4961_;
goto v_resetjp_4952_;
}
v_resetjp_4952_:
{
lean_object* v___x_4956_; 
if (v_isShared_4872_ == 0)
{
lean_ctor_set(v___x_4871_, 0, v_a_4951_);
v___x_4956_ = v___x_4871_;
goto v_reusejp_4955_;
}
else
{
lean_object* v_reuseFailAlloc_4960_; 
v_reuseFailAlloc_4960_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4960_, 0, v_a_4951_);
lean_ctor_set(v_reuseFailAlloc_4960_, 1, v_trace_4868_);
lean_ctor_set(v_reuseFailAlloc_4960_, 2, v_buildTime_4869_);
lean_ctor_set_uint8(v_reuseFailAlloc_4960_, sizeof(void*)*3, v_action_4866_);
lean_ctor_set_uint8(v_reuseFailAlloc_4960_, sizeof(void*)*3 + 1, v_wantsRebuild_4867_);
v___x_4956_ = v_reuseFailAlloc_4960_;
goto v_reusejp_4955_;
}
v_reusejp_4955_:
{
lean_object* v___x_4958_; 
if (v_isShared_4954_ == 0)
{
lean_ctor_set(v___x_4953_, 1, v___x_4956_);
v___x_4958_ = v___x_4953_;
goto v_reusejp_4957_;
}
else
{
lean_object* v_reuseFailAlloc_4959_; 
v_reuseFailAlloc_4959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4959_, 0, v_a_4950_);
lean_ctor_set(v_reuseFailAlloc_4959_, 1, v___x_4956_);
v___x_4958_ = v_reuseFailAlloc_4959_;
goto v_reusejp_4957_;
}
v_reusejp_4957_:
{
return v___x_4958_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object* v_exe_4963_, lean_object* v___y_4964_, lean_object* v_inputHash_4965_, lean_object* v_pkg_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_, lean_object* v_a_4971_, lean_object* v_a_4972_){
_start:
{
uint8_t v_exe_boxed_4973_; uint64_t v_inputHash_boxed_4974_; lean_object* v_res_4975_; 
v_exe_boxed_4973_ = lean_unbox(v_exe_4963_);
v_inputHash_boxed_4974_ = lean_unbox_uint64(v_inputHash_4965_);
lean_dec_ref(v_inputHash_4965_);
v_res_4975_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(v_exe_boxed_4973_, v___y_4964_, v_inputHash_boxed_4974_, v_pkg_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_);
lean_dec(v_a_4969_);
lean_dec(v_a_4968_);
lean_dec(v_a_4967_);
return v_res_4975_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(uint8_t v_exe_4976_, uint64_t v_hash_4977_, lean_object* v_val_4978_, lean_object* v_file_4979_, lean_object* v___x_4980_, lean_object* v_a_4981_, uint8_t v_restore_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_){
_start:
{
lean_object* v_a_4991_; lean_object* v___y_4995_; lean_object* v___y_4996_; lean_object* v___y_4997_; uint8_t v___y_5035_; lean_object* v___y_5036_; lean_object* v___y_5037_; uint8_t v___y_5038_; lean_object* v___y_5039_; lean_object* v___y_5040_; lean_object* v___y_5041_; lean_object* v___y_5042_; lean_object* v___y_5056_; lean_object* v___x_5113_; 
lean_inc_ref(v___y_4987_);
lean_inc_ref(v_val_4978_);
lean_inc_ref(v___y_4983_);
v___x_5113_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(v_exe_4976_, v___y_4983_, v_hash_4977_, v_val_4978_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_);
if (lean_obj_tag(v___x_5113_) == 0)
{
lean_object* v_a_5114_; 
v_a_5114_ = lean_ctor_get(v___x_5113_, 0);
lean_inc(v_a_5114_);
if (lean_obj_tag(v_a_5114_) == 1)
{
lean_dec_ref(v_a_5114_);
lean_dec_ref(v___y_4983_);
lean_dec_ref(v_val_4978_);
v___y_5056_ = v___x_5113_;
goto v___jp_5055_;
}
else
{
lean_object* v_a_5115_; lean_object* v___x_5116_; lean_object* v_a_5117_; 
lean_dec(v_a_5114_);
v_a_5115_ = lean_ctor_get(v___x_5113_, 1);
lean_inc(v_a_5115_);
lean_dec_ref(v___x_5113_);
lean_inc_ref(v___y_4987_);
lean_inc(v_a_4981_);
v___x_5116_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(v_exe_4976_, v___y_4983_, v_hash_4977_, v_a_4981_, v_val_4978_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_, v_a_5115_);
v_a_5117_ = lean_ctor_get(v___x_5116_, 0);
lean_inc(v_a_5117_);
if (lean_obj_tag(v_a_5117_) == 1)
{
lean_dec_ref(v_a_5117_);
v___y_5056_ = v___x_5116_;
goto v___jp_5055_;
}
else
{
lean_object* v_a_5118_; 
lean_dec(v_a_5117_);
lean_dec(v_a_4981_);
lean_dec_ref(v___x_4980_);
lean_dec_ref(v_file_4979_);
v_a_5118_ = lean_ctor_get(v___x_5116_, 1);
lean_inc(v_a_5118_);
lean_dec_ref(v___x_5116_);
v_a_4991_ = v_a_5118_;
goto v___jp_4990_;
}
}
}
else
{
lean_dec_ref(v___y_4983_);
lean_dec_ref(v_val_4978_);
v___y_5056_ = v___x_5113_;
goto v___jp_5055_;
}
v___jp_4990_:
{
lean_object* v___x_4992_; lean_object* v___x_4993_; 
v___x_4992_ = lean_box(0);
v___x_4993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4993_, 0, v___x_4992_);
lean_ctor_set(v___x_4993_, 1, v_a_4991_);
return v___x_4993_;
}
v___jp_4994_:
{
if (v_restore_4982_ == 0)
{
lean_object* v___x_4998_; 
lean_dec_ref(v___y_4996_);
lean_dec_ref(v_file_4979_);
v___x_4998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4998_, 0, v___y_4995_);
lean_ctor_set(v___x_4998_, 1, v___y_4997_);
return v___x_4998_;
}
else
{
lean_object* v_log_4999_; uint8_t v_action_5000_; uint8_t v_wantsRebuild_5001_; lean_object* v_trace_5002_; lean_object* v_buildTime_5003_; lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5033_; 
lean_dec(v___y_4995_);
v_log_4999_ = lean_ctor_get(v___y_4997_, 0);
v_action_5000_ = lean_ctor_get_uint8(v___y_4997_, sizeof(void*)*3);
v_wantsRebuild_5001_ = lean_ctor_get_uint8(v___y_4997_, sizeof(void*)*3 + 1);
v_trace_5002_ = lean_ctor_get(v___y_4997_, 1);
v_buildTime_5003_ = lean_ctor_get(v___y_4997_, 2);
v_isSharedCheck_5033_ = !lean_is_exclusive(v___y_4997_);
if (v_isSharedCheck_5033_ == 0)
{
v___x_5005_ = v___y_4997_;
v_isShared_5006_ = v_isSharedCheck_5033_;
goto v_resetjp_5004_;
}
else
{
lean_inc(v_buildTime_5003_);
lean_inc(v_trace_5002_);
lean_inc(v_log_4999_);
lean_dec(v___y_4997_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5033_;
goto v_resetjp_5004_;
}
v_resetjp_5004_:
{
lean_object* v___x_5007_; 
v___x_5007_ = l_Lake_restoreArtifact(v_file_4979_, v___y_4996_, v_exe_4976_, v_log_4999_);
if (lean_obj_tag(v___x_5007_) == 0)
{
lean_object* v_a_5008_; lean_object* v_a_5009_; lean_object* v___x_5011_; uint8_t v_isShared_5012_; uint8_t v_isSharedCheck_5020_; 
v_a_5008_ = lean_ctor_get(v___x_5007_, 0);
v_a_5009_ = lean_ctor_get(v___x_5007_, 1);
v_isSharedCheck_5020_ = !lean_is_exclusive(v___x_5007_);
if (v_isSharedCheck_5020_ == 0)
{
v___x_5011_ = v___x_5007_;
v_isShared_5012_ = v_isSharedCheck_5020_;
goto v_resetjp_5010_;
}
else
{
lean_inc(v_a_5009_);
lean_inc(v_a_5008_);
lean_dec(v___x_5007_);
v___x_5011_ = lean_box(0);
v_isShared_5012_ = v_isSharedCheck_5020_;
goto v_resetjp_5010_;
}
v_resetjp_5010_:
{
lean_object* v___x_5014_; 
if (v_isShared_5006_ == 0)
{
lean_ctor_set(v___x_5005_, 0, v_a_5009_);
v___x_5014_ = v___x_5005_;
goto v_reusejp_5013_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v_a_5009_);
lean_ctor_set(v_reuseFailAlloc_5019_, 1, v_trace_5002_);
lean_ctor_set(v_reuseFailAlloc_5019_, 2, v_buildTime_5003_);
lean_ctor_set_uint8(v_reuseFailAlloc_5019_, sizeof(void*)*3, v_action_5000_);
lean_ctor_set_uint8(v_reuseFailAlloc_5019_, sizeof(void*)*3 + 1, v_wantsRebuild_5001_);
v___x_5014_ = v_reuseFailAlloc_5019_;
goto v_reusejp_5013_;
}
v_reusejp_5013_:
{
lean_object* v___x_5015_; lean_object* v___x_5017_; 
v___x_5015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5015_, 0, v_a_5008_);
if (v_isShared_5012_ == 0)
{
lean_ctor_set(v___x_5011_, 1, v___x_5014_);
lean_ctor_set(v___x_5011_, 0, v___x_5015_);
v___x_5017_ = v___x_5011_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v___x_5015_);
lean_ctor_set(v_reuseFailAlloc_5018_, 1, v___x_5014_);
v___x_5017_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5016_;
}
v_reusejp_5016_:
{
return v___x_5017_;
}
}
}
}
else
{
lean_object* v_a_5021_; lean_object* v_a_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5032_; 
v_a_5021_ = lean_ctor_get(v___x_5007_, 0);
v_a_5022_ = lean_ctor_get(v___x_5007_, 1);
v_isSharedCheck_5032_ = !lean_is_exclusive(v___x_5007_);
if (v_isSharedCheck_5032_ == 0)
{
v___x_5024_ = v___x_5007_;
v_isShared_5025_ = v_isSharedCheck_5032_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_a_5022_);
lean_inc(v_a_5021_);
lean_dec(v___x_5007_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5032_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v___x_5027_; 
if (v_isShared_5006_ == 0)
{
lean_ctor_set(v___x_5005_, 0, v_a_5022_);
v___x_5027_ = v___x_5005_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v_a_5022_);
lean_ctor_set(v_reuseFailAlloc_5031_, 1, v_trace_5002_);
lean_ctor_set(v_reuseFailAlloc_5031_, 2, v_buildTime_5003_);
lean_ctor_set_uint8(v_reuseFailAlloc_5031_, sizeof(void*)*3, v_action_5000_);
lean_ctor_set_uint8(v_reuseFailAlloc_5031_, sizeof(void*)*3 + 1, v_wantsRebuild_5001_);
v___x_5027_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
lean_object* v___x_5029_; 
if (v_isShared_5025_ == 0)
{
lean_ctor_set(v___x_5024_, 1, v___x_5027_);
v___x_5029_ = v___x_5024_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v_a_5021_);
lean_ctor_set(v_reuseFailAlloc_5030_, 1, v___x_5027_);
v___x_5029_ = v_reuseFailAlloc_5030_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
return v___x_5029_;
}
}
}
}
}
}
}
v___jp_5034_:
{
lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; 
v___x_5043_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5043_, 0, v___y_5042_);
v___x_5044_ = l_Lake_BuildMetadata_ofFetch(v_hash_4977_, v___x_5043_);
v___x_5045_ = l_Lake_BuildMetadata_writeFile(v___x_4980_, v___x_5044_);
if (lean_obj_tag(v___x_5045_) == 0)
{
lean_object* v___x_5046_; 
lean_dec_ref(v___x_5045_);
v___x_5046_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5046_, 0, v___y_5036_);
lean_ctor_set(v___x_5046_, 1, v___y_5037_);
lean_ctor_set(v___x_5046_, 2, v___y_5039_);
lean_ctor_set_uint8(v___x_5046_, sizeof(void*)*3, v___y_5038_);
lean_ctor_set_uint8(v___x_5046_, sizeof(void*)*3 + 1, v___y_5035_);
v___y_4995_ = v___y_5040_;
v___y_4996_ = v___y_5041_;
v___y_4997_ = v___x_5046_;
goto v___jp_4994_;
}
else
{
lean_object* v_a_5047_; lean_object* v___x_5048_; uint8_t v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; 
lean_dec_ref(v___y_5041_);
lean_dec(v___y_5040_);
lean_dec_ref(v_file_4979_);
v_a_5047_ = lean_ctor_get(v___x_5045_, 0);
lean_inc(v_a_5047_);
lean_dec_ref(v___x_5045_);
v___x_5048_ = lean_io_error_to_string(v_a_5047_);
v___x_5049_ = 3;
v___x_5050_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5050_, 0, v___x_5048_);
lean_ctor_set_uint8(v___x_5050_, sizeof(void*)*1, v___x_5049_);
v___x_5051_ = lean_array_get_size(v___y_5036_);
v___x_5052_ = lean_array_push(v___y_5036_, v___x_5050_);
v___x_5053_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5053_, 0, v___x_5052_);
lean_ctor_set(v___x_5053_, 1, v___y_5037_);
lean_ctor_set(v___x_5053_, 2, v___y_5039_);
lean_ctor_set_uint8(v___x_5053_, sizeof(void*)*3, v___y_5038_);
lean_ctor_set_uint8(v___x_5053_, sizeof(void*)*3 + 1, v___y_5035_);
v___x_5054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5054_, 0, v___x_5051_);
lean_ctor_set(v___x_5054_, 1, v___x_5053_);
return v___x_5054_;
}
}
v___jp_5055_:
{
if (lean_obj_tag(v___y_5056_) == 0)
{
lean_object* v_a_5057_; 
v_a_5057_ = lean_ctor_get(v___y_5056_, 0);
if (lean_obj_tag(v_a_5057_) == 1)
{
lean_object* v_a_5058_; lean_object* v_val_5059_; lean_object* v___x_5060_; 
lean_inc_ref(v_a_5057_);
v_a_5058_ = lean_ctor_get(v___y_5056_, 1);
lean_inc(v_a_5058_);
lean_dec_ref(v___y_5056_);
v_val_5059_ = lean_ctor_get(v_a_5057_, 0);
lean_inc(v_val_5059_);
v___x_5060_ = l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(v_hash_4977_, v_a_4981_, v_a_5058_);
lean_dec(v_a_4981_);
if (lean_obj_tag(v___x_5060_) == 0)
{
lean_object* v_a_5061_; uint8_t v___x_5062_; 
v_a_5061_ = lean_ctor_get(v___x_5060_, 0);
lean_inc(v_a_5061_);
v___x_5062_ = lean_unbox(v_a_5061_);
lean_dec(v_a_5061_);
if (v___x_5062_ == 0)
{
lean_object* v_a_5063_; lean_object* v___x_5065_; uint8_t v_isShared_5066_; uint8_t v_isSharedCheck_5100_; 
v_a_5063_ = lean_ctor_get(v___x_5060_, 1);
v_isSharedCheck_5100_ = !lean_is_exclusive(v___x_5060_);
if (v_isSharedCheck_5100_ == 0)
{
lean_object* v_unused_5101_; 
v_unused_5101_ = lean_ctor_get(v___x_5060_, 0);
lean_dec(v_unused_5101_);
v___x_5065_ = v___x_5060_;
v_isShared_5066_ = v_isSharedCheck_5100_;
goto v_resetjp_5064_;
}
else
{
lean_inc(v_a_5063_);
lean_dec(v___x_5060_);
v___x_5065_ = lean_box(0);
v_isShared_5066_ = v_isSharedCheck_5100_;
goto v_resetjp_5064_;
}
v_resetjp_5064_:
{
lean_object* v_log_5067_; uint8_t v_action_5068_; uint8_t v_wantsRebuild_5069_; lean_object* v_trace_5070_; lean_object* v_buildTime_5071_; lean_object* v___x_5073_; uint8_t v_isShared_5074_; uint8_t v_isSharedCheck_5099_; 
v_log_5067_ = lean_ctor_get(v_a_5063_, 0);
v_action_5068_ = lean_ctor_get_uint8(v_a_5063_, sizeof(void*)*3);
v_wantsRebuild_5069_ = lean_ctor_get_uint8(v_a_5063_, sizeof(void*)*3 + 1);
v_trace_5070_ = lean_ctor_get(v_a_5063_, 1);
v_buildTime_5071_ = lean_ctor_get(v_a_5063_, 2);
v_isSharedCheck_5099_ = !lean_is_exclusive(v_a_5063_);
if (v_isSharedCheck_5099_ == 0)
{
v___x_5073_ = v_a_5063_;
v_isShared_5074_ = v_isSharedCheck_5099_;
goto v_resetjp_5072_;
}
else
{
lean_inc(v_buildTime_5071_);
lean_inc(v_trace_5070_);
lean_inc(v_log_5067_);
lean_dec(v_a_5063_);
v___x_5073_ = lean_box(0);
v_isShared_5074_ = v_isSharedCheck_5099_;
goto v_resetjp_5072_;
}
v_resetjp_5072_:
{
lean_object* v___x_5075_; 
v___x_5075_ = l_Lake_removeFileIfExists(v_file_4979_);
if (lean_obj_tag(v___x_5075_) == 0)
{
lean_object* v_descr_5076_; uint64_t v_hash_5077_; lean_object* v_ext_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; uint8_t v___x_5081_; 
lean_dec_ref(v___x_5075_);
lean_del_object(v___x_5073_);
lean_del_object(v___x_5065_);
v_descr_5076_ = lean_ctor_get(v_val_5059_, 0);
v_hash_5077_ = lean_ctor_get_uint64(v_descr_5076_, sizeof(void*)*1);
v_ext_5078_ = lean_ctor_get(v_descr_5076_, 0);
v___x_5079_ = lean_string_utf8_byte_size(v_ext_5078_);
v___x_5080_ = lean_unsigned_to_nat(0u);
v___x_5081_ = lean_nat_dec_eq(v___x_5079_, v___x_5080_);
if (v___x_5081_ == 0)
{
lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; 
v___x_5082_ = l_Lake_Hash_hex(v_hash_5077_);
v___x_5083_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5084_ = lean_string_append(v___x_5082_, v___x_5083_);
v___x_5085_ = lean_string_append(v___x_5084_, v_ext_5078_);
v___y_5035_ = v_wantsRebuild_5069_;
v___y_5036_ = v_log_5067_;
v___y_5037_ = v_trace_5070_;
v___y_5038_ = v_action_5068_;
v___y_5039_ = v_buildTime_5071_;
v___y_5040_ = v_a_5057_;
v___y_5041_ = v_val_5059_;
v___y_5042_ = v___x_5085_;
goto v___jp_5034_;
}
else
{
lean_object* v___x_5086_; 
v___x_5086_ = l_Lake_Hash_hex(v_hash_5077_);
v___y_5035_ = v_wantsRebuild_5069_;
v___y_5036_ = v_log_5067_;
v___y_5037_ = v_trace_5070_;
v___y_5038_ = v_action_5068_;
v___y_5039_ = v_buildTime_5071_;
v___y_5040_ = v_a_5057_;
v___y_5041_ = v_val_5059_;
v___y_5042_ = v___x_5086_;
goto v___jp_5034_;
}
}
else
{
lean_object* v_a_5087_; lean_object* v___x_5088_; uint8_t v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5094_; 
lean_dec(v_val_5059_);
lean_dec_ref(v_a_5057_);
lean_dec_ref(v___x_4980_);
lean_dec_ref(v_file_4979_);
v_a_5087_ = lean_ctor_get(v___x_5075_, 0);
lean_inc(v_a_5087_);
lean_dec_ref(v___x_5075_);
v___x_5088_ = lean_io_error_to_string(v_a_5087_);
v___x_5089_ = 3;
v___x_5090_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5090_, 0, v___x_5088_);
lean_ctor_set_uint8(v___x_5090_, sizeof(void*)*1, v___x_5089_);
v___x_5091_ = lean_array_get_size(v_log_5067_);
v___x_5092_ = lean_array_push(v_log_5067_, v___x_5090_);
if (v_isShared_5074_ == 0)
{
lean_ctor_set(v___x_5073_, 0, v___x_5092_);
v___x_5094_ = v___x_5073_;
goto v_reusejp_5093_;
}
else
{
lean_object* v_reuseFailAlloc_5098_; 
v_reuseFailAlloc_5098_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5098_, 0, v___x_5092_);
lean_ctor_set(v_reuseFailAlloc_5098_, 1, v_trace_5070_);
lean_ctor_set(v_reuseFailAlloc_5098_, 2, v_buildTime_5071_);
lean_ctor_set_uint8(v_reuseFailAlloc_5098_, sizeof(void*)*3, v_action_5068_);
lean_ctor_set_uint8(v_reuseFailAlloc_5098_, sizeof(void*)*3 + 1, v_wantsRebuild_5069_);
v___x_5094_ = v_reuseFailAlloc_5098_;
goto v_reusejp_5093_;
}
v_reusejp_5093_:
{
lean_object* v___x_5096_; 
if (v_isShared_5066_ == 0)
{
lean_ctor_set_tag(v___x_5065_, 1);
lean_ctor_set(v___x_5065_, 1, v___x_5094_);
lean_ctor_set(v___x_5065_, 0, v___x_5091_);
v___x_5096_ = v___x_5065_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5097_; 
v_reuseFailAlloc_5097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5097_, 0, v___x_5091_);
lean_ctor_set(v_reuseFailAlloc_5097_, 1, v___x_5094_);
v___x_5096_ = v_reuseFailAlloc_5097_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
return v___x_5096_;
}
}
}
}
}
}
else
{
lean_object* v_a_5102_; 
lean_dec_ref(v___x_4980_);
v_a_5102_ = lean_ctor_get(v___x_5060_, 1);
lean_inc(v_a_5102_);
lean_dec_ref(v___x_5060_);
v___y_4995_ = v_a_5057_;
v___y_4996_ = v_val_5059_;
v___y_4997_ = v_a_5102_;
goto v___jp_4994_;
}
}
else
{
lean_object* v_a_5103_; lean_object* v_a_5104_; lean_object* v___x_5106_; uint8_t v_isShared_5107_; uint8_t v_isSharedCheck_5111_; 
lean_dec(v_val_5059_);
lean_dec_ref(v_a_5057_);
lean_dec_ref(v___x_4980_);
lean_dec_ref(v_file_4979_);
v_a_5103_ = lean_ctor_get(v___x_5060_, 0);
v_a_5104_ = lean_ctor_get(v___x_5060_, 1);
v_isSharedCheck_5111_ = !lean_is_exclusive(v___x_5060_);
if (v_isSharedCheck_5111_ == 0)
{
v___x_5106_ = v___x_5060_;
v_isShared_5107_ = v_isSharedCheck_5111_;
goto v_resetjp_5105_;
}
else
{
lean_inc(v_a_5104_);
lean_inc(v_a_5103_);
lean_dec(v___x_5060_);
v___x_5106_ = lean_box(0);
v_isShared_5107_ = v_isSharedCheck_5111_;
goto v_resetjp_5105_;
}
v_resetjp_5105_:
{
lean_object* v___x_5109_; 
if (v_isShared_5107_ == 0)
{
v___x_5109_ = v___x_5106_;
goto v_reusejp_5108_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v_a_5103_);
lean_ctor_set(v_reuseFailAlloc_5110_, 1, v_a_5104_);
v___x_5109_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5108_;
}
v_reusejp_5108_:
{
return v___x_5109_;
}
}
}
}
else
{
lean_object* v_a_5112_; 
lean_dec(v_a_4981_);
lean_dec_ref(v___x_4980_);
lean_dec_ref(v_file_4979_);
v_a_5112_ = lean_ctor_get(v___y_5056_, 1);
lean_inc(v_a_5112_);
lean_dec_ref(v___y_5056_);
v_a_4991_ = v_a_5112_;
goto v___jp_4990_;
}
}
else
{
lean_dec(v_a_4981_);
lean_dec_ref(v___x_4980_);
lean_dec_ref(v_file_4979_);
return v___y_5056_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object* v_exe_5119_, lean_object* v_hash_5120_, lean_object* v_val_5121_, lean_object* v_file_5122_, lean_object* v___x_5123_, lean_object* v_a_5124_, lean_object* v_restore_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_){
_start:
{
uint8_t v_exe_boxed_5133_; uint64_t v_hash_boxed_5134_; uint8_t v_restore_boxed_5135_; lean_object* v_res_5136_; 
v_exe_boxed_5133_ = lean_unbox(v_exe_5119_);
v_hash_boxed_5134_ = lean_unbox_uint64(v_hash_5120_);
lean_dec_ref(v_hash_5120_);
v_restore_boxed_5135_ = lean_unbox(v_restore_5125_);
v_res_5136_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_boxed_5133_, v_hash_boxed_5134_, v_val_5121_, v_file_5122_, v___x_5123_, v_a_5124_, v_restore_boxed_5135_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_);
lean_dec_ref(v___y_5130_);
lean_dec(v___y_5129_);
lean_dec(v___y_5128_);
lean_dec(v___y_5127_);
return v_res_5136_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1(uint8_t v_a_5137_, lean_object* v_file_5138_, lean_object* v_ext_5139_, uint8_t v_text_5140_, uint8_t v_exe_5141_, uint8_t v___y_5142_, lean_object* v_val_5143_, uint64_t v_hash_5144_, lean_object* v_____r_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_){
_start:
{
uint8_t v___x_5153_; uint8_t v___x_5154_; 
v___x_5153_ = 1;
v___x_5154_ = l_Lake_instDecidableEqOutputStatus(v_a_5137_, v___x_5153_);
if (v___x_5154_ == 0)
{
lean_object* v_toContext_5155_; lean_object* v_log_5156_; uint8_t v_action_5157_; uint8_t v_wantsRebuild_5158_; lean_object* v_trace_5159_; lean_object* v_buildTime_5160_; lean_object* v_lakeCache_5161_; lean_object* v___x_5162_; 
v_toContext_5155_ = lean_ctor_get(v___y_5150_, 1);
lean_inc(v_toContext_5155_);
lean_dec_ref(v___y_5150_);
v_log_5156_ = lean_ctor_get(v___y_5151_, 0);
v_action_5157_ = lean_ctor_get_uint8(v___y_5151_, sizeof(void*)*3);
v_wantsRebuild_5158_ = lean_ctor_get_uint8(v___y_5151_, sizeof(void*)*3 + 1);
v_trace_5159_ = lean_ctor_get(v___y_5151_, 1);
v_buildTime_5160_ = lean_ctor_get(v___y_5151_, 2);
v_lakeCache_5161_ = lean_ctor_get(v_toContext_5155_, 3);
lean_inc_ref(v_lakeCache_5161_);
lean_dec(v_toContext_5155_);
lean_inc_ref(v_lakeCache_5161_);
v___x_5162_ = l_Lake_Cache_saveArtifact(v_lakeCache_5161_, v_file_5138_, v_ext_5139_, v_text_5140_, v_exe_5141_, v___y_5142_);
if (lean_obj_tag(v___x_5162_) == 0)
{
lean_object* v_a_5163_; lean_object* v___x_5165_; uint8_t v_isShared_5166_; uint8_t v_isSharedCheck_5204_; 
v_a_5163_ = lean_ctor_get(v___x_5162_, 0);
v_isSharedCheck_5204_ = !lean_is_exclusive(v___x_5162_);
if (v_isSharedCheck_5204_ == 0)
{
v___x_5165_ = v___x_5162_;
v_isShared_5166_ = v_isSharedCheck_5204_;
goto v_resetjp_5164_;
}
else
{
lean_inc(v_a_5163_);
lean_dec(v___x_5162_);
v___x_5165_ = lean_box(0);
v_isShared_5166_ = v_isSharedCheck_5204_;
goto v_resetjp_5164_;
}
v_resetjp_5164_:
{
lean_object* v_descr_5167_; uint64_t v_hash_5168_; lean_object* v_ext_5169_; lean_object* v___x_5170_; lean_object* v___y_5172_; lean_object* v___x_5196_; lean_object* v___x_5197_; uint8_t v___x_5198_; 
v_descr_5167_ = lean_ctor_get(v_a_5163_, 0);
v_hash_5168_ = lean_ctor_get_uint64(v_descr_5167_, sizeof(void*)*1);
v_ext_5169_ = lean_ctor_get(v_descr_5167_, 0);
v___x_5170_ = l_Lake_Package_cacheScope(v_val_5143_);
v___x_5196_ = lean_string_utf8_byte_size(v_ext_5169_);
v___x_5197_ = lean_unsigned_to_nat(0u);
v___x_5198_ = lean_nat_dec_eq(v___x_5196_, v___x_5197_);
if (v___x_5198_ == 0)
{
lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; 
v___x_5199_ = l_Lake_Hash_hex(v_hash_5168_);
v___x_5200_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5201_ = lean_string_append(v___x_5199_, v___x_5200_);
v___x_5202_ = lean_string_append(v___x_5201_, v_ext_5169_);
v___y_5172_ = v___x_5202_;
goto v___jp_5171_;
}
else
{
lean_object* v___x_5203_; 
v___x_5203_ = l_Lake_Hash_hex(v_hash_5168_);
v___y_5172_ = v___x_5203_;
goto v___jp_5171_;
}
v___jp_5171_:
{
lean_object* v___x_5174_; 
if (v_isShared_5166_ == 0)
{
lean_ctor_set_tag(v___x_5165_, 3);
lean_ctor_set(v___x_5165_, 0, v___y_5172_);
v___x_5174_ = v___x_5165_;
goto v_reusejp_5173_;
}
else
{
lean_object* v_reuseFailAlloc_5195_; 
v_reuseFailAlloc_5195_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5195_, 0, v___y_5172_);
v___x_5174_ = v_reuseFailAlloc_5195_;
goto v_reusejp_5173_;
}
v_reusejp_5173_:
{
lean_object* v___x_5175_; lean_object* v___x_5176_; 
v___x_5175_ = lean_box(0);
v___x_5176_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_5161_, v___x_5170_, v_hash_5144_, v___x_5174_, v___x_5175_, v___x_5175_);
if (lean_obj_tag(v___x_5176_) == 0)
{
lean_object* v___x_5177_; 
lean_dec_ref(v___x_5176_);
v___x_5177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5177_, 0, v_a_5163_);
lean_ctor_set(v___x_5177_, 1, v___y_5151_);
return v___x_5177_;
}
else
{
lean_object* v___x_5179_; uint8_t v_isShared_5180_; uint8_t v_isSharedCheck_5191_; 
lean_inc(v_buildTime_5160_);
lean_inc_ref(v_trace_5159_);
lean_inc_ref(v_log_5156_);
lean_dec(v_a_5163_);
v_isSharedCheck_5191_ = !lean_is_exclusive(v___y_5151_);
if (v_isSharedCheck_5191_ == 0)
{
lean_object* v_unused_5192_; lean_object* v_unused_5193_; lean_object* v_unused_5194_; 
v_unused_5192_ = lean_ctor_get(v___y_5151_, 2);
lean_dec(v_unused_5192_);
v_unused_5193_ = lean_ctor_get(v___y_5151_, 1);
lean_dec(v_unused_5193_);
v_unused_5194_ = lean_ctor_get(v___y_5151_, 0);
lean_dec(v_unused_5194_);
v___x_5179_ = v___y_5151_;
v_isShared_5180_ = v_isSharedCheck_5191_;
goto v_resetjp_5178_;
}
else
{
lean_dec(v___y_5151_);
v___x_5179_ = lean_box(0);
v_isShared_5180_ = v_isSharedCheck_5191_;
goto v_resetjp_5178_;
}
v_resetjp_5178_:
{
lean_object* v_a_5181_; lean_object* v___x_5182_; uint8_t v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5188_; 
v_a_5181_ = lean_ctor_get(v___x_5176_, 0);
lean_inc(v_a_5181_);
lean_dec_ref(v___x_5176_);
v___x_5182_ = lean_io_error_to_string(v_a_5181_);
v___x_5183_ = 3;
v___x_5184_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5184_, 0, v___x_5182_);
lean_ctor_set_uint8(v___x_5184_, sizeof(void*)*1, v___x_5183_);
v___x_5185_ = lean_array_get_size(v_log_5156_);
v___x_5186_ = lean_array_push(v_log_5156_, v___x_5184_);
if (v_isShared_5180_ == 0)
{
lean_ctor_set(v___x_5179_, 0, v___x_5186_);
v___x_5188_ = v___x_5179_;
goto v_reusejp_5187_;
}
else
{
lean_object* v_reuseFailAlloc_5190_; 
v_reuseFailAlloc_5190_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5190_, 0, v___x_5186_);
lean_ctor_set(v_reuseFailAlloc_5190_, 1, v_trace_5159_);
lean_ctor_set(v_reuseFailAlloc_5190_, 2, v_buildTime_5160_);
lean_ctor_set_uint8(v_reuseFailAlloc_5190_, sizeof(void*)*3, v_action_5157_);
lean_ctor_set_uint8(v_reuseFailAlloc_5190_, sizeof(void*)*3 + 1, v_wantsRebuild_5158_);
v___x_5188_ = v_reuseFailAlloc_5190_;
goto v_reusejp_5187_;
}
v_reusejp_5187_:
{
lean_object* v___x_5189_; 
v___x_5189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5189_, 0, v___x_5185_);
lean_ctor_set(v___x_5189_, 1, v___x_5188_);
return v___x_5189_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5206_; uint8_t v_isShared_5207_; uint8_t v_isSharedCheck_5218_; 
lean_inc(v_buildTime_5160_);
lean_inc_ref(v_trace_5159_);
lean_inc_ref(v_log_5156_);
lean_dec_ref(v_lakeCache_5161_);
lean_dec_ref(v_val_5143_);
v_isSharedCheck_5218_ = !lean_is_exclusive(v___y_5151_);
if (v_isSharedCheck_5218_ == 0)
{
lean_object* v_unused_5219_; lean_object* v_unused_5220_; lean_object* v_unused_5221_; 
v_unused_5219_ = lean_ctor_get(v___y_5151_, 2);
lean_dec(v_unused_5219_);
v_unused_5220_ = lean_ctor_get(v___y_5151_, 1);
lean_dec(v_unused_5220_);
v_unused_5221_ = lean_ctor_get(v___y_5151_, 0);
lean_dec(v_unused_5221_);
v___x_5206_ = v___y_5151_;
v_isShared_5207_ = v_isSharedCheck_5218_;
goto v_resetjp_5205_;
}
else
{
lean_dec(v___y_5151_);
v___x_5206_ = lean_box(0);
v_isShared_5207_ = v_isSharedCheck_5218_;
goto v_resetjp_5205_;
}
v_resetjp_5205_:
{
lean_object* v_a_5208_; lean_object* v___x_5209_; uint8_t v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5215_; 
v_a_5208_ = lean_ctor_get(v___x_5162_, 0);
lean_inc(v_a_5208_);
lean_dec_ref(v___x_5162_);
v___x_5209_ = lean_io_error_to_string(v_a_5208_);
v___x_5210_ = 3;
v___x_5211_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5211_, 0, v___x_5209_);
lean_ctor_set_uint8(v___x_5211_, sizeof(void*)*1, v___x_5210_);
v___x_5212_ = lean_array_get_size(v_log_5156_);
v___x_5213_ = lean_array_push(v_log_5156_, v___x_5211_);
if (v_isShared_5207_ == 0)
{
lean_ctor_set(v___x_5206_, 0, v___x_5213_);
v___x_5215_ = v___x_5206_;
goto v_reusejp_5214_;
}
else
{
lean_object* v_reuseFailAlloc_5217_; 
v_reuseFailAlloc_5217_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5217_, 0, v___x_5213_);
lean_ctor_set(v_reuseFailAlloc_5217_, 1, v_trace_5159_);
lean_ctor_set(v_reuseFailAlloc_5217_, 2, v_buildTime_5160_);
lean_ctor_set_uint8(v_reuseFailAlloc_5217_, sizeof(void*)*3, v_action_5157_);
lean_ctor_set_uint8(v_reuseFailAlloc_5217_, sizeof(void*)*3 + 1, v_wantsRebuild_5158_);
v___x_5215_ = v_reuseFailAlloc_5217_;
goto v_reusejp_5214_;
}
v_reusejp_5214_:
{
lean_object* v___x_5216_; 
v___x_5216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5216_, 0, v___x_5212_);
lean_ctor_set(v___x_5216_, 1, v___x_5215_);
return v___x_5216_;
}
}
}
}
else
{
lean_object* v___x_5222_; 
lean_dec_ref(v_val_5143_);
v___x_5222_ = l_Lake_computeArtifact___redArg(v_file_5138_, v_ext_5139_, v_text_5140_, v___y_5150_, v___y_5151_);
lean_dec_ref(v___y_5150_);
return v___x_5222_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___boxed(lean_object* v_a_5223_, lean_object* v_file_5224_, lean_object* v_ext_5225_, lean_object* v_text_5226_, lean_object* v_exe_5227_, lean_object* v___y_5228_, lean_object* v_val_5229_, lean_object* v_hash_5230_, lean_object* v_____r_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_){
_start:
{
uint8_t v_a_294484__boxed_5239_; uint8_t v_text_boxed_5240_; uint8_t v_exe_boxed_5241_; uint8_t v___y_294485__boxed_5242_; uint64_t v_hash_boxed_5243_; lean_object* v_res_5244_; 
v_a_294484__boxed_5239_ = lean_unbox(v_a_5223_);
v_text_boxed_5240_ = lean_unbox(v_text_5226_);
v_exe_boxed_5241_ = lean_unbox(v_exe_5227_);
v___y_294485__boxed_5242_ = lean_unbox(v___y_5228_);
v_hash_boxed_5243_ = lean_unbox_uint64(v_hash_5230_);
lean_dec_ref(v_hash_5230_);
v_res_5244_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v_a_294484__boxed_5239_, v_file_5224_, v_ext_5225_, v_text_boxed_5240_, v_exe_boxed_5241_, v___y_294485__boxed_5242_, v_val_5229_, v_hash_boxed_5243_, v_____r_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_, v___y_5237_);
lean_dec(v___y_5235_);
lean_dec(v___y_5234_);
lean_dec(v___y_5233_);
lean_dec_ref(v___y_5232_);
return v_res_5244_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object* v_file_5245_, lean_object* v_build_5246_, uint8_t v_text_5247_, lean_object* v_ext_5248_, uint8_t v_restore_5249_, uint8_t v_exe_5250_, uint8_t v_platformIndependent_5251_, lean_object* v_a_5252_, lean_object* v_a_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_, lean_object* v_a_5257_){
_start:
{
lean_object* v_log_5259_; uint8_t v_action_5260_; uint8_t v_wantsRebuild_5261_; lean_object* v_trace_5262_; lean_object* v_buildTime_5263_; lean_object* v___x_5265_; uint8_t v_isShared_5266_; uint8_t v_isSharedCheck_5512_; 
v_log_5259_ = lean_ctor_get(v_a_5257_, 0);
v_action_5260_ = lean_ctor_get_uint8(v_a_5257_, sizeof(void*)*3);
v_wantsRebuild_5261_ = lean_ctor_get_uint8(v_a_5257_, sizeof(void*)*3 + 1);
v_trace_5262_ = lean_ctor_get(v_a_5257_, 1);
v_buildTime_5263_ = lean_ctor_get(v_a_5257_, 2);
v_isSharedCheck_5512_ = !lean_is_exclusive(v_a_5257_);
if (v_isSharedCheck_5512_ == 0)
{
v___x_5265_ = v_a_5257_;
v_isShared_5266_ = v_isSharedCheck_5512_;
goto v_resetjp_5264_;
}
else
{
lean_inc(v_buildTime_5263_);
lean_inc(v_trace_5262_);
lean_inc(v_log_5259_);
lean_dec(v_a_5257_);
v___x_5265_ = lean_box(0);
v_isShared_5266_ = v_isSharedCheck_5512_;
goto v_resetjp_5264_;
}
v_resetjp_5264_:
{
lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v_art_5270_; lean_object* v___y_5271_; lean_object* v___y_5287_; lean_object* v_log_5288_; uint8_t v_action_5289_; uint8_t v_wantsRebuild_5290_; lean_object* v_buildTime_5291_; lean_object* v___x_5297_; 
v___x_5267_ = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(v_file_5245_);
v___x_5268_ = lean_string_append(v_file_5245_, v___x_5267_);
lean_inc_ref(v___x_5268_);
v___x_5297_ = l_Lake_readTraceFile(v___x_5268_, v_log_5259_);
if (lean_obj_tag(v___x_5297_) == 0)
{
if (lean_obj_tag(v_a_5253_) == 1)
{
lean_object* v_a_5298_; lean_object* v_a_5299_; lean_object* v_val_5300_; uint64_t v_hash_5301_; lean_object* v_mtime_5302_; lean_object* v___y_5304_; uint8_t v___y_5305_; lean_object* v___y_5306_; lean_object* v___y_5307_; lean_object* v___y_5308_; uint8_t v___y_5309_; lean_object* v___y_5310_; lean_object* v___y_5311_; lean_object* v___y_5312_; lean_object* v_wsIdx_5316_; lean_object* v_config_5317_; lean_object* v_a_5319_; lean_object* v_a_5320_; lean_object* v___y_5350_; lean_object* v_enableArtifactCache_x3f_5353_; lean_object* v_restoreAllArtifacts_x3f_5354_; uint8_t v___y_5356_; lean_object* v_a_5357_; uint8_t v___y_5374_; uint8_t v_a_5375_; lean_object* v_a_5376_; lean_object* v_a_5379_; lean_object* v___y_5409_; uint8_t v___y_5410_; uint8_t v___y_5449_; uint8_t v_a_5450_; lean_object* v_a_5451_; uint8_t v_a_5453_; lean_object* v_a_5454_; lean_object* v___x_5464_; 
v_a_5298_ = lean_ctor_get(v___x_5297_, 0);
lean_inc(v_a_5298_);
v_a_5299_ = lean_ctor_get(v___x_5297_, 1);
lean_inc(v_a_5299_);
lean_dec_ref(v___x_5297_);
v_val_5300_ = lean_ctor_get(v_a_5253_, 0);
v_hash_5301_ = lean_ctor_get_uint64(v_trace_5262_, sizeof(void*)*3);
v_mtime_5302_ = lean_ctor_get(v_trace_5262_, 2);
v_wsIdx_5316_ = lean_ctor_get(v_val_5300_, 0);
lean_inc(v_wsIdx_5316_);
v_config_5317_ = lean_ctor_get(v_val_5300_, 6);
v_enableArtifactCache_x3f_5353_ = lean_ctor_get(v_config_5317_, 24);
v_restoreAllArtifacts_x3f_5354_ = lean_ctor_get(v_config_5317_, 25);
lean_inc_ref(v_trace_5262_);
v___x_5464_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5464_, 0, v_a_5299_);
lean_ctor_set(v___x_5464_, 1, v_trace_5262_);
lean_ctor_set(v___x_5464_, 2, v_buildTime_5263_);
lean_ctor_set_uint8(v___x_5464_, sizeof(void*)*3, v_action_5260_);
lean_ctor_set_uint8(v___x_5464_, sizeof(void*)*3 + 1, v_wantsRebuild_5261_);
if (lean_obj_tag(v_enableArtifactCache_x3f_5353_) == 0)
{
lean_object* v_toContext_5465_; lean_object* v_lakeEnv_5466_; lean_object* v_enableArtifactCache_x3f_5467_; 
v_toContext_5465_ = lean_ctor_get(v_a_5256_, 1);
v_lakeEnv_5466_ = lean_ctor_get(v_toContext_5465_, 1);
v_enableArtifactCache_x3f_5467_ = lean_ctor_get(v_lakeEnv_5466_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_5467_) == 0)
{
lean_object* v_root_5468_; lean_object* v_config_5469_; lean_object* v_enableArtifactCache_x3f_5470_; 
v_root_5468_ = lean_ctor_get(v_toContext_5465_, 0);
v_config_5469_ = lean_ctor_get(v_root_5468_, 6);
v_enableArtifactCache_x3f_5470_ = lean_ctor_get(v_config_5469_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_5470_) == 0)
{
v_a_5379_ = v___x_5464_;
goto v___jp_5378_;
}
else
{
lean_object* v_val_5471_; uint8_t v___x_5472_; 
v_val_5471_ = lean_ctor_get(v_enableArtifactCache_x3f_5470_, 0);
v___x_5472_ = lean_unbox(v_val_5471_);
v_a_5453_ = v___x_5472_;
v_a_5454_ = v___x_5464_;
goto v___jp_5452_;
}
}
else
{
lean_object* v_val_5473_; uint8_t v___x_5474_; 
v_val_5473_ = lean_ctor_get(v_enableArtifactCache_x3f_5467_, 0);
v___x_5474_ = lean_unbox(v_val_5473_);
v_a_5453_ = v___x_5474_;
v_a_5454_ = v___x_5464_;
goto v___jp_5452_;
}
}
else
{
lean_object* v_val_5475_; uint8_t v___x_5476_; 
v_val_5475_ = lean_ctor_get(v_enableArtifactCache_x3f_5353_, 0);
v___x_5476_ = lean_unbox(v_val_5475_);
v_a_5453_ = v___x_5476_;
v_a_5454_ = v___x_5464_;
goto v___jp_5452_;
}
v___jp_5303_:
{
lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; 
lean_dec_ref(v___y_5311_);
v___x_5313_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5313_, 0, v___y_5312_);
v___x_5314_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_hash_5301_, v___x_5313_, v___y_5307_, v_platformIndependent_5251_);
v___x_5315_ = lean_st_ref_set(v___y_5308_, v___x_5314_);
v___y_5287_ = v___y_5304_;
v_log_5288_ = v___y_5306_;
v_action_5289_ = v___y_5305_;
v_wantsRebuild_5290_ = v___y_5309_;
v_buildTime_5291_ = v___y_5310_;
goto v___jp_5286_;
}
v___jp_5318_:
{
lean_object* v___x_5321_; uint8_t v___x_5322_; 
v___x_5321_ = lean_unsigned_to_nat(0u);
v___x_5322_ = lean_nat_dec_eq(v_wsIdx_5316_, v___x_5321_);
lean_dec(v_wsIdx_5316_);
if (v___x_5322_ == 0)
{
lean_object* v_log_5323_; uint8_t v_action_5324_; uint8_t v_wantsRebuild_5325_; lean_object* v_buildTime_5326_; 
v_log_5323_ = lean_ctor_get(v_a_5320_, 0);
lean_inc_ref(v_log_5323_);
v_action_5324_ = lean_ctor_get_uint8(v_a_5320_, sizeof(void*)*3);
v_wantsRebuild_5325_ = lean_ctor_get_uint8(v_a_5320_, sizeof(void*)*3 + 1);
v_buildTime_5326_ = lean_ctor_get(v_a_5320_, 2);
lean_inc(v_buildTime_5326_);
lean_dec_ref(v_a_5320_);
v___y_5287_ = v_a_5319_;
v_log_5288_ = v_log_5323_;
v_action_5289_ = v_action_5324_;
v_wantsRebuild_5290_ = v_wantsRebuild_5325_;
v_buildTime_5291_ = v_buildTime_5326_;
goto v___jp_5286_;
}
else
{
lean_object* v_outputsRef_x3f_5327_; 
v_outputsRef_x3f_5327_ = lean_ctor_get(v_a_5256_, 4);
if (lean_obj_tag(v_outputsRef_x3f_5327_) == 1)
{
lean_object* v_log_5328_; uint8_t v_action_5329_; uint8_t v_wantsRebuild_5330_; lean_object* v_trace_5331_; lean_object* v_buildTime_5332_; lean_object* v_val_5333_; lean_object* v___x_5334_; lean_object* v_descr_5335_; uint64_t v_hash_5336_; lean_object* v_ext_5337_; lean_object* v___x_5338_; uint8_t v___x_5339_; 
v_log_5328_ = lean_ctor_get(v_a_5320_, 0);
lean_inc_ref(v_log_5328_);
v_action_5329_ = lean_ctor_get_uint8(v_a_5320_, sizeof(void*)*3);
v_wantsRebuild_5330_ = lean_ctor_get_uint8(v_a_5320_, sizeof(void*)*3 + 1);
v_trace_5331_ = lean_ctor_get(v_a_5320_, 1);
lean_inc_ref(v_trace_5331_);
v_buildTime_5332_ = lean_ctor_get(v_a_5320_, 2);
lean_inc(v_buildTime_5332_);
lean_dec_ref(v_a_5320_);
v_val_5333_ = lean_ctor_get(v_outputsRef_x3f_5327_, 0);
v___x_5334_ = lean_st_ref_take(v_val_5333_);
v_descr_5335_ = lean_ctor_get(v_a_5319_, 0);
v_hash_5336_ = lean_ctor_get_uint64(v_descr_5335_, sizeof(void*)*1);
v_ext_5337_ = lean_ctor_get(v_descr_5335_, 0);
v___x_5338_ = lean_string_utf8_byte_size(v_ext_5337_);
v___x_5339_ = lean_nat_dec_eq(v___x_5338_, v___x_5321_);
if (v___x_5339_ == 0)
{
lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; 
v___x_5340_ = l_Lake_Hash_hex(v_hash_5336_);
v___x_5341_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5342_ = lean_string_append(v___x_5340_, v___x_5341_);
v___x_5343_ = lean_string_append(v___x_5342_, v_ext_5337_);
v___y_5304_ = v_a_5319_;
v___y_5305_ = v_action_5329_;
v___y_5306_ = v_log_5328_;
v___y_5307_ = v___x_5334_;
v___y_5308_ = v_val_5333_;
v___y_5309_ = v_wantsRebuild_5330_;
v___y_5310_ = v_buildTime_5332_;
v___y_5311_ = v_trace_5331_;
v___y_5312_ = v___x_5343_;
goto v___jp_5303_;
}
else
{
lean_object* v___x_5344_; 
v___x_5344_ = l_Lake_Hash_hex(v_hash_5336_);
v___y_5304_ = v_a_5319_;
v___y_5305_ = v_action_5329_;
v___y_5306_ = v_log_5328_;
v___y_5307_ = v___x_5334_;
v___y_5308_ = v_val_5333_;
v___y_5309_ = v_wantsRebuild_5330_;
v___y_5310_ = v_buildTime_5332_;
v___y_5311_ = v_trace_5331_;
v___y_5312_ = v___x_5344_;
goto v___jp_5303_;
}
}
else
{
lean_object* v_log_5345_; uint8_t v_action_5346_; uint8_t v_wantsRebuild_5347_; lean_object* v_buildTime_5348_; 
v_log_5345_ = lean_ctor_get(v_a_5320_, 0);
lean_inc_ref(v_log_5345_);
v_action_5346_ = lean_ctor_get_uint8(v_a_5320_, sizeof(void*)*3);
v_wantsRebuild_5347_ = lean_ctor_get_uint8(v_a_5320_, sizeof(void*)*3 + 1);
v_buildTime_5348_ = lean_ctor_get(v_a_5320_, 2);
lean_inc(v_buildTime_5348_);
lean_dec_ref(v_a_5320_);
v___y_5287_ = v_a_5319_;
v_log_5288_ = v_log_5345_;
v_action_5289_ = v_action_5346_;
v_wantsRebuild_5290_ = v_wantsRebuild_5347_;
v_buildTime_5291_ = v_buildTime_5348_;
goto v___jp_5286_;
}
}
}
v___jp_5349_:
{
if (lean_obj_tag(v___y_5350_) == 0)
{
lean_object* v_a_5351_; lean_object* v_a_5352_; 
v_a_5351_ = lean_ctor_get(v___y_5350_, 0);
lean_inc(v_a_5351_);
v_a_5352_ = lean_ctor_get(v___y_5350_, 1);
lean_inc(v_a_5352_);
lean_dec_ref(v___y_5350_);
v_a_5319_ = v_a_5351_;
v_a_5320_ = v_a_5352_;
goto v___jp_5318_;
}
else
{
lean_dec(v_wsIdx_5316_);
lean_dec_ref(v___x_5268_);
lean_del_object(v___x_5265_);
return v___y_5350_;
}
}
v___jp_5355_:
{
lean_object* v___x_5358_; 
lean_inc_ref(v_a_5252_);
lean_inc_ref(v___x_5268_);
lean_inc_ref(v_file_5245_);
lean_inc(v_val_5300_);
v___x_5358_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_5250_, v_hash_5301_, v_val_5300_, v_file_5245_, v___x_5268_, v_a_5298_, v___y_5356_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5357_);
if (lean_obj_tag(v___x_5358_) == 0)
{
lean_object* v_a_5359_; 
v_a_5359_ = lean_ctor_get(v___x_5358_, 0);
lean_inc(v_a_5359_);
if (lean_obj_tag(v_a_5359_) == 1)
{
lean_object* v_a_5360_; lean_object* v_val_5361_; 
lean_dec_ref(v_a_5253_);
lean_dec_ref(v_trace_5262_);
lean_dec_ref(v_a_5252_);
lean_dec_ref(v_ext_5248_);
lean_dec_ref(v_build_5246_);
lean_dec_ref(v_file_5245_);
v_a_5360_ = lean_ctor_get(v___x_5358_, 1);
lean_inc(v_a_5360_);
lean_dec_ref(v___x_5358_);
v_val_5361_ = lean_ctor_get(v_a_5359_, 0);
lean_inc(v_val_5361_);
lean_dec_ref(v_a_5359_);
v_a_5319_ = v_val_5361_;
v_a_5320_ = v_a_5360_;
goto v___jp_5318_;
}
else
{
lean_object* v_a_5362_; lean_object* v___x_5363_; 
lean_dec(v_a_5359_);
v_a_5362_ = lean_ctor_get(v___x_5358_, 1);
lean_inc(v_a_5362_);
lean_dec_ref(v___x_5358_);
lean_inc_ref(v___x_5268_);
v___x_5363_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5245_, v_build_5246_, v_text_5247_, v_ext_5248_, v_trace_5262_, v___x_5268_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5362_);
lean_dec_ref(v_a_5253_);
lean_dec_ref(v_trace_5262_);
v___y_5350_ = v___x_5363_;
goto v___jp_5349_;
}
}
else
{
lean_object* v_a_5364_; lean_object* v_a_5365_; lean_object* v___x_5367_; uint8_t v_isShared_5368_; uint8_t v_isSharedCheck_5372_; 
lean_dec(v_wsIdx_5316_);
lean_dec_ref(v_a_5253_);
lean_dec_ref(v___x_5268_);
lean_del_object(v___x_5265_);
lean_dec_ref(v_trace_5262_);
lean_dec_ref(v_a_5252_);
lean_dec_ref(v_ext_5248_);
lean_dec_ref(v_build_5246_);
lean_dec_ref(v_file_5245_);
v_a_5364_ = lean_ctor_get(v___x_5358_, 0);
v_a_5365_ = lean_ctor_get(v___x_5358_, 1);
v_isSharedCheck_5372_ = !lean_is_exclusive(v___x_5358_);
if (v_isSharedCheck_5372_ == 0)
{
v___x_5367_ = v___x_5358_;
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
else
{
lean_inc(v_a_5365_);
lean_inc(v_a_5364_);
lean_dec(v___x_5358_);
v___x_5367_ = lean_box(0);
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
v_resetjp_5366_:
{
lean_object* v___x_5370_; 
if (v_isShared_5368_ == 0)
{
v___x_5370_ = v___x_5367_;
goto v_reusejp_5369_;
}
else
{
lean_object* v_reuseFailAlloc_5371_; 
v_reuseFailAlloc_5371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5371_, 0, v_a_5364_);
lean_ctor_set(v_reuseFailAlloc_5371_, 1, v_a_5365_);
v___x_5370_ = v_reuseFailAlloc_5371_;
goto v_reusejp_5369_;
}
v_reusejp_5369_:
{
return v___x_5370_;
}
}
}
}
v___jp_5373_:
{
if (v_a_5375_ == 0)
{
lean_object* v___x_5377_; 
lean_dec(v_a_5298_);
lean_inc_ref(v___x_5268_);
v___x_5377_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5245_, v_build_5246_, v_text_5247_, v_ext_5248_, v_trace_5262_, v___x_5268_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5376_);
lean_dec_ref(v_a_5253_);
lean_dec_ref(v_trace_5262_);
v___y_5350_ = v___x_5377_;
goto v___jp_5349_;
}
else
{
v___y_5356_ = v___y_5374_;
v_a_5357_ = v_a_5376_;
goto v___jp_5355_;
}
}
v___jp_5378_:
{
lean_object* v___x_5380_; 
lean_inc(v_a_5298_);
v___x_5380_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5252_, v_file_5245_, v_trace_5262_, v_a_5298_, v_mtime_5302_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5379_);
if (lean_obj_tag(v___x_5380_) == 0)
{
lean_object* v_a_5381_; lean_object* v_a_5382_; uint8_t v___x_5383_; uint8_t v___x_5384_; uint8_t v___x_5385_; 
v_a_5381_ = lean_ctor_get(v___x_5380_, 0);
lean_inc(v_a_5381_);
v_a_5382_ = lean_ctor_get(v___x_5380_, 1);
lean_inc(v_a_5382_);
lean_dec_ref(v___x_5380_);
v___x_5383_ = 0;
v___x_5384_ = lean_unbox(v_a_5381_);
lean_dec(v_a_5381_);
v___x_5385_ = l_Lake_instDecidableEqOutputStatus(v___x_5384_, v___x_5383_);
if (v___x_5385_ == 0)
{
lean_object* v___x_5386_; 
lean_dec_ref(v_a_5253_);
lean_dec(v_a_5298_);
lean_dec_ref(v_trace_5262_);
lean_dec_ref(v_a_5252_);
lean_dec_ref(v_build_5246_);
v___x_5386_ = l_Lake_computeArtifact___redArg(v_file_5245_, v_ext_5248_, v_text_5247_, v_a_5256_, v_a_5382_);
v___y_5350_ = v___x_5386_;
goto v___jp_5349_;
}
else
{
if (lean_obj_tag(v_enableArtifactCache_x3f_5353_) == 0)
{
lean_object* v_toContext_5387_; lean_object* v_lakeEnv_5388_; lean_object* v_enableArtifactCache_x3f_5389_; 
v_toContext_5387_ = lean_ctor_get(v_a_5256_, 1);
v_lakeEnv_5388_ = lean_ctor_get(v_toContext_5387_, 1);
v_enableArtifactCache_x3f_5389_ = lean_ctor_get(v_lakeEnv_5388_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_5389_) == 0)
{
lean_object* v_root_5390_; lean_object* v_config_5391_; lean_object* v_enableArtifactCache_x3f_5392_; 
v_root_5390_ = lean_ctor_get(v_toContext_5387_, 0);
v_config_5391_ = lean_ctor_get(v_root_5390_, 6);
v_enableArtifactCache_x3f_5392_ = lean_ctor_get(v_config_5391_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_5392_) == 0)
{
v___y_5356_ = v___x_5385_;
v_a_5357_ = v_a_5382_;
goto v___jp_5355_;
}
else
{
lean_object* v_val_5393_; uint8_t v___x_5394_; 
v_val_5393_ = lean_ctor_get(v_enableArtifactCache_x3f_5392_, 0);
v___x_5394_ = lean_unbox(v_val_5393_);
v___y_5374_ = v___x_5385_;
v_a_5375_ = v___x_5394_;
v_a_5376_ = v_a_5382_;
goto v___jp_5373_;
}
}
else
{
lean_object* v_val_5395_; uint8_t v___x_5396_; 
v_val_5395_ = lean_ctor_get(v_enableArtifactCache_x3f_5389_, 0);
v___x_5396_ = lean_unbox(v_val_5395_);
v___y_5374_ = v___x_5385_;
v_a_5375_ = v___x_5396_;
v_a_5376_ = v_a_5382_;
goto v___jp_5373_;
}
}
else
{
lean_object* v_val_5397_; uint8_t v___x_5398_; 
v_val_5397_ = lean_ctor_get(v_enableArtifactCache_x3f_5353_, 0);
v___x_5398_ = lean_unbox(v_val_5397_);
v___y_5374_ = v___x_5385_;
v_a_5375_ = v___x_5398_;
v_a_5376_ = v_a_5382_;
goto v___jp_5373_;
}
}
}
else
{
lean_object* v_a_5399_; lean_object* v_a_5400_; lean_object* v___x_5402_; uint8_t v_isShared_5403_; uint8_t v_isSharedCheck_5407_; 
lean_dec(v_wsIdx_5316_);
lean_dec_ref(v_a_5253_);
lean_dec(v_a_5298_);
lean_dec_ref(v___x_5268_);
lean_del_object(v___x_5265_);
lean_dec_ref(v_trace_5262_);
lean_dec_ref(v_a_5252_);
lean_dec_ref(v_ext_5248_);
lean_dec_ref(v_build_5246_);
lean_dec_ref(v_file_5245_);
v_a_5399_ = lean_ctor_get(v___x_5380_, 0);
v_a_5400_ = lean_ctor_get(v___x_5380_, 1);
v_isSharedCheck_5407_ = !lean_is_exclusive(v___x_5380_);
if (v_isSharedCheck_5407_ == 0)
{
v___x_5402_ = v___x_5380_;
v_isShared_5403_ = v_isSharedCheck_5407_;
goto v_resetjp_5401_;
}
else
{
lean_inc(v_a_5400_);
lean_inc(v_a_5399_);
lean_dec(v___x_5380_);
v___x_5402_ = lean_box(0);
v_isShared_5403_ = v_isSharedCheck_5407_;
goto v_resetjp_5401_;
}
v_resetjp_5401_:
{
lean_object* v___x_5405_; 
if (v_isShared_5403_ == 0)
{
v___x_5405_ = v___x_5402_;
goto v_reusejp_5404_;
}
else
{
lean_object* v_reuseFailAlloc_5406_; 
v_reuseFailAlloc_5406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5406_, 0, v_a_5399_);
lean_ctor_set(v_reuseFailAlloc_5406_, 1, v_a_5400_);
v___x_5405_ = v_reuseFailAlloc_5406_;
goto v_reusejp_5404_;
}
v_reusejp_5404_:
{
return v___x_5405_;
}
}
}
}
v___jp_5408_:
{
lean_object* v___x_5411_; 
lean_inc_ref(v_a_5252_);
lean_inc(v_a_5298_);
lean_inc_ref(v___x_5268_);
lean_inc_ref(v_file_5245_);
lean_inc(v_val_5300_);
v___x_5411_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_5250_, v_hash_5301_, v_val_5300_, v_file_5245_, v___x_5268_, v_a_5298_, v___y_5410_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v___y_5409_);
if (lean_obj_tag(v___x_5411_) == 0)
{
lean_object* v_a_5412_; 
v_a_5412_ = lean_ctor_get(v___x_5411_, 0);
lean_inc(v_a_5412_);
if (lean_obj_tag(v_a_5412_) == 1)
{
lean_object* v_a_5413_; lean_object* v_val_5414_; 
lean_dec(v_val_5300_);
lean_dec(v_a_5298_);
lean_dec_ref(v_a_5253_);
lean_dec_ref(v_trace_5262_);
lean_dec_ref(v_a_5252_);
lean_dec_ref(v_ext_5248_);
lean_dec_ref(v_build_5246_);
lean_dec_ref(v_file_5245_);
v_a_5413_ = lean_ctor_get(v___x_5411_, 1);
lean_inc(v_a_5413_);
lean_dec_ref(v___x_5411_);
v_val_5414_ = lean_ctor_get(v_a_5412_, 0);
lean_inc(v_val_5414_);
lean_dec_ref(v_a_5412_);
v_a_5319_ = v_val_5414_;
v_a_5320_ = v_a_5413_;
goto v___jp_5318_;
}
else
{
lean_object* v_a_5415_; lean_object* v___x_5416_; 
lean_dec(v_a_5412_);
v_a_5415_ = lean_ctor_get(v___x_5411_, 1);
lean_inc(v_a_5415_);
lean_dec_ref(v___x_5411_);
v___x_5416_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5252_, v_file_5245_, v_trace_5262_, v_a_5298_, v_mtime_5302_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5415_);
if (lean_obj_tag(v___x_5416_) == 0)
{
lean_object* v_a_5417_; lean_object* v_a_5418_; uint8_t v___x_5419_; uint8_t v___x_5420_; uint8_t v___x_5421_; 
v_a_5417_ = lean_ctor_get(v___x_5416_, 0);
lean_inc(v_a_5417_);
v_a_5418_ = lean_ctor_get(v___x_5416_, 1);
lean_inc(v_a_5418_);
lean_dec_ref(v___x_5416_);
v___x_5419_ = 0;
v___x_5420_ = lean_unbox(v_a_5417_);
v___x_5421_ = l_Lake_instDecidableEqOutputStatus(v___x_5420_, v___x_5419_);
if (v___x_5421_ == 0)
{
lean_object* v___x_5422_; uint8_t v___x_5423_; lean_object* v___x_5424_; 
lean_dec_ref(v_trace_5262_);
lean_dec_ref(v_build_5246_);
v___x_5422_ = lean_box(0);
v___x_5423_ = lean_unbox(v_a_5417_);
lean_dec(v_a_5417_);
lean_inc_ref(v_a_5256_);
v___x_5424_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v___x_5423_, v_file_5245_, v_ext_5248_, v_text_5247_, v_exe_5250_, v___y_5410_, v_val_5300_, v_hash_5301_, v___x_5422_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5418_);
lean_dec_ref(v_a_5253_);
lean_dec_ref(v_a_5252_);
v___y_5350_ = v___x_5424_;
goto v___jp_5349_;
}
else
{
lean_object* v___x_5425_; 
lean_inc_ref(v_a_5252_);
lean_inc_ref(v___x_5268_);
lean_inc_ref(v_ext_5248_);
lean_inc_ref(v_file_5245_);
v___x_5425_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5245_, v_build_5246_, v_text_5247_, v_ext_5248_, v_trace_5262_, v___x_5268_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5418_);
lean_dec_ref(v_trace_5262_);
if (lean_obj_tag(v___x_5425_) == 0)
{
lean_object* v_a_5426_; lean_object* v___x_5427_; uint8_t v___x_5428_; lean_object* v___x_5429_; 
v_a_5426_ = lean_ctor_get(v___x_5425_, 1);
lean_inc(v_a_5426_);
lean_dec_ref(v___x_5425_);
v___x_5427_ = lean_box(0);
v___x_5428_ = lean_unbox(v_a_5417_);
lean_dec(v_a_5417_);
lean_inc_ref(v_a_5256_);
v___x_5429_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v___x_5428_, v_file_5245_, v_ext_5248_, v_text_5247_, v_exe_5250_, v___y_5410_, v_val_5300_, v_hash_5301_, v___x_5427_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5426_);
lean_dec_ref(v_a_5253_);
lean_dec_ref(v_a_5252_);
v___y_5350_ = v___x_5429_;
goto v___jp_5349_;
}
else
{
lean_dec(v_a_5417_);
lean_dec(v_wsIdx_5316_);
lean_dec(v_val_5300_);
lean_dec_ref(v_a_5253_);
lean_dec_ref(v___x_5268_);
lean_del_object(v___x_5265_);
lean_dec_ref(v_a_5252_);
lean_dec_ref(v_ext_5248_);
lean_dec_ref(v_file_5245_);
return v___x_5425_;
}
}
}
else
{
lean_object* v_a_5430_; lean_object* v_a_5431_; lean_object* v___x_5433_; uint8_t v_isShared_5434_; uint8_t v_isSharedCheck_5438_; 
lean_dec(v_wsIdx_5316_);
lean_dec(v_val_5300_);
lean_dec_ref(v_a_5253_);
lean_dec_ref(v___x_5268_);
lean_del_object(v___x_5265_);
lean_dec_ref(v_trace_5262_);
lean_dec_ref(v_a_5252_);
lean_dec_ref(v_ext_5248_);
lean_dec_ref(v_build_5246_);
lean_dec_ref(v_file_5245_);
v_a_5430_ = lean_ctor_get(v___x_5416_, 0);
v_a_5431_ = lean_ctor_get(v___x_5416_, 1);
v_isSharedCheck_5438_ = !lean_is_exclusive(v___x_5416_);
if (v_isSharedCheck_5438_ == 0)
{
v___x_5433_ = v___x_5416_;
v_isShared_5434_ = v_isSharedCheck_5438_;
goto v_resetjp_5432_;
}
else
{
lean_inc(v_a_5431_);
lean_inc(v_a_5430_);
lean_dec(v___x_5416_);
v___x_5433_ = lean_box(0);
v_isShared_5434_ = v_isSharedCheck_5438_;
goto v_resetjp_5432_;
}
v_resetjp_5432_:
{
lean_object* v___x_5436_; 
if (v_isShared_5434_ == 0)
{
v___x_5436_ = v___x_5433_;
goto v_reusejp_5435_;
}
else
{
lean_object* v_reuseFailAlloc_5437_; 
v_reuseFailAlloc_5437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5437_, 0, v_a_5430_);
lean_ctor_set(v_reuseFailAlloc_5437_, 1, v_a_5431_);
v___x_5436_ = v_reuseFailAlloc_5437_;
goto v_reusejp_5435_;
}
v_reusejp_5435_:
{
return v___x_5436_;
}
}
}
}
}
else
{
lean_object* v_a_5439_; lean_object* v_a_5440_; lean_object* v___x_5442_; uint8_t v_isShared_5443_; uint8_t v_isSharedCheck_5447_; 
lean_dec(v_wsIdx_5316_);
lean_dec(v_val_5300_);
lean_dec(v_a_5298_);
lean_dec_ref(v_a_5253_);
lean_dec_ref(v___x_5268_);
lean_del_object(v___x_5265_);
lean_dec_ref(v_trace_5262_);
lean_dec_ref(v_a_5252_);
lean_dec_ref(v_ext_5248_);
lean_dec_ref(v_build_5246_);
lean_dec_ref(v_file_5245_);
v_a_5439_ = lean_ctor_get(v___x_5411_, 0);
v_a_5440_ = lean_ctor_get(v___x_5411_, 1);
v_isSharedCheck_5447_ = !lean_is_exclusive(v___x_5411_);
if (v_isSharedCheck_5447_ == 0)
{
v___x_5442_ = v___x_5411_;
v_isShared_5443_ = v_isSharedCheck_5447_;
goto v_resetjp_5441_;
}
else
{
lean_inc(v_a_5440_);
lean_inc(v_a_5439_);
lean_dec(v___x_5411_);
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
v___jp_5448_:
{
if (v_restore_5249_ == 0)
{
v___y_5409_ = v_a_5451_;
v___y_5410_ = v_a_5450_;
goto v___jp_5408_;
}
else
{
v___y_5409_ = v_a_5451_;
v___y_5410_ = v___y_5449_;
goto v___jp_5408_;
}
}
v___jp_5452_:
{
if (v_a_5453_ == 0)
{
v_a_5379_ = v_a_5454_;
goto v___jp_5378_;
}
else
{
lean_inc(v_val_5300_);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5354_) == 0)
{
lean_object* v_toContext_5455_; lean_object* v_root_5456_; lean_object* v_config_5457_; lean_object* v_restoreAllArtifacts_x3f_5458_; 
v_toContext_5455_ = lean_ctor_get(v_a_5256_, 1);
v_root_5456_ = lean_ctor_get(v_toContext_5455_, 0);
v_config_5457_ = lean_ctor_get(v_root_5456_, 6);
v_restoreAllArtifacts_x3f_5458_ = lean_ctor_get(v_config_5457_, 25);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5458_) == 0)
{
uint8_t v___x_5459_; 
v___x_5459_ = 0;
v___y_5449_ = v_a_5453_;
v_a_5450_ = v___x_5459_;
v_a_5451_ = v_a_5454_;
goto v___jp_5448_;
}
else
{
lean_object* v_val_5460_; uint8_t v___x_5461_; 
v_val_5460_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5458_, 0);
v___x_5461_ = lean_unbox(v_val_5460_);
v___y_5449_ = v_a_5453_;
v_a_5450_ = v___x_5461_;
v_a_5451_ = v_a_5454_;
goto v___jp_5448_;
}
}
else
{
lean_object* v_val_5462_; uint8_t v___x_5463_; 
v_val_5462_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5354_, 0);
v___x_5463_ = lean_unbox(v_val_5462_);
v___y_5449_ = v_a_5453_;
v_a_5450_ = v___x_5463_;
v_a_5451_ = v_a_5454_;
goto v___jp_5448_;
}
}
}
}
else
{
lean_object* v_a_5477_; lean_object* v_a_5478_; lean_object* v_mtime_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; 
lean_del_object(v___x_5265_);
v_a_5477_ = lean_ctor_get(v___x_5297_, 0);
lean_inc(v_a_5477_);
v_a_5478_ = lean_ctor_get(v___x_5297_, 1);
lean_inc(v_a_5478_);
lean_dec_ref(v___x_5297_);
v_mtime_5479_ = lean_ctor_get(v_trace_5262_, 2);
lean_inc_ref(v_trace_5262_);
v___x_5480_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5480_, 0, v_a_5478_);
lean_ctor_set(v___x_5480_, 1, v_trace_5262_);
lean_ctor_set(v___x_5480_, 2, v_buildTime_5263_);
lean_ctor_set_uint8(v___x_5480_, sizeof(void*)*3, v_action_5260_);
lean_ctor_set_uint8(v___x_5480_, sizeof(void*)*3 + 1, v_wantsRebuild_5261_);
v___x_5481_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5252_, v_file_5245_, v_trace_5262_, v_a_5477_, v_mtime_5479_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v___x_5480_);
if (lean_obj_tag(v___x_5481_) == 0)
{
lean_object* v_a_5482_; lean_object* v_a_5483_; uint8_t v___x_5484_; uint8_t v___x_5485_; uint8_t v___x_5486_; 
v_a_5482_ = lean_ctor_get(v___x_5481_, 0);
lean_inc(v_a_5482_);
v_a_5483_ = lean_ctor_get(v___x_5481_, 1);
lean_inc(v_a_5483_);
lean_dec_ref(v___x_5481_);
v___x_5484_ = 0;
v___x_5485_ = lean_unbox(v_a_5482_);
lean_dec(v_a_5482_);
v___x_5486_ = l_Lake_instDecidableEqOutputStatus(v___x_5485_, v___x_5484_);
if (v___x_5486_ == 0)
{
lean_object* v___x_5487_; 
lean_dec_ref(v_trace_5262_);
lean_dec(v_a_5253_);
lean_dec_ref(v_a_5252_);
lean_dec_ref(v_build_5246_);
v___x_5487_ = l_Lake_computeArtifact___redArg(v_file_5245_, v_ext_5248_, v_text_5247_, v_a_5256_, v_a_5483_);
if (lean_obj_tag(v___x_5487_) == 0)
{
lean_object* v_a_5488_; lean_object* v_a_5489_; 
v_a_5488_ = lean_ctor_get(v___x_5487_, 0);
lean_inc(v_a_5488_);
v_a_5489_ = lean_ctor_get(v___x_5487_, 1);
lean_inc(v_a_5489_);
lean_dec_ref(v___x_5487_);
v_art_5270_ = v_a_5488_;
v___y_5271_ = v_a_5489_;
goto v___jp_5269_;
}
else
{
lean_dec_ref(v___x_5268_);
return v___x_5487_;
}
}
else
{
lean_object* v___x_5490_; 
lean_inc_ref(v___x_5268_);
v___x_5490_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5245_, v_build_5246_, v_text_5247_, v_ext_5248_, v_trace_5262_, v___x_5268_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5483_);
lean_dec(v_a_5253_);
lean_dec_ref(v_trace_5262_);
if (lean_obj_tag(v___x_5490_) == 0)
{
lean_object* v_a_5491_; lean_object* v_a_5492_; 
v_a_5491_ = lean_ctor_get(v___x_5490_, 0);
lean_inc(v_a_5491_);
v_a_5492_ = lean_ctor_get(v___x_5490_, 1);
lean_inc(v_a_5492_);
lean_dec_ref(v___x_5490_);
v_art_5270_ = v_a_5491_;
v___y_5271_ = v_a_5492_;
goto v___jp_5269_;
}
else
{
lean_dec_ref(v___x_5268_);
return v___x_5490_;
}
}
}
else
{
lean_object* v_a_5493_; lean_object* v_a_5494_; lean_object* v___x_5496_; uint8_t v_isShared_5497_; uint8_t v_isSharedCheck_5501_; 
lean_dec_ref(v___x_5268_);
lean_dec_ref(v_trace_5262_);
lean_dec(v_a_5253_);
lean_dec_ref(v_a_5252_);
lean_dec_ref(v_ext_5248_);
lean_dec_ref(v_build_5246_);
lean_dec_ref(v_file_5245_);
v_a_5493_ = lean_ctor_get(v___x_5481_, 0);
v_a_5494_ = lean_ctor_get(v___x_5481_, 1);
v_isSharedCheck_5501_ = !lean_is_exclusive(v___x_5481_);
if (v_isSharedCheck_5501_ == 0)
{
v___x_5496_ = v___x_5481_;
v_isShared_5497_ = v_isSharedCheck_5501_;
goto v_resetjp_5495_;
}
else
{
lean_inc(v_a_5494_);
lean_inc(v_a_5493_);
lean_dec(v___x_5481_);
v___x_5496_ = lean_box(0);
v_isShared_5497_ = v_isSharedCheck_5501_;
goto v_resetjp_5495_;
}
v_resetjp_5495_:
{
lean_object* v___x_5499_; 
if (v_isShared_5497_ == 0)
{
v___x_5499_ = v___x_5496_;
goto v_reusejp_5498_;
}
else
{
lean_object* v_reuseFailAlloc_5500_; 
v_reuseFailAlloc_5500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5500_, 0, v_a_5493_);
lean_ctor_set(v_reuseFailAlloc_5500_, 1, v_a_5494_);
v___x_5499_ = v_reuseFailAlloc_5500_;
goto v_reusejp_5498_;
}
v_reusejp_5498_:
{
return v___x_5499_;
}
}
}
}
}
else
{
lean_object* v_a_5502_; lean_object* v_a_5503_; lean_object* v___x_5505_; uint8_t v_isShared_5506_; uint8_t v_isSharedCheck_5511_; 
lean_dec_ref(v___x_5268_);
lean_del_object(v___x_5265_);
lean_dec(v_a_5253_);
lean_dec_ref(v_a_5252_);
lean_dec_ref(v_ext_5248_);
lean_dec_ref(v_build_5246_);
lean_dec_ref(v_file_5245_);
v_a_5502_ = lean_ctor_get(v___x_5297_, 0);
v_a_5503_ = lean_ctor_get(v___x_5297_, 1);
v_isSharedCheck_5511_ = !lean_is_exclusive(v___x_5297_);
if (v_isSharedCheck_5511_ == 0)
{
v___x_5505_ = v___x_5297_;
v_isShared_5506_ = v_isSharedCheck_5511_;
goto v_resetjp_5504_;
}
else
{
lean_inc(v_a_5503_);
lean_inc(v_a_5502_);
lean_dec(v___x_5297_);
v___x_5505_ = lean_box(0);
v_isShared_5506_ = v_isSharedCheck_5511_;
goto v_resetjp_5504_;
}
v_resetjp_5504_:
{
lean_object* v___x_5507_; lean_object* v___x_5509_; 
v___x_5507_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5507_, 0, v_a_5503_);
lean_ctor_set(v___x_5507_, 1, v_trace_5262_);
lean_ctor_set(v___x_5507_, 2, v_buildTime_5263_);
lean_ctor_set_uint8(v___x_5507_, sizeof(void*)*3, v_action_5260_);
lean_ctor_set_uint8(v___x_5507_, sizeof(void*)*3 + 1, v_wantsRebuild_5261_);
if (v_isShared_5506_ == 0)
{
lean_ctor_set(v___x_5505_, 1, v___x_5507_);
v___x_5509_ = v___x_5505_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5510_; 
v_reuseFailAlloc_5510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5510_, 0, v_a_5502_);
lean_ctor_set(v_reuseFailAlloc_5510_, 1, v___x_5507_);
v___x_5509_ = v_reuseFailAlloc_5510_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
return v___x_5509_;
}
}
}
v___jp_5269_:
{
lean_object* v_log_5272_; uint8_t v_action_5273_; uint8_t v_wantsRebuild_5274_; lean_object* v_buildTime_5275_; lean_object* v___x_5277_; uint8_t v_isShared_5278_; uint8_t v_isSharedCheck_5284_; 
v_log_5272_ = lean_ctor_get(v___y_5271_, 0);
v_action_5273_ = lean_ctor_get_uint8(v___y_5271_, sizeof(void*)*3);
v_wantsRebuild_5274_ = lean_ctor_get_uint8(v___y_5271_, sizeof(void*)*3 + 1);
v_buildTime_5275_ = lean_ctor_get(v___y_5271_, 2);
v_isSharedCheck_5284_ = !lean_is_exclusive(v___y_5271_);
if (v_isSharedCheck_5284_ == 0)
{
lean_object* v_unused_5285_; 
v_unused_5285_ = lean_ctor_get(v___y_5271_, 1);
lean_dec(v_unused_5285_);
v___x_5277_ = v___y_5271_;
v_isShared_5278_ = v_isSharedCheck_5284_;
goto v_resetjp_5276_;
}
else
{
lean_inc(v_buildTime_5275_);
lean_inc(v_log_5272_);
lean_dec(v___y_5271_);
v___x_5277_ = lean_box(0);
v_isShared_5278_ = v_isSharedCheck_5284_;
goto v_resetjp_5276_;
}
v_resetjp_5276_:
{
lean_object* v___x_5279_; lean_object* v___x_5281_; 
v___x_5279_ = l_Lake_Artifact_trace(v_art_5270_);
if (v_isShared_5278_ == 0)
{
lean_ctor_set(v___x_5277_, 1, v___x_5279_);
v___x_5281_ = v___x_5277_;
goto v_reusejp_5280_;
}
else
{
lean_object* v_reuseFailAlloc_5283_; 
v_reuseFailAlloc_5283_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5283_, 0, v_log_5272_);
lean_ctor_set(v_reuseFailAlloc_5283_, 1, v___x_5279_);
lean_ctor_set(v_reuseFailAlloc_5283_, 2, v_buildTime_5275_);
lean_ctor_set_uint8(v_reuseFailAlloc_5283_, sizeof(void*)*3, v_action_5273_);
lean_ctor_set_uint8(v_reuseFailAlloc_5283_, sizeof(void*)*3 + 1, v_wantsRebuild_5274_);
v___x_5281_ = v_reuseFailAlloc_5283_;
goto v_reusejp_5280_;
}
v_reusejp_5280_:
{
lean_object* v___x_5282_; 
v___x_5282_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_5270_, v___x_5268_, v___x_5281_);
lean_dec_ref(v___x_5268_);
return v___x_5282_;
}
}
}
v___jp_5286_:
{
lean_object* v___x_5292_; lean_object* v___x_5294_; 
v___x_5292_ = l_Lake_Artifact_trace(v___y_5287_);
if (v_isShared_5266_ == 0)
{
lean_ctor_set(v___x_5265_, 2, v_buildTime_5291_);
lean_ctor_set(v___x_5265_, 1, v___x_5292_);
lean_ctor_set(v___x_5265_, 0, v_log_5288_);
v___x_5294_ = v___x_5265_;
goto v_reusejp_5293_;
}
else
{
lean_object* v_reuseFailAlloc_5296_; 
v_reuseFailAlloc_5296_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5296_, 0, v_log_5288_);
lean_ctor_set(v_reuseFailAlloc_5296_, 1, v___x_5292_);
lean_ctor_set(v_reuseFailAlloc_5296_, 2, v_buildTime_5291_);
v___x_5294_ = v_reuseFailAlloc_5296_;
goto v_reusejp_5293_;
}
v_reusejp_5293_:
{
lean_object* v___x_5295_; 
lean_ctor_set_uint8(v___x_5294_, sizeof(void*)*3, v_action_5289_);
lean_ctor_set_uint8(v___x_5294_, sizeof(void*)*3 + 1, v_wantsRebuild_5290_);
v___x_5295_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v___y_5287_, v___x_5268_, v___x_5294_);
lean_dec_ref(v___x_5268_);
return v___x_5295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___boxed(lean_object* v_file_5513_, lean_object* v_build_5514_, lean_object* v_text_5515_, lean_object* v_ext_5516_, lean_object* v_restore_5517_, lean_object* v_exe_5518_, lean_object* v_platformIndependent_5519_, lean_object* v_a_5520_, lean_object* v_a_5521_, lean_object* v_a_5522_, lean_object* v_a_5523_, lean_object* v_a_5524_, lean_object* v_a_5525_, lean_object* v_a_5526_){
_start:
{
uint8_t v_text_boxed_5527_; uint8_t v_restore_boxed_5528_; uint8_t v_exe_boxed_5529_; uint8_t v_platformIndependent_boxed_5530_; lean_object* v_res_5531_; 
v_text_boxed_5527_ = lean_unbox(v_text_5515_);
v_restore_boxed_5528_ = lean_unbox(v_restore_5517_);
v_exe_boxed_5529_ = lean_unbox(v_exe_5518_);
v_platformIndependent_boxed_5530_ = lean_unbox(v_platformIndependent_5519_);
v_res_5531_ = l_Lake_buildArtifactUnlessUpToDate(v_file_5513_, v_build_5514_, v_text_boxed_5527_, v_ext_5516_, v_restore_boxed_5528_, v_exe_boxed_5529_, v_platformIndependent_boxed_5530_, v_a_5520_, v_a_5521_, v_a_5522_, v_a_5523_, v_a_5524_, v_a_5525_);
lean_dec_ref(v_a_5524_);
lean_dec(v_a_5523_);
lean_dec(v_a_5522_);
return v_res_5531_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0(lean_object* v_extraDepTrace_5533_, lean_object* v_build_5534_, lean_object* v_file_5535_, uint8_t v_text_5536_, lean_object* v_depInfo_5537_, lean_object* v___y_5538_, lean_object* v___y_5539_, lean_object* v___y_5540_, lean_object* v___y_5541_, lean_object* v___y_5542_, lean_object* v___y_5543_){
_start:
{
lean_object* v___x_5545_; 
lean_inc_ref(v___y_5542_);
lean_inc(v___y_5541_);
lean_inc(v___y_5540_);
lean_inc(v___y_5539_);
lean_inc_ref(v___y_5538_);
v___x_5545_ = lean_apply_7(v_extraDepTrace_5533_, v___y_5538_, v___y_5539_, v___y_5540_, v___y_5541_, v___y_5542_, v___y_5543_, lean_box(0));
if (lean_obj_tag(v___x_5545_) == 0)
{
lean_object* v_a_5546_; lean_object* v_a_5547_; lean_object* v_log_5548_; uint8_t v_action_5549_; uint8_t v_wantsRebuild_5550_; lean_object* v_trace_5551_; lean_object* v_buildTime_5552_; lean_object* v___x_5554_; uint8_t v_isShared_5555_; uint8_t v_isSharedCheck_5583_; 
v_a_5546_ = lean_ctor_get(v___x_5545_, 1);
lean_inc(v_a_5546_);
v_a_5547_ = lean_ctor_get(v___x_5545_, 0);
lean_inc(v_a_5547_);
lean_dec_ref(v___x_5545_);
v_log_5548_ = lean_ctor_get(v_a_5546_, 0);
v_action_5549_ = lean_ctor_get_uint8(v_a_5546_, sizeof(void*)*3);
v_wantsRebuild_5550_ = lean_ctor_get_uint8(v_a_5546_, sizeof(void*)*3 + 1);
v_trace_5551_ = lean_ctor_get(v_a_5546_, 1);
v_buildTime_5552_ = lean_ctor_get(v_a_5546_, 2);
v_isSharedCheck_5583_ = !lean_is_exclusive(v_a_5546_);
if (v_isSharedCheck_5583_ == 0)
{
v___x_5554_ = v_a_5546_;
v_isShared_5555_ = v_isSharedCheck_5583_;
goto v_resetjp_5553_;
}
else
{
lean_inc(v_buildTime_5552_);
lean_inc(v_trace_5551_);
lean_inc(v_log_5548_);
lean_dec(v_a_5546_);
v___x_5554_ = lean_box(0);
v_isShared_5555_ = v_isSharedCheck_5583_;
goto v_resetjp_5553_;
}
v_resetjp_5553_:
{
lean_object* v___x_5556_; lean_object* v___x_5558_; 
v___x_5556_ = l_Lake_BuildTrace_mix(v_trace_5551_, v_a_5547_);
if (v_isShared_5555_ == 0)
{
lean_ctor_set(v___x_5554_, 1, v___x_5556_);
v___x_5558_ = v___x_5554_;
goto v_reusejp_5557_;
}
else
{
lean_object* v_reuseFailAlloc_5582_; 
v_reuseFailAlloc_5582_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5582_, 0, v_log_5548_);
lean_ctor_set(v_reuseFailAlloc_5582_, 1, v___x_5556_);
lean_ctor_set(v_reuseFailAlloc_5582_, 2, v_buildTime_5552_);
lean_ctor_set_uint8(v_reuseFailAlloc_5582_, sizeof(void*)*3, v_action_5549_);
lean_ctor_set_uint8(v_reuseFailAlloc_5582_, sizeof(void*)*3 + 1, v_wantsRebuild_5550_);
v___x_5558_ = v_reuseFailAlloc_5582_;
goto v_reusejp_5557_;
}
v_reusejp_5557_:
{
lean_object* v___x_5559_; lean_object* v___x_5560_; uint8_t v___x_5561_; lean_object* v___x_5562_; 
v___x_5559_ = lean_apply_1(v_build_5534_, v_depInfo_5537_);
v___x_5560_ = ((lean_object*)(l_Lake_buildFileAfterDep___redArg___lam__0___closed__0));
v___x_5561_ = 0;
lean_inc(v___y_5539_);
v___x_5562_ = l_Lake_buildArtifactUnlessUpToDate(v_file_5535_, v___x_5559_, v_text_5536_, v___x_5560_, v___x_5561_, v___x_5561_, v___x_5561_, v___y_5538_, v___y_5539_, v___y_5540_, v___y_5541_, v___y_5542_, v___x_5558_);
if (lean_obj_tag(v___x_5562_) == 0)
{
lean_object* v_a_5563_; lean_object* v_a_5564_; lean_object* v___x_5566_; uint8_t v_isShared_5567_; uint8_t v_isSharedCheck_5572_; 
v_a_5563_ = lean_ctor_get(v___x_5562_, 0);
v_a_5564_ = lean_ctor_get(v___x_5562_, 1);
v_isSharedCheck_5572_ = !lean_is_exclusive(v___x_5562_);
if (v_isSharedCheck_5572_ == 0)
{
v___x_5566_ = v___x_5562_;
v_isShared_5567_ = v_isSharedCheck_5572_;
goto v_resetjp_5565_;
}
else
{
lean_inc(v_a_5564_);
lean_inc(v_a_5563_);
lean_dec(v___x_5562_);
v___x_5566_ = lean_box(0);
v_isShared_5567_ = v_isSharedCheck_5572_;
goto v_resetjp_5565_;
}
v_resetjp_5565_:
{
lean_object* v_path_5568_; lean_object* v___x_5570_; 
v_path_5568_ = lean_ctor_get(v_a_5563_, 1);
lean_inc_ref(v_path_5568_);
lean_dec(v_a_5563_);
if (v_isShared_5567_ == 0)
{
lean_ctor_set(v___x_5566_, 0, v_path_5568_);
v___x_5570_ = v___x_5566_;
goto v_reusejp_5569_;
}
else
{
lean_object* v_reuseFailAlloc_5571_; 
v_reuseFailAlloc_5571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5571_, 0, v_path_5568_);
lean_ctor_set(v_reuseFailAlloc_5571_, 1, v_a_5564_);
v___x_5570_ = v_reuseFailAlloc_5571_;
goto v_reusejp_5569_;
}
v_reusejp_5569_:
{
return v___x_5570_;
}
}
}
else
{
lean_object* v_a_5573_; lean_object* v_a_5574_; lean_object* v___x_5576_; uint8_t v_isShared_5577_; uint8_t v_isSharedCheck_5581_; 
v_a_5573_ = lean_ctor_get(v___x_5562_, 0);
v_a_5574_ = lean_ctor_get(v___x_5562_, 1);
v_isSharedCheck_5581_ = !lean_is_exclusive(v___x_5562_);
if (v_isSharedCheck_5581_ == 0)
{
v___x_5576_ = v___x_5562_;
v_isShared_5577_ = v_isSharedCheck_5581_;
goto v_resetjp_5575_;
}
else
{
lean_inc(v_a_5574_);
lean_inc(v_a_5573_);
lean_dec(v___x_5562_);
v___x_5576_ = lean_box(0);
v_isShared_5577_ = v_isSharedCheck_5581_;
goto v_resetjp_5575_;
}
v_resetjp_5575_:
{
lean_object* v___x_5579_; 
if (v_isShared_5577_ == 0)
{
v___x_5579_ = v___x_5576_;
goto v_reusejp_5578_;
}
else
{
lean_object* v_reuseFailAlloc_5580_; 
v_reuseFailAlloc_5580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5580_, 0, v_a_5573_);
lean_ctor_set(v_reuseFailAlloc_5580_, 1, v_a_5574_);
v___x_5579_ = v_reuseFailAlloc_5580_;
goto v_reusejp_5578_;
}
v_reusejp_5578_:
{
return v___x_5579_;
}
}
}
}
}
}
else
{
lean_object* v_a_5584_; lean_object* v_a_5585_; lean_object* v___x_5587_; uint8_t v_isShared_5588_; uint8_t v_isSharedCheck_5592_; 
lean_dec_ref(v___y_5538_);
lean_dec(v_depInfo_5537_);
lean_dec_ref(v_file_5535_);
lean_dec_ref(v_build_5534_);
v_a_5584_ = lean_ctor_get(v___x_5545_, 0);
v_a_5585_ = lean_ctor_get(v___x_5545_, 1);
v_isSharedCheck_5592_ = !lean_is_exclusive(v___x_5545_);
if (v_isSharedCheck_5592_ == 0)
{
v___x_5587_ = v___x_5545_;
v_isShared_5588_ = v_isSharedCheck_5592_;
goto v_resetjp_5586_;
}
else
{
lean_inc(v_a_5585_);
lean_inc(v_a_5584_);
lean_dec(v___x_5545_);
v___x_5587_ = lean_box(0);
v_isShared_5588_ = v_isSharedCheck_5592_;
goto v_resetjp_5586_;
}
v_resetjp_5586_:
{
lean_object* v___x_5590_; 
if (v_isShared_5588_ == 0)
{
v___x_5590_ = v___x_5587_;
goto v_reusejp_5589_;
}
else
{
lean_object* v_reuseFailAlloc_5591_; 
v_reuseFailAlloc_5591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5591_, 0, v_a_5584_);
lean_ctor_set(v_reuseFailAlloc_5591_, 1, v_a_5585_);
v___x_5590_ = v_reuseFailAlloc_5591_;
goto v_reusejp_5589_;
}
v_reusejp_5589_:
{
return v___x_5590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___boxed(lean_object* v_extraDepTrace_5593_, lean_object* v_build_5594_, lean_object* v_file_5595_, lean_object* v_text_5596_, lean_object* v_depInfo_5597_, lean_object* v___y_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_){
_start:
{
uint8_t v_text_boxed_5605_; lean_object* v_res_5606_; 
v_text_boxed_5605_ = lean_unbox(v_text_5596_);
v_res_5606_ = l_Lake_buildFileAfterDep___redArg___lam__0(v_extraDepTrace_5593_, v_build_5594_, v_file_5595_, v_text_boxed_5605_, v_depInfo_5597_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_);
lean_dec_ref(v___y_5602_);
lean_dec(v___y_5601_);
lean_dec(v___y_5600_);
lean_dec(v___y_5599_);
return v_res_5606_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg(lean_object* v_file_5607_, lean_object* v_dep_5608_, lean_object* v_build_5609_, lean_object* v_extraDepTrace_5610_, uint8_t v_text_5611_, lean_object* v_a_5612_, lean_object* v_a_5613_, lean_object* v_a_5614_, lean_object* v_a_5615_, lean_object* v_a_5616_, lean_object* v_a_5617_){
_start:
{
lean_object* v___x_5619_; lean_object* v___f_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; uint8_t v___x_5623_; lean_object* v___x_5624_; 
v___x_5619_ = lean_box(v_text_5611_);
v___f_5620_ = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_5620_, 0, v_extraDepTrace_5610_);
lean_closure_set(v___f_5620_, 1, v_build_5609_);
lean_closure_set(v___f_5620_, 2, v_file_5607_);
lean_closure_set(v___f_5620_, 3, v___x_5619_);
v___x_5621_ = l_Lake_instDataKindFilePath;
v___x_5622_ = lean_unsigned_to_nat(0u);
v___x_5623_ = 0;
v___x_5624_ = l_Lake_Job_mapM___redArg(v___x_5621_, v_dep_5608_, v___f_5620_, v___x_5622_, v___x_5623_, v_a_5612_, v_a_5613_, v_a_5614_, v_a_5615_, v_a_5616_, v_a_5617_);
return v___x_5624_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___boxed(lean_object* v_file_5625_, lean_object* v_dep_5626_, lean_object* v_build_5627_, lean_object* v_extraDepTrace_5628_, lean_object* v_text_5629_, lean_object* v_a_5630_, lean_object* v_a_5631_, lean_object* v_a_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_){
_start:
{
uint8_t v_text_boxed_5637_; lean_object* v_res_5638_; 
v_text_boxed_5637_ = lean_unbox(v_text_5629_);
v_res_5638_ = l_Lake_buildFileAfterDep___redArg(v_file_5625_, v_dep_5626_, v_build_5627_, v_extraDepTrace_5628_, v_text_boxed_5637_, v_a_5630_, v_a_5631_, v_a_5632_, v_a_5633_, v_a_5634_, v_a_5635_);
lean_dec_ref(v_a_5635_);
lean_dec_ref(v_a_5634_);
lean_dec(v_a_5633_);
lean_dec(v_a_5632_);
lean_dec(v_a_5631_);
return v_res_5638_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object* v_00_u03b1_5639_, lean_object* v_file_5640_, lean_object* v_dep_5641_, lean_object* v_build_5642_, lean_object* v_extraDepTrace_5643_, uint8_t v_text_5644_, lean_object* v_a_5645_, lean_object* v_a_5646_, lean_object* v_a_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_){
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
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___boxed(lean_object* v_00_u03b1_5658_, lean_object* v_file_5659_, lean_object* v_dep_5660_, lean_object* v_build_5661_, lean_object* v_extraDepTrace_5662_, lean_object* v_text_5663_, lean_object* v_a_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_, lean_object* v_a_5668_, lean_object* v_a_5669_, lean_object* v_a_5670_){
_start:
{
uint8_t v_text_boxed_5671_; lean_object* v_res_5672_; 
v_text_boxed_5671_ = lean_unbox(v_text_5663_);
v_res_5672_ = l_Lake_buildFileAfterDep(v_00_u03b1_5658_, v_file_5659_, v_dep_5660_, v_build_5661_, v_extraDepTrace_5662_, v_text_boxed_5671_, v_a_5664_, v_a_5665_, v_a_5666_, v_a_5667_, v_a_5668_, v_a_5669_);
lean_dec_ref(v_a_5669_);
lean_dec_ref(v_a_5668_);
lean_dec(v_a_5667_);
lean_dec(v_a_5666_);
lean_dec(v_a_5665_);
return v_res_5672_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(lean_object* v_info_5673_){
_start:
{
lean_object* v___x_5675_; 
v___x_5675_ = l_Lake_computeBinFileHash(v_info_5673_);
if (lean_obj_tag(v___x_5675_) == 0)
{
lean_object* v_a_5676_; lean_object* v___x_5677_; 
v_a_5676_ = lean_ctor_get(v___x_5675_, 0);
lean_inc(v_a_5676_);
lean_dec_ref(v___x_5675_);
v___x_5677_ = lean_io_metadata(v_info_5673_);
if (lean_obj_tag(v___x_5677_) == 0)
{
lean_object* v_a_5678_; lean_object* v___x_5680_; uint8_t v_isShared_5681_; uint8_t v_isSharedCheck_5689_; 
v_a_5678_ = lean_ctor_get(v___x_5677_, 0);
v_isSharedCheck_5689_ = !lean_is_exclusive(v___x_5677_);
if (v_isSharedCheck_5689_ == 0)
{
v___x_5680_ = v___x_5677_;
v_isShared_5681_ = v_isSharedCheck_5689_;
goto v_resetjp_5679_;
}
else
{
lean_inc(v_a_5678_);
lean_dec(v___x_5677_);
v___x_5680_ = lean_box(0);
v_isShared_5681_ = v_isSharedCheck_5689_;
goto v_resetjp_5679_;
}
v_resetjp_5679_:
{
lean_object* v_modified_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; uint64_t v___x_5685_; lean_object* v___x_5687_; 
v_modified_5682_ = lean_ctor_get(v_a_5678_, 1);
lean_inc_ref(v_modified_5682_);
lean_dec(v_a_5678_);
v___x_5683_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_5684_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_5684_, 0, v_info_5673_);
lean_ctor_set(v___x_5684_, 1, v___x_5683_);
lean_ctor_set(v___x_5684_, 2, v_modified_5682_);
v___x_5685_ = lean_unbox_uint64(v_a_5676_);
lean_dec(v_a_5676_);
lean_ctor_set_uint64(v___x_5684_, sizeof(void*)*3, v___x_5685_);
if (v_isShared_5681_ == 0)
{
lean_ctor_set(v___x_5680_, 0, v___x_5684_);
v___x_5687_ = v___x_5680_;
goto v_reusejp_5686_;
}
else
{
lean_object* v_reuseFailAlloc_5688_; 
v_reuseFailAlloc_5688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5688_, 0, v___x_5684_);
v___x_5687_ = v_reuseFailAlloc_5688_;
goto v_reusejp_5686_;
}
v_reusejp_5686_:
{
return v___x_5687_;
}
}
}
else
{
lean_object* v_a_5690_; lean_object* v___x_5692_; uint8_t v_isShared_5693_; uint8_t v_isSharedCheck_5697_; 
lean_dec(v_a_5676_);
lean_dec_ref(v_info_5673_);
v_a_5690_ = lean_ctor_get(v___x_5677_, 0);
v_isSharedCheck_5697_ = !lean_is_exclusive(v___x_5677_);
if (v_isSharedCheck_5697_ == 0)
{
v___x_5692_ = v___x_5677_;
v_isShared_5693_ = v_isSharedCheck_5697_;
goto v_resetjp_5691_;
}
else
{
lean_inc(v_a_5690_);
lean_dec(v___x_5677_);
v___x_5692_ = lean_box(0);
v_isShared_5693_ = v_isSharedCheck_5697_;
goto v_resetjp_5691_;
}
v_resetjp_5691_:
{
lean_object* v___x_5695_; 
if (v_isShared_5693_ == 0)
{
v___x_5695_ = v___x_5692_;
goto v_reusejp_5694_;
}
else
{
lean_object* v_reuseFailAlloc_5696_; 
v_reuseFailAlloc_5696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5696_, 0, v_a_5690_);
v___x_5695_ = v_reuseFailAlloc_5696_;
goto v_reusejp_5694_;
}
v_reusejp_5694_:
{
return v___x_5695_;
}
}
}
}
else
{
lean_object* v_a_5698_; lean_object* v___x_5700_; uint8_t v_isShared_5701_; uint8_t v_isSharedCheck_5705_; 
lean_dec_ref(v_info_5673_);
v_a_5698_ = lean_ctor_get(v___x_5675_, 0);
v_isSharedCheck_5705_ = !lean_is_exclusive(v___x_5675_);
if (v_isSharedCheck_5705_ == 0)
{
v___x_5700_ = v___x_5675_;
v_isShared_5701_ = v_isSharedCheck_5705_;
goto v_resetjp_5699_;
}
else
{
lean_inc(v_a_5698_);
lean_dec(v___x_5675_);
v___x_5700_ = lean_box(0);
v_isShared_5701_ = v_isSharedCheck_5705_;
goto v_resetjp_5699_;
}
v_resetjp_5699_:
{
lean_object* v___x_5703_; 
if (v_isShared_5701_ == 0)
{
v___x_5703_ = v___x_5700_;
goto v_reusejp_5702_;
}
else
{
lean_object* v_reuseFailAlloc_5704_; 
v_reuseFailAlloc_5704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5704_, 0, v_a_5698_);
v___x_5703_ = v_reuseFailAlloc_5704_;
goto v_reusejp_5702_;
}
v_reusejp_5702_:
{
return v___x_5703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0___boxed(lean_object* v_info_5706_, lean_object* v_a_5707_){
_start:
{
lean_object* v_res_5708_; 
v_res_5708_ = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(v_info_5706_);
return v_res_5708_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0(lean_object* v_path_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_, lean_object* v___y_5715_){
_start:
{
lean_object* v_log_5717_; uint8_t v_action_5718_; uint8_t v_wantsRebuild_5719_; lean_object* v_trace_5720_; lean_object* v_buildTime_5721_; lean_object* v___x_5723_; uint8_t v_isShared_5724_; uint8_t v_isSharedCheck_5741_; 
v_log_5717_ = lean_ctor_get(v___y_5715_, 0);
v_action_5718_ = lean_ctor_get_uint8(v___y_5715_, sizeof(void*)*3);
v_wantsRebuild_5719_ = lean_ctor_get_uint8(v___y_5715_, sizeof(void*)*3 + 1);
v_trace_5720_ = lean_ctor_get(v___y_5715_, 1);
v_buildTime_5721_ = lean_ctor_get(v___y_5715_, 2);
v_isSharedCheck_5741_ = !lean_is_exclusive(v___y_5715_);
if (v_isSharedCheck_5741_ == 0)
{
v___x_5723_ = v___y_5715_;
v_isShared_5724_ = v_isSharedCheck_5741_;
goto v_resetjp_5722_;
}
else
{
lean_inc(v_buildTime_5721_);
lean_inc(v_trace_5720_);
lean_inc(v_log_5717_);
lean_dec(v___y_5715_);
v___x_5723_ = lean_box(0);
v_isShared_5724_ = v_isSharedCheck_5741_;
goto v_resetjp_5722_;
}
v_resetjp_5722_:
{
lean_object* v___x_5725_; 
lean_inc_ref(v_path_5709_);
v___x_5725_ = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(v_path_5709_);
if (lean_obj_tag(v___x_5725_) == 0)
{
lean_object* v_a_5726_; lean_object* v___x_5728_; 
lean_dec_ref(v_trace_5720_);
v_a_5726_ = lean_ctor_get(v___x_5725_, 0);
lean_inc(v_a_5726_);
lean_dec_ref(v___x_5725_);
if (v_isShared_5724_ == 0)
{
lean_ctor_set(v___x_5723_, 1, v_a_5726_);
v___x_5728_ = v___x_5723_;
goto v_reusejp_5727_;
}
else
{
lean_object* v_reuseFailAlloc_5730_; 
v_reuseFailAlloc_5730_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5730_, 0, v_log_5717_);
lean_ctor_set(v_reuseFailAlloc_5730_, 1, v_a_5726_);
lean_ctor_set(v_reuseFailAlloc_5730_, 2, v_buildTime_5721_);
lean_ctor_set_uint8(v_reuseFailAlloc_5730_, sizeof(void*)*3, v_action_5718_);
lean_ctor_set_uint8(v_reuseFailAlloc_5730_, sizeof(void*)*3 + 1, v_wantsRebuild_5719_);
v___x_5728_ = v_reuseFailAlloc_5730_;
goto v_reusejp_5727_;
}
v_reusejp_5727_:
{
lean_object* v___x_5729_; 
v___x_5729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5729_, 0, v_path_5709_);
lean_ctor_set(v___x_5729_, 1, v___x_5728_);
return v___x_5729_;
}
}
else
{
lean_object* v_a_5731_; lean_object* v___x_5732_; uint8_t v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5738_; 
lean_dec_ref(v_path_5709_);
v_a_5731_ = lean_ctor_get(v___x_5725_, 0);
lean_inc(v_a_5731_);
lean_dec_ref(v___x_5725_);
v___x_5732_ = lean_io_error_to_string(v_a_5731_);
v___x_5733_ = 3;
v___x_5734_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5734_, 0, v___x_5732_);
lean_ctor_set_uint8(v___x_5734_, sizeof(void*)*1, v___x_5733_);
v___x_5735_ = lean_array_get_size(v_log_5717_);
v___x_5736_ = lean_array_push(v_log_5717_, v___x_5734_);
if (v_isShared_5724_ == 0)
{
lean_ctor_set(v___x_5723_, 0, v___x_5736_);
v___x_5738_ = v___x_5723_;
goto v_reusejp_5737_;
}
else
{
lean_object* v_reuseFailAlloc_5740_; 
v_reuseFailAlloc_5740_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5740_, 0, v___x_5736_);
lean_ctor_set(v_reuseFailAlloc_5740_, 1, v_trace_5720_);
lean_ctor_set(v_reuseFailAlloc_5740_, 2, v_buildTime_5721_);
lean_ctor_set_uint8(v_reuseFailAlloc_5740_, sizeof(void*)*3, v_action_5718_);
lean_ctor_set_uint8(v_reuseFailAlloc_5740_, sizeof(void*)*3 + 1, v_wantsRebuild_5719_);
v___x_5738_ = v_reuseFailAlloc_5740_;
goto v_reusejp_5737_;
}
v_reusejp_5737_:
{
lean_object* v___x_5739_; 
v___x_5739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5739_, 0, v___x_5735_);
lean_ctor_set(v___x_5739_, 1, v___x_5738_);
return v___x_5739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0___boxed(lean_object* v_path_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_, lean_object* v___y_5745_, lean_object* v___y_5746_, lean_object* v___y_5747_, lean_object* v___y_5748_, lean_object* v___y_5749_){
_start:
{
lean_object* v_res_5750_; 
v_res_5750_ = l_Lake_inputBinFile___redArg___lam__0(v_path_5742_, v___y_5743_, v___y_5744_, v___y_5745_, v___y_5746_, v___y_5747_, v___y_5748_);
lean_dec_ref(v___y_5747_);
lean_dec(v___y_5746_);
lean_dec(v___y_5745_);
lean_dec(v___y_5744_);
lean_dec_ref(v___y_5743_);
return v_res_5750_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg(lean_object* v_path_5752_, lean_object* v_a_5753_, lean_object* v_a_5754_, lean_object* v_a_5755_, lean_object* v_a_5756_, lean_object* v_a_5757_){
_start:
{
lean_object* v___f_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5763_; 
v___f_5759_ = lean_alloc_closure((void*)(l_Lake_inputBinFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5759_, 0, v_path_5752_);
v___x_5760_ = l_Lake_instDataKindFilePath;
v___x_5761_ = lean_unsigned_to_nat(0u);
v___x_5762_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
v___x_5763_ = l_Lake_Job_async___redArg(v___x_5760_, v___f_5759_, v___x_5761_, v___x_5762_, v_a_5753_, v_a_5754_, v_a_5755_, v_a_5756_, v_a_5757_);
return v___x_5763_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___boxed(lean_object* v_path_5764_, lean_object* v_a_5765_, lean_object* v_a_5766_, lean_object* v_a_5767_, lean_object* v_a_5768_, lean_object* v_a_5769_, lean_object* v_a_5770_){
_start:
{
lean_object* v_res_5771_; 
v_res_5771_ = l_Lake_inputBinFile___redArg(v_path_5764_, v_a_5765_, v_a_5766_, v_a_5767_, v_a_5768_, v_a_5769_);
lean_dec_ref(v_a_5769_);
lean_dec(v_a_5768_);
lean_dec(v_a_5767_);
lean_dec(v_a_5766_);
return v_res_5771_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object* v_path_5772_, lean_object* v_a_5773_, lean_object* v_a_5774_, lean_object* v_a_5775_, lean_object* v_a_5776_, lean_object* v_a_5777_, lean_object* v_a_5778_){
_start:
{
lean_object* v___x_5780_; 
v___x_5780_ = l_Lake_inputBinFile___redArg(v_path_5772_, v_a_5773_, v_a_5774_, v_a_5775_, v_a_5776_, v_a_5777_);
return v___x_5780_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___boxed(lean_object* v_path_5781_, lean_object* v_a_5782_, lean_object* v_a_5783_, lean_object* v_a_5784_, lean_object* v_a_5785_, lean_object* v_a_5786_, lean_object* v_a_5787_, lean_object* v_a_5788_){
_start:
{
lean_object* v_res_5789_; 
v_res_5789_ = l_Lake_inputBinFile(v_path_5781_, v_a_5782_, v_a_5783_, v_a_5784_, v_a_5785_, v_a_5786_, v_a_5787_);
lean_dec_ref(v_a_5787_);
lean_dec_ref(v_a_5786_);
lean_dec(v_a_5785_);
lean_dec(v_a_5784_);
lean_dec(v_a_5783_);
return v_res_5789_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(lean_object* v_info_5790_){
_start:
{
lean_object* v___x_5792_; 
v___x_5792_ = l_Lake_computeTextFileHash(v_info_5790_);
if (lean_obj_tag(v___x_5792_) == 0)
{
lean_object* v_a_5793_; lean_object* v___x_5794_; 
v_a_5793_ = lean_ctor_get(v___x_5792_, 0);
lean_inc(v_a_5793_);
lean_dec_ref(v___x_5792_);
v___x_5794_ = lean_io_metadata(v_info_5790_);
if (lean_obj_tag(v___x_5794_) == 0)
{
lean_object* v_a_5795_; lean_object* v___x_5797_; uint8_t v_isShared_5798_; uint8_t v_isSharedCheck_5806_; 
v_a_5795_ = lean_ctor_get(v___x_5794_, 0);
v_isSharedCheck_5806_ = !lean_is_exclusive(v___x_5794_);
if (v_isSharedCheck_5806_ == 0)
{
v___x_5797_ = v___x_5794_;
v_isShared_5798_ = v_isSharedCheck_5806_;
goto v_resetjp_5796_;
}
else
{
lean_inc(v_a_5795_);
lean_dec(v___x_5794_);
v___x_5797_ = lean_box(0);
v_isShared_5798_ = v_isSharedCheck_5806_;
goto v_resetjp_5796_;
}
v_resetjp_5796_:
{
lean_object* v_modified_5799_; lean_object* v___x_5800_; lean_object* v___x_5801_; uint64_t v___x_5802_; lean_object* v___x_5804_; 
v_modified_5799_ = lean_ctor_get(v_a_5795_, 1);
lean_inc_ref(v_modified_5799_);
lean_dec(v_a_5795_);
v___x_5800_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_5801_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_5801_, 0, v_info_5790_);
lean_ctor_set(v___x_5801_, 1, v___x_5800_);
lean_ctor_set(v___x_5801_, 2, v_modified_5799_);
v___x_5802_ = lean_unbox_uint64(v_a_5793_);
lean_dec(v_a_5793_);
lean_ctor_set_uint64(v___x_5801_, sizeof(void*)*3, v___x_5802_);
if (v_isShared_5798_ == 0)
{
lean_ctor_set(v___x_5797_, 0, v___x_5801_);
v___x_5804_ = v___x_5797_;
goto v_reusejp_5803_;
}
else
{
lean_object* v_reuseFailAlloc_5805_; 
v_reuseFailAlloc_5805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5805_, 0, v___x_5801_);
v___x_5804_ = v_reuseFailAlloc_5805_;
goto v_reusejp_5803_;
}
v_reusejp_5803_:
{
return v___x_5804_;
}
}
}
else
{
lean_object* v_a_5807_; lean_object* v___x_5809_; uint8_t v_isShared_5810_; uint8_t v_isSharedCheck_5814_; 
lean_dec(v_a_5793_);
lean_dec_ref(v_info_5790_);
v_a_5807_ = lean_ctor_get(v___x_5794_, 0);
v_isSharedCheck_5814_ = !lean_is_exclusive(v___x_5794_);
if (v_isSharedCheck_5814_ == 0)
{
v___x_5809_ = v___x_5794_;
v_isShared_5810_ = v_isSharedCheck_5814_;
goto v_resetjp_5808_;
}
else
{
lean_inc(v_a_5807_);
lean_dec(v___x_5794_);
v___x_5809_ = lean_box(0);
v_isShared_5810_ = v_isSharedCheck_5814_;
goto v_resetjp_5808_;
}
v_resetjp_5808_:
{
lean_object* v___x_5812_; 
if (v_isShared_5810_ == 0)
{
v___x_5812_ = v___x_5809_;
goto v_reusejp_5811_;
}
else
{
lean_object* v_reuseFailAlloc_5813_; 
v_reuseFailAlloc_5813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5813_, 0, v_a_5807_);
v___x_5812_ = v_reuseFailAlloc_5813_;
goto v_reusejp_5811_;
}
v_reusejp_5811_:
{
return v___x_5812_;
}
}
}
}
else
{
lean_object* v_a_5815_; lean_object* v___x_5817_; uint8_t v_isShared_5818_; uint8_t v_isSharedCheck_5822_; 
lean_dec_ref(v_info_5790_);
v_a_5815_ = lean_ctor_get(v___x_5792_, 0);
v_isSharedCheck_5822_ = !lean_is_exclusive(v___x_5792_);
if (v_isSharedCheck_5822_ == 0)
{
v___x_5817_ = v___x_5792_;
v_isShared_5818_ = v_isSharedCheck_5822_;
goto v_resetjp_5816_;
}
else
{
lean_inc(v_a_5815_);
lean_dec(v___x_5792_);
v___x_5817_ = lean_box(0);
v_isShared_5818_ = v_isSharedCheck_5822_;
goto v_resetjp_5816_;
}
v_resetjp_5816_:
{
lean_object* v___x_5820_; 
if (v_isShared_5818_ == 0)
{
v___x_5820_ = v___x_5817_;
goto v_reusejp_5819_;
}
else
{
lean_object* v_reuseFailAlloc_5821_; 
v_reuseFailAlloc_5821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5821_, 0, v_a_5815_);
v___x_5820_ = v_reuseFailAlloc_5821_;
goto v_reusejp_5819_;
}
v_reusejp_5819_:
{
return v___x_5820_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0___boxed(lean_object* v_info_5823_, lean_object* v_a_5824_){
_start:
{
lean_object* v_res_5825_; 
v_res_5825_ = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(v_info_5823_);
return v_res_5825_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0(lean_object* v_path_5826_, lean_object* v___y_5827_, lean_object* v___y_5828_, lean_object* v___y_5829_, lean_object* v___y_5830_, lean_object* v___y_5831_, lean_object* v___y_5832_){
_start:
{
lean_object* v_log_5834_; uint8_t v_action_5835_; uint8_t v_wantsRebuild_5836_; lean_object* v_trace_5837_; lean_object* v_buildTime_5838_; lean_object* v___x_5840_; uint8_t v_isShared_5841_; uint8_t v_isSharedCheck_5858_; 
v_log_5834_ = lean_ctor_get(v___y_5832_, 0);
v_action_5835_ = lean_ctor_get_uint8(v___y_5832_, sizeof(void*)*3);
v_wantsRebuild_5836_ = lean_ctor_get_uint8(v___y_5832_, sizeof(void*)*3 + 1);
v_trace_5837_ = lean_ctor_get(v___y_5832_, 1);
v_buildTime_5838_ = lean_ctor_get(v___y_5832_, 2);
v_isSharedCheck_5858_ = !lean_is_exclusive(v___y_5832_);
if (v_isSharedCheck_5858_ == 0)
{
v___x_5840_ = v___y_5832_;
v_isShared_5841_ = v_isSharedCheck_5858_;
goto v_resetjp_5839_;
}
else
{
lean_inc(v_buildTime_5838_);
lean_inc(v_trace_5837_);
lean_inc(v_log_5834_);
lean_dec(v___y_5832_);
v___x_5840_ = lean_box(0);
v_isShared_5841_ = v_isSharedCheck_5858_;
goto v_resetjp_5839_;
}
v_resetjp_5839_:
{
lean_object* v___x_5842_; 
lean_inc_ref(v_path_5826_);
v___x_5842_ = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(v_path_5826_);
if (lean_obj_tag(v___x_5842_) == 0)
{
lean_object* v_a_5843_; lean_object* v___x_5845_; 
lean_dec_ref(v_trace_5837_);
v_a_5843_ = lean_ctor_get(v___x_5842_, 0);
lean_inc(v_a_5843_);
lean_dec_ref(v___x_5842_);
if (v_isShared_5841_ == 0)
{
lean_ctor_set(v___x_5840_, 1, v_a_5843_);
v___x_5845_ = v___x_5840_;
goto v_reusejp_5844_;
}
else
{
lean_object* v_reuseFailAlloc_5847_; 
v_reuseFailAlloc_5847_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5847_, 0, v_log_5834_);
lean_ctor_set(v_reuseFailAlloc_5847_, 1, v_a_5843_);
lean_ctor_set(v_reuseFailAlloc_5847_, 2, v_buildTime_5838_);
lean_ctor_set_uint8(v_reuseFailAlloc_5847_, sizeof(void*)*3, v_action_5835_);
lean_ctor_set_uint8(v_reuseFailAlloc_5847_, sizeof(void*)*3 + 1, v_wantsRebuild_5836_);
v___x_5845_ = v_reuseFailAlloc_5847_;
goto v_reusejp_5844_;
}
v_reusejp_5844_:
{
lean_object* v___x_5846_; 
v___x_5846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5846_, 0, v_path_5826_);
lean_ctor_set(v___x_5846_, 1, v___x_5845_);
return v___x_5846_;
}
}
else
{
lean_object* v_a_5848_; lean_object* v___x_5849_; uint8_t v___x_5850_; lean_object* v___x_5851_; lean_object* v___x_5852_; lean_object* v___x_5853_; lean_object* v___x_5855_; 
lean_dec_ref(v_path_5826_);
v_a_5848_ = lean_ctor_get(v___x_5842_, 0);
lean_inc(v_a_5848_);
lean_dec_ref(v___x_5842_);
v___x_5849_ = lean_io_error_to_string(v_a_5848_);
v___x_5850_ = 3;
v___x_5851_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5851_, 0, v___x_5849_);
lean_ctor_set_uint8(v___x_5851_, sizeof(void*)*1, v___x_5850_);
v___x_5852_ = lean_array_get_size(v_log_5834_);
v___x_5853_ = lean_array_push(v_log_5834_, v___x_5851_);
if (v_isShared_5841_ == 0)
{
lean_ctor_set(v___x_5840_, 0, v___x_5853_);
v___x_5855_ = v___x_5840_;
goto v_reusejp_5854_;
}
else
{
lean_object* v_reuseFailAlloc_5857_; 
v_reuseFailAlloc_5857_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5857_, 0, v___x_5853_);
lean_ctor_set(v_reuseFailAlloc_5857_, 1, v_trace_5837_);
lean_ctor_set(v_reuseFailAlloc_5857_, 2, v_buildTime_5838_);
lean_ctor_set_uint8(v_reuseFailAlloc_5857_, sizeof(void*)*3, v_action_5835_);
lean_ctor_set_uint8(v_reuseFailAlloc_5857_, sizeof(void*)*3 + 1, v_wantsRebuild_5836_);
v___x_5855_ = v_reuseFailAlloc_5857_;
goto v_reusejp_5854_;
}
v_reusejp_5854_:
{
lean_object* v___x_5856_; 
v___x_5856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5856_, 0, v___x_5852_);
lean_ctor_set(v___x_5856_, 1, v___x_5855_);
return v___x_5856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0___boxed(lean_object* v_path_5859_, lean_object* v___y_5860_, lean_object* v___y_5861_, lean_object* v___y_5862_, lean_object* v___y_5863_, lean_object* v___y_5864_, lean_object* v___y_5865_, lean_object* v___y_5866_){
_start:
{
lean_object* v_res_5867_; 
v_res_5867_ = l_Lake_inputTextFile___redArg___lam__0(v_path_5859_, v___y_5860_, v___y_5861_, v___y_5862_, v___y_5863_, v___y_5864_, v___y_5865_);
lean_dec_ref(v___y_5864_);
lean_dec(v___y_5863_);
lean_dec(v___y_5862_);
lean_dec(v___y_5861_);
lean_dec_ref(v___y_5860_);
return v_res_5867_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg(lean_object* v_path_5868_, lean_object* v_a_5869_, lean_object* v_a_5870_, lean_object* v_a_5871_, lean_object* v_a_5872_, lean_object* v_a_5873_){
_start:
{
lean_object* v___f_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; 
v___f_5875_ = lean_alloc_closure((void*)(l_Lake_inputTextFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5875_, 0, v_path_5868_);
v___x_5876_ = l_Lake_instDataKindFilePath;
v___x_5877_ = lean_unsigned_to_nat(0u);
v___x_5878_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
v___x_5879_ = l_Lake_Job_async___redArg(v___x_5876_, v___f_5875_, v___x_5877_, v___x_5878_, v_a_5869_, v_a_5870_, v_a_5871_, v_a_5872_, v_a_5873_);
return v___x_5879_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___boxed(lean_object* v_path_5880_, lean_object* v_a_5881_, lean_object* v_a_5882_, lean_object* v_a_5883_, lean_object* v_a_5884_, lean_object* v_a_5885_, lean_object* v_a_5886_){
_start:
{
lean_object* v_res_5887_; 
v_res_5887_ = l_Lake_inputTextFile___redArg(v_path_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_);
lean_dec_ref(v_a_5885_);
lean_dec(v_a_5884_);
lean_dec(v_a_5883_);
lean_dec(v_a_5882_);
return v_res_5887_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object* v_path_5888_, lean_object* v_a_5889_, lean_object* v_a_5890_, lean_object* v_a_5891_, lean_object* v_a_5892_, lean_object* v_a_5893_, lean_object* v_a_5894_){
_start:
{
lean_object* v___x_5896_; 
v___x_5896_ = l_Lake_inputTextFile___redArg(v_path_5888_, v_a_5889_, v_a_5890_, v_a_5891_, v_a_5892_, v_a_5893_);
return v___x_5896_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___boxed(lean_object* v_path_5897_, lean_object* v_a_5898_, lean_object* v_a_5899_, lean_object* v_a_5900_, lean_object* v_a_5901_, lean_object* v_a_5902_, lean_object* v_a_5903_, lean_object* v_a_5904_){
_start:
{
lean_object* v_res_5905_; 
v_res_5905_ = l_Lake_inputTextFile(v_path_5897_, v_a_5898_, v_a_5899_, v_a_5900_, v_a_5901_, v_a_5902_, v_a_5903_);
lean_dec_ref(v_a_5903_);
lean_dec_ref(v_a_5902_);
lean_dec(v_a_5901_);
lean_dec(v_a_5900_);
lean_dec(v_a_5899_);
return v_res_5905_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg(lean_object* v_path_5906_, uint8_t v_text_5907_, lean_object* v_a_5908_, lean_object* v_a_5909_, lean_object* v_a_5910_, lean_object* v_a_5911_, lean_object* v_a_5912_){
_start:
{
if (v_text_5907_ == 0)
{
lean_object* v___x_5914_; 
v___x_5914_ = l_Lake_inputBinFile___redArg(v_path_5906_, v_a_5908_, v_a_5909_, v_a_5910_, v_a_5911_, v_a_5912_);
return v___x_5914_;
}
else
{
lean_object* v___x_5915_; 
v___x_5915_ = l_Lake_inputTextFile___redArg(v_path_5906_, v_a_5908_, v_a_5909_, v_a_5910_, v_a_5911_, v_a_5912_);
return v___x_5915_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg___boxed(lean_object* v_path_5916_, lean_object* v_text_5917_, lean_object* v_a_5918_, lean_object* v_a_5919_, lean_object* v_a_5920_, lean_object* v_a_5921_, lean_object* v_a_5922_, lean_object* v_a_5923_){
_start:
{
uint8_t v_text_boxed_5924_; lean_object* v_res_5925_; 
v_text_boxed_5924_ = lean_unbox(v_text_5917_);
v_res_5925_ = l_Lake_inputFile___redArg(v_path_5916_, v_text_boxed_5924_, v_a_5918_, v_a_5919_, v_a_5920_, v_a_5921_, v_a_5922_);
lean_dec_ref(v_a_5922_);
lean_dec(v_a_5921_);
lean_dec(v_a_5920_);
lean_dec(v_a_5919_);
return v_res_5925_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object* v_path_5926_, uint8_t v_text_5927_, lean_object* v_a_5928_, lean_object* v_a_5929_, lean_object* v_a_5930_, lean_object* v_a_5931_, lean_object* v_a_5932_, lean_object* v_a_5933_){
_start:
{
if (v_text_5927_ == 0)
{
lean_object* v___x_5935_; 
v___x_5935_ = l_Lake_inputBinFile___redArg(v_path_5926_, v_a_5928_, v_a_5929_, v_a_5930_, v_a_5931_, v_a_5932_);
return v___x_5935_;
}
else
{
lean_object* v___x_5936_; 
v___x_5936_ = l_Lake_inputTextFile___redArg(v_path_5926_, v_a_5928_, v_a_5929_, v_a_5930_, v_a_5931_, v_a_5932_);
return v___x_5936_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object* v_path_5937_, lean_object* v_text_5938_, lean_object* v_a_5939_, lean_object* v_a_5940_, lean_object* v_a_5941_, lean_object* v_a_5942_, lean_object* v_a_5943_, lean_object* v_a_5944_, lean_object* v_a_5945_){
_start:
{
uint8_t v_text_boxed_5946_; lean_object* v_res_5947_; 
v_text_boxed_5946_ = lean_unbox(v_text_5938_);
v_res_5947_ = l_Lake_inputFile(v_path_5937_, v_text_boxed_5946_, v_a_5939_, v_a_5940_, v_a_5941_, v_a_5942_, v_a_5943_, v_a_5944_);
lean_dec_ref(v_a_5944_);
lean_dec_ref(v_a_5943_);
lean_dec(v_a_5942_);
lean_dec(v_a_5941_);
lean_dec(v_a_5940_);
return v_res_5947_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0(lean_object* v_x_5948_){
_start:
{
uint8_t v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; 
v___x_5950_ = 1;
v___x_5951_ = lean_box(v___x_5950_);
v___x_5952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5952_, 0, v___x_5951_);
return v___x_5952_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0___boxed(lean_object* v_x_5953_, lean_object* v___y_5954_){
_start:
{
lean_object* v_res_5955_; 
v_res_5955_ = l_Lake_inputDir___lam__0(v_x_5953_);
lean_dec_ref(v_x_5953_);
return v_res_5955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(lean_object* v_filter_5956_, lean_object* v_as_5957_, size_t v_i_5958_, size_t v_stop_5959_, lean_object* v_b_5960_, lean_object* v___y_5961_){
_start:
{
lean_object* v_a_5964_; lean_object* v_a_5965_; uint8_t v___x_5969_; 
v___x_5969_ = lean_usize_dec_eq(v_i_5958_, v_stop_5959_);
if (v___x_5969_ == 0)
{
lean_object* v___x_5970_; uint8_t v___x_5971_; 
v___x_5970_ = lean_array_uget_borrowed(v_as_5957_, v_i_5958_);
v___x_5971_ = l_System_FilePath_isDir(v___x_5970_);
if (v___x_5971_ == 0)
{
lean_object* v___x_5972_; uint8_t v___x_5973_; 
lean_inc_ref(v_filter_5956_);
lean_inc(v___x_5970_);
v___x_5972_ = lean_apply_1(v_filter_5956_, v___x_5970_);
v___x_5973_ = lean_unbox(v___x_5972_);
if (v___x_5973_ == 0)
{
v_a_5964_ = v_b_5960_;
v_a_5965_ = v___y_5961_;
goto v___jp_5963_;
}
else
{
lean_object* v___x_5974_; 
lean_inc(v___x_5970_);
v___x_5974_ = lean_array_push(v_b_5960_, v___x_5970_);
v_a_5964_ = v___x_5974_;
v_a_5965_ = v___y_5961_;
goto v___jp_5963_;
}
}
else
{
v_a_5964_ = v_b_5960_;
v_a_5965_ = v___y_5961_;
goto v___jp_5963_;
}
}
else
{
lean_object* v___x_5975_; 
lean_dec_ref(v_filter_5956_);
v___x_5975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5975_, 0, v_b_5960_);
lean_ctor_set(v___x_5975_, 1, v___y_5961_);
return v___x_5975_;
}
v___jp_5963_:
{
size_t v___x_5966_; size_t v___x_5967_; 
v___x_5966_ = ((size_t)1ULL);
v___x_5967_ = lean_usize_add(v_i_5958_, v___x_5966_);
v_i_5958_ = v___x_5967_;
v_b_5960_ = v_a_5964_;
v___y_5961_ = v_a_5965_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg___boxed(lean_object* v_filter_5976_, lean_object* v_as_5977_, lean_object* v_i_5978_, lean_object* v_stop_5979_, lean_object* v_b_5980_, lean_object* v___y_5981_, lean_object* v___y_5982_){
_start:
{
size_t v_i_boxed_5983_; size_t v_stop_boxed_5984_; lean_object* v_res_5985_; 
v_i_boxed_5983_ = lean_unbox_usize(v_i_5978_);
lean_dec(v_i_5978_);
v_stop_boxed_5984_ = lean_unbox_usize(v_stop_5979_);
lean_dec(v_stop_5979_);
v_res_5985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_5976_, v_as_5977_, v_i_boxed_5983_, v_stop_boxed_5984_, v_b_5980_, v___y_5981_);
lean_dec_ref(v_as_5977_);
return v_res_5985_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(lean_object* v_as_5987_, lean_object* v_lo_5988_, lean_object* v_hi_5989_){
_start:
{
uint8_t v___x_5990_; 
v___x_5990_ = lean_nat_dec_lt(v_lo_5988_, v_hi_5989_);
if (v___x_5990_ == 0)
{
lean_dec(v_lo_5988_);
return v_as_5987_;
}
else
{
lean_object* v___f_5991_; lean_object* v___x_5992_; lean_object* v_fst_5993_; lean_object* v_snd_5994_; uint8_t v___x_5995_; 
v___f_5991_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___closed__0));
lean_inc(v_lo_5988_);
v___x_5992_ = l_Array_qpartition___redArg(v_as_5987_, v___f_5991_, v_lo_5988_, v_hi_5989_);
v_fst_5993_ = lean_ctor_get(v___x_5992_, 0);
lean_inc(v_fst_5993_);
v_snd_5994_ = lean_ctor_get(v___x_5992_, 1);
lean_inc(v_snd_5994_);
lean_dec_ref(v___x_5992_);
v___x_5995_ = lean_nat_dec_le(v_hi_5989_, v_fst_5993_);
if (v___x_5995_ == 0)
{
lean_object* v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; 
v___x_5996_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_snd_5994_, v_lo_5988_, v_fst_5993_);
v___x_5997_ = lean_unsigned_to_nat(1u);
v___x_5998_ = lean_nat_add(v_fst_5993_, v___x_5997_);
lean_dec(v_fst_5993_);
v_as_5987_ = v___x_5996_;
v_lo_5988_ = v___x_5998_;
goto _start;
}
else
{
lean_dec(v_fst_5993_);
lean_dec(v_lo_5988_);
return v_snd_5994_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___boxed(lean_object* v_as_6000_, lean_object* v_lo_6001_, lean_object* v_hi_6002_){
_start:
{
lean_object* v_res_6003_; 
v_res_6003_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_as_6000_, v_lo_6001_, v_hi_6002_);
lean_dec(v_hi_6002_);
return v_res_6003_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1(lean_object* v_path_6006_, lean_object* v___f_6007_, lean_object* v_filter_6008_, lean_object* v___y_6009_, lean_object* v___y_6010_, lean_object* v___y_6011_, lean_object* v___y_6012_, lean_object* v___y_6013_, lean_object* v___y_6014_){
_start:
{
lean_object* v___y_6017_; lean_object* v___y_6018_; lean_object* v___y_6021_; lean_object* v___y_6022_; lean_object* v___y_6023_; lean_object* v___y_6024_; lean_object* v___y_6025_; lean_object* v___y_6028_; lean_object* v___y_6029_; lean_object* v___y_6030_; lean_object* v___y_6031_; lean_object* v___y_6032_; lean_object* v_log_6034_; uint8_t v_action_6035_; uint8_t v_wantsRebuild_6036_; lean_object* v_trace_6037_; lean_object* v_buildTime_6038_; lean_object* v___x_6039_; 
v_log_6034_ = lean_ctor_get(v___y_6014_, 0);
v_action_6035_ = lean_ctor_get_uint8(v___y_6014_, sizeof(void*)*3);
v_wantsRebuild_6036_ = lean_ctor_get_uint8(v___y_6014_, sizeof(void*)*3 + 1);
v_trace_6037_ = lean_ctor_get(v___y_6014_, 1);
v_buildTime_6038_ = lean_ctor_get(v___y_6014_, 2);
v___x_6039_ = l_System_FilePath_walkDir(v_path_6006_, v___f_6007_);
if (lean_obj_tag(v___x_6039_) == 0)
{
lean_object* v_a_6040_; lean_object* v___x_6041_; lean_object* v_a_6043_; lean_object* v_a_6044_; lean_object* v___y_6051_; lean_object* v___x_6054_; lean_object* v___x_6055_; uint8_t v___x_6056_; 
v_a_6040_ = lean_ctor_get(v___x_6039_, 0);
lean_inc(v_a_6040_);
lean_dec_ref(v___x_6039_);
v___x_6041_ = lean_unsigned_to_nat(0u);
v___x_6054_ = lean_array_get_size(v_a_6040_);
v___x_6055_ = ((lean_object*)(l_Lake_inputDir___lam__1___closed__0));
v___x_6056_ = lean_nat_dec_lt(v___x_6041_, v___x_6054_);
if (v___x_6056_ == 0)
{
lean_dec(v_a_6040_);
lean_dec_ref(v_filter_6008_);
v_a_6043_ = v___x_6055_;
v_a_6044_ = v___y_6014_;
goto v___jp_6042_;
}
else
{
uint8_t v___x_6057_; 
v___x_6057_ = lean_nat_dec_le(v___x_6054_, v___x_6054_);
if (v___x_6057_ == 0)
{
if (v___x_6056_ == 0)
{
lean_dec(v_a_6040_);
lean_dec_ref(v_filter_6008_);
v_a_6043_ = v___x_6055_;
v_a_6044_ = v___y_6014_;
goto v___jp_6042_;
}
else
{
size_t v___x_6058_; size_t v___x_6059_; lean_object* v___x_6060_; 
v___x_6058_ = ((size_t)0ULL);
v___x_6059_ = lean_usize_of_nat(v___x_6054_);
v___x_6060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6008_, v_a_6040_, v___x_6058_, v___x_6059_, v___x_6055_, v___y_6014_);
lean_dec(v_a_6040_);
v___y_6051_ = v___x_6060_;
goto v___jp_6050_;
}
}
else
{
size_t v___x_6061_; size_t v___x_6062_; lean_object* v___x_6063_; 
v___x_6061_ = ((size_t)0ULL);
v___x_6062_ = lean_usize_of_nat(v___x_6054_);
v___x_6063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6008_, v_a_6040_, v___x_6061_, v___x_6062_, v___x_6055_, v___y_6014_);
lean_dec(v_a_6040_);
v___y_6051_ = v___x_6063_;
goto v___jp_6050_;
}
}
v___jp_6042_:
{
lean_object* v___x_6045_; uint8_t v___x_6046_; 
v___x_6045_ = lean_array_get_size(v_a_6043_);
v___x_6046_ = lean_nat_dec_eq(v___x_6045_, v___x_6041_);
if (v___x_6046_ == 0)
{
lean_object* v___x_6047_; lean_object* v___x_6048_; uint8_t v___x_6049_; 
v___x_6047_ = lean_unsigned_to_nat(1u);
v___x_6048_ = lean_nat_sub(v___x_6045_, v___x_6047_);
v___x_6049_ = lean_nat_dec_le(v___x_6041_, v___x_6048_);
if (v___x_6049_ == 0)
{
lean_inc(v___x_6048_);
v___y_6028_ = v_a_6044_;
v___y_6029_ = v___x_6045_;
v___y_6030_ = v_a_6043_;
v___y_6031_ = v___x_6048_;
v___y_6032_ = v___x_6048_;
goto v___jp_6027_;
}
else
{
v___y_6028_ = v_a_6044_;
v___y_6029_ = v___x_6045_;
v___y_6030_ = v_a_6043_;
v___y_6031_ = v___x_6048_;
v___y_6032_ = v___x_6041_;
goto v___jp_6027_;
}
}
else
{
v___y_6017_ = v_a_6044_;
v___y_6018_ = v_a_6043_;
goto v___jp_6016_;
}
}
v___jp_6050_:
{
if (lean_obj_tag(v___y_6051_) == 0)
{
lean_object* v_a_6052_; lean_object* v_a_6053_; 
v_a_6052_ = lean_ctor_get(v___y_6051_, 0);
lean_inc(v_a_6052_);
v_a_6053_ = lean_ctor_get(v___y_6051_, 1);
lean_inc(v_a_6053_);
lean_dec_ref(v___y_6051_);
v_a_6043_ = v_a_6052_;
v_a_6044_ = v_a_6053_;
goto v___jp_6042_;
}
else
{
return v___y_6051_;
}
}
}
else
{
lean_object* v___x_6065_; uint8_t v_isShared_6066_; uint8_t v_isSharedCheck_6077_; 
lean_inc(v_buildTime_6038_);
lean_inc_ref(v_trace_6037_);
lean_inc_ref(v_log_6034_);
lean_dec_ref(v_filter_6008_);
v_isSharedCheck_6077_ = !lean_is_exclusive(v___y_6014_);
if (v_isSharedCheck_6077_ == 0)
{
lean_object* v_unused_6078_; lean_object* v_unused_6079_; lean_object* v_unused_6080_; 
v_unused_6078_ = lean_ctor_get(v___y_6014_, 2);
lean_dec(v_unused_6078_);
v_unused_6079_ = lean_ctor_get(v___y_6014_, 1);
lean_dec(v_unused_6079_);
v_unused_6080_ = lean_ctor_get(v___y_6014_, 0);
lean_dec(v_unused_6080_);
v___x_6065_ = v___y_6014_;
v_isShared_6066_ = v_isSharedCheck_6077_;
goto v_resetjp_6064_;
}
else
{
lean_dec(v___y_6014_);
v___x_6065_ = lean_box(0);
v_isShared_6066_ = v_isSharedCheck_6077_;
goto v_resetjp_6064_;
}
v_resetjp_6064_:
{
lean_object* v_a_6067_; lean_object* v___x_6068_; uint8_t v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6074_; 
v_a_6067_ = lean_ctor_get(v___x_6039_, 0);
lean_inc(v_a_6067_);
lean_dec_ref(v___x_6039_);
v___x_6068_ = lean_io_error_to_string(v_a_6067_);
v___x_6069_ = 3;
v___x_6070_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6070_, 0, v___x_6068_);
lean_ctor_set_uint8(v___x_6070_, sizeof(void*)*1, v___x_6069_);
v___x_6071_ = lean_array_get_size(v_log_6034_);
v___x_6072_ = lean_array_push(v_log_6034_, v___x_6070_);
if (v_isShared_6066_ == 0)
{
lean_ctor_set(v___x_6065_, 0, v___x_6072_);
v___x_6074_ = v___x_6065_;
goto v_reusejp_6073_;
}
else
{
lean_object* v_reuseFailAlloc_6076_; 
v_reuseFailAlloc_6076_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6076_, 0, v___x_6072_);
lean_ctor_set(v_reuseFailAlloc_6076_, 1, v_trace_6037_);
lean_ctor_set(v_reuseFailAlloc_6076_, 2, v_buildTime_6038_);
lean_ctor_set_uint8(v_reuseFailAlloc_6076_, sizeof(void*)*3, v_action_6035_);
lean_ctor_set_uint8(v_reuseFailAlloc_6076_, sizeof(void*)*3 + 1, v_wantsRebuild_6036_);
v___x_6074_ = v_reuseFailAlloc_6076_;
goto v_reusejp_6073_;
}
v_reusejp_6073_:
{
lean_object* v___x_6075_; 
v___x_6075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6075_, 0, v___x_6071_);
lean_ctor_set(v___x_6075_, 1, v___x_6074_);
return v___x_6075_;
}
}
}
v___jp_6016_:
{
lean_object* v___x_6019_; 
v___x_6019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6019_, 0, v___y_6018_);
lean_ctor_set(v___x_6019_, 1, v___y_6017_);
return v___x_6019_;
}
v___jp_6020_:
{
lean_object* v___x_6026_; 
lean_dec(v___y_6023_);
v___x_6026_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v___y_6024_, v___y_6022_, v___y_6025_);
lean_dec(v___y_6025_);
v___y_6017_ = v___y_6021_;
v___y_6018_ = v___x_6026_;
goto v___jp_6016_;
}
v___jp_6027_:
{
uint8_t v___x_6033_; 
v___x_6033_ = lean_nat_dec_le(v___y_6032_, v___y_6031_);
if (v___x_6033_ == 0)
{
lean_dec(v___y_6031_);
lean_inc(v___y_6032_);
v___y_6021_ = v___y_6028_;
v___y_6022_ = v___y_6032_;
v___y_6023_ = v___y_6029_;
v___y_6024_ = v___y_6030_;
v___y_6025_ = v___y_6032_;
goto v___jp_6020_;
}
else
{
v___y_6021_ = v___y_6028_;
v___y_6022_ = v___y_6032_;
v___y_6023_ = v___y_6029_;
v___y_6024_ = v___y_6030_;
v___y_6025_ = v___y_6031_;
goto v___jp_6020_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1___boxed(lean_object* v_path_6081_, lean_object* v___f_6082_, lean_object* v_filter_6083_, lean_object* v___y_6084_, lean_object* v___y_6085_, lean_object* v___y_6086_, lean_object* v___y_6087_, lean_object* v___y_6088_, lean_object* v___y_6089_, lean_object* v___y_6090_){
_start:
{
lean_object* v_res_6091_; 
v_res_6091_ = l_Lake_inputDir___lam__1(v_path_6081_, v___f_6082_, v_filter_6083_, v___y_6084_, v___y_6085_, v___y_6086_, v___y_6087_, v___y_6088_, v___y_6089_);
lean_dec_ref(v___y_6088_);
lean_dec(v___y_6087_);
lean_dec(v___y_6086_);
lean_dec(v___y_6085_);
lean_dec_ref(v___y_6084_);
return v_res_6091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(uint8_t v_text_6092_, size_t v_sz_6093_, size_t v_i_6094_, lean_object* v_bs_6095_, lean_object* v___y_6096_, lean_object* v___y_6097_, lean_object* v___y_6098_, lean_object* v___y_6099_, lean_object* v___y_6100_, lean_object* v___y_6101_){
_start:
{
uint8_t v___x_6103_; 
v___x_6103_ = lean_usize_dec_lt(v_i_6094_, v_sz_6093_);
if (v___x_6103_ == 0)
{
lean_object* v___x_6104_; 
lean_dec_ref(v___y_6096_);
v___x_6104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6104_, 0, v_bs_6095_);
lean_ctor_set(v___x_6104_, 1, v___y_6101_);
return v___x_6104_;
}
else
{
lean_object* v_v_6105_; lean_object* v___x_6106_; lean_object* v_bs_x27_6107_; lean_object* v___y_6109_; 
v_v_6105_ = lean_array_uget(v_bs_6095_, v_i_6094_);
v___x_6106_ = lean_unsigned_to_nat(0u);
v_bs_x27_6107_ = lean_array_uset(v_bs_6095_, v_i_6094_, v___x_6106_);
if (v_text_6092_ == 0)
{
lean_object* v___x_6114_; 
lean_inc_ref(v___y_6096_);
v___x_6114_ = l_Lake_inputBinFile___redArg(v_v_6105_, v___y_6096_, v___y_6097_, v___y_6098_, v___y_6099_, v___y_6100_);
v___y_6109_ = v___x_6114_;
goto v___jp_6108_;
}
else
{
lean_object* v___x_6115_; 
lean_inc_ref(v___y_6096_);
v___x_6115_ = l_Lake_inputTextFile___redArg(v_v_6105_, v___y_6096_, v___y_6097_, v___y_6098_, v___y_6099_, v___y_6100_);
v___y_6109_ = v___x_6115_;
goto v___jp_6108_;
}
v___jp_6108_:
{
size_t v___x_6110_; size_t v___x_6111_; lean_object* v___x_6112_; 
v___x_6110_ = ((size_t)1ULL);
v___x_6111_ = lean_usize_add(v_i_6094_, v___x_6110_);
v___x_6112_ = lean_array_uset(v_bs_x27_6107_, v_i_6094_, v___y_6109_);
v_i_6094_ = v___x_6111_;
v_bs_6095_ = v___x_6112_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0___boxed(lean_object* v_text_6116_, lean_object* v_sz_6117_, lean_object* v_i_6118_, lean_object* v_bs_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_, lean_object* v___y_6122_, lean_object* v___y_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_){
_start:
{
uint8_t v_text_boxed_6127_; size_t v_sz_boxed_6128_; size_t v_i_boxed_6129_; lean_object* v_res_6130_; 
v_text_boxed_6127_ = lean_unbox(v_text_6116_);
v_sz_boxed_6128_ = lean_unbox_usize(v_sz_6117_);
lean_dec(v_sz_6117_);
v_i_boxed_6129_ = lean_unbox_usize(v_i_6118_);
lean_dec(v_i_6118_);
v_res_6130_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(v_text_boxed_6127_, v_sz_boxed_6128_, v_i_boxed_6129_, v_bs_6119_, v___y_6120_, v___y_6121_, v___y_6122_, v___y_6123_, v___y_6124_, v___y_6125_);
lean_dec_ref(v___y_6124_);
lean_dec(v___y_6123_);
lean_dec(v___y_6122_);
lean_dec(v___y_6121_);
return v_res_6130_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2(uint8_t v_text_6131_, lean_object* v_path_6132_, lean_object* v_ps_6133_, lean_object* v___y_6134_, lean_object* v___y_6135_, lean_object* v___y_6136_, lean_object* v___y_6137_, lean_object* v___y_6138_, lean_object* v___y_6139_){
_start:
{
size_t v_sz_6141_; size_t v___x_6142_; lean_object* v___x_6143_; 
v_sz_6141_ = lean_array_size(v_ps_6133_);
v___x_6142_ = ((size_t)0ULL);
v___x_6143_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(v_text_6131_, v_sz_6141_, v___x_6142_, v_ps_6133_, v___y_6134_, v___y_6135_, v___y_6136_, v___y_6137_, v___y_6138_, v___y_6139_);
if (lean_obj_tag(v___x_6143_) == 0)
{
lean_object* v_a_6144_; lean_object* v_a_6145_; lean_object* v___x_6147_; uint8_t v_isShared_6148_; uint8_t v_isSharedCheck_6153_; 
v_a_6144_ = lean_ctor_get(v___x_6143_, 0);
v_a_6145_ = lean_ctor_get(v___x_6143_, 1);
v_isSharedCheck_6153_ = !lean_is_exclusive(v___x_6143_);
if (v_isSharedCheck_6153_ == 0)
{
v___x_6147_ = v___x_6143_;
v_isShared_6148_ = v_isSharedCheck_6153_;
goto v_resetjp_6146_;
}
else
{
lean_inc(v_a_6145_);
lean_inc(v_a_6144_);
lean_dec(v___x_6143_);
v___x_6147_ = lean_box(0);
v_isShared_6148_ = v_isSharedCheck_6153_;
goto v_resetjp_6146_;
}
v_resetjp_6146_:
{
lean_object* v___x_6149_; lean_object* v___x_6151_; 
v___x_6149_ = l_Lake_Job_collectArray___redArg(v_a_6144_, v_path_6132_);
lean_dec(v_a_6144_);
if (v_isShared_6148_ == 0)
{
lean_ctor_set(v___x_6147_, 0, v___x_6149_);
v___x_6151_ = v___x_6147_;
goto v_reusejp_6150_;
}
else
{
lean_object* v_reuseFailAlloc_6152_; 
v_reuseFailAlloc_6152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6152_, 0, v___x_6149_);
lean_ctor_set(v_reuseFailAlloc_6152_, 1, v_a_6145_);
v___x_6151_ = v_reuseFailAlloc_6152_;
goto v_reusejp_6150_;
}
v_reusejp_6150_:
{
return v___x_6151_;
}
}
}
else
{
lean_object* v_a_6154_; lean_object* v_a_6155_; lean_object* v___x_6157_; uint8_t v_isShared_6158_; uint8_t v_isSharedCheck_6162_; 
lean_dec_ref(v_path_6132_);
v_a_6154_ = lean_ctor_get(v___x_6143_, 0);
v_a_6155_ = lean_ctor_get(v___x_6143_, 1);
v_isSharedCheck_6162_ = !lean_is_exclusive(v___x_6143_);
if (v_isSharedCheck_6162_ == 0)
{
v___x_6157_ = v___x_6143_;
v_isShared_6158_ = v_isSharedCheck_6162_;
goto v_resetjp_6156_;
}
else
{
lean_inc(v_a_6155_);
lean_inc(v_a_6154_);
lean_dec(v___x_6143_);
v___x_6157_ = lean_box(0);
v_isShared_6158_ = v_isSharedCheck_6162_;
goto v_resetjp_6156_;
}
v_resetjp_6156_:
{
lean_object* v___x_6160_; 
if (v_isShared_6158_ == 0)
{
v___x_6160_ = v___x_6157_;
goto v_reusejp_6159_;
}
else
{
lean_object* v_reuseFailAlloc_6161_; 
v_reuseFailAlloc_6161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6161_, 0, v_a_6154_);
lean_ctor_set(v_reuseFailAlloc_6161_, 1, v_a_6155_);
v___x_6160_ = v_reuseFailAlloc_6161_;
goto v_reusejp_6159_;
}
v_reusejp_6159_:
{
return v___x_6160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2___boxed(lean_object* v_text_6163_, lean_object* v_path_6164_, lean_object* v_ps_6165_, lean_object* v___y_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_){
_start:
{
uint8_t v_text_boxed_6173_; lean_object* v_res_6174_; 
v_text_boxed_6173_ = lean_unbox(v_text_6163_);
v_res_6174_ = l_Lake_inputDir___lam__2(v_text_boxed_6173_, v_path_6164_, v_ps_6165_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_, v___y_6170_, v___y_6171_);
lean_dec_ref(v___y_6170_);
lean_dec(v___y_6169_);
lean_dec(v___y_6168_);
lean_dec(v___y_6167_);
return v_res_6174_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir(lean_object* v_path_6176_, uint8_t v_text_6177_, lean_object* v_filter_6178_, lean_object* v_a_6179_, lean_object* v_a_6180_, lean_object* v_a_6181_, lean_object* v_a_6182_, lean_object* v_a_6183_, lean_object* v_a_6184_){
_start:
{
lean_object* v___f_6186_; lean_object* v___f_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___f_6193_; uint8_t v___x_6194_; lean_object* v___x_6195_; 
v___f_6186_ = ((lean_object*)(l_Lake_inputDir___closed__0));
lean_inc_ref(v_path_6176_);
v___f_6187_ = lean_alloc_closure((void*)(l_Lake_inputDir___lam__1___boxed), 10, 3);
lean_closure_set(v___f_6187_, 0, v_path_6176_);
lean_closure_set(v___f_6187_, 1, v___f_6186_);
lean_closure_set(v___f_6187_, 2, v_filter_6178_);
v___x_6188_ = lean_box(0);
v___x_6189_ = lean_unsigned_to_nat(0u);
v___x_6190_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
lean_inc_ref(v_a_6179_);
v___x_6191_ = l_Lake_Job_async___redArg(v___x_6188_, v___f_6187_, v___x_6189_, v___x_6190_, v_a_6179_, v_a_6180_, v_a_6181_, v_a_6182_, v_a_6183_);
v___x_6192_ = lean_box(v_text_6177_);
v___f_6193_ = lean_alloc_closure((void*)(l_Lake_inputDir___lam__2___boxed), 10, 2);
lean_closure_set(v___f_6193_, 0, v___x_6192_);
lean_closure_set(v___f_6193_, 1, v_path_6176_);
v___x_6194_ = 0;
v___x_6195_ = l_Lake_Job_bindM___redArg(v___x_6188_, v___x_6191_, v___f_6193_, v___x_6189_, v___x_6194_, v_a_6179_, v_a_6180_, v_a_6181_, v_a_6182_, v_a_6183_, v_a_6184_);
return v___x_6195_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___boxed(lean_object* v_path_6196_, lean_object* v_text_6197_, lean_object* v_filter_6198_, lean_object* v_a_6199_, lean_object* v_a_6200_, lean_object* v_a_6201_, lean_object* v_a_6202_, lean_object* v_a_6203_, lean_object* v_a_6204_, lean_object* v_a_6205_){
_start:
{
uint8_t v_text_boxed_6206_; lean_object* v_res_6207_; 
v_text_boxed_6206_ = lean_unbox(v_text_6197_);
v_res_6207_ = l_Lake_inputDir(v_path_6196_, v_text_boxed_6206_, v_filter_6198_, v_a_6199_, v_a_6200_, v_a_6201_, v_a_6202_, v_a_6203_, v_a_6204_);
lean_dec_ref(v_a_6204_);
lean_dec_ref(v_a_6203_);
lean_dec(v_a_6202_);
lean_dec(v_a_6201_);
lean_dec(v_a_6200_);
return v_res_6207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(lean_object* v_n_6208_, lean_object* v_as_6209_, lean_object* v_lo_6210_, lean_object* v_hi_6211_, lean_object* v_w_6212_, lean_object* v_hlo_6213_, lean_object* v_hhi_6214_){
_start:
{
lean_object* v___x_6215_; 
v___x_6215_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_as_6209_, v_lo_6210_, v_hi_6211_);
return v___x_6215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___boxed(lean_object* v_n_6216_, lean_object* v_as_6217_, lean_object* v_lo_6218_, lean_object* v_hi_6219_, lean_object* v_w_6220_, lean_object* v_hlo_6221_, lean_object* v_hhi_6222_){
_start:
{
lean_object* v_res_6223_; 
v_res_6223_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(v_n_6216_, v_as_6217_, v_lo_6218_, v_hi_6219_, v_w_6220_, v_hlo_6221_, v_hhi_6222_);
lean_dec(v_hi_6219_);
lean_dec(v_n_6216_);
return v_res_6223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(lean_object* v_filter_6224_, lean_object* v_as_6225_, size_t v_i_6226_, size_t v_stop_6227_, lean_object* v_b_6228_, lean_object* v___y_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_){
_start:
{
lean_object* v___x_6236_; 
v___x_6236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6224_, v_as_6225_, v_i_6226_, v_stop_6227_, v_b_6228_, v___y_6234_);
return v___x_6236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___boxed(lean_object* v_filter_6237_, lean_object* v_as_6238_, lean_object* v_i_6239_, lean_object* v_stop_6240_, lean_object* v_b_6241_, lean_object* v___y_6242_, lean_object* v___y_6243_, lean_object* v___y_6244_, lean_object* v___y_6245_, lean_object* v___y_6246_, lean_object* v___y_6247_, lean_object* v___y_6248_){
_start:
{
size_t v_i_boxed_6249_; size_t v_stop_boxed_6250_; lean_object* v_res_6251_; 
v_i_boxed_6249_ = lean_unbox_usize(v_i_6239_);
lean_dec(v_i_6239_);
v_stop_boxed_6250_ = lean_unbox_usize(v_stop_6240_);
lean_dec(v_stop_6240_);
v_res_6251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(v_filter_6237_, v_as_6238_, v_i_boxed_6249_, v_stop_boxed_6250_, v_b_6241_, v___y_6242_, v___y_6243_, v___y_6244_, v___y_6245_, v___y_6246_, v___y_6247_);
lean_dec_ref(v___y_6246_);
lean_dec(v___y_6245_);
lean_dec(v___y_6244_);
lean_dec(v___y_6243_);
lean_dec_ref(v___y_6242_);
lean_dec_ref(v_as_6238_);
return v_res_6251_;
}
}
LEAN_EXPORT uint64_t l_Lake_buildO___lam__0(uint64_t v_ts_6252_, lean_object* v_t_6253_){
_start:
{
uint64_t v___x_6254_; uint64_t v___x_6255_; uint64_t v___x_6256_; uint64_t v___x_6257_; 
v___x_6254_ = l_Lake_Hash_nil;
v___x_6255_ = lean_string_hash(v_t_6253_);
v___x_6256_ = lean_uint64_mix_hash(v___x_6254_, v___x_6255_);
v___x_6257_ = lean_uint64_mix_hash(v_ts_6252_, v___x_6256_);
return v___x_6257_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__0___boxed(lean_object* v_ts_6258_, lean_object* v_t_6259_){
_start:
{
uint64_t v_ts_boxed_6260_; uint64_t v_res_6261_; lean_object* v_r_6262_; 
v_ts_boxed_6260_ = lean_unbox_uint64(v_ts_6258_);
lean_dec_ref(v_ts_6258_);
v_res_6261_ = l_Lake_buildO___lam__0(v_ts_boxed_6260_, v_t_6259_);
lean_dec_ref(v_t_6259_);
v_r_6262_ = lean_box_uint64(v_res_6261_);
return v_r_6262_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1(lean_object* v_oFile_6263_, lean_object* v_srcFile_6264_, lean_object* v___x_6265_, lean_object* v_compiler_6266_, lean_object* v___y_6267_, lean_object* v___y_6268_, lean_object* v___y_6269_, lean_object* v___y_6270_, lean_object* v___y_6271_, lean_object* v___y_6272_){
_start:
{
lean_object* v_log_6274_; uint8_t v_action_6275_; uint8_t v_wantsRebuild_6276_; lean_object* v_trace_6277_; lean_object* v_buildTime_6278_; lean_object* v___x_6280_; uint8_t v_isShared_6281_; uint8_t v_isSharedCheck_6307_; 
v_log_6274_ = lean_ctor_get(v___y_6272_, 0);
v_action_6275_ = lean_ctor_get_uint8(v___y_6272_, sizeof(void*)*3);
v_wantsRebuild_6276_ = lean_ctor_get_uint8(v___y_6272_, sizeof(void*)*3 + 1);
v_trace_6277_ = lean_ctor_get(v___y_6272_, 1);
v_buildTime_6278_ = lean_ctor_get(v___y_6272_, 2);
v_isSharedCheck_6307_ = !lean_is_exclusive(v___y_6272_);
if (v_isSharedCheck_6307_ == 0)
{
v___x_6280_ = v___y_6272_;
v_isShared_6281_ = v_isSharedCheck_6307_;
goto v_resetjp_6279_;
}
else
{
lean_inc(v_buildTime_6278_);
lean_inc(v_trace_6277_);
lean_inc(v_log_6274_);
lean_dec(v___y_6272_);
v___x_6280_ = lean_box(0);
v_isShared_6281_ = v_isSharedCheck_6307_;
goto v_resetjp_6279_;
}
v_resetjp_6279_:
{
lean_object* v___x_6282_; 
v___x_6282_ = l_Lake_compileO(v_oFile_6263_, v_srcFile_6264_, v___x_6265_, v_compiler_6266_, v_log_6274_);
if (lean_obj_tag(v___x_6282_) == 0)
{
lean_object* v_a_6283_; lean_object* v_a_6284_; lean_object* v___x_6286_; uint8_t v_isShared_6287_; uint8_t v_isSharedCheck_6294_; 
v_a_6283_ = lean_ctor_get(v___x_6282_, 0);
v_a_6284_ = lean_ctor_get(v___x_6282_, 1);
v_isSharedCheck_6294_ = !lean_is_exclusive(v___x_6282_);
if (v_isSharedCheck_6294_ == 0)
{
v___x_6286_ = v___x_6282_;
v_isShared_6287_ = v_isSharedCheck_6294_;
goto v_resetjp_6285_;
}
else
{
lean_inc(v_a_6284_);
lean_inc(v_a_6283_);
lean_dec(v___x_6282_);
v___x_6286_ = lean_box(0);
v_isShared_6287_ = v_isSharedCheck_6294_;
goto v_resetjp_6285_;
}
v_resetjp_6285_:
{
lean_object* v___x_6289_; 
if (v_isShared_6281_ == 0)
{
lean_ctor_set(v___x_6280_, 0, v_a_6284_);
v___x_6289_ = v___x_6280_;
goto v_reusejp_6288_;
}
else
{
lean_object* v_reuseFailAlloc_6293_; 
v_reuseFailAlloc_6293_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6293_, 0, v_a_6284_);
lean_ctor_set(v_reuseFailAlloc_6293_, 1, v_trace_6277_);
lean_ctor_set(v_reuseFailAlloc_6293_, 2, v_buildTime_6278_);
lean_ctor_set_uint8(v_reuseFailAlloc_6293_, sizeof(void*)*3, v_action_6275_);
lean_ctor_set_uint8(v_reuseFailAlloc_6293_, sizeof(void*)*3 + 1, v_wantsRebuild_6276_);
v___x_6289_ = v_reuseFailAlloc_6293_;
goto v_reusejp_6288_;
}
v_reusejp_6288_:
{
lean_object* v___x_6291_; 
if (v_isShared_6287_ == 0)
{
lean_ctor_set(v___x_6286_, 1, v___x_6289_);
v___x_6291_ = v___x_6286_;
goto v_reusejp_6290_;
}
else
{
lean_object* v_reuseFailAlloc_6292_; 
v_reuseFailAlloc_6292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6292_, 0, v_a_6283_);
lean_ctor_set(v_reuseFailAlloc_6292_, 1, v___x_6289_);
v___x_6291_ = v_reuseFailAlloc_6292_;
goto v_reusejp_6290_;
}
v_reusejp_6290_:
{
return v___x_6291_;
}
}
}
}
else
{
lean_object* v_a_6295_; lean_object* v_a_6296_; lean_object* v___x_6298_; uint8_t v_isShared_6299_; uint8_t v_isSharedCheck_6306_; 
v_a_6295_ = lean_ctor_get(v___x_6282_, 0);
v_a_6296_ = lean_ctor_get(v___x_6282_, 1);
v_isSharedCheck_6306_ = !lean_is_exclusive(v___x_6282_);
if (v_isSharedCheck_6306_ == 0)
{
v___x_6298_ = v___x_6282_;
v_isShared_6299_ = v_isSharedCheck_6306_;
goto v_resetjp_6297_;
}
else
{
lean_inc(v_a_6296_);
lean_inc(v_a_6295_);
lean_dec(v___x_6282_);
v___x_6298_ = lean_box(0);
v_isShared_6299_ = v_isSharedCheck_6306_;
goto v_resetjp_6297_;
}
v_resetjp_6297_:
{
lean_object* v___x_6301_; 
if (v_isShared_6281_ == 0)
{
lean_ctor_set(v___x_6280_, 0, v_a_6296_);
v___x_6301_ = v___x_6280_;
goto v_reusejp_6300_;
}
else
{
lean_object* v_reuseFailAlloc_6305_; 
v_reuseFailAlloc_6305_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6305_, 0, v_a_6296_);
lean_ctor_set(v_reuseFailAlloc_6305_, 1, v_trace_6277_);
lean_ctor_set(v_reuseFailAlloc_6305_, 2, v_buildTime_6278_);
lean_ctor_set_uint8(v_reuseFailAlloc_6305_, sizeof(void*)*3, v_action_6275_);
lean_ctor_set_uint8(v_reuseFailAlloc_6305_, sizeof(void*)*3 + 1, v_wantsRebuild_6276_);
v___x_6301_ = v_reuseFailAlloc_6305_;
goto v_reusejp_6300_;
}
v_reusejp_6300_:
{
lean_object* v___x_6303_; 
if (v_isShared_6299_ == 0)
{
lean_ctor_set(v___x_6298_, 1, v___x_6301_);
v___x_6303_ = v___x_6298_;
goto v_reusejp_6302_;
}
else
{
lean_object* v_reuseFailAlloc_6304_; 
v_reuseFailAlloc_6304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6304_, 0, v_a_6295_);
lean_ctor_set(v_reuseFailAlloc_6304_, 1, v___x_6301_);
v___x_6303_ = v_reuseFailAlloc_6304_;
goto v_reusejp_6302_;
}
v_reusejp_6302_:
{
return v___x_6303_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1___boxed(lean_object* v_oFile_6308_, lean_object* v_srcFile_6309_, lean_object* v___x_6310_, lean_object* v_compiler_6311_, lean_object* v___y_6312_, lean_object* v___y_6313_, lean_object* v___y_6314_, lean_object* v___y_6315_, lean_object* v___y_6316_, lean_object* v___y_6317_, lean_object* v___y_6318_){
_start:
{
lean_object* v_res_6319_; 
v_res_6319_ = l_Lake_buildO___lam__1(v_oFile_6308_, v_srcFile_6309_, v___x_6310_, v_compiler_6311_, v___y_6312_, v___y_6313_, v___y_6314_, v___y_6315_, v___y_6316_, v___y_6317_);
lean_dec_ref(v___y_6316_);
lean_dec(v___y_6315_);
lean_dec(v___y_6314_);
lean_dec(v___y_6313_);
lean_dec_ref(v___y_6312_);
lean_dec_ref(v___x_6310_);
return v_res_6319_;
}
}
static lean_object* _init_l_Lake_buildO___lam__2___boxed__const__1(void){
_start:
{
uint64_t v___x_6323_; lean_object* v___x_6324_; 
v___x_6323_ = l_Lake_Hash_nil;
v___x_6324_ = lean_box_uint64(v___x_6323_);
return v___x_6324_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2(lean_object* v_traceArgs_6325_, lean_object* v___f_6326_, lean_object* v_extraDepTrace_6327_, lean_object* v_weakArgs_6328_, lean_object* v_oFile_6329_, lean_object* v_compiler_6330_, lean_object* v___x_6331_, lean_object* v___f_6332_, lean_object* v_srcFile_6333_, lean_object* v___y_6334_, lean_object* v___y_6335_, lean_object* v___y_6336_, lean_object* v___y_6337_, lean_object* v___y_6338_, lean_object* v___y_6339_){
_start:
{
lean_object* v_log_6341_; uint8_t v_action_6342_; uint8_t v_wantsRebuild_6343_; lean_object* v_trace_6344_; lean_object* v_buildTime_6345_; lean_object* v___x_6347_; uint8_t v_isShared_6348_; uint8_t v_isSharedCheck_6430_; 
v_log_6341_ = lean_ctor_get(v___y_6339_, 0);
v_action_6342_ = lean_ctor_get_uint8(v___y_6339_, sizeof(void*)*3);
v_wantsRebuild_6343_ = lean_ctor_get_uint8(v___y_6339_, sizeof(void*)*3 + 1);
v_trace_6344_ = lean_ctor_get(v___y_6339_, 1);
v_buildTime_6345_ = lean_ctor_get(v___y_6339_, 2);
v_isSharedCheck_6430_ = !lean_is_exclusive(v___y_6339_);
if (v_isSharedCheck_6430_ == 0)
{
v___x_6347_ = v___y_6339_;
v_isShared_6348_ = v_isSharedCheck_6430_;
goto v_resetjp_6346_;
}
else
{
lean_inc(v_buildTime_6345_);
lean_inc(v_trace_6344_);
lean_inc(v_log_6341_);
lean_dec(v___y_6339_);
v___x_6347_ = lean_box(0);
v_isShared_6348_ = v_isSharedCheck_6430_;
goto v_resetjp_6346_;
}
v_resetjp_6346_:
{
lean_object* v___x_6349_; lean_object* v___x_6350_; uint64_t v___y_6352_; uint64_t v___x_6415_; lean_object* v___x_6416_; lean_object* v___x_6417_; uint8_t v___x_6418_; 
v___x_6349_ = l_Lake_platformTrace;
v___x_6350_ = l_Lake_BuildTrace_mix(v_trace_6344_, v___x_6349_);
v___x_6415_ = l_Lake_Hash_nil;
v___x_6416_ = lean_unsigned_to_nat(0u);
v___x_6417_ = lean_array_get_size(v_traceArgs_6325_);
v___x_6418_ = lean_nat_dec_lt(v___x_6416_, v___x_6417_);
if (v___x_6418_ == 0)
{
lean_dec_ref(v___f_6332_);
lean_dec_ref(v___x_6331_);
v___y_6352_ = v___x_6415_;
goto v___jp_6351_;
}
else
{
uint8_t v___x_6419_; 
v___x_6419_ = lean_nat_dec_le(v___x_6417_, v___x_6417_);
if (v___x_6419_ == 0)
{
if (v___x_6418_ == 0)
{
lean_dec_ref(v___f_6332_);
lean_dec_ref(v___x_6331_);
v___y_6352_ = v___x_6415_;
goto v___jp_6351_;
}
else
{
size_t v___x_6420_; size_t v___x_6421_; lean_object* v___x_6422_; lean_object* v___x_6423_; uint64_t v___x_6424_; 
v___x_6420_ = ((size_t)0ULL);
v___x_6421_ = lean_usize_of_nat(v___x_6417_);
v___x_6422_ = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(v_traceArgs_6325_);
v___x_6423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_6331_, v___f_6332_, v_traceArgs_6325_, v___x_6420_, v___x_6421_, v___x_6422_);
v___x_6424_ = lean_unbox_uint64(v___x_6423_);
lean_dec(v___x_6423_);
v___y_6352_ = v___x_6424_;
goto v___jp_6351_;
}
}
else
{
size_t v___x_6425_; size_t v___x_6426_; lean_object* v___x_6427_; lean_object* v___x_6428_; uint64_t v___x_6429_; 
v___x_6425_ = ((size_t)0ULL);
v___x_6426_ = lean_usize_of_nat(v___x_6417_);
v___x_6427_ = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(v_traceArgs_6325_);
v___x_6428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_6331_, v___f_6332_, v_traceArgs_6325_, v___x_6425_, v___x_6426_, v___x_6427_);
v___x_6429_ = lean_unbox_uint64(v___x_6428_);
lean_dec(v___x_6428_);
v___y_6352_ = v___x_6429_;
goto v___jp_6351_;
}
}
v___jp_6351_:
{
lean_object* v___x_6353_; lean_object* v___x_6354_; lean_object* v___x_6355_; lean_object* v___x_6356_; lean_object* v___x_6357_; lean_object* v___x_6358_; lean_object* v___x_6359_; lean_object* v___x_6360_; lean_object* v___x_6361_; lean_object* v___x_6362_; lean_object* v___x_6364_; 
v___x_6353_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_6354_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_6325_);
v___x_6355_ = lean_array_to_list(v_traceArgs_6325_);
v___x_6356_ = l_List_toString___redArg(v___f_6326_, v___x_6355_);
v___x_6357_ = lean_string_append(v___x_6354_, v___x_6356_);
lean_dec_ref(v___x_6356_);
v___x_6358_ = lean_string_append(v___x_6353_, v___x_6357_);
lean_dec_ref(v___x_6357_);
v___x_6359_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_6360_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_6361_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6361_, 0, v___x_6358_);
lean_ctor_set(v___x_6361_, 1, v___x_6359_);
lean_ctor_set(v___x_6361_, 2, v___x_6360_);
lean_ctor_set_uint64(v___x_6361_, sizeof(void*)*3, v___y_6352_);
v___x_6362_ = l_Lake_BuildTrace_mix(v___x_6350_, v___x_6361_);
if (v_isShared_6348_ == 0)
{
lean_ctor_set(v___x_6347_, 1, v___x_6362_);
v___x_6364_ = v___x_6347_;
goto v_reusejp_6363_;
}
else
{
lean_object* v_reuseFailAlloc_6414_; 
v_reuseFailAlloc_6414_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6414_, 0, v_log_6341_);
lean_ctor_set(v_reuseFailAlloc_6414_, 1, v___x_6362_);
lean_ctor_set(v_reuseFailAlloc_6414_, 2, v_buildTime_6345_);
lean_ctor_set_uint8(v_reuseFailAlloc_6414_, sizeof(void*)*3, v_action_6342_);
lean_ctor_set_uint8(v_reuseFailAlloc_6414_, sizeof(void*)*3 + 1, v_wantsRebuild_6343_);
v___x_6364_ = v_reuseFailAlloc_6414_;
goto v_reusejp_6363_;
}
v_reusejp_6363_:
{
lean_object* v___x_6365_; 
lean_inc_ref(v___y_6338_);
lean_inc(v___y_6337_);
lean_inc(v___y_6336_);
lean_inc(v___y_6335_);
lean_inc_ref(v___y_6334_);
v___x_6365_ = lean_apply_7(v_extraDepTrace_6327_, v___y_6334_, v___y_6335_, v___y_6336_, v___y_6337_, v___y_6338_, v___x_6364_, lean_box(0));
if (lean_obj_tag(v___x_6365_) == 0)
{
lean_object* v_a_6366_; lean_object* v_a_6367_; lean_object* v_log_6368_; uint8_t v_action_6369_; uint8_t v_wantsRebuild_6370_; lean_object* v_trace_6371_; lean_object* v_buildTime_6372_; lean_object* v___x_6374_; uint8_t v_isShared_6375_; uint8_t v_isSharedCheck_6404_; 
v_a_6366_ = lean_ctor_get(v___x_6365_, 1);
lean_inc(v_a_6366_);
v_a_6367_ = lean_ctor_get(v___x_6365_, 0);
lean_inc(v_a_6367_);
lean_dec_ref(v___x_6365_);
v_log_6368_ = lean_ctor_get(v_a_6366_, 0);
v_action_6369_ = lean_ctor_get_uint8(v_a_6366_, sizeof(void*)*3);
v_wantsRebuild_6370_ = lean_ctor_get_uint8(v_a_6366_, sizeof(void*)*3 + 1);
v_trace_6371_ = lean_ctor_get(v_a_6366_, 1);
v_buildTime_6372_ = lean_ctor_get(v_a_6366_, 2);
v_isSharedCheck_6404_ = !lean_is_exclusive(v_a_6366_);
if (v_isSharedCheck_6404_ == 0)
{
v___x_6374_ = v_a_6366_;
v_isShared_6375_ = v_isSharedCheck_6404_;
goto v_resetjp_6373_;
}
else
{
lean_inc(v_buildTime_6372_);
lean_inc(v_trace_6371_);
lean_inc(v_log_6368_);
lean_dec(v_a_6366_);
v___x_6374_ = lean_box(0);
v_isShared_6375_ = v_isSharedCheck_6404_;
goto v_resetjp_6373_;
}
v_resetjp_6373_:
{
lean_object* v___x_6376_; lean_object* v___x_6378_; 
v___x_6376_ = l_Lake_BuildTrace_mix(v_trace_6371_, v_a_6367_);
if (v_isShared_6375_ == 0)
{
lean_ctor_set(v___x_6374_, 1, v___x_6376_);
v___x_6378_ = v___x_6374_;
goto v_reusejp_6377_;
}
else
{
lean_object* v_reuseFailAlloc_6403_; 
v_reuseFailAlloc_6403_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6403_, 0, v_log_6368_);
lean_ctor_set(v_reuseFailAlloc_6403_, 1, v___x_6376_);
lean_ctor_set(v_reuseFailAlloc_6403_, 2, v_buildTime_6372_);
lean_ctor_set_uint8(v_reuseFailAlloc_6403_, sizeof(void*)*3, v_action_6369_);
lean_ctor_set_uint8(v_reuseFailAlloc_6403_, sizeof(void*)*3 + 1, v_wantsRebuild_6370_);
v___x_6378_ = v_reuseFailAlloc_6403_;
goto v_reusejp_6377_;
}
v_reusejp_6377_:
{
lean_object* v___x_6379_; lean_object* v___f_6380_; uint8_t v___x_6381_; lean_object* v___x_6382_; lean_object* v___x_6383_; 
v___x_6379_ = l_Array_append___redArg(v_weakArgs_6328_, v_traceArgs_6325_);
lean_dec_ref(v_traceArgs_6325_);
lean_inc_ref(v_oFile_6329_);
v___f_6380_ = lean_alloc_closure((void*)(l_Lake_buildO___lam__1___boxed), 11, 4);
lean_closure_set(v___f_6380_, 0, v_oFile_6329_);
lean_closure_set(v___f_6380_, 1, v_srcFile_6333_);
lean_closure_set(v___f_6380_, 2, v___x_6379_);
lean_closure_set(v___f_6380_, 3, v_compiler_6330_);
v___x_6381_ = 0;
v___x_6382_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
lean_inc(v___y_6335_);
v___x_6383_ = l_Lake_buildArtifactUnlessUpToDate(v_oFile_6329_, v___f_6380_, v___x_6381_, v___x_6382_, v___x_6381_, v___x_6381_, v___x_6381_, v___y_6334_, v___y_6335_, v___y_6336_, v___y_6337_, v___y_6338_, v___x_6378_);
if (lean_obj_tag(v___x_6383_) == 0)
{
lean_object* v_a_6384_; lean_object* v_a_6385_; lean_object* v___x_6387_; uint8_t v_isShared_6388_; uint8_t v_isSharedCheck_6393_; 
v_a_6384_ = lean_ctor_get(v___x_6383_, 0);
v_a_6385_ = lean_ctor_get(v___x_6383_, 1);
v_isSharedCheck_6393_ = !lean_is_exclusive(v___x_6383_);
if (v_isSharedCheck_6393_ == 0)
{
v___x_6387_ = v___x_6383_;
v_isShared_6388_ = v_isSharedCheck_6393_;
goto v_resetjp_6386_;
}
else
{
lean_inc(v_a_6385_);
lean_inc(v_a_6384_);
lean_dec(v___x_6383_);
v___x_6387_ = lean_box(0);
v_isShared_6388_ = v_isSharedCheck_6393_;
goto v_resetjp_6386_;
}
v_resetjp_6386_:
{
lean_object* v_path_6389_; lean_object* v___x_6391_; 
v_path_6389_ = lean_ctor_get(v_a_6384_, 1);
lean_inc_ref(v_path_6389_);
lean_dec(v_a_6384_);
if (v_isShared_6388_ == 0)
{
lean_ctor_set(v___x_6387_, 0, v_path_6389_);
v___x_6391_ = v___x_6387_;
goto v_reusejp_6390_;
}
else
{
lean_object* v_reuseFailAlloc_6392_; 
v_reuseFailAlloc_6392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6392_, 0, v_path_6389_);
lean_ctor_set(v_reuseFailAlloc_6392_, 1, v_a_6385_);
v___x_6391_ = v_reuseFailAlloc_6392_;
goto v_reusejp_6390_;
}
v_reusejp_6390_:
{
return v___x_6391_;
}
}
}
else
{
lean_object* v_a_6394_; lean_object* v_a_6395_; lean_object* v___x_6397_; uint8_t v_isShared_6398_; uint8_t v_isSharedCheck_6402_; 
v_a_6394_ = lean_ctor_get(v___x_6383_, 0);
v_a_6395_ = lean_ctor_get(v___x_6383_, 1);
v_isSharedCheck_6402_ = !lean_is_exclusive(v___x_6383_);
if (v_isSharedCheck_6402_ == 0)
{
v___x_6397_ = v___x_6383_;
v_isShared_6398_ = v_isSharedCheck_6402_;
goto v_resetjp_6396_;
}
else
{
lean_inc(v_a_6395_);
lean_inc(v_a_6394_);
lean_dec(v___x_6383_);
v___x_6397_ = lean_box(0);
v_isShared_6398_ = v_isSharedCheck_6402_;
goto v_resetjp_6396_;
}
v_resetjp_6396_:
{
lean_object* v___x_6400_; 
if (v_isShared_6398_ == 0)
{
v___x_6400_ = v___x_6397_;
goto v_reusejp_6399_;
}
else
{
lean_object* v_reuseFailAlloc_6401_; 
v_reuseFailAlloc_6401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6401_, 0, v_a_6394_);
lean_ctor_set(v_reuseFailAlloc_6401_, 1, v_a_6395_);
v___x_6400_ = v_reuseFailAlloc_6401_;
goto v_reusejp_6399_;
}
v_reusejp_6399_:
{
return v___x_6400_;
}
}
}
}
}
}
else
{
lean_object* v_a_6405_; lean_object* v_a_6406_; lean_object* v___x_6408_; uint8_t v_isShared_6409_; uint8_t v_isSharedCheck_6413_; 
lean_dec_ref(v___y_6334_);
lean_dec_ref(v_srcFile_6333_);
lean_dec_ref(v_compiler_6330_);
lean_dec_ref(v_oFile_6329_);
lean_dec_ref(v_weakArgs_6328_);
lean_dec_ref(v_traceArgs_6325_);
v_a_6405_ = lean_ctor_get(v___x_6365_, 0);
v_a_6406_ = lean_ctor_get(v___x_6365_, 1);
v_isSharedCheck_6413_ = !lean_is_exclusive(v___x_6365_);
if (v_isSharedCheck_6413_ == 0)
{
v___x_6408_ = v___x_6365_;
v_isShared_6409_ = v_isSharedCheck_6413_;
goto v_resetjp_6407_;
}
else
{
lean_inc(v_a_6406_);
lean_inc(v_a_6405_);
lean_dec(v___x_6365_);
v___x_6408_ = lean_box(0);
v_isShared_6409_ = v_isSharedCheck_6413_;
goto v_resetjp_6407_;
}
v_resetjp_6407_:
{
lean_object* v___x_6411_; 
if (v_isShared_6409_ == 0)
{
v___x_6411_ = v___x_6408_;
goto v_reusejp_6410_;
}
else
{
lean_object* v_reuseFailAlloc_6412_; 
v_reuseFailAlloc_6412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6412_, 0, v_a_6405_);
lean_ctor_set(v_reuseFailAlloc_6412_, 1, v_a_6406_);
v___x_6411_ = v_reuseFailAlloc_6412_;
goto v_reusejp_6410_;
}
v_reusejp_6410_:
{
return v___x_6411_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed(lean_object* v_traceArgs_6431_, lean_object* v___f_6432_, lean_object* v_extraDepTrace_6433_, lean_object* v_weakArgs_6434_, lean_object* v_oFile_6435_, lean_object* v_compiler_6436_, lean_object* v___x_6437_, lean_object* v___f_6438_, lean_object* v_srcFile_6439_, lean_object* v___y_6440_, lean_object* v___y_6441_, lean_object* v___y_6442_, lean_object* v___y_6443_, lean_object* v___y_6444_, lean_object* v___y_6445_, lean_object* v___y_6446_){
_start:
{
lean_object* v_res_6447_; 
v_res_6447_ = l_Lake_buildO___lam__2(v_traceArgs_6431_, v___f_6432_, v_extraDepTrace_6433_, v_weakArgs_6434_, v_oFile_6435_, v_compiler_6436_, v___x_6437_, v___f_6438_, v_srcFile_6439_, v___y_6440_, v___y_6441_, v___y_6442_, v___y_6443_, v___y_6444_, v___y_6445_);
lean_dec_ref(v___y_6444_);
lean_dec(v___y_6443_);
lean_dec(v___y_6442_);
lean_dec(v___y_6441_);
return v_res_6447_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object* v_oFile_6450_, lean_object* v_srcJob_6451_, lean_object* v_weakArgs_6452_, lean_object* v_traceArgs_6453_, lean_object* v_compiler_6454_, lean_object* v_extraDepTrace_6455_, lean_object* v_a_6456_, lean_object* v_a_6457_, lean_object* v_a_6458_, lean_object* v_a_6459_, lean_object* v_a_6460_, lean_object* v_a_6461_){
_start:
{
lean_object* v___f_6463_; lean_object* v___x_6464_; lean_object* v___f_6465_; lean_object* v___x_6466_; lean_object* v___f_6467_; lean_object* v___x_6468_; uint8_t v___x_6469_; lean_object* v___x_6470_; 
v___f_6463_ = ((lean_object*)(l_Lake_buildO___closed__0));
v___x_6464_ = l_Lake_instDataKindFilePath;
v___f_6465_ = ((lean_object*)(l_Lake_buildO___closed__1));
v___x_6466_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__9));
v___f_6467_ = lean_alloc_closure((void*)(l_Lake_buildO___lam__2___boxed), 16, 8);
lean_closure_set(v___f_6467_, 0, v_traceArgs_6453_);
lean_closure_set(v___f_6467_, 1, v___f_6465_);
lean_closure_set(v___f_6467_, 2, v_extraDepTrace_6455_);
lean_closure_set(v___f_6467_, 3, v_weakArgs_6452_);
lean_closure_set(v___f_6467_, 4, v_oFile_6450_);
lean_closure_set(v___f_6467_, 5, v_compiler_6454_);
lean_closure_set(v___f_6467_, 6, v___x_6466_);
lean_closure_set(v___f_6467_, 7, v___f_6463_);
v___x_6468_ = lean_unsigned_to_nat(0u);
v___x_6469_ = 0;
v___x_6470_ = l_Lake_Job_mapM___redArg(v___x_6464_, v_srcJob_6451_, v___f_6467_, v___x_6468_, v___x_6469_, v_a_6456_, v_a_6457_, v_a_6458_, v_a_6459_, v_a_6460_, v_a_6461_);
return v___x_6470_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___boxed(lean_object* v_oFile_6471_, lean_object* v_srcJob_6472_, lean_object* v_weakArgs_6473_, lean_object* v_traceArgs_6474_, lean_object* v_compiler_6475_, lean_object* v_extraDepTrace_6476_, lean_object* v_a_6477_, lean_object* v_a_6478_, lean_object* v_a_6479_, lean_object* v_a_6480_, lean_object* v_a_6481_, lean_object* v_a_6482_, lean_object* v_a_6483_){
_start:
{
lean_object* v_res_6484_; 
v_res_6484_ = l_Lake_buildO(v_oFile_6471_, v_srcJob_6472_, v_weakArgs_6473_, v_traceArgs_6474_, v_compiler_6475_, v_extraDepTrace_6476_, v_a_6477_, v_a_6478_, v_a_6479_, v_a_6480_, v_a_6481_, v_a_6482_);
lean_dec_ref(v_a_6482_);
lean_dec_ref(v_a_6481_);
lean_dec(v_a_6480_);
lean_dec(v_a_6479_);
lean_dec(v_a_6478_);
return v_res_6484_;
}
}
static lean_object* _init_l_Lake_buildLeanO___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6486_; lean_object* v___x_6487_; lean_object* v___x_6488_; lean_object* v___x_6489_; 
v___x_6486_ = ((lean_object*)(l_Lake_buildLeanO___lam__0___closed__0));
v___x_6487_ = lean_unsigned_to_nat(2u);
v___x_6488_ = lean_mk_empty_array_with_capacity(v___x_6487_);
v___x_6489_ = lean_array_push(v___x_6488_, v___x_6486_);
return v___x_6489_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0(lean_object* v_weakArgs_6490_, lean_object* v_traceArgs_6491_, lean_object* v_oFile_6492_, lean_object* v_srcFile_6493_, lean_object* v_leanIncludeDir_x3f_6494_, lean_object* v___y_6495_, lean_object* v___y_6496_, lean_object* v___y_6497_, lean_object* v___y_6498_, lean_object* v___y_6499_, lean_object* v___y_6500_){
_start:
{
lean_object* v_toContext_6502_; lean_object* v_lakeEnv_6503_; lean_object* v_log_6504_; uint8_t v_action_6505_; uint8_t v_wantsRebuild_6506_; lean_object* v_trace_6507_; lean_object* v_buildTime_6508_; lean_object* v___x_6510_; uint8_t v_isShared_6511_; uint8_t v_isSharedCheck_6549_; 
v_toContext_6502_ = lean_ctor_get(v___y_6499_, 1);
lean_inc(v_toContext_6502_);
lean_dec_ref(v___y_6499_);
v_lakeEnv_6503_ = lean_ctor_get(v_toContext_6502_, 1);
lean_inc_ref(v_lakeEnv_6503_);
lean_dec(v_toContext_6502_);
v_log_6504_ = lean_ctor_get(v___y_6500_, 0);
v_action_6505_ = lean_ctor_get_uint8(v___y_6500_, sizeof(void*)*3);
v_wantsRebuild_6506_ = lean_ctor_get_uint8(v___y_6500_, sizeof(void*)*3 + 1);
v_trace_6507_ = lean_ctor_get(v___y_6500_, 1);
v_buildTime_6508_ = lean_ctor_get(v___y_6500_, 2);
v_isSharedCheck_6549_ = !lean_is_exclusive(v___y_6500_);
if (v_isSharedCheck_6549_ == 0)
{
v___x_6510_ = v___y_6500_;
v_isShared_6511_ = v_isSharedCheck_6549_;
goto v_resetjp_6509_;
}
else
{
lean_inc(v_buildTime_6508_);
lean_inc(v_trace_6507_);
lean_inc(v_log_6504_);
lean_dec(v___y_6500_);
v___x_6510_ = lean_box(0);
v_isShared_6511_ = v_isSharedCheck_6549_;
goto v_resetjp_6509_;
}
v_resetjp_6509_:
{
lean_object* v_lean_6512_; lean_object* v___y_6514_; 
v_lean_6512_ = lean_ctor_get(v_lakeEnv_6503_, 1);
lean_inc_ref(v_lean_6512_);
lean_dec_ref(v_lakeEnv_6503_);
if (lean_obj_tag(v_leanIncludeDir_x3f_6494_) == 0)
{
lean_object* v_includeDir_6547_; 
v_includeDir_6547_ = lean_ctor_get(v_lean_6512_, 4);
lean_inc_ref(v_includeDir_6547_);
v___y_6514_ = v_includeDir_6547_;
goto v___jp_6513_;
}
else
{
lean_object* v_val_6548_; 
v_val_6548_ = lean_ctor_get(v_leanIncludeDir_x3f_6494_, 0);
lean_inc(v_val_6548_);
lean_dec_ref(v_leanIncludeDir_x3f_6494_);
v___y_6514_ = v_val_6548_;
goto v___jp_6513_;
}
v___jp_6513_:
{
lean_object* v_cc_6515_; lean_object* v_ccFlags_6516_; lean_object* v___x_6517_; lean_object* v___x_6518_; lean_object* v___x_6519_; lean_object* v___x_6520_; lean_object* v___x_6521_; lean_object* v___x_6522_; 
v_cc_6515_ = lean_ctor_get(v_lean_6512_, 14);
lean_inc_ref(v_cc_6515_);
v_ccFlags_6516_ = lean_ctor_get(v_lean_6512_, 18);
lean_inc_ref(v_ccFlags_6516_);
lean_dec_ref(v_lean_6512_);
v___x_6517_ = lean_obj_once(&l_Lake_buildLeanO___lam__0___closed__1, &l_Lake_buildLeanO___lam__0___closed__1_once, _init_l_Lake_buildLeanO___lam__0___closed__1);
v___x_6518_ = lean_array_push(v___x_6517_, v___y_6514_);
v___x_6519_ = l_Array_append___redArg(v___x_6518_, v_ccFlags_6516_);
lean_dec_ref(v_ccFlags_6516_);
v___x_6520_ = l_Array_append___redArg(v___x_6519_, v_weakArgs_6490_);
v___x_6521_ = l_Array_append___redArg(v___x_6520_, v_traceArgs_6491_);
v___x_6522_ = l_Lake_compileO(v_oFile_6492_, v_srcFile_6493_, v___x_6521_, v_cc_6515_, v_log_6504_);
lean_dec_ref(v___x_6521_);
if (lean_obj_tag(v___x_6522_) == 0)
{
lean_object* v_a_6523_; lean_object* v_a_6524_; lean_object* v___x_6526_; uint8_t v_isShared_6527_; uint8_t v_isSharedCheck_6534_; 
v_a_6523_ = lean_ctor_get(v___x_6522_, 0);
v_a_6524_ = lean_ctor_get(v___x_6522_, 1);
v_isSharedCheck_6534_ = !lean_is_exclusive(v___x_6522_);
if (v_isSharedCheck_6534_ == 0)
{
v___x_6526_ = v___x_6522_;
v_isShared_6527_ = v_isSharedCheck_6534_;
goto v_resetjp_6525_;
}
else
{
lean_inc(v_a_6524_);
lean_inc(v_a_6523_);
lean_dec(v___x_6522_);
v___x_6526_ = lean_box(0);
v_isShared_6527_ = v_isSharedCheck_6534_;
goto v_resetjp_6525_;
}
v_resetjp_6525_:
{
lean_object* v___x_6529_; 
if (v_isShared_6511_ == 0)
{
lean_ctor_set(v___x_6510_, 0, v_a_6524_);
v___x_6529_ = v___x_6510_;
goto v_reusejp_6528_;
}
else
{
lean_object* v_reuseFailAlloc_6533_; 
v_reuseFailAlloc_6533_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6533_, 0, v_a_6524_);
lean_ctor_set(v_reuseFailAlloc_6533_, 1, v_trace_6507_);
lean_ctor_set(v_reuseFailAlloc_6533_, 2, v_buildTime_6508_);
lean_ctor_set_uint8(v_reuseFailAlloc_6533_, sizeof(void*)*3, v_action_6505_);
lean_ctor_set_uint8(v_reuseFailAlloc_6533_, sizeof(void*)*3 + 1, v_wantsRebuild_6506_);
v___x_6529_ = v_reuseFailAlloc_6533_;
goto v_reusejp_6528_;
}
v_reusejp_6528_:
{
lean_object* v___x_6531_; 
if (v_isShared_6527_ == 0)
{
lean_ctor_set(v___x_6526_, 1, v___x_6529_);
v___x_6531_ = v___x_6526_;
goto v_reusejp_6530_;
}
else
{
lean_object* v_reuseFailAlloc_6532_; 
v_reuseFailAlloc_6532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6532_, 0, v_a_6523_);
lean_ctor_set(v_reuseFailAlloc_6532_, 1, v___x_6529_);
v___x_6531_ = v_reuseFailAlloc_6532_;
goto v_reusejp_6530_;
}
v_reusejp_6530_:
{
return v___x_6531_;
}
}
}
}
else
{
lean_object* v_a_6535_; lean_object* v_a_6536_; lean_object* v___x_6538_; uint8_t v_isShared_6539_; uint8_t v_isSharedCheck_6546_; 
v_a_6535_ = lean_ctor_get(v___x_6522_, 0);
v_a_6536_ = lean_ctor_get(v___x_6522_, 1);
v_isSharedCheck_6546_ = !lean_is_exclusive(v___x_6522_);
if (v_isSharedCheck_6546_ == 0)
{
v___x_6538_ = v___x_6522_;
v_isShared_6539_ = v_isSharedCheck_6546_;
goto v_resetjp_6537_;
}
else
{
lean_inc(v_a_6536_);
lean_inc(v_a_6535_);
lean_dec(v___x_6522_);
v___x_6538_ = lean_box(0);
v_isShared_6539_ = v_isSharedCheck_6546_;
goto v_resetjp_6537_;
}
v_resetjp_6537_:
{
lean_object* v___x_6541_; 
if (v_isShared_6511_ == 0)
{
lean_ctor_set(v___x_6510_, 0, v_a_6536_);
v___x_6541_ = v___x_6510_;
goto v_reusejp_6540_;
}
else
{
lean_object* v_reuseFailAlloc_6545_; 
v_reuseFailAlloc_6545_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6545_, 0, v_a_6536_);
lean_ctor_set(v_reuseFailAlloc_6545_, 1, v_trace_6507_);
lean_ctor_set(v_reuseFailAlloc_6545_, 2, v_buildTime_6508_);
lean_ctor_set_uint8(v_reuseFailAlloc_6545_, sizeof(void*)*3, v_action_6505_);
lean_ctor_set_uint8(v_reuseFailAlloc_6545_, sizeof(void*)*3 + 1, v_wantsRebuild_6506_);
v___x_6541_ = v_reuseFailAlloc_6545_;
goto v_reusejp_6540_;
}
v_reusejp_6540_:
{
lean_object* v___x_6543_; 
if (v_isShared_6539_ == 0)
{
lean_ctor_set(v___x_6538_, 1, v___x_6541_);
v___x_6543_ = v___x_6538_;
goto v_reusejp_6542_;
}
else
{
lean_object* v_reuseFailAlloc_6544_; 
v_reuseFailAlloc_6544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6544_, 0, v_a_6535_);
lean_ctor_set(v_reuseFailAlloc_6544_, 1, v___x_6541_);
v___x_6543_ = v_reuseFailAlloc_6544_;
goto v_reusejp_6542_;
}
v_reusejp_6542_:
{
return v___x_6543_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0___boxed(lean_object* v_weakArgs_6550_, lean_object* v_traceArgs_6551_, lean_object* v_oFile_6552_, lean_object* v_srcFile_6553_, lean_object* v_leanIncludeDir_x3f_6554_, lean_object* v___y_6555_, lean_object* v___y_6556_, lean_object* v___y_6557_, lean_object* v___y_6558_, lean_object* v___y_6559_, lean_object* v___y_6560_, lean_object* v___y_6561_){
_start:
{
lean_object* v_res_6562_; 
v_res_6562_ = l_Lake_buildLeanO___lam__0(v_weakArgs_6550_, v_traceArgs_6551_, v_oFile_6552_, v_srcFile_6553_, v_leanIncludeDir_x3f_6554_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_, v___y_6559_, v___y_6560_);
lean_dec(v___y_6558_);
lean_dec(v___y_6557_);
lean_dec(v___y_6556_);
lean_dec_ref(v___y_6555_);
lean_dec_ref(v_traceArgs_6551_);
lean_dec_ref(v_weakArgs_6550_);
return v_res_6562_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(lean_object* v_as_6563_, size_t v_i_6564_, size_t v_stop_6565_, uint64_t v_b_6566_){
_start:
{
uint8_t v___x_6567_; 
v___x_6567_ = lean_usize_dec_eq(v_i_6564_, v_stop_6565_);
if (v___x_6567_ == 0)
{
lean_object* v___x_6568_; uint64_t v___x_6569_; uint64_t v___x_6570_; uint64_t v___x_6571_; uint64_t v___x_6572_; size_t v___x_6573_; size_t v___x_6574_; 
v___x_6568_ = lean_array_uget_borrowed(v_as_6563_, v_i_6564_);
v___x_6569_ = l_Lake_Hash_nil;
v___x_6570_ = lean_string_hash(v___x_6568_);
v___x_6571_ = lean_uint64_mix_hash(v___x_6569_, v___x_6570_);
v___x_6572_ = lean_uint64_mix_hash(v_b_6566_, v___x_6571_);
v___x_6573_ = ((size_t)1ULL);
v___x_6574_ = lean_usize_add(v_i_6564_, v___x_6573_);
v_i_6564_ = v___x_6574_;
v_b_6566_ = v___x_6572_;
goto _start;
}
else
{
return v_b_6566_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1___boxed(lean_object* v_as_6576_, lean_object* v_i_6577_, lean_object* v_stop_6578_, lean_object* v_b_6579_){
_start:
{
size_t v_i_boxed_6580_; size_t v_stop_boxed_6581_; uint64_t v_b_boxed_6582_; uint64_t v_res_6583_; lean_object* v_r_6584_; 
v_i_boxed_6580_ = lean_unbox_usize(v_i_6577_);
lean_dec(v_i_6577_);
v_stop_boxed_6581_ = lean_unbox_usize(v_stop_6578_);
lean_dec(v_stop_6578_);
v_b_boxed_6582_ = lean_unbox_uint64(v_b_6579_);
lean_dec_ref(v_b_6579_);
v_res_6583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_as_6576_, v_i_boxed_6580_, v_stop_boxed_6581_, v_b_boxed_6582_);
lean_dec_ref(v_as_6576_);
v_r_6584_ = lean_box_uint64(v_res_6583_);
return v_r_6584_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(lean_object* v_x_6586_, lean_object* v_x_6587_){
_start:
{
if (lean_obj_tag(v_x_6587_) == 0)
{
return v_x_6586_;
}
else
{
lean_object* v_head_6588_; lean_object* v_tail_6589_; lean_object* v___x_6590_; lean_object* v___x_6591_; lean_object* v___x_6592_; 
v_head_6588_ = lean_ctor_get(v_x_6587_, 0);
v_tail_6589_ = lean_ctor_get(v_x_6587_, 1);
v___x_6590_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0));
v___x_6591_ = lean_string_append(v_x_6586_, v___x_6590_);
v___x_6592_ = lean_string_append(v___x_6591_, v_head_6588_);
v_x_6586_ = v___x_6592_;
v_x_6587_ = v_tail_6589_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___boxed(lean_object* v_x_6594_, lean_object* v_x_6595_){
_start:
{
lean_object* v_res_6596_; 
v_res_6596_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(v_x_6594_, v_x_6595_);
lean_dec(v_x_6595_);
return v_res_6596_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0(lean_object* v_x_6600_){
_start:
{
if (lean_obj_tag(v_x_6600_) == 0)
{
lean_object* v___x_6601_; 
v___x_6601_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0));
return v___x_6601_;
}
else
{
lean_object* v_tail_6602_; 
v_tail_6602_ = lean_ctor_get(v_x_6600_, 1);
if (lean_obj_tag(v_tail_6602_) == 0)
{
lean_object* v_head_6603_; lean_object* v___x_6604_; lean_object* v___x_6605_; lean_object* v___x_6606_; lean_object* v___x_6607_; 
v_head_6603_ = lean_ctor_get(v_x_6600_, 0);
v___x_6604_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1));
v___x_6605_ = lean_string_append(v___x_6604_, v_head_6603_);
v___x_6606_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2));
v___x_6607_ = lean_string_append(v___x_6605_, v___x_6606_);
return v___x_6607_;
}
else
{
lean_object* v_head_6608_; lean_object* v___x_6609_; lean_object* v___x_6610_; lean_object* v___x_6611_; uint32_t v___x_6612_; lean_object* v___x_6613_; 
v_head_6608_ = lean_ctor_get(v_x_6600_, 0);
v___x_6609_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1));
v___x_6610_ = lean_string_append(v___x_6609_, v_head_6608_);
v___x_6611_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(v___x_6610_, v_tail_6602_);
v___x_6612_ = 93;
v___x_6613_ = lean_string_push(v___x_6611_, v___x_6612_);
return v___x_6613_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___boxed(lean_object* v_x_6614_){
_start:
{
lean_object* v_res_6615_; 
v_res_6615_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v_x_6614_);
lean_dec(v_x_6614_);
return v_res_6615_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1(lean_object* v_weakArgs_6616_, lean_object* v_traceArgs_6617_, lean_object* v_oFile_6618_, lean_object* v_leanIncludeDir_x3f_6619_, lean_object* v_srcFile_6620_, lean_object* v___y_6621_, lean_object* v___y_6622_, lean_object* v___y_6623_, lean_object* v___y_6624_, lean_object* v___y_6625_, lean_object* v___y_6626_){
_start:
{
lean_object* v_log_6628_; uint8_t v_action_6629_; uint8_t v_wantsRebuild_6630_; lean_object* v_trace_6631_; lean_object* v_buildTime_6632_; lean_object* v___x_6634_; uint8_t v_isShared_6635_; uint8_t v_isSharedCheck_6689_; 
v_log_6628_ = lean_ctor_get(v___y_6626_, 0);
v_action_6629_ = lean_ctor_get_uint8(v___y_6626_, sizeof(void*)*3);
v_wantsRebuild_6630_ = lean_ctor_get_uint8(v___y_6626_, sizeof(void*)*3 + 1);
v_trace_6631_ = lean_ctor_get(v___y_6626_, 1);
v_buildTime_6632_ = lean_ctor_get(v___y_6626_, 2);
v_isSharedCheck_6689_ = !lean_is_exclusive(v___y_6626_);
if (v_isSharedCheck_6689_ == 0)
{
v___x_6634_ = v___y_6626_;
v_isShared_6635_ = v_isSharedCheck_6689_;
goto v_resetjp_6633_;
}
else
{
lean_inc(v_buildTime_6632_);
lean_inc(v_trace_6631_);
lean_inc(v_log_6628_);
lean_dec(v___y_6626_);
v___x_6634_ = lean_box(0);
v_isShared_6635_ = v_isSharedCheck_6689_;
goto v_resetjp_6633_;
}
v_resetjp_6633_:
{
lean_object* v_leanTrace_6636_; lean_object* v___f_6637_; lean_object* v___x_6638_; uint64_t v___y_6640_; uint64_t v___x_6678_; lean_object* v___x_6679_; lean_object* v___x_6680_; uint8_t v___x_6681_; 
v_leanTrace_6636_ = lean_ctor_get(v___y_6625_, 2);
lean_inc_ref(v_oFile_6618_);
lean_inc_ref(v_traceArgs_6617_);
v___f_6637_ = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__0___boxed), 12, 5);
lean_closure_set(v___f_6637_, 0, v_weakArgs_6616_);
lean_closure_set(v___f_6637_, 1, v_traceArgs_6617_);
lean_closure_set(v___f_6637_, 2, v_oFile_6618_);
lean_closure_set(v___f_6637_, 3, v_srcFile_6620_);
lean_closure_set(v___f_6637_, 4, v_leanIncludeDir_x3f_6619_);
lean_inc_ref(v_leanTrace_6636_);
v___x_6638_ = l_Lake_BuildTrace_mix(v_trace_6631_, v_leanTrace_6636_);
v___x_6678_ = l_Lake_Hash_nil;
v___x_6679_ = lean_unsigned_to_nat(0u);
v___x_6680_ = lean_array_get_size(v_traceArgs_6617_);
v___x_6681_ = lean_nat_dec_lt(v___x_6679_, v___x_6680_);
if (v___x_6681_ == 0)
{
v___y_6640_ = v___x_6678_;
goto v___jp_6639_;
}
else
{
uint8_t v___x_6682_; 
v___x_6682_ = lean_nat_dec_le(v___x_6680_, v___x_6680_);
if (v___x_6682_ == 0)
{
if (v___x_6681_ == 0)
{
v___y_6640_ = v___x_6678_;
goto v___jp_6639_;
}
else
{
size_t v___x_6683_; size_t v___x_6684_; uint64_t v___x_6685_; 
v___x_6683_ = ((size_t)0ULL);
v___x_6684_ = lean_usize_of_nat(v___x_6680_);
v___x_6685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_6617_, v___x_6683_, v___x_6684_, v___x_6678_);
v___y_6640_ = v___x_6685_;
goto v___jp_6639_;
}
}
else
{
size_t v___x_6686_; size_t v___x_6687_; uint64_t v___x_6688_; 
v___x_6686_ = ((size_t)0ULL);
v___x_6687_ = lean_usize_of_nat(v___x_6680_);
v___x_6688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_6617_, v___x_6686_, v___x_6687_, v___x_6678_);
v___y_6640_ = v___x_6688_;
goto v___jp_6639_;
}
}
v___jp_6639_:
{
lean_object* v___x_6641_; lean_object* v___x_6642_; lean_object* v___x_6643_; lean_object* v___x_6644_; lean_object* v___x_6645_; lean_object* v___x_6646_; lean_object* v___x_6647_; lean_object* v___x_6648_; lean_object* v___x_6649_; lean_object* v___x_6650_; lean_object* v___x_6651_; lean_object* v___x_6652_; lean_object* v___x_6654_; 
v___x_6641_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_6642_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_6643_ = lean_array_to_list(v_traceArgs_6617_);
v___x_6644_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_6643_);
lean_dec(v___x_6643_);
v___x_6645_ = lean_string_append(v___x_6642_, v___x_6644_);
lean_dec_ref(v___x_6644_);
v___x_6646_ = lean_string_append(v___x_6641_, v___x_6645_);
lean_dec_ref(v___x_6645_);
v___x_6647_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_6648_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_6649_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6649_, 0, v___x_6646_);
lean_ctor_set(v___x_6649_, 1, v___x_6647_);
lean_ctor_set(v___x_6649_, 2, v___x_6648_);
lean_ctor_set_uint64(v___x_6649_, sizeof(void*)*3, v___y_6640_);
v___x_6650_ = l_Lake_BuildTrace_mix(v___x_6638_, v___x_6649_);
v___x_6651_ = l_Lake_platformTrace;
v___x_6652_ = l_Lake_BuildTrace_mix(v___x_6650_, v___x_6651_);
if (v_isShared_6635_ == 0)
{
lean_ctor_set(v___x_6634_, 1, v___x_6652_);
v___x_6654_ = v___x_6634_;
goto v_reusejp_6653_;
}
else
{
lean_object* v_reuseFailAlloc_6677_; 
v_reuseFailAlloc_6677_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6677_, 0, v_log_6628_);
lean_ctor_set(v_reuseFailAlloc_6677_, 1, v___x_6652_);
lean_ctor_set(v_reuseFailAlloc_6677_, 2, v_buildTime_6632_);
lean_ctor_set_uint8(v_reuseFailAlloc_6677_, sizeof(void*)*3, v_action_6629_);
lean_ctor_set_uint8(v_reuseFailAlloc_6677_, sizeof(void*)*3 + 1, v_wantsRebuild_6630_);
v___x_6654_ = v_reuseFailAlloc_6677_;
goto v_reusejp_6653_;
}
v_reusejp_6653_:
{
uint8_t v___x_6655_; lean_object* v___x_6656_; lean_object* v___x_6657_; 
v___x_6655_ = 0;
v___x_6656_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
lean_inc(v___y_6622_);
v___x_6657_ = l_Lake_buildArtifactUnlessUpToDate(v_oFile_6618_, v___f_6637_, v___x_6655_, v___x_6656_, v___x_6655_, v___x_6655_, v___x_6655_, v___y_6621_, v___y_6622_, v___y_6623_, v___y_6624_, v___y_6625_, v___x_6654_);
lean_dec_ref(v___y_6625_);
if (lean_obj_tag(v___x_6657_) == 0)
{
lean_object* v_a_6658_; lean_object* v_a_6659_; lean_object* v___x_6661_; uint8_t v_isShared_6662_; uint8_t v_isSharedCheck_6667_; 
v_a_6658_ = lean_ctor_get(v___x_6657_, 0);
v_a_6659_ = lean_ctor_get(v___x_6657_, 1);
v_isSharedCheck_6667_ = !lean_is_exclusive(v___x_6657_);
if (v_isSharedCheck_6667_ == 0)
{
v___x_6661_ = v___x_6657_;
v_isShared_6662_ = v_isSharedCheck_6667_;
goto v_resetjp_6660_;
}
else
{
lean_inc(v_a_6659_);
lean_inc(v_a_6658_);
lean_dec(v___x_6657_);
v___x_6661_ = lean_box(0);
v_isShared_6662_ = v_isSharedCheck_6667_;
goto v_resetjp_6660_;
}
v_resetjp_6660_:
{
lean_object* v_path_6663_; lean_object* v___x_6665_; 
v_path_6663_ = lean_ctor_get(v_a_6658_, 1);
lean_inc_ref(v_path_6663_);
lean_dec(v_a_6658_);
if (v_isShared_6662_ == 0)
{
lean_ctor_set(v___x_6661_, 0, v_path_6663_);
v___x_6665_ = v___x_6661_;
goto v_reusejp_6664_;
}
else
{
lean_object* v_reuseFailAlloc_6666_; 
v_reuseFailAlloc_6666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6666_, 0, v_path_6663_);
lean_ctor_set(v_reuseFailAlloc_6666_, 1, v_a_6659_);
v___x_6665_ = v_reuseFailAlloc_6666_;
goto v_reusejp_6664_;
}
v_reusejp_6664_:
{
return v___x_6665_;
}
}
}
else
{
lean_object* v_a_6668_; lean_object* v_a_6669_; lean_object* v___x_6671_; uint8_t v_isShared_6672_; uint8_t v_isSharedCheck_6676_; 
v_a_6668_ = lean_ctor_get(v___x_6657_, 0);
v_a_6669_ = lean_ctor_get(v___x_6657_, 1);
v_isSharedCheck_6676_ = !lean_is_exclusive(v___x_6657_);
if (v_isSharedCheck_6676_ == 0)
{
v___x_6671_ = v___x_6657_;
v_isShared_6672_ = v_isSharedCheck_6676_;
goto v_resetjp_6670_;
}
else
{
lean_inc(v_a_6669_);
lean_inc(v_a_6668_);
lean_dec(v___x_6657_);
v___x_6671_ = lean_box(0);
v_isShared_6672_ = v_isSharedCheck_6676_;
goto v_resetjp_6670_;
}
v_resetjp_6670_:
{
lean_object* v___x_6674_; 
if (v_isShared_6672_ == 0)
{
v___x_6674_ = v___x_6671_;
goto v_reusejp_6673_;
}
else
{
lean_object* v_reuseFailAlloc_6675_; 
v_reuseFailAlloc_6675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6675_, 0, v_a_6668_);
lean_ctor_set(v_reuseFailAlloc_6675_, 1, v_a_6669_);
v___x_6674_ = v_reuseFailAlloc_6675_;
goto v_reusejp_6673_;
}
v_reusejp_6673_:
{
return v___x_6674_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1___boxed(lean_object* v_weakArgs_6690_, lean_object* v_traceArgs_6691_, lean_object* v_oFile_6692_, lean_object* v_leanIncludeDir_x3f_6693_, lean_object* v_srcFile_6694_, lean_object* v___y_6695_, lean_object* v___y_6696_, lean_object* v___y_6697_, lean_object* v___y_6698_, lean_object* v___y_6699_, lean_object* v___y_6700_, lean_object* v___y_6701_){
_start:
{
lean_object* v_res_6702_; 
v_res_6702_ = l_Lake_buildLeanO___lam__1(v_weakArgs_6690_, v_traceArgs_6691_, v_oFile_6692_, v_leanIncludeDir_x3f_6693_, v_srcFile_6694_, v___y_6695_, v___y_6696_, v___y_6697_, v___y_6698_, v___y_6699_, v___y_6700_);
lean_dec(v___y_6698_);
lean_dec(v___y_6697_);
lean_dec(v___y_6696_);
return v_res_6702_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object* v_oFile_6703_, lean_object* v_srcJob_6704_, lean_object* v_weakArgs_6705_, lean_object* v_traceArgs_6706_, lean_object* v_leanIncludeDir_x3f_6707_, lean_object* v_a_6708_, lean_object* v_a_6709_, lean_object* v_a_6710_, lean_object* v_a_6711_, lean_object* v_a_6712_, lean_object* v_a_6713_){
_start:
{
lean_object* v___f_6715_; lean_object* v___x_6716_; lean_object* v___x_6717_; uint8_t v___x_6718_; lean_object* v___x_6719_; 
v___f_6715_ = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__1___boxed), 12, 4);
lean_closure_set(v___f_6715_, 0, v_weakArgs_6705_);
lean_closure_set(v___f_6715_, 1, v_traceArgs_6706_);
lean_closure_set(v___f_6715_, 2, v_oFile_6703_);
lean_closure_set(v___f_6715_, 3, v_leanIncludeDir_x3f_6707_);
v___x_6716_ = l_Lake_instDataKindFilePath;
v___x_6717_ = lean_unsigned_to_nat(0u);
v___x_6718_ = 0;
v___x_6719_ = l_Lake_Job_mapM___redArg(v___x_6716_, v_srcJob_6704_, v___f_6715_, v___x_6717_, v___x_6718_, v_a_6708_, v_a_6709_, v_a_6710_, v_a_6711_, v_a_6712_, v_a_6713_);
return v___x_6719_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___boxed(lean_object* v_oFile_6720_, lean_object* v_srcJob_6721_, lean_object* v_weakArgs_6722_, lean_object* v_traceArgs_6723_, lean_object* v_leanIncludeDir_x3f_6724_, lean_object* v_a_6725_, lean_object* v_a_6726_, lean_object* v_a_6727_, lean_object* v_a_6728_, lean_object* v_a_6729_, lean_object* v_a_6730_, lean_object* v_a_6731_){
_start:
{
lean_object* v_res_6732_; 
v_res_6732_ = l_Lake_buildLeanO(v_oFile_6720_, v_srcJob_6721_, v_weakArgs_6722_, v_traceArgs_6723_, v_leanIncludeDir_x3f_6724_, v_a_6725_, v_a_6726_, v_a_6727_, v_a_6728_, v_a_6729_, v_a_6730_);
lean_dec_ref(v_a_6730_);
lean_dec_ref(v_a_6729_);
lean_dec(v_a_6728_);
lean_dec(v_a_6727_);
lean_dec(v_a_6726_);
return v_res_6732_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0(lean_object* v_libFile_6733_, lean_object* v_oFiles_6734_, uint8_t v_thin_6735_, lean_object* v___y_6736_, lean_object* v___y_6737_, lean_object* v___y_6738_, lean_object* v___y_6739_, lean_object* v___y_6740_, lean_object* v___y_6741_){
_start:
{
lean_object* v_toContext_6743_; lean_object* v_lakeEnv_6744_; lean_object* v_lean_6745_; lean_object* v_log_6746_; uint8_t v_action_6747_; uint8_t v_wantsRebuild_6748_; lean_object* v_trace_6749_; lean_object* v_buildTime_6750_; lean_object* v___x_6752_; uint8_t v_isShared_6753_; uint8_t v_isSharedCheck_6780_; 
v_toContext_6743_ = lean_ctor_get(v___y_6740_, 1);
lean_inc(v_toContext_6743_);
lean_dec_ref(v___y_6740_);
v_lakeEnv_6744_ = lean_ctor_get(v_toContext_6743_, 1);
lean_inc_ref(v_lakeEnv_6744_);
lean_dec(v_toContext_6743_);
v_lean_6745_ = lean_ctor_get(v_lakeEnv_6744_, 1);
lean_inc_ref(v_lean_6745_);
lean_dec_ref(v_lakeEnv_6744_);
v_log_6746_ = lean_ctor_get(v___y_6741_, 0);
v_action_6747_ = lean_ctor_get_uint8(v___y_6741_, sizeof(void*)*3);
v_wantsRebuild_6748_ = lean_ctor_get_uint8(v___y_6741_, sizeof(void*)*3 + 1);
v_trace_6749_ = lean_ctor_get(v___y_6741_, 1);
v_buildTime_6750_ = lean_ctor_get(v___y_6741_, 2);
v_isSharedCheck_6780_ = !lean_is_exclusive(v___y_6741_);
if (v_isSharedCheck_6780_ == 0)
{
v___x_6752_ = v___y_6741_;
v_isShared_6753_ = v_isSharedCheck_6780_;
goto v_resetjp_6751_;
}
else
{
lean_inc(v_buildTime_6750_);
lean_inc(v_trace_6749_);
lean_inc(v_log_6746_);
lean_dec(v___y_6741_);
v___x_6752_ = lean_box(0);
v_isShared_6753_ = v_isSharedCheck_6780_;
goto v_resetjp_6751_;
}
v_resetjp_6751_:
{
lean_object* v_ar_6754_; lean_object* v___x_6755_; 
v_ar_6754_ = lean_ctor_get(v_lean_6745_, 13);
lean_inc_ref(v_ar_6754_);
lean_dec_ref(v_lean_6745_);
v___x_6755_ = l_Lake_compileStaticLib(v_libFile_6733_, v_oFiles_6734_, v_ar_6754_, v_thin_6735_, v_log_6746_);
if (lean_obj_tag(v___x_6755_) == 0)
{
lean_object* v_a_6756_; lean_object* v_a_6757_; lean_object* v___x_6759_; uint8_t v_isShared_6760_; uint8_t v_isSharedCheck_6767_; 
v_a_6756_ = lean_ctor_get(v___x_6755_, 0);
v_a_6757_ = lean_ctor_get(v___x_6755_, 1);
v_isSharedCheck_6767_ = !lean_is_exclusive(v___x_6755_);
if (v_isSharedCheck_6767_ == 0)
{
v___x_6759_ = v___x_6755_;
v_isShared_6760_ = v_isSharedCheck_6767_;
goto v_resetjp_6758_;
}
else
{
lean_inc(v_a_6757_);
lean_inc(v_a_6756_);
lean_dec(v___x_6755_);
v___x_6759_ = lean_box(0);
v_isShared_6760_ = v_isSharedCheck_6767_;
goto v_resetjp_6758_;
}
v_resetjp_6758_:
{
lean_object* v___x_6762_; 
if (v_isShared_6753_ == 0)
{
lean_ctor_set(v___x_6752_, 0, v_a_6757_);
v___x_6762_ = v___x_6752_;
goto v_reusejp_6761_;
}
else
{
lean_object* v_reuseFailAlloc_6766_; 
v_reuseFailAlloc_6766_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6766_, 0, v_a_6757_);
lean_ctor_set(v_reuseFailAlloc_6766_, 1, v_trace_6749_);
lean_ctor_set(v_reuseFailAlloc_6766_, 2, v_buildTime_6750_);
lean_ctor_set_uint8(v_reuseFailAlloc_6766_, sizeof(void*)*3, v_action_6747_);
lean_ctor_set_uint8(v_reuseFailAlloc_6766_, sizeof(void*)*3 + 1, v_wantsRebuild_6748_);
v___x_6762_ = v_reuseFailAlloc_6766_;
goto v_reusejp_6761_;
}
v_reusejp_6761_:
{
lean_object* v___x_6764_; 
if (v_isShared_6760_ == 0)
{
lean_ctor_set(v___x_6759_, 1, v___x_6762_);
v___x_6764_ = v___x_6759_;
goto v_reusejp_6763_;
}
else
{
lean_object* v_reuseFailAlloc_6765_; 
v_reuseFailAlloc_6765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6765_, 0, v_a_6756_);
lean_ctor_set(v_reuseFailAlloc_6765_, 1, v___x_6762_);
v___x_6764_ = v_reuseFailAlloc_6765_;
goto v_reusejp_6763_;
}
v_reusejp_6763_:
{
return v___x_6764_;
}
}
}
}
else
{
lean_object* v_a_6768_; lean_object* v_a_6769_; lean_object* v___x_6771_; uint8_t v_isShared_6772_; uint8_t v_isSharedCheck_6779_; 
v_a_6768_ = lean_ctor_get(v___x_6755_, 0);
v_a_6769_ = lean_ctor_get(v___x_6755_, 1);
v_isSharedCheck_6779_ = !lean_is_exclusive(v___x_6755_);
if (v_isSharedCheck_6779_ == 0)
{
v___x_6771_ = v___x_6755_;
v_isShared_6772_ = v_isSharedCheck_6779_;
goto v_resetjp_6770_;
}
else
{
lean_inc(v_a_6769_);
lean_inc(v_a_6768_);
lean_dec(v___x_6755_);
v___x_6771_ = lean_box(0);
v_isShared_6772_ = v_isSharedCheck_6779_;
goto v_resetjp_6770_;
}
v_resetjp_6770_:
{
lean_object* v___x_6774_; 
if (v_isShared_6753_ == 0)
{
lean_ctor_set(v___x_6752_, 0, v_a_6769_);
v___x_6774_ = v___x_6752_;
goto v_reusejp_6773_;
}
else
{
lean_object* v_reuseFailAlloc_6778_; 
v_reuseFailAlloc_6778_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6778_, 0, v_a_6769_);
lean_ctor_set(v_reuseFailAlloc_6778_, 1, v_trace_6749_);
lean_ctor_set(v_reuseFailAlloc_6778_, 2, v_buildTime_6750_);
lean_ctor_set_uint8(v_reuseFailAlloc_6778_, sizeof(void*)*3, v_action_6747_);
lean_ctor_set_uint8(v_reuseFailAlloc_6778_, sizeof(void*)*3 + 1, v_wantsRebuild_6748_);
v___x_6774_ = v_reuseFailAlloc_6778_;
goto v_reusejp_6773_;
}
v_reusejp_6773_:
{
lean_object* v___x_6776_; 
if (v_isShared_6772_ == 0)
{
lean_ctor_set(v___x_6771_, 1, v___x_6774_);
v___x_6776_ = v___x_6771_;
goto v_reusejp_6775_;
}
else
{
lean_object* v_reuseFailAlloc_6777_; 
v_reuseFailAlloc_6777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6777_, 0, v_a_6768_);
lean_ctor_set(v_reuseFailAlloc_6777_, 1, v___x_6774_);
v___x_6776_ = v_reuseFailAlloc_6777_;
goto v_reusejp_6775_;
}
v_reusejp_6775_:
{
return v___x_6776_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0___boxed(lean_object* v_libFile_6781_, lean_object* v_oFiles_6782_, lean_object* v_thin_6783_, lean_object* v___y_6784_, lean_object* v___y_6785_, lean_object* v___y_6786_, lean_object* v___y_6787_, lean_object* v___y_6788_, lean_object* v___y_6789_, lean_object* v___y_6790_){
_start:
{
uint8_t v_thin_boxed_6791_; lean_object* v_res_6792_; 
v_thin_boxed_6791_ = lean_unbox(v_thin_6783_);
v_res_6792_ = l_Lake_buildStaticLib___lam__0(v_libFile_6781_, v_oFiles_6782_, v_thin_boxed_6791_, v___y_6784_, v___y_6785_, v___y_6786_, v___y_6787_, v___y_6788_, v___y_6789_);
lean_dec(v___y_6787_);
lean_dec(v___y_6786_);
lean_dec(v___y_6785_);
lean_dec_ref(v___y_6784_);
return v_res_6792_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1(lean_object* v_libFile_6794_, uint8_t v_thin_6795_, lean_object* v_oFiles_6796_, lean_object* v___y_6797_, lean_object* v___y_6798_, lean_object* v___y_6799_, lean_object* v___y_6800_, lean_object* v___y_6801_, lean_object* v___y_6802_){
_start:
{
lean_object* v___x_6804_; lean_object* v___f_6805_; uint8_t v___x_6806_; lean_object* v___x_6807_; uint8_t v___x_6808_; lean_object* v___x_6809_; 
v___x_6804_ = lean_box(v_thin_6795_);
lean_inc_ref(v_libFile_6794_);
v___f_6805_ = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6805_, 0, v_libFile_6794_);
lean_closure_set(v___f_6805_, 1, v_oFiles_6796_);
lean_closure_set(v___f_6805_, 2, v___x_6804_);
v___x_6806_ = 0;
v___x_6807_ = ((lean_object*)(l_Lake_buildStaticLib___lam__1___closed__0));
v___x_6808_ = 1;
lean_inc(v___y_6798_);
v___x_6809_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_6794_, v___f_6805_, v___x_6806_, v___x_6807_, v___x_6808_, v___x_6806_, v___x_6806_, v___y_6797_, v___y_6798_, v___y_6799_, v___y_6800_, v___y_6801_, v___y_6802_);
if (lean_obj_tag(v___x_6809_) == 0)
{
lean_object* v_a_6810_; lean_object* v_a_6811_; lean_object* v___x_6813_; uint8_t v_isShared_6814_; uint8_t v_isSharedCheck_6819_; 
v_a_6810_ = lean_ctor_get(v___x_6809_, 0);
v_a_6811_ = lean_ctor_get(v___x_6809_, 1);
v_isSharedCheck_6819_ = !lean_is_exclusive(v___x_6809_);
if (v_isSharedCheck_6819_ == 0)
{
v___x_6813_ = v___x_6809_;
v_isShared_6814_ = v_isSharedCheck_6819_;
goto v_resetjp_6812_;
}
else
{
lean_inc(v_a_6811_);
lean_inc(v_a_6810_);
lean_dec(v___x_6809_);
v___x_6813_ = lean_box(0);
v_isShared_6814_ = v_isSharedCheck_6819_;
goto v_resetjp_6812_;
}
v_resetjp_6812_:
{
lean_object* v_path_6815_; lean_object* v___x_6817_; 
v_path_6815_ = lean_ctor_get(v_a_6810_, 1);
lean_inc_ref(v_path_6815_);
lean_dec(v_a_6810_);
if (v_isShared_6814_ == 0)
{
lean_ctor_set(v___x_6813_, 0, v_path_6815_);
v___x_6817_ = v___x_6813_;
goto v_reusejp_6816_;
}
else
{
lean_object* v_reuseFailAlloc_6818_; 
v_reuseFailAlloc_6818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6818_, 0, v_path_6815_);
lean_ctor_set(v_reuseFailAlloc_6818_, 1, v_a_6811_);
v___x_6817_ = v_reuseFailAlloc_6818_;
goto v_reusejp_6816_;
}
v_reusejp_6816_:
{
return v___x_6817_;
}
}
}
else
{
lean_object* v_a_6820_; lean_object* v_a_6821_; lean_object* v___x_6823_; uint8_t v_isShared_6824_; uint8_t v_isSharedCheck_6828_; 
v_a_6820_ = lean_ctor_get(v___x_6809_, 0);
v_a_6821_ = lean_ctor_get(v___x_6809_, 1);
v_isSharedCheck_6828_ = !lean_is_exclusive(v___x_6809_);
if (v_isSharedCheck_6828_ == 0)
{
v___x_6823_ = v___x_6809_;
v_isShared_6824_ = v_isSharedCheck_6828_;
goto v_resetjp_6822_;
}
else
{
lean_inc(v_a_6821_);
lean_inc(v_a_6820_);
lean_dec(v___x_6809_);
v___x_6823_ = lean_box(0);
v_isShared_6824_ = v_isSharedCheck_6828_;
goto v_resetjp_6822_;
}
v_resetjp_6822_:
{
lean_object* v___x_6826_; 
if (v_isShared_6824_ == 0)
{
v___x_6826_ = v___x_6823_;
goto v_reusejp_6825_;
}
else
{
lean_object* v_reuseFailAlloc_6827_; 
v_reuseFailAlloc_6827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6827_, 0, v_a_6820_);
lean_ctor_set(v_reuseFailAlloc_6827_, 1, v_a_6821_);
v___x_6826_ = v_reuseFailAlloc_6827_;
goto v_reusejp_6825_;
}
v_reusejp_6825_:
{
return v___x_6826_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1___boxed(lean_object* v_libFile_6829_, lean_object* v_thin_6830_, lean_object* v_oFiles_6831_, lean_object* v___y_6832_, lean_object* v___y_6833_, lean_object* v___y_6834_, lean_object* v___y_6835_, lean_object* v___y_6836_, lean_object* v___y_6837_, lean_object* v___y_6838_){
_start:
{
uint8_t v_thin_boxed_6839_; lean_object* v_res_6840_; 
v_thin_boxed_6839_ = lean_unbox(v_thin_6830_);
v_res_6840_ = l_Lake_buildStaticLib___lam__1(v_libFile_6829_, v_thin_boxed_6839_, v_oFiles_6831_, v___y_6832_, v___y_6833_, v___y_6834_, v___y_6835_, v___y_6836_, v___y_6837_);
lean_dec_ref(v___y_6836_);
lean_dec(v___y_6835_);
lean_dec(v___y_6834_);
lean_dec(v___y_6833_);
return v_res_6840_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object* v_libFile_6842_, lean_object* v_oFileJobs_6843_, uint8_t v_thin_6844_, lean_object* v_a_6845_, lean_object* v_a_6846_, lean_object* v_a_6847_, lean_object* v_a_6848_, lean_object* v_a_6849_, lean_object* v_a_6850_){
_start:
{
lean_object* v___x_6852_; lean_object* v___f_6853_; lean_object* v___x_6854_; lean_object* v___x_6855_; lean_object* v___x_6856_; lean_object* v___x_6857_; uint8_t v___x_6858_; lean_object* v___x_6859_; 
v___x_6852_ = lean_box(v_thin_6844_);
v___f_6853_ = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__1___boxed), 10, 2);
lean_closure_set(v___f_6853_, 0, v_libFile_6842_);
lean_closure_set(v___f_6853_, 1, v___x_6852_);
v___x_6854_ = l_Lake_instDataKindFilePath;
v___x_6855_ = ((lean_object*)(l_Lake_buildStaticLib___closed__0));
v___x_6856_ = l_Lake_Job_collectArray___redArg(v_oFileJobs_6843_, v___x_6855_);
v___x_6857_ = lean_unsigned_to_nat(0u);
v___x_6858_ = 0;
v___x_6859_ = l_Lake_Job_mapM___redArg(v___x_6854_, v___x_6856_, v___f_6853_, v___x_6857_, v___x_6858_, v_a_6845_, v_a_6846_, v_a_6847_, v_a_6848_, v_a_6849_, v_a_6850_);
return v___x_6859_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object* v_libFile_6860_, lean_object* v_oFileJobs_6861_, lean_object* v_thin_6862_, lean_object* v_a_6863_, lean_object* v_a_6864_, lean_object* v_a_6865_, lean_object* v_a_6866_, lean_object* v_a_6867_, lean_object* v_a_6868_, lean_object* v_a_6869_){
_start:
{
uint8_t v_thin_boxed_6870_; lean_object* v_res_6871_; 
v_thin_boxed_6870_ = lean_unbox(v_thin_6862_);
v_res_6871_ = l_Lake_buildStaticLib(v_libFile_6860_, v_oFileJobs_6861_, v_thin_boxed_6870_, v_a_6863_, v_a_6864_, v_a_6865_, v_a_6866_, v_a_6867_, v_a_6868_);
lean_dec_ref(v_a_6868_);
lean_dec_ref(v_a_6867_);
lean_dec(v_a_6866_);
lean_dec(v_a_6865_);
lean_dec(v_a_6864_);
lean_dec_ref(v_oFileJobs_6861_);
return v_res_6871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(lean_object* v_as_6872_, size_t v_sz_6873_, size_t v_i_6874_, lean_object* v_b_6875_){
_start:
{
uint8_t v___x_6876_; 
v___x_6876_ = lean_usize_dec_lt(v_i_6874_, v_sz_6873_);
if (v___x_6876_ == 0)
{
return v_b_6875_;
}
else
{
lean_object* v_a_6877_; lean_object* v___x_6878_; size_t v___x_6879_; size_t v___x_6880_; 
v_a_6877_ = lean_array_uget_borrowed(v_as_6872_, v_i_6874_);
lean_inc(v_a_6877_);
v___x_6878_ = lean_array_push(v_b_6875_, v_a_6877_);
v___x_6879_ = ((size_t)1ULL);
v___x_6880_ = lean_usize_add(v_i_6874_, v___x_6879_);
v_i_6874_ = v___x_6880_;
v_b_6875_ = v___x_6878_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0___boxed(lean_object* v_as_6882_, lean_object* v_sz_6883_, lean_object* v_i_6884_, lean_object* v_b_6885_){
_start:
{
size_t v_sz_boxed_6886_; size_t v_i_boxed_6887_; lean_object* v_res_6888_; 
v_sz_boxed_6886_ = lean_unbox_usize(v_sz_6883_);
lean_dec(v_sz_6883_);
v_i_boxed_6887_ = lean_unbox_usize(v_i_6884_);
lean_dec(v_i_6884_);
v_res_6888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(v_as_6882_, v_sz_boxed_6886_, v_i_boxed_6887_, v_b_6885_);
lean_dec_ref(v_as_6882_);
return v_res_6888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(lean_object* v_as_6891_, size_t v_sz_6892_, size_t v_i_6893_, lean_object* v_b_6894_){
_start:
{
uint8_t v___x_6895_; 
v___x_6895_ = lean_usize_dec_lt(v_i_6893_, v_sz_6892_);
if (v___x_6895_ == 0)
{
return v_b_6894_;
}
else
{
lean_object* v_a_6896_; lean_object* v_args_6898_; lean_object* v___x_6906_; 
v_a_6896_ = lean_array_uget_borrowed(v_as_6891_, v_i_6893_);
lean_inc(v_a_6896_);
v___x_6906_ = l_Lake_Dynlib_dir_x3f(v_a_6896_);
if (lean_obj_tag(v___x_6906_) == 1)
{
lean_object* v_val_6907_; lean_object* v___x_6908_; lean_object* v___x_6909_; lean_object* v___x_6910_; 
v_val_6907_ = lean_ctor_get(v___x_6906_, 0);
lean_inc(v_val_6907_);
lean_dec_ref(v___x_6906_);
v___x_6908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
v___x_6909_ = lean_string_append(v___x_6908_, v_val_6907_);
lean_dec(v_val_6907_);
v___x_6910_ = lean_array_push(v_b_6894_, v___x_6909_);
v_args_6898_ = v___x_6910_;
goto v___jp_6897_;
}
else
{
lean_dec(v___x_6906_);
v_args_6898_ = v_b_6894_;
goto v___jp_6897_;
}
v___jp_6897_:
{
lean_object* v_name_6899_; lean_object* v___x_6900_; lean_object* v___x_6901_; lean_object* v___x_6902_; size_t v___x_6903_; size_t v___x_6904_; 
v_name_6899_ = lean_ctor_get(v_a_6896_, 1);
v___x_6900_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0));
v___x_6901_ = lean_string_append(v___x_6900_, v_name_6899_);
v___x_6902_ = lean_array_push(v_args_6898_, v___x_6901_);
v___x_6903_ = ((size_t)1ULL);
v___x_6904_ = lean_usize_add(v_i_6893_, v___x_6903_);
v_i_6893_ = v___x_6904_;
v_b_6894_ = v___x_6902_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___boxed(lean_object* v_as_6911_, lean_object* v_sz_6912_, lean_object* v_i_6913_, lean_object* v_b_6914_){
_start:
{
size_t v_sz_boxed_6915_; size_t v_i_boxed_6916_; lean_object* v_res_6917_; 
v_sz_boxed_6915_ = lean_unbox_usize(v_sz_6912_);
lean_dec(v_sz_6912_);
v_i_boxed_6916_ = lean_unbox_usize(v_i_6913_);
lean_dec(v_i_6913_);
v_res_6917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(v_as_6911_, v_sz_boxed_6915_, v_i_boxed_6916_, v_b_6914_);
lean_dec_ref(v_as_6911_);
return v_res_6917_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(lean_object* v_objs_6918_, lean_object* v_libs_6919_){
_start:
{
lean_object* v_args_6920_; size_t v_sz_6921_; size_t v___x_6922_; lean_object* v___x_6923_; size_t v_sz_6924_; lean_object* v___x_6925_; 
v_args_6920_ = ((lean_object*)(l_Lake_inputDir___lam__1___closed__0));
v_sz_6921_ = lean_array_size(v_objs_6918_);
v___x_6922_ = ((size_t)0ULL);
v___x_6923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(v_objs_6918_, v_sz_6921_, v___x_6922_, v_args_6920_);
v_sz_6924_ = lean_array_size(v_libs_6919_);
v___x_6925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(v_libs_6919_, v_sz_6924_, v___x_6922_, v___x_6923_);
return v___x_6925_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs___boxed(lean_object* v_objs_6926_, lean_object* v_libs_6927_){
_start:
{
lean_object* v_res_6928_; 
v_res_6928_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_6926_, v_libs_6927_);
lean_dec_ref(v_libs_6927_);
lean_dec_ref(v_objs_6926_);
return v_res_6928_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(lean_object* v_k_6929_, lean_object* v_t_6930_){
_start:
{
if (lean_obj_tag(v_t_6930_) == 0)
{
lean_object* v_k_6931_; lean_object* v_l_6932_; lean_object* v_r_6933_; uint8_t v___x_6934_; 
v_k_6931_ = lean_ctor_get(v_t_6930_, 1);
v_l_6932_ = lean_ctor_get(v_t_6930_, 3);
v_r_6933_ = lean_ctor_get(v_t_6930_, 4);
v___x_6934_ = lean_string_dec_lt(v_k_6929_, v_k_6931_);
if (v___x_6934_ == 0)
{
uint8_t v___x_6935_; 
v___x_6935_ = lean_string_dec_eq(v_k_6929_, v_k_6931_);
if (v___x_6935_ == 0)
{
v_t_6930_ = v_r_6933_;
goto _start;
}
else
{
return v___x_6935_;
}
}
else
{
v_t_6930_ = v_l_6932_;
goto _start;
}
}
else
{
uint8_t v___x_6938_; 
v___x_6938_ = 0;
return v___x_6938_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg___boxed(lean_object* v_k_6939_, lean_object* v_t_6940_){
_start:
{
uint8_t v_res_6941_; lean_object* v_r_6942_; 
v_res_6941_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_k_6939_, v_t_6940_);
lean_dec(v_t_6940_);
lean_dec_ref(v_k_6939_);
v_r_6942_ = lean_box(v_res_6941_);
return v_r_6942_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(lean_object* v_a_6943_, lean_object* v_x_6944_){
_start:
{
if (lean_obj_tag(v_x_6944_) == 0)
{
uint8_t v___x_6945_; 
v___x_6945_ = 0;
return v___x_6945_;
}
else
{
lean_object* v_head_6946_; lean_object* v_tail_6947_; uint8_t v___x_6948_; 
v_head_6946_ = lean_ctor_get(v_x_6944_, 0);
v_tail_6947_ = lean_ctor_get(v_x_6944_, 1);
v___x_6948_ = lean_string_dec_eq(v_a_6943_, v_head_6946_);
if (v___x_6948_ == 0)
{
v_x_6944_ = v_tail_6947_;
goto _start;
}
else
{
return v___x_6948_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1___boxed(lean_object* v_a_6950_, lean_object* v_x_6951_){
_start:
{
uint8_t v_res_6952_; lean_object* v_r_6953_; 
v_res_6952_ = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(v_a_6950_, v_x_6951_);
lean_dec(v_x_6951_);
lean_dec_ref(v_a_6950_);
v_r_6953_ = lean_box(v_res_6952_);
return v_r_6953_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(lean_object* v_k_6954_, lean_object* v_v_6955_, lean_object* v_t_6956_){
_start:
{
if (lean_obj_tag(v_t_6956_) == 0)
{
lean_object* v_size_6957_; lean_object* v_k_6958_; lean_object* v_v_6959_; lean_object* v_l_6960_; lean_object* v_r_6961_; lean_object* v___x_6963_; uint8_t v_isShared_6964_; uint8_t v_isSharedCheck_7242_; 
v_size_6957_ = lean_ctor_get(v_t_6956_, 0);
v_k_6958_ = lean_ctor_get(v_t_6956_, 1);
v_v_6959_ = lean_ctor_get(v_t_6956_, 2);
v_l_6960_ = lean_ctor_get(v_t_6956_, 3);
v_r_6961_ = lean_ctor_get(v_t_6956_, 4);
v_isSharedCheck_7242_ = !lean_is_exclusive(v_t_6956_);
if (v_isSharedCheck_7242_ == 0)
{
v___x_6963_ = v_t_6956_;
v_isShared_6964_ = v_isSharedCheck_7242_;
goto v_resetjp_6962_;
}
else
{
lean_inc(v_r_6961_);
lean_inc(v_l_6960_);
lean_inc(v_v_6959_);
lean_inc(v_k_6958_);
lean_inc(v_size_6957_);
lean_dec(v_t_6956_);
v___x_6963_ = lean_box(0);
v_isShared_6964_ = v_isSharedCheck_7242_;
goto v_resetjp_6962_;
}
v_resetjp_6962_:
{
uint8_t v___x_6965_; 
v___x_6965_ = lean_string_dec_lt(v_k_6954_, v_k_6958_);
if (v___x_6965_ == 0)
{
uint8_t v___x_6966_; 
v___x_6966_ = lean_string_dec_eq(v_k_6954_, v_k_6958_);
if (v___x_6966_ == 0)
{
lean_object* v_impl_6967_; lean_object* v___x_6968_; 
lean_dec(v_size_6957_);
v_impl_6967_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_6954_, v_v_6955_, v_r_6961_);
v___x_6968_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_6960_) == 0)
{
lean_object* v_size_6969_; lean_object* v_size_6970_; lean_object* v_k_6971_; lean_object* v_v_6972_; lean_object* v_l_6973_; lean_object* v_r_6974_; lean_object* v___x_6975_; lean_object* v___x_6976_; uint8_t v___x_6977_; 
v_size_6969_ = lean_ctor_get(v_l_6960_, 0);
v_size_6970_ = lean_ctor_get(v_impl_6967_, 0);
lean_inc(v_size_6970_);
v_k_6971_ = lean_ctor_get(v_impl_6967_, 1);
lean_inc(v_k_6971_);
v_v_6972_ = lean_ctor_get(v_impl_6967_, 2);
lean_inc(v_v_6972_);
v_l_6973_ = lean_ctor_get(v_impl_6967_, 3);
lean_inc(v_l_6973_);
v_r_6974_ = lean_ctor_get(v_impl_6967_, 4);
lean_inc(v_r_6974_);
v___x_6975_ = lean_unsigned_to_nat(3u);
v___x_6976_ = lean_nat_mul(v___x_6975_, v_size_6969_);
v___x_6977_ = lean_nat_dec_lt(v___x_6976_, v_size_6970_);
lean_dec(v___x_6976_);
if (v___x_6977_ == 0)
{
lean_object* v___x_6978_; lean_object* v___x_6979_; lean_object* v___x_6981_; 
lean_dec(v_r_6974_);
lean_dec(v_l_6973_);
lean_dec(v_v_6972_);
lean_dec(v_k_6971_);
v___x_6978_ = lean_nat_add(v___x_6968_, v_size_6969_);
v___x_6979_ = lean_nat_add(v___x_6978_, v_size_6970_);
lean_dec(v_size_6970_);
lean_dec(v___x_6978_);
if (v_isShared_6964_ == 0)
{
lean_ctor_set(v___x_6963_, 4, v_impl_6967_);
lean_ctor_set(v___x_6963_, 0, v___x_6979_);
v___x_6981_ = v___x_6963_;
goto v_reusejp_6980_;
}
else
{
lean_object* v_reuseFailAlloc_6982_; 
v_reuseFailAlloc_6982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6982_, 0, v___x_6979_);
lean_ctor_set(v_reuseFailAlloc_6982_, 1, v_k_6958_);
lean_ctor_set(v_reuseFailAlloc_6982_, 2, v_v_6959_);
lean_ctor_set(v_reuseFailAlloc_6982_, 3, v_l_6960_);
lean_ctor_set(v_reuseFailAlloc_6982_, 4, v_impl_6967_);
v___x_6981_ = v_reuseFailAlloc_6982_;
goto v_reusejp_6980_;
}
v_reusejp_6980_:
{
return v___x_6981_;
}
}
else
{
lean_object* v___x_6984_; uint8_t v_isShared_6985_; uint8_t v_isSharedCheck_7046_; 
v_isSharedCheck_7046_ = !lean_is_exclusive(v_impl_6967_);
if (v_isSharedCheck_7046_ == 0)
{
lean_object* v_unused_7047_; lean_object* v_unused_7048_; lean_object* v_unused_7049_; lean_object* v_unused_7050_; lean_object* v_unused_7051_; 
v_unused_7047_ = lean_ctor_get(v_impl_6967_, 4);
lean_dec(v_unused_7047_);
v_unused_7048_ = lean_ctor_get(v_impl_6967_, 3);
lean_dec(v_unused_7048_);
v_unused_7049_ = lean_ctor_get(v_impl_6967_, 2);
lean_dec(v_unused_7049_);
v_unused_7050_ = lean_ctor_get(v_impl_6967_, 1);
lean_dec(v_unused_7050_);
v_unused_7051_ = lean_ctor_get(v_impl_6967_, 0);
lean_dec(v_unused_7051_);
v___x_6984_ = v_impl_6967_;
v_isShared_6985_ = v_isSharedCheck_7046_;
goto v_resetjp_6983_;
}
else
{
lean_dec(v_impl_6967_);
v___x_6984_ = lean_box(0);
v_isShared_6985_ = v_isSharedCheck_7046_;
goto v_resetjp_6983_;
}
v_resetjp_6983_:
{
lean_object* v_size_6986_; lean_object* v_k_6987_; lean_object* v_v_6988_; lean_object* v_l_6989_; lean_object* v_r_6990_; lean_object* v_size_6991_; lean_object* v___x_6992_; lean_object* v___x_6993_; uint8_t v___x_6994_; 
v_size_6986_ = lean_ctor_get(v_l_6973_, 0);
v_k_6987_ = lean_ctor_get(v_l_6973_, 1);
v_v_6988_ = lean_ctor_get(v_l_6973_, 2);
v_l_6989_ = lean_ctor_get(v_l_6973_, 3);
v_r_6990_ = lean_ctor_get(v_l_6973_, 4);
v_size_6991_ = lean_ctor_get(v_r_6974_, 0);
v___x_6992_ = lean_unsigned_to_nat(2u);
v___x_6993_ = lean_nat_mul(v___x_6992_, v_size_6991_);
v___x_6994_ = lean_nat_dec_lt(v_size_6986_, v___x_6993_);
lean_dec(v___x_6993_);
if (v___x_6994_ == 0)
{
lean_object* v___x_6996_; uint8_t v_isShared_6997_; uint8_t v_isSharedCheck_7022_; 
lean_inc(v_r_6990_);
lean_inc(v_l_6989_);
lean_inc(v_v_6988_);
lean_inc(v_k_6987_);
v_isSharedCheck_7022_ = !lean_is_exclusive(v_l_6973_);
if (v_isSharedCheck_7022_ == 0)
{
lean_object* v_unused_7023_; lean_object* v_unused_7024_; lean_object* v_unused_7025_; lean_object* v_unused_7026_; lean_object* v_unused_7027_; 
v_unused_7023_ = lean_ctor_get(v_l_6973_, 4);
lean_dec(v_unused_7023_);
v_unused_7024_ = lean_ctor_get(v_l_6973_, 3);
lean_dec(v_unused_7024_);
v_unused_7025_ = lean_ctor_get(v_l_6973_, 2);
lean_dec(v_unused_7025_);
v_unused_7026_ = lean_ctor_get(v_l_6973_, 1);
lean_dec(v_unused_7026_);
v_unused_7027_ = lean_ctor_get(v_l_6973_, 0);
lean_dec(v_unused_7027_);
v___x_6996_ = v_l_6973_;
v_isShared_6997_ = v_isSharedCheck_7022_;
goto v_resetjp_6995_;
}
else
{
lean_dec(v_l_6973_);
v___x_6996_ = lean_box(0);
v_isShared_6997_ = v_isSharedCheck_7022_;
goto v_resetjp_6995_;
}
v_resetjp_6995_:
{
lean_object* v___x_6998_; lean_object* v___x_6999_; lean_object* v___y_7001_; lean_object* v___y_7002_; lean_object* v___y_7003_; lean_object* v___y_7012_; 
v___x_6998_ = lean_nat_add(v___x_6968_, v_size_6969_);
v___x_6999_ = lean_nat_add(v___x_6998_, v_size_6970_);
lean_dec(v_size_6970_);
if (lean_obj_tag(v_l_6989_) == 0)
{
lean_object* v_size_7020_; 
v_size_7020_ = lean_ctor_get(v_l_6989_, 0);
lean_inc(v_size_7020_);
v___y_7012_ = v_size_7020_;
goto v___jp_7011_;
}
else
{
lean_object* v___x_7021_; 
v___x_7021_ = lean_unsigned_to_nat(0u);
v___y_7012_ = v___x_7021_;
goto v___jp_7011_;
}
v___jp_7000_:
{
lean_object* v___x_7004_; lean_object* v___x_7006_; 
v___x_7004_ = lean_nat_add(v___y_7002_, v___y_7003_);
lean_dec(v___y_7003_);
lean_dec(v___y_7002_);
if (v_isShared_6997_ == 0)
{
lean_ctor_set(v___x_6996_, 4, v_r_6974_);
lean_ctor_set(v___x_6996_, 3, v_r_6990_);
lean_ctor_set(v___x_6996_, 2, v_v_6972_);
lean_ctor_set(v___x_6996_, 1, v_k_6971_);
lean_ctor_set(v___x_6996_, 0, v___x_7004_);
v___x_7006_ = v___x_6996_;
goto v_reusejp_7005_;
}
else
{
lean_object* v_reuseFailAlloc_7010_; 
v_reuseFailAlloc_7010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7010_, 0, v___x_7004_);
lean_ctor_set(v_reuseFailAlloc_7010_, 1, v_k_6971_);
lean_ctor_set(v_reuseFailAlloc_7010_, 2, v_v_6972_);
lean_ctor_set(v_reuseFailAlloc_7010_, 3, v_r_6990_);
lean_ctor_set(v_reuseFailAlloc_7010_, 4, v_r_6974_);
v___x_7006_ = v_reuseFailAlloc_7010_;
goto v_reusejp_7005_;
}
v_reusejp_7005_:
{
lean_object* v___x_7008_; 
if (v_isShared_6985_ == 0)
{
lean_ctor_set(v___x_6984_, 4, v___x_7006_);
lean_ctor_set(v___x_6984_, 3, v___y_7001_);
lean_ctor_set(v___x_6984_, 2, v_v_6988_);
lean_ctor_set(v___x_6984_, 1, v_k_6987_);
lean_ctor_set(v___x_6984_, 0, v___x_6999_);
v___x_7008_ = v___x_6984_;
goto v_reusejp_7007_;
}
else
{
lean_object* v_reuseFailAlloc_7009_; 
v_reuseFailAlloc_7009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7009_, 0, v___x_6999_);
lean_ctor_set(v_reuseFailAlloc_7009_, 1, v_k_6987_);
lean_ctor_set(v_reuseFailAlloc_7009_, 2, v_v_6988_);
lean_ctor_set(v_reuseFailAlloc_7009_, 3, v___y_7001_);
lean_ctor_set(v_reuseFailAlloc_7009_, 4, v___x_7006_);
v___x_7008_ = v_reuseFailAlloc_7009_;
goto v_reusejp_7007_;
}
v_reusejp_7007_:
{
return v___x_7008_;
}
}
}
v___jp_7011_:
{
lean_object* v___x_7013_; lean_object* v___x_7015_; 
v___x_7013_ = lean_nat_add(v___x_6998_, v___y_7012_);
lean_dec(v___y_7012_);
lean_dec(v___x_6998_);
if (v_isShared_6964_ == 0)
{
lean_ctor_set(v___x_6963_, 4, v_l_6989_);
lean_ctor_set(v___x_6963_, 0, v___x_7013_);
v___x_7015_ = v___x_6963_;
goto v_reusejp_7014_;
}
else
{
lean_object* v_reuseFailAlloc_7019_; 
v_reuseFailAlloc_7019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7019_, 0, v___x_7013_);
lean_ctor_set(v_reuseFailAlloc_7019_, 1, v_k_6958_);
lean_ctor_set(v_reuseFailAlloc_7019_, 2, v_v_6959_);
lean_ctor_set(v_reuseFailAlloc_7019_, 3, v_l_6960_);
lean_ctor_set(v_reuseFailAlloc_7019_, 4, v_l_6989_);
v___x_7015_ = v_reuseFailAlloc_7019_;
goto v_reusejp_7014_;
}
v_reusejp_7014_:
{
lean_object* v___x_7016_; 
v___x_7016_ = lean_nat_add(v___x_6968_, v_size_6991_);
if (lean_obj_tag(v_r_6990_) == 0)
{
lean_object* v_size_7017_; 
v_size_7017_ = lean_ctor_get(v_r_6990_, 0);
lean_inc(v_size_7017_);
v___y_7001_ = v___x_7015_;
v___y_7002_ = v___x_7016_;
v___y_7003_ = v_size_7017_;
goto v___jp_7000_;
}
else
{
lean_object* v___x_7018_; 
v___x_7018_ = lean_unsigned_to_nat(0u);
v___y_7001_ = v___x_7015_;
v___y_7002_ = v___x_7016_;
v___y_7003_ = v___x_7018_;
goto v___jp_7000_;
}
}
}
}
}
else
{
lean_object* v___x_7028_; lean_object* v___x_7029_; lean_object* v___x_7030_; lean_object* v___x_7032_; 
lean_del_object(v___x_6963_);
v___x_7028_ = lean_nat_add(v___x_6968_, v_size_6969_);
v___x_7029_ = lean_nat_add(v___x_7028_, v_size_6970_);
lean_dec(v_size_6970_);
v___x_7030_ = lean_nat_add(v___x_7028_, v_size_6986_);
lean_dec(v___x_7028_);
lean_inc_ref(v_l_6960_);
if (v_isShared_6985_ == 0)
{
lean_ctor_set(v___x_6984_, 4, v_l_6973_);
lean_ctor_set(v___x_6984_, 3, v_l_6960_);
lean_ctor_set(v___x_6984_, 2, v_v_6959_);
lean_ctor_set(v___x_6984_, 1, v_k_6958_);
lean_ctor_set(v___x_6984_, 0, v___x_7030_);
v___x_7032_ = v___x_6984_;
goto v_reusejp_7031_;
}
else
{
lean_object* v_reuseFailAlloc_7045_; 
v_reuseFailAlloc_7045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7045_, 0, v___x_7030_);
lean_ctor_set(v_reuseFailAlloc_7045_, 1, v_k_6958_);
lean_ctor_set(v_reuseFailAlloc_7045_, 2, v_v_6959_);
lean_ctor_set(v_reuseFailAlloc_7045_, 3, v_l_6960_);
lean_ctor_set(v_reuseFailAlloc_7045_, 4, v_l_6973_);
v___x_7032_ = v_reuseFailAlloc_7045_;
goto v_reusejp_7031_;
}
v_reusejp_7031_:
{
lean_object* v___x_7034_; uint8_t v_isShared_7035_; uint8_t v_isSharedCheck_7039_; 
v_isSharedCheck_7039_ = !lean_is_exclusive(v_l_6960_);
if (v_isSharedCheck_7039_ == 0)
{
lean_object* v_unused_7040_; lean_object* v_unused_7041_; lean_object* v_unused_7042_; lean_object* v_unused_7043_; lean_object* v_unused_7044_; 
v_unused_7040_ = lean_ctor_get(v_l_6960_, 4);
lean_dec(v_unused_7040_);
v_unused_7041_ = lean_ctor_get(v_l_6960_, 3);
lean_dec(v_unused_7041_);
v_unused_7042_ = lean_ctor_get(v_l_6960_, 2);
lean_dec(v_unused_7042_);
v_unused_7043_ = lean_ctor_get(v_l_6960_, 1);
lean_dec(v_unused_7043_);
v_unused_7044_ = lean_ctor_get(v_l_6960_, 0);
lean_dec(v_unused_7044_);
v___x_7034_ = v_l_6960_;
v_isShared_7035_ = v_isSharedCheck_7039_;
goto v_resetjp_7033_;
}
else
{
lean_dec(v_l_6960_);
v___x_7034_ = lean_box(0);
v_isShared_7035_ = v_isSharedCheck_7039_;
goto v_resetjp_7033_;
}
v_resetjp_7033_:
{
lean_object* v___x_7037_; 
if (v_isShared_7035_ == 0)
{
lean_ctor_set(v___x_7034_, 4, v_r_6974_);
lean_ctor_set(v___x_7034_, 3, v___x_7032_);
lean_ctor_set(v___x_7034_, 2, v_v_6972_);
lean_ctor_set(v___x_7034_, 1, v_k_6971_);
lean_ctor_set(v___x_7034_, 0, v___x_7029_);
v___x_7037_ = v___x_7034_;
goto v_reusejp_7036_;
}
else
{
lean_object* v_reuseFailAlloc_7038_; 
v_reuseFailAlloc_7038_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7038_, 0, v___x_7029_);
lean_ctor_set(v_reuseFailAlloc_7038_, 1, v_k_6971_);
lean_ctor_set(v_reuseFailAlloc_7038_, 2, v_v_6972_);
lean_ctor_set(v_reuseFailAlloc_7038_, 3, v___x_7032_);
lean_ctor_set(v_reuseFailAlloc_7038_, 4, v_r_6974_);
v___x_7037_ = v_reuseFailAlloc_7038_;
goto v_reusejp_7036_;
}
v_reusejp_7036_:
{
return v___x_7037_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_7052_; 
v_l_7052_ = lean_ctor_get(v_impl_6967_, 3);
lean_inc(v_l_7052_);
if (lean_obj_tag(v_l_7052_) == 0)
{
lean_object* v_r_7053_; lean_object* v_k_7054_; lean_object* v_v_7055_; lean_object* v___x_7057_; uint8_t v_isShared_7058_; uint8_t v_isSharedCheck_7078_; 
v_r_7053_ = lean_ctor_get(v_impl_6967_, 4);
v_k_7054_ = lean_ctor_get(v_impl_6967_, 1);
v_v_7055_ = lean_ctor_get(v_impl_6967_, 2);
v_isSharedCheck_7078_ = !lean_is_exclusive(v_impl_6967_);
if (v_isSharedCheck_7078_ == 0)
{
lean_object* v_unused_7079_; lean_object* v_unused_7080_; 
v_unused_7079_ = lean_ctor_get(v_impl_6967_, 3);
lean_dec(v_unused_7079_);
v_unused_7080_ = lean_ctor_get(v_impl_6967_, 0);
lean_dec(v_unused_7080_);
v___x_7057_ = v_impl_6967_;
v_isShared_7058_ = v_isSharedCheck_7078_;
goto v_resetjp_7056_;
}
else
{
lean_inc(v_r_7053_);
lean_inc(v_v_7055_);
lean_inc(v_k_7054_);
lean_dec(v_impl_6967_);
v___x_7057_ = lean_box(0);
v_isShared_7058_ = v_isSharedCheck_7078_;
goto v_resetjp_7056_;
}
v_resetjp_7056_:
{
lean_object* v_k_7059_; lean_object* v_v_7060_; lean_object* v___x_7062_; uint8_t v_isShared_7063_; uint8_t v_isSharedCheck_7074_; 
v_k_7059_ = lean_ctor_get(v_l_7052_, 1);
v_v_7060_ = lean_ctor_get(v_l_7052_, 2);
v_isSharedCheck_7074_ = !lean_is_exclusive(v_l_7052_);
if (v_isSharedCheck_7074_ == 0)
{
lean_object* v_unused_7075_; lean_object* v_unused_7076_; lean_object* v_unused_7077_; 
v_unused_7075_ = lean_ctor_get(v_l_7052_, 4);
lean_dec(v_unused_7075_);
v_unused_7076_ = lean_ctor_get(v_l_7052_, 3);
lean_dec(v_unused_7076_);
v_unused_7077_ = lean_ctor_get(v_l_7052_, 0);
lean_dec(v_unused_7077_);
v___x_7062_ = v_l_7052_;
v_isShared_7063_ = v_isSharedCheck_7074_;
goto v_resetjp_7061_;
}
else
{
lean_inc(v_v_7060_);
lean_inc(v_k_7059_);
lean_dec(v_l_7052_);
v___x_7062_ = lean_box(0);
v_isShared_7063_ = v_isSharedCheck_7074_;
goto v_resetjp_7061_;
}
v_resetjp_7061_:
{
lean_object* v___x_7064_; lean_object* v___x_7066_; 
v___x_7064_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_7053_, 2);
if (v_isShared_7063_ == 0)
{
lean_ctor_set(v___x_7062_, 4, v_r_7053_);
lean_ctor_set(v___x_7062_, 3, v_r_7053_);
lean_ctor_set(v___x_7062_, 2, v_v_6959_);
lean_ctor_set(v___x_7062_, 1, v_k_6958_);
lean_ctor_set(v___x_7062_, 0, v___x_6968_);
v___x_7066_ = v___x_7062_;
goto v_reusejp_7065_;
}
else
{
lean_object* v_reuseFailAlloc_7073_; 
v_reuseFailAlloc_7073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7073_, 0, v___x_6968_);
lean_ctor_set(v_reuseFailAlloc_7073_, 1, v_k_6958_);
lean_ctor_set(v_reuseFailAlloc_7073_, 2, v_v_6959_);
lean_ctor_set(v_reuseFailAlloc_7073_, 3, v_r_7053_);
lean_ctor_set(v_reuseFailAlloc_7073_, 4, v_r_7053_);
v___x_7066_ = v_reuseFailAlloc_7073_;
goto v_reusejp_7065_;
}
v_reusejp_7065_:
{
lean_object* v___x_7068_; 
lean_inc(v_r_7053_);
if (v_isShared_7058_ == 0)
{
lean_ctor_set(v___x_7057_, 3, v_r_7053_);
lean_ctor_set(v___x_7057_, 0, v___x_6968_);
v___x_7068_ = v___x_7057_;
goto v_reusejp_7067_;
}
else
{
lean_object* v_reuseFailAlloc_7072_; 
v_reuseFailAlloc_7072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7072_, 0, v___x_6968_);
lean_ctor_set(v_reuseFailAlloc_7072_, 1, v_k_7054_);
lean_ctor_set(v_reuseFailAlloc_7072_, 2, v_v_7055_);
lean_ctor_set(v_reuseFailAlloc_7072_, 3, v_r_7053_);
lean_ctor_set(v_reuseFailAlloc_7072_, 4, v_r_7053_);
v___x_7068_ = v_reuseFailAlloc_7072_;
goto v_reusejp_7067_;
}
v_reusejp_7067_:
{
lean_object* v___x_7070_; 
if (v_isShared_6964_ == 0)
{
lean_ctor_set(v___x_6963_, 4, v___x_7068_);
lean_ctor_set(v___x_6963_, 3, v___x_7066_);
lean_ctor_set(v___x_6963_, 2, v_v_7060_);
lean_ctor_set(v___x_6963_, 1, v_k_7059_);
lean_ctor_set(v___x_6963_, 0, v___x_7064_);
v___x_7070_ = v___x_6963_;
goto v_reusejp_7069_;
}
else
{
lean_object* v_reuseFailAlloc_7071_; 
v_reuseFailAlloc_7071_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7071_, 0, v___x_7064_);
lean_ctor_set(v_reuseFailAlloc_7071_, 1, v_k_7059_);
lean_ctor_set(v_reuseFailAlloc_7071_, 2, v_v_7060_);
lean_ctor_set(v_reuseFailAlloc_7071_, 3, v___x_7066_);
lean_ctor_set(v_reuseFailAlloc_7071_, 4, v___x_7068_);
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
else
{
lean_object* v_r_7081_; 
v_r_7081_ = lean_ctor_get(v_impl_6967_, 4);
lean_inc(v_r_7081_);
if (lean_obj_tag(v_r_7081_) == 0)
{
lean_object* v_k_7082_; lean_object* v_v_7083_; lean_object* v___x_7085_; uint8_t v_isShared_7086_; uint8_t v_isSharedCheck_7094_; 
v_k_7082_ = lean_ctor_get(v_impl_6967_, 1);
v_v_7083_ = lean_ctor_get(v_impl_6967_, 2);
v_isSharedCheck_7094_ = !lean_is_exclusive(v_impl_6967_);
if (v_isSharedCheck_7094_ == 0)
{
lean_object* v_unused_7095_; lean_object* v_unused_7096_; lean_object* v_unused_7097_; 
v_unused_7095_ = lean_ctor_get(v_impl_6967_, 4);
lean_dec(v_unused_7095_);
v_unused_7096_ = lean_ctor_get(v_impl_6967_, 3);
lean_dec(v_unused_7096_);
v_unused_7097_ = lean_ctor_get(v_impl_6967_, 0);
lean_dec(v_unused_7097_);
v___x_7085_ = v_impl_6967_;
v_isShared_7086_ = v_isSharedCheck_7094_;
goto v_resetjp_7084_;
}
else
{
lean_inc(v_v_7083_);
lean_inc(v_k_7082_);
lean_dec(v_impl_6967_);
v___x_7085_ = lean_box(0);
v_isShared_7086_ = v_isSharedCheck_7094_;
goto v_resetjp_7084_;
}
v_resetjp_7084_:
{
lean_object* v___x_7087_; lean_object* v___x_7089_; 
v___x_7087_ = lean_unsigned_to_nat(3u);
if (v_isShared_7086_ == 0)
{
lean_ctor_set(v___x_7085_, 4, v_l_7052_);
lean_ctor_set(v___x_7085_, 2, v_v_6959_);
lean_ctor_set(v___x_7085_, 1, v_k_6958_);
lean_ctor_set(v___x_7085_, 0, v___x_6968_);
v___x_7089_ = v___x_7085_;
goto v_reusejp_7088_;
}
else
{
lean_object* v_reuseFailAlloc_7093_; 
v_reuseFailAlloc_7093_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7093_, 0, v___x_6968_);
lean_ctor_set(v_reuseFailAlloc_7093_, 1, v_k_6958_);
lean_ctor_set(v_reuseFailAlloc_7093_, 2, v_v_6959_);
lean_ctor_set(v_reuseFailAlloc_7093_, 3, v_l_7052_);
lean_ctor_set(v_reuseFailAlloc_7093_, 4, v_l_7052_);
v___x_7089_ = v_reuseFailAlloc_7093_;
goto v_reusejp_7088_;
}
v_reusejp_7088_:
{
lean_object* v___x_7091_; 
if (v_isShared_6964_ == 0)
{
lean_ctor_set(v___x_6963_, 4, v_r_7081_);
lean_ctor_set(v___x_6963_, 3, v___x_7089_);
lean_ctor_set(v___x_6963_, 2, v_v_7083_);
lean_ctor_set(v___x_6963_, 1, v_k_7082_);
lean_ctor_set(v___x_6963_, 0, v___x_7087_);
v___x_7091_ = v___x_6963_;
goto v_reusejp_7090_;
}
else
{
lean_object* v_reuseFailAlloc_7092_; 
v_reuseFailAlloc_7092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7092_, 0, v___x_7087_);
lean_ctor_set(v_reuseFailAlloc_7092_, 1, v_k_7082_);
lean_ctor_set(v_reuseFailAlloc_7092_, 2, v_v_7083_);
lean_ctor_set(v_reuseFailAlloc_7092_, 3, v___x_7089_);
lean_ctor_set(v_reuseFailAlloc_7092_, 4, v_r_7081_);
v___x_7091_ = v_reuseFailAlloc_7092_;
goto v_reusejp_7090_;
}
v_reusejp_7090_:
{
return v___x_7091_;
}
}
}
}
else
{
lean_object* v___x_7098_; lean_object* v___x_7100_; 
v___x_7098_ = lean_unsigned_to_nat(2u);
if (v_isShared_6964_ == 0)
{
lean_ctor_set(v___x_6963_, 4, v_impl_6967_);
lean_ctor_set(v___x_6963_, 3, v_r_7081_);
lean_ctor_set(v___x_6963_, 0, v___x_7098_);
v___x_7100_ = v___x_6963_;
goto v_reusejp_7099_;
}
else
{
lean_object* v_reuseFailAlloc_7101_; 
v_reuseFailAlloc_7101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7101_, 0, v___x_7098_);
lean_ctor_set(v_reuseFailAlloc_7101_, 1, v_k_6958_);
lean_ctor_set(v_reuseFailAlloc_7101_, 2, v_v_6959_);
lean_ctor_set(v_reuseFailAlloc_7101_, 3, v_r_7081_);
lean_ctor_set(v_reuseFailAlloc_7101_, 4, v_impl_6967_);
v___x_7100_ = v_reuseFailAlloc_7101_;
goto v_reusejp_7099_;
}
v_reusejp_7099_:
{
return v___x_7100_;
}
}
}
}
}
else
{
lean_object* v___x_7103_; 
lean_dec(v_v_6959_);
lean_dec(v_k_6958_);
if (v_isShared_6964_ == 0)
{
lean_ctor_set(v___x_6963_, 2, v_v_6955_);
lean_ctor_set(v___x_6963_, 1, v_k_6954_);
v___x_7103_ = v___x_6963_;
goto v_reusejp_7102_;
}
else
{
lean_object* v_reuseFailAlloc_7104_; 
v_reuseFailAlloc_7104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7104_, 0, v_size_6957_);
lean_ctor_set(v_reuseFailAlloc_7104_, 1, v_k_6954_);
lean_ctor_set(v_reuseFailAlloc_7104_, 2, v_v_6955_);
lean_ctor_set(v_reuseFailAlloc_7104_, 3, v_l_6960_);
lean_ctor_set(v_reuseFailAlloc_7104_, 4, v_r_6961_);
v___x_7103_ = v_reuseFailAlloc_7104_;
goto v_reusejp_7102_;
}
v_reusejp_7102_:
{
return v___x_7103_;
}
}
}
else
{
lean_object* v_impl_7105_; lean_object* v___x_7106_; 
lean_dec(v_size_6957_);
v_impl_7105_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_6954_, v_v_6955_, v_l_6960_);
v___x_7106_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_6961_) == 0)
{
lean_object* v_size_7107_; lean_object* v_size_7108_; lean_object* v_k_7109_; lean_object* v_v_7110_; lean_object* v_l_7111_; lean_object* v_r_7112_; lean_object* v___x_7113_; lean_object* v___x_7114_; uint8_t v___x_7115_; 
v_size_7107_ = lean_ctor_get(v_r_6961_, 0);
v_size_7108_ = lean_ctor_get(v_impl_7105_, 0);
lean_inc(v_size_7108_);
v_k_7109_ = lean_ctor_get(v_impl_7105_, 1);
lean_inc(v_k_7109_);
v_v_7110_ = lean_ctor_get(v_impl_7105_, 2);
lean_inc(v_v_7110_);
v_l_7111_ = lean_ctor_get(v_impl_7105_, 3);
lean_inc(v_l_7111_);
v_r_7112_ = lean_ctor_get(v_impl_7105_, 4);
lean_inc(v_r_7112_);
v___x_7113_ = lean_unsigned_to_nat(3u);
v___x_7114_ = lean_nat_mul(v___x_7113_, v_size_7107_);
v___x_7115_ = lean_nat_dec_lt(v___x_7114_, v_size_7108_);
lean_dec(v___x_7114_);
if (v___x_7115_ == 0)
{
lean_object* v___x_7116_; lean_object* v___x_7117_; lean_object* v___x_7119_; 
lean_dec(v_r_7112_);
lean_dec(v_l_7111_);
lean_dec(v_v_7110_);
lean_dec(v_k_7109_);
v___x_7116_ = lean_nat_add(v___x_7106_, v_size_7108_);
lean_dec(v_size_7108_);
v___x_7117_ = lean_nat_add(v___x_7116_, v_size_7107_);
lean_dec(v___x_7116_);
if (v_isShared_6964_ == 0)
{
lean_ctor_set(v___x_6963_, 3, v_impl_7105_);
lean_ctor_set(v___x_6963_, 0, v___x_7117_);
v___x_7119_ = v___x_6963_;
goto v_reusejp_7118_;
}
else
{
lean_object* v_reuseFailAlloc_7120_; 
v_reuseFailAlloc_7120_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7120_, 0, v___x_7117_);
lean_ctor_set(v_reuseFailAlloc_7120_, 1, v_k_6958_);
lean_ctor_set(v_reuseFailAlloc_7120_, 2, v_v_6959_);
lean_ctor_set(v_reuseFailAlloc_7120_, 3, v_impl_7105_);
lean_ctor_set(v_reuseFailAlloc_7120_, 4, v_r_6961_);
v___x_7119_ = v_reuseFailAlloc_7120_;
goto v_reusejp_7118_;
}
v_reusejp_7118_:
{
return v___x_7119_;
}
}
else
{
lean_object* v___x_7122_; uint8_t v_isShared_7123_; uint8_t v_isSharedCheck_7186_; 
v_isSharedCheck_7186_ = !lean_is_exclusive(v_impl_7105_);
if (v_isSharedCheck_7186_ == 0)
{
lean_object* v_unused_7187_; lean_object* v_unused_7188_; lean_object* v_unused_7189_; lean_object* v_unused_7190_; lean_object* v_unused_7191_; 
v_unused_7187_ = lean_ctor_get(v_impl_7105_, 4);
lean_dec(v_unused_7187_);
v_unused_7188_ = lean_ctor_get(v_impl_7105_, 3);
lean_dec(v_unused_7188_);
v_unused_7189_ = lean_ctor_get(v_impl_7105_, 2);
lean_dec(v_unused_7189_);
v_unused_7190_ = lean_ctor_get(v_impl_7105_, 1);
lean_dec(v_unused_7190_);
v_unused_7191_ = lean_ctor_get(v_impl_7105_, 0);
lean_dec(v_unused_7191_);
v___x_7122_ = v_impl_7105_;
v_isShared_7123_ = v_isSharedCheck_7186_;
goto v_resetjp_7121_;
}
else
{
lean_dec(v_impl_7105_);
v___x_7122_ = lean_box(0);
v_isShared_7123_ = v_isSharedCheck_7186_;
goto v_resetjp_7121_;
}
v_resetjp_7121_:
{
lean_object* v_size_7124_; lean_object* v_size_7125_; lean_object* v_k_7126_; lean_object* v_v_7127_; lean_object* v_l_7128_; lean_object* v_r_7129_; lean_object* v___x_7130_; lean_object* v___x_7131_; uint8_t v___x_7132_; 
v_size_7124_ = lean_ctor_get(v_l_7111_, 0);
v_size_7125_ = lean_ctor_get(v_r_7112_, 0);
v_k_7126_ = lean_ctor_get(v_r_7112_, 1);
v_v_7127_ = lean_ctor_get(v_r_7112_, 2);
v_l_7128_ = lean_ctor_get(v_r_7112_, 3);
v_r_7129_ = lean_ctor_get(v_r_7112_, 4);
v___x_7130_ = lean_unsigned_to_nat(2u);
v___x_7131_ = lean_nat_mul(v___x_7130_, v_size_7124_);
v___x_7132_ = lean_nat_dec_lt(v_size_7125_, v___x_7131_);
lean_dec(v___x_7131_);
if (v___x_7132_ == 0)
{
lean_object* v___x_7134_; uint8_t v_isShared_7135_; uint8_t v_isSharedCheck_7161_; 
lean_inc(v_r_7129_);
lean_inc(v_l_7128_);
lean_inc(v_v_7127_);
lean_inc(v_k_7126_);
v_isSharedCheck_7161_ = !lean_is_exclusive(v_r_7112_);
if (v_isSharedCheck_7161_ == 0)
{
lean_object* v_unused_7162_; lean_object* v_unused_7163_; lean_object* v_unused_7164_; lean_object* v_unused_7165_; lean_object* v_unused_7166_; 
v_unused_7162_ = lean_ctor_get(v_r_7112_, 4);
lean_dec(v_unused_7162_);
v_unused_7163_ = lean_ctor_get(v_r_7112_, 3);
lean_dec(v_unused_7163_);
v_unused_7164_ = lean_ctor_get(v_r_7112_, 2);
lean_dec(v_unused_7164_);
v_unused_7165_ = lean_ctor_get(v_r_7112_, 1);
lean_dec(v_unused_7165_);
v_unused_7166_ = lean_ctor_get(v_r_7112_, 0);
lean_dec(v_unused_7166_);
v___x_7134_ = v_r_7112_;
v_isShared_7135_ = v_isSharedCheck_7161_;
goto v_resetjp_7133_;
}
else
{
lean_dec(v_r_7112_);
v___x_7134_ = lean_box(0);
v_isShared_7135_ = v_isSharedCheck_7161_;
goto v_resetjp_7133_;
}
v_resetjp_7133_:
{
lean_object* v___x_7136_; lean_object* v___x_7137_; lean_object* v___y_7139_; lean_object* v___y_7140_; lean_object* v___y_7141_; lean_object* v___x_7149_; lean_object* v___y_7151_; 
v___x_7136_ = lean_nat_add(v___x_7106_, v_size_7108_);
lean_dec(v_size_7108_);
v___x_7137_ = lean_nat_add(v___x_7136_, v_size_7107_);
lean_dec(v___x_7136_);
v___x_7149_ = lean_nat_add(v___x_7106_, v_size_7124_);
if (lean_obj_tag(v_l_7128_) == 0)
{
lean_object* v_size_7159_; 
v_size_7159_ = lean_ctor_get(v_l_7128_, 0);
lean_inc(v_size_7159_);
v___y_7151_ = v_size_7159_;
goto v___jp_7150_;
}
else
{
lean_object* v___x_7160_; 
v___x_7160_ = lean_unsigned_to_nat(0u);
v___y_7151_ = v___x_7160_;
goto v___jp_7150_;
}
v___jp_7138_:
{
lean_object* v___x_7142_; lean_object* v___x_7144_; 
v___x_7142_ = lean_nat_add(v___y_7140_, v___y_7141_);
lean_dec(v___y_7141_);
lean_dec(v___y_7140_);
if (v_isShared_7135_ == 0)
{
lean_ctor_set(v___x_7134_, 4, v_r_6961_);
lean_ctor_set(v___x_7134_, 3, v_r_7129_);
lean_ctor_set(v___x_7134_, 2, v_v_6959_);
lean_ctor_set(v___x_7134_, 1, v_k_6958_);
lean_ctor_set(v___x_7134_, 0, v___x_7142_);
v___x_7144_ = v___x_7134_;
goto v_reusejp_7143_;
}
else
{
lean_object* v_reuseFailAlloc_7148_; 
v_reuseFailAlloc_7148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7148_, 0, v___x_7142_);
lean_ctor_set(v_reuseFailAlloc_7148_, 1, v_k_6958_);
lean_ctor_set(v_reuseFailAlloc_7148_, 2, v_v_6959_);
lean_ctor_set(v_reuseFailAlloc_7148_, 3, v_r_7129_);
lean_ctor_set(v_reuseFailAlloc_7148_, 4, v_r_6961_);
v___x_7144_ = v_reuseFailAlloc_7148_;
goto v_reusejp_7143_;
}
v_reusejp_7143_:
{
lean_object* v___x_7146_; 
if (v_isShared_7123_ == 0)
{
lean_ctor_set(v___x_7122_, 4, v___x_7144_);
lean_ctor_set(v___x_7122_, 3, v___y_7139_);
lean_ctor_set(v___x_7122_, 2, v_v_7127_);
lean_ctor_set(v___x_7122_, 1, v_k_7126_);
lean_ctor_set(v___x_7122_, 0, v___x_7137_);
v___x_7146_ = v___x_7122_;
goto v_reusejp_7145_;
}
else
{
lean_object* v_reuseFailAlloc_7147_; 
v_reuseFailAlloc_7147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7147_, 0, v___x_7137_);
lean_ctor_set(v_reuseFailAlloc_7147_, 1, v_k_7126_);
lean_ctor_set(v_reuseFailAlloc_7147_, 2, v_v_7127_);
lean_ctor_set(v_reuseFailAlloc_7147_, 3, v___y_7139_);
lean_ctor_set(v_reuseFailAlloc_7147_, 4, v___x_7144_);
v___x_7146_ = v_reuseFailAlloc_7147_;
goto v_reusejp_7145_;
}
v_reusejp_7145_:
{
return v___x_7146_;
}
}
}
v___jp_7150_:
{
lean_object* v___x_7152_; lean_object* v___x_7154_; 
v___x_7152_ = lean_nat_add(v___x_7149_, v___y_7151_);
lean_dec(v___y_7151_);
lean_dec(v___x_7149_);
if (v_isShared_6964_ == 0)
{
lean_ctor_set(v___x_6963_, 4, v_l_7128_);
lean_ctor_set(v___x_6963_, 3, v_l_7111_);
lean_ctor_set(v___x_6963_, 2, v_v_7110_);
lean_ctor_set(v___x_6963_, 1, v_k_7109_);
lean_ctor_set(v___x_6963_, 0, v___x_7152_);
v___x_7154_ = v___x_6963_;
goto v_reusejp_7153_;
}
else
{
lean_object* v_reuseFailAlloc_7158_; 
v_reuseFailAlloc_7158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7158_, 0, v___x_7152_);
lean_ctor_set(v_reuseFailAlloc_7158_, 1, v_k_7109_);
lean_ctor_set(v_reuseFailAlloc_7158_, 2, v_v_7110_);
lean_ctor_set(v_reuseFailAlloc_7158_, 3, v_l_7111_);
lean_ctor_set(v_reuseFailAlloc_7158_, 4, v_l_7128_);
v___x_7154_ = v_reuseFailAlloc_7158_;
goto v_reusejp_7153_;
}
v_reusejp_7153_:
{
lean_object* v___x_7155_; 
v___x_7155_ = lean_nat_add(v___x_7106_, v_size_7107_);
if (lean_obj_tag(v_r_7129_) == 0)
{
lean_object* v_size_7156_; 
v_size_7156_ = lean_ctor_get(v_r_7129_, 0);
lean_inc(v_size_7156_);
v___y_7139_ = v___x_7154_;
v___y_7140_ = v___x_7155_;
v___y_7141_ = v_size_7156_;
goto v___jp_7138_;
}
else
{
lean_object* v___x_7157_; 
v___x_7157_ = lean_unsigned_to_nat(0u);
v___y_7139_ = v___x_7154_;
v___y_7140_ = v___x_7155_;
v___y_7141_ = v___x_7157_;
goto v___jp_7138_;
}
}
}
}
}
else
{
lean_object* v___x_7167_; lean_object* v___x_7168_; lean_object* v___x_7169_; lean_object* v___x_7170_; lean_object* v___x_7172_; 
lean_del_object(v___x_6963_);
v___x_7167_ = lean_nat_add(v___x_7106_, v_size_7108_);
lean_dec(v_size_7108_);
v___x_7168_ = lean_nat_add(v___x_7167_, v_size_7107_);
lean_dec(v___x_7167_);
v___x_7169_ = lean_nat_add(v___x_7106_, v_size_7107_);
v___x_7170_ = lean_nat_add(v___x_7169_, v_size_7125_);
lean_dec(v___x_7169_);
lean_inc_ref(v_r_6961_);
if (v_isShared_7123_ == 0)
{
lean_ctor_set(v___x_7122_, 4, v_r_6961_);
lean_ctor_set(v___x_7122_, 3, v_r_7112_);
lean_ctor_set(v___x_7122_, 2, v_v_6959_);
lean_ctor_set(v___x_7122_, 1, v_k_6958_);
lean_ctor_set(v___x_7122_, 0, v___x_7170_);
v___x_7172_ = v___x_7122_;
goto v_reusejp_7171_;
}
else
{
lean_object* v_reuseFailAlloc_7185_; 
v_reuseFailAlloc_7185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7185_, 0, v___x_7170_);
lean_ctor_set(v_reuseFailAlloc_7185_, 1, v_k_6958_);
lean_ctor_set(v_reuseFailAlloc_7185_, 2, v_v_6959_);
lean_ctor_set(v_reuseFailAlloc_7185_, 3, v_r_7112_);
lean_ctor_set(v_reuseFailAlloc_7185_, 4, v_r_6961_);
v___x_7172_ = v_reuseFailAlloc_7185_;
goto v_reusejp_7171_;
}
v_reusejp_7171_:
{
lean_object* v___x_7174_; uint8_t v_isShared_7175_; uint8_t v_isSharedCheck_7179_; 
v_isSharedCheck_7179_ = !lean_is_exclusive(v_r_6961_);
if (v_isSharedCheck_7179_ == 0)
{
lean_object* v_unused_7180_; lean_object* v_unused_7181_; lean_object* v_unused_7182_; lean_object* v_unused_7183_; lean_object* v_unused_7184_; 
v_unused_7180_ = lean_ctor_get(v_r_6961_, 4);
lean_dec(v_unused_7180_);
v_unused_7181_ = lean_ctor_get(v_r_6961_, 3);
lean_dec(v_unused_7181_);
v_unused_7182_ = lean_ctor_get(v_r_6961_, 2);
lean_dec(v_unused_7182_);
v_unused_7183_ = lean_ctor_get(v_r_6961_, 1);
lean_dec(v_unused_7183_);
v_unused_7184_ = lean_ctor_get(v_r_6961_, 0);
lean_dec(v_unused_7184_);
v___x_7174_ = v_r_6961_;
v_isShared_7175_ = v_isSharedCheck_7179_;
goto v_resetjp_7173_;
}
else
{
lean_dec(v_r_6961_);
v___x_7174_ = lean_box(0);
v_isShared_7175_ = v_isSharedCheck_7179_;
goto v_resetjp_7173_;
}
v_resetjp_7173_:
{
lean_object* v___x_7177_; 
if (v_isShared_7175_ == 0)
{
lean_ctor_set(v___x_7174_, 4, v___x_7172_);
lean_ctor_set(v___x_7174_, 3, v_l_7111_);
lean_ctor_set(v___x_7174_, 2, v_v_7110_);
lean_ctor_set(v___x_7174_, 1, v_k_7109_);
lean_ctor_set(v___x_7174_, 0, v___x_7168_);
v___x_7177_ = v___x_7174_;
goto v_reusejp_7176_;
}
else
{
lean_object* v_reuseFailAlloc_7178_; 
v_reuseFailAlloc_7178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7178_, 0, v___x_7168_);
lean_ctor_set(v_reuseFailAlloc_7178_, 1, v_k_7109_);
lean_ctor_set(v_reuseFailAlloc_7178_, 2, v_v_7110_);
lean_ctor_set(v_reuseFailAlloc_7178_, 3, v_l_7111_);
lean_ctor_set(v_reuseFailAlloc_7178_, 4, v___x_7172_);
v___x_7177_ = v_reuseFailAlloc_7178_;
goto v_reusejp_7176_;
}
v_reusejp_7176_:
{
return v___x_7177_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_7192_; 
v_l_7192_ = lean_ctor_get(v_impl_7105_, 3);
lean_inc(v_l_7192_);
if (lean_obj_tag(v_l_7192_) == 0)
{
lean_object* v_r_7193_; lean_object* v_k_7194_; lean_object* v_v_7195_; lean_object* v___x_7197_; uint8_t v_isShared_7198_; uint8_t v_isSharedCheck_7206_; 
v_r_7193_ = lean_ctor_get(v_impl_7105_, 4);
v_k_7194_ = lean_ctor_get(v_impl_7105_, 1);
v_v_7195_ = lean_ctor_get(v_impl_7105_, 2);
v_isSharedCheck_7206_ = !lean_is_exclusive(v_impl_7105_);
if (v_isSharedCheck_7206_ == 0)
{
lean_object* v_unused_7207_; lean_object* v_unused_7208_; 
v_unused_7207_ = lean_ctor_get(v_impl_7105_, 3);
lean_dec(v_unused_7207_);
v_unused_7208_ = lean_ctor_get(v_impl_7105_, 0);
lean_dec(v_unused_7208_);
v___x_7197_ = v_impl_7105_;
v_isShared_7198_ = v_isSharedCheck_7206_;
goto v_resetjp_7196_;
}
else
{
lean_inc(v_r_7193_);
lean_inc(v_v_7195_);
lean_inc(v_k_7194_);
lean_dec(v_impl_7105_);
v___x_7197_ = lean_box(0);
v_isShared_7198_ = v_isSharedCheck_7206_;
goto v_resetjp_7196_;
}
v_resetjp_7196_:
{
lean_object* v___x_7199_; lean_object* v___x_7201_; 
v___x_7199_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_7193_);
if (v_isShared_7198_ == 0)
{
lean_ctor_set(v___x_7197_, 3, v_r_7193_);
lean_ctor_set(v___x_7197_, 2, v_v_6959_);
lean_ctor_set(v___x_7197_, 1, v_k_6958_);
lean_ctor_set(v___x_7197_, 0, v___x_7106_);
v___x_7201_ = v___x_7197_;
goto v_reusejp_7200_;
}
else
{
lean_object* v_reuseFailAlloc_7205_; 
v_reuseFailAlloc_7205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7205_, 0, v___x_7106_);
lean_ctor_set(v_reuseFailAlloc_7205_, 1, v_k_6958_);
lean_ctor_set(v_reuseFailAlloc_7205_, 2, v_v_6959_);
lean_ctor_set(v_reuseFailAlloc_7205_, 3, v_r_7193_);
lean_ctor_set(v_reuseFailAlloc_7205_, 4, v_r_7193_);
v___x_7201_ = v_reuseFailAlloc_7205_;
goto v_reusejp_7200_;
}
v_reusejp_7200_:
{
lean_object* v___x_7203_; 
if (v_isShared_6964_ == 0)
{
lean_ctor_set(v___x_6963_, 4, v___x_7201_);
lean_ctor_set(v___x_6963_, 3, v_l_7192_);
lean_ctor_set(v___x_6963_, 2, v_v_7195_);
lean_ctor_set(v___x_6963_, 1, v_k_7194_);
lean_ctor_set(v___x_6963_, 0, v___x_7199_);
v___x_7203_ = v___x_6963_;
goto v_reusejp_7202_;
}
else
{
lean_object* v_reuseFailAlloc_7204_; 
v_reuseFailAlloc_7204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7204_, 0, v___x_7199_);
lean_ctor_set(v_reuseFailAlloc_7204_, 1, v_k_7194_);
lean_ctor_set(v_reuseFailAlloc_7204_, 2, v_v_7195_);
lean_ctor_set(v_reuseFailAlloc_7204_, 3, v_l_7192_);
lean_ctor_set(v_reuseFailAlloc_7204_, 4, v___x_7201_);
v___x_7203_ = v_reuseFailAlloc_7204_;
goto v_reusejp_7202_;
}
v_reusejp_7202_:
{
return v___x_7203_;
}
}
}
}
else
{
lean_object* v_r_7209_; 
v_r_7209_ = lean_ctor_get(v_impl_7105_, 4);
lean_inc(v_r_7209_);
if (lean_obj_tag(v_r_7209_) == 0)
{
lean_object* v_k_7210_; lean_object* v_v_7211_; lean_object* v___x_7213_; uint8_t v_isShared_7214_; uint8_t v_isSharedCheck_7234_; 
v_k_7210_ = lean_ctor_get(v_impl_7105_, 1);
v_v_7211_ = lean_ctor_get(v_impl_7105_, 2);
v_isSharedCheck_7234_ = !lean_is_exclusive(v_impl_7105_);
if (v_isSharedCheck_7234_ == 0)
{
lean_object* v_unused_7235_; lean_object* v_unused_7236_; lean_object* v_unused_7237_; 
v_unused_7235_ = lean_ctor_get(v_impl_7105_, 4);
lean_dec(v_unused_7235_);
v_unused_7236_ = lean_ctor_get(v_impl_7105_, 3);
lean_dec(v_unused_7236_);
v_unused_7237_ = lean_ctor_get(v_impl_7105_, 0);
lean_dec(v_unused_7237_);
v___x_7213_ = v_impl_7105_;
v_isShared_7214_ = v_isSharedCheck_7234_;
goto v_resetjp_7212_;
}
else
{
lean_inc(v_v_7211_);
lean_inc(v_k_7210_);
lean_dec(v_impl_7105_);
v___x_7213_ = lean_box(0);
v_isShared_7214_ = v_isSharedCheck_7234_;
goto v_resetjp_7212_;
}
v_resetjp_7212_:
{
lean_object* v_k_7215_; lean_object* v_v_7216_; lean_object* v___x_7218_; uint8_t v_isShared_7219_; uint8_t v_isSharedCheck_7230_; 
v_k_7215_ = lean_ctor_get(v_r_7209_, 1);
v_v_7216_ = lean_ctor_get(v_r_7209_, 2);
v_isSharedCheck_7230_ = !lean_is_exclusive(v_r_7209_);
if (v_isSharedCheck_7230_ == 0)
{
lean_object* v_unused_7231_; lean_object* v_unused_7232_; lean_object* v_unused_7233_; 
v_unused_7231_ = lean_ctor_get(v_r_7209_, 4);
lean_dec(v_unused_7231_);
v_unused_7232_ = lean_ctor_get(v_r_7209_, 3);
lean_dec(v_unused_7232_);
v_unused_7233_ = lean_ctor_get(v_r_7209_, 0);
lean_dec(v_unused_7233_);
v___x_7218_ = v_r_7209_;
v_isShared_7219_ = v_isSharedCheck_7230_;
goto v_resetjp_7217_;
}
else
{
lean_inc(v_v_7216_);
lean_inc(v_k_7215_);
lean_dec(v_r_7209_);
v___x_7218_ = lean_box(0);
v_isShared_7219_ = v_isSharedCheck_7230_;
goto v_resetjp_7217_;
}
v_resetjp_7217_:
{
lean_object* v___x_7220_; lean_object* v___x_7222_; 
v___x_7220_ = lean_unsigned_to_nat(3u);
if (v_isShared_7219_ == 0)
{
lean_ctor_set(v___x_7218_, 4, v_l_7192_);
lean_ctor_set(v___x_7218_, 3, v_l_7192_);
lean_ctor_set(v___x_7218_, 2, v_v_7211_);
lean_ctor_set(v___x_7218_, 1, v_k_7210_);
lean_ctor_set(v___x_7218_, 0, v___x_7106_);
v___x_7222_ = v___x_7218_;
goto v_reusejp_7221_;
}
else
{
lean_object* v_reuseFailAlloc_7229_; 
v_reuseFailAlloc_7229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7229_, 0, v___x_7106_);
lean_ctor_set(v_reuseFailAlloc_7229_, 1, v_k_7210_);
lean_ctor_set(v_reuseFailAlloc_7229_, 2, v_v_7211_);
lean_ctor_set(v_reuseFailAlloc_7229_, 3, v_l_7192_);
lean_ctor_set(v_reuseFailAlloc_7229_, 4, v_l_7192_);
v___x_7222_ = v_reuseFailAlloc_7229_;
goto v_reusejp_7221_;
}
v_reusejp_7221_:
{
lean_object* v___x_7224_; 
if (v_isShared_7214_ == 0)
{
lean_ctor_set(v___x_7213_, 4, v_l_7192_);
lean_ctor_set(v___x_7213_, 2, v_v_6959_);
lean_ctor_set(v___x_7213_, 1, v_k_6958_);
lean_ctor_set(v___x_7213_, 0, v___x_7106_);
v___x_7224_ = v___x_7213_;
goto v_reusejp_7223_;
}
else
{
lean_object* v_reuseFailAlloc_7228_; 
v_reuseFailAlloc_7228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7228_, 0, v___x_7106_);
lean_ctor_set(v_reuseFailAlloc_7228_, 1, v_k_6958_);
lean_ctor_set(v_reuseFailAlloc_7228_, 2, v_v_6959_);
lean_ctor_set(v_reuseFailAlloc_7228_, 3, v_l_7192_);
lean_ctor_set(v_reuseFailAlloc_7228_, 4, v_l_7192_);
v___x_7224_ = v_reuseFailAlloc_7228_;
goto v_reusejp_7223_;
}
v_reusejp_7223_:
{
lean_object* v___x_7226_; 
if (v_isShared_6964_ == 0)
{
lean_ctor_set(v___x_6963_, 4, v___x_7224_);
lean_ctor_set(v___x_6963_, 3, v___x_7222_);
lean_ctor_set(v___x_6963_, 2, v_v_7216_);
lean_ctor_set(v___x_6963_, 1, v_k_7215_);
lean_ctor_set(v___x_6963_, 0, v___x_7220_);
v___x_7226_ = v___x_6963_;
goto v_reusejp_7225_;
}
else
{
lean_object* v_reuseFailAlloc_7227_; 
v_reuseFailAlloc_7227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7227_, 0, v___x_7220_);
lean_ctor_set(v_reuseFailAlloc_7227_, 1, v_k_7215_);
lean_ctor_set(v_reuseFailAlloc_7227_, 2, v_v_7216_);
lean_ctor_set(v_reuseFailAlloc_7227_, 3, v___x_7222_);
lean_ctor_set(v_reuseFailAlloc_7227_, 4, v___x_7224_);
v___x_7226_ = v_reuseFailAlloc_7227_;
goto v_reusejp_7225_;
}
v_reusejp_7225_:
{
return v___x_7226_;
}
}
}
}
}
}
else
{
lean_object* v___x_7238_; lean_object* v___x_7240_; 
v___x_7238_ = lean_unsigned_to_nat(2u);
if (v_isShared_6964_ == 0)
{
lean_ctor_set(v___x_6963_, 4, v_r_7209_);
lean_ctor_set(v___x_6963_, 3, v_impl_7105_);
lean_ctor_set(v___x_6963_, 0, v___x_7238_);
v___x_7240_ = v___x_6963_;
goto v_reusejp_7239_;
}
else
{
lean_object* v_reuseFailAlloc_7241_; 
v_reuseFailAlloc_7241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7241_, 0, v___x_7238_);
lean_ctor_set(v_reuseFailAlloc_7241_, 1, v_k_6958_);
lean_ctor_set(v_reuseFailAlloc_7241_, 2, v_v_6959_);
lean_ctor_set(v_reuseFailAlloc_7241_, 3, v_impl_7105_);
lean_ctor_set(v_reuseFailAlloc_7241_, 4, v_r_7209_);
v___x_7240_ = v_reuseFailAlloc_7241_;
goto v_reusejp_7239_;
}
v_reusejp_7239_:
{
return v___x_7240_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_7243_; lean_object* v___x_7244_; 
v___x_7243_ = lean_unsigned_to_nat(1u);
v___x_7244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_7244_, 0, v___x_7243_);
lean_ctor_set(v___x_7244_, 1, v_k_6954_);
lean_ctor_set(v___x_7244_, 2, v_v_6955_);
lean_ctor_set(v___x_7244_, 3, v_t_6956_);
lean_ctor_set(v___x_7244_, 4, v_t_6956_);
return v___x_7244_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(lean_object* v_lib_7245_, lean_object* v_ps_7246_, lean_object* v_v_7247_, lean_object* v_o_7248_){
_start:
{
lean_object* v_name_7249_; lean_object* v_deps_7250_; lean_object* v_o_7251_; uint8_t v___x_7252_; 
v_name_7249_ = lean_ctor_get(v_lib_7245_, 1);
lean_inc_ref(v_name_7249_);
v_deps_7250_ = lean_ctor_get(v_lib_7245_, 2);
lean_inc_ref(v_deps_7250_);
v_o_7251_ = lean_array_push(v_o_7248_, v_lib_7245_);
v___x_7252_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_name_7249_, v_v_7247_);
if (v___x_7252_ == 0)
{
uint8_t v___x_7253_; 
v___x_7253_ = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(v_name_7249_, v_ps_7246_);
if (v___x_7253_ == 0)
{
lean_object* v_ps_7254_; lean_object* v___y_7256_; 
lean_inc_ref(v_name_7249_);
v_ps_7254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_ps_7254_, 0, v_name_7249_);
lean_ctor_set(v_ps_7254_, 1, v_ps_7246_);
if (v___x_7252_ == 0)
{
lean_object* v___x_7270_; lean_object* v___x_7271_; 
v___x_7270_ = lean_box(0);
v___x_7271_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_name_7249_, v___x_7270_, v_v_7247_);
v___y_7256_ = v___x_7271_;
goto v___jp_7255_;
}
else
{
lean_dec_ref(v_name_7249_);
v___y_7256_ = v_v_7247_;
goto v___jp_7255_;
}
v___jp_7255_:
{
lean_object* v___x_7257_; lean_object* v___x_7258_; lean_object* v___x_7259_; uint8_t v___x_7260_; 
v___x_7257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7257_, 0, v___y_7256_);
lean_ctor_set(v___x_7257_, 1, v_o_7251_);
v___x_7258_ = lean_unsigned_to_nat(0u);
v___x_7259_ = lean_array_get_size(v_deps_7250_);
v___x_7260_ = lean_nat_dec_lt(v___x_7258_, v___x_7259_);
if (v___x_7260_ == 0)
{
lean_object* v___x_7261_; 
lean_dec_ref(v_ps_7254_);
lean_dec_ref(v_deps_7250_);
v___x_7261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7261_, 0, v___x_7257_);
return v___x_7261_;
}
else
{
uint8_t v___x_7262_; 
v___x_7262_ = lean_nat_dec_le(v___x_7259_, v___x_7259_);
if (v___x_7262_ == 0)
{
if (v___x_7260_ == 0)
{
lean_object* v___x_7263_; 
lean_dec_ref(v_ps_7254_);
lean_dec_ref(v_deps_7250_);
v___x_7263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7263_, 0, v___x_7257_);
return v___x_7263_;
}
else
{
size_t v___x_7264_; size_t v___x_7265_; lean_object* v___x_7266_; 
v___x_7264_ = ((size_t)0ULL);
v___x_7265_ = lean_usize_of_nat(v___x_7259_);
v___x_7266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7254_, v_deps_7250_, v___x_7264_, v___x_7265_, v___x_7257_);
lean_dec_ref(v_deps_7250_);
return v___x_7266_;
}
}
else
{
size_t v___x_7267_; size_t v___x_7268_; lean_object* v___x_7269_; 
v___x_7267_ = ((size_t)0ULL);
v___x_7268_ = lean_usize_of_nat(v___x_7259_);
v___x_7269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7254_, v_deps_7250_, v___x_7267_, v___x_7268_, v___x_7257_);
lean_dec_ref(v_deps_7250_);
return v___x_7269_;
}
}
}
}
else
{
lean_object* v___x_7272_; lean_object* v___x_7273_; 
lean_dec_ref(v_o_7251_);
lean_dec_ref(v_deps_7250_);
lean_dec(v_v_7247_);
v___x_7272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7272_, 0, v_name_7249_);
lean_ctor_set(v___x_7272_, 1, v_ps_7246_);
v___x_7273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7273_, 0, v___x_7272_);
return v___x_7273_;
}
}
else
{
lean_object* v___x_7274_; lean_object* v___x_7275_; 
lean_dec_ref(v_deps_7250_);
lean_dec_ref(v_name_7249_);
lean_dec(v_ps_7246_);
v___x_7274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7274_, 0, v_v_7247_);
lean_ctor_set(v___x_7274_, 1, v_o_7251_);
v___x_7275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7275_, 0, v___x_7274_);
return v___x_7275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(lean_object* v_ps_7276_, lean_object* v_as_7277_, size_t v_i_7278_, size_t v_stop_7279_, lean_object* v_b_7280_){
_start:
{
uint8_t v___x_7281_; 
v___x_7281_ = lean_usize_dec_eq(v_i_7278_, v_stop_7279_);
if (v___x_7281_ == 0)
{
lean_object* v_fst_7282_; lean_object* v_snd_7283_; lean_object* v___x_7284_; lean_object* v___x_7285_; 
v_fst_7282_ = lean_ctor_get(v_b_7280_, 0);
lean_inc(v_fst_7282_);
v_snd_7283_ = lean_ctor_get(v_b_7280_, 1);
lean_inc(v_snd_7283_);
lean_dec_ref(v_b_7280_);
v___x_7284_ = lean_array_uget_borrowed(v_as_7277_, v_i_7278_);
lean_inc(v_ps_7276_);
lean_inc(v___x_7284_);
v___x_7285_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(v___x_7284_, v_ps_7276_, v_fst_7282_, v_snd_7283_);
if (lean_obj_tag(v___x_7285_) == 0)
{
lean_dec(v_ps_7276_);
return v___x_7285_;
}
else
{
lean_object* v_a_7286_; size_t v___x_7287_; size_t v___x_7288_; 
v_a_7286_ = lean_ctor_get(v___x_7285_, 0);
lean_inc(v_a_7286_);
lean_dec_ref(v___x_7285_);
v___x_7287_ = ((size_t)1ULL);
v___x_7288_ = lean_usize_add(v_i_7278_, v___x_7287_);
v_i_7278_ = v___x_7288_;
v_b_7280_ = v_a_7286_;
goto _start;
}
}
else
{
lean_object* v___x_7290_; 
lean_dec(v_ps_7276_);
v___x_7290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7290_, 0, v_b_7280_);
return v___x_7290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2___boxed(lean_object* v_ps_7291_, lean_object* v_as_7292_, lean_object* v_i_7293_, lean_object* v_stop_7294_, lean_object* v_b_7295_){
_start:
{
size_t v_i_boxed_7296_; size_t v_stop_boxed_7297_; lean_object* v_res_7298_; 
v_i_boxed_7296_ = lean_unbox_usize(v_i_7293_);
lean_dec(v_i_7293_);
v_stop_boxed_7297_ = lean_unbox_usize(v_stop_7294_);
lean_dec(v_stop_7294_);
v_res_7298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7291_, v_as_7292_, v_i_boxed_7296_, v_stop_boxed_7297_, v_b_7295_);
lean_dec_ref(v_as_7292_);
return v_res_7298_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(lean_object* v_00_u03b2_7299_, lean_object* v_k_7300_, lean_object* v_t_7301_){
_start:
{
uint8_t v___x_7302_; 
v___x_7302_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_k_7300_, v_t_7301_);
return v___x_7302_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___boxed(lean_object* v_00_u03b2_7303_, lean_object* v_k_7304_, lean_object* v_t_7305_){
_start:
{
uint8_t v_res_7306_; lean_object* v_r_7307_; 
v_res_7306_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(v_00_u03b2_7303_, v_k_7304_, v_t_7305_);
lean_dec(v_t_7305_);
lean_dec_ref(v_k_7304_);
v_r_7307_ = lean_box(v_res_7306_);
return v_r_7307_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3(lean_object* v_00_u03b2_7308_, lean_object* v_k_7309_, lean_object* v_v_7310_, lean_object* v_t_7311_, lean_object* v_hl_7312_){
_start:
{
lean_object* v___x_7313_; 
v___x_7313_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7309_, v_v_7310_, v_t_7311_);
return v___x_7313_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0(lean_object* v_a_7315_, lean_object* v_a_7316_){
_start:
{
if (lean_obj_tag(v_a_7315_) == 0)
{
lean_object* v___x_7317_; 
v___x_7317_ = l_List_reverse___redArg(v_a_7316_);
return v___x_7317_;
}
else
{
lean_object* v_head_7318_; lean_object* v_tail_7319_; lean_object* v___x_7321_; uint8_t v_isShared_7322_; uint8_t v_isSharedCheck_7329_; 
v_head_7318_ = lean_ctor_get(v_a_7315_, 0);
v_tail_7319_ = lean_ctor_get(v_a_7315_, 1);
v_isSharedCheck_7329_ = !lean_is_exclusive(v_a_7315_);
if (v_isSharedCheck_7329_ == 0)
{
v___x_7321_ = v_a_7315_;
v_isShared_7322_ = v_isSharedCheck_7329_;
goto v_resetjp_7320_;
}
else
{
lean_inc(v_tail_7319_);
lean_inc(v_head_7318_);
lean_dec(v_a_7315_);
v___x_7321_ = lean_box(0);
v_isShared_7322_ = v_isSharedCheck_7329_;
goto v_resetjp_7320_;
}
v_resetjp_7320_:
{
lean_object* v___x_7323_; lean_object* v___x_7324_; lean_object* v___x_7326_; 
v___x_7323_ = ((lean_object*)(l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0));
v___x_7324_ = lean_string_append(v___x_7323_, v_head_7318_);
lean_dec(v_head_7318_);
if (v_isShared_7322_ == 0)
{
lean_ctor_set(v___x_7321_, 1, v_a_7316_);
lean_ctor_set(v___x_7321_, 0, v___x_7324_);
v___x_7326_ = v___x_7321_;
goto v_reusejp_7325_;
}
else
{
lean_object* v_reuseFailAlloc_7328_; 
v_reuseFailAlloc_7328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7328_, 0, v___x_7324_);
lean_ctor_set(v_reuseFailAlloc_7328_, 1, v_a_7316_);
v___x_7326_ = v_reuseFailAlloc_7328_;
goto v_reusejp_7325_;
}
v_reusejp_7325_:
{
v_a_7315_ = v_tail_7319_;
v_a_7316_ = v___x_7326_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(lean_object* v_cycle_7330_){
_start:
{
lean_object* v___x_7331_; lean_object* v___x_7332_; lean_object* v___x_7333_; lean_object* v___x_7334_; 
v___x_7331_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__1));
v___x_7332_ = lean_box(0);
v___x_7333_ = l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0(v_cycle_7330_, v___x_7332_);
v___x_7334_ = l_String_intercalate(v___x_7331_, v___x_7333_);
return v___x_7334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(lean_object* v_as_7335_, size_t v_i_7336_, size_t v_stop_7337_, lean_object* v_b_7338_){
_start:
{
uint8_t v___x_7339_; 
v___x_7339_ = lean_usize_dec_eq(v_i_7336_, v_stop_7337_);
if (v___x_7339_ == 0)
{
lean_object* v_fst_7340_; lean_object* v_snd_7341_; lean_object* v___x_7342_; lean_object* v___x_7343_; lean_object* v___x_7344_; 
v_fst_7340_ = lean_ctor_get(v_b_7338_, 0);
lean_inc(v_fst_7340_);
v_snd_7341_ = lean_ctor_get(v_b_7338_, 1);
lean_inc(v_snd_7341_);
lean_dec_ref(v_b_7338_);
v___x_7342_ = lean_array_uget_borrowed(v_as_7335_, v_i_7336_);
v___x_7343_ = lean_box(0);
lean_inc(v___x_7342_);
v___x_7344_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(v___x_7342_, v___x_7343_, v_fst_7340_, v_snd_7341_);
if (lean_obj_tag(v___x_7344_) == 0)
{
return v___x_7344_;
}
else
{
lean_object* v_a_7345_; size_t v___x_7346_; size_t v___x_7347_; 
v_a_7345_ = lean_ctor_get(v___x_7344_, 0);
lean_inc(v_a_7345_);
lean_dec_ref(v___x_7344_);
v___x_7346_ = ((size_t)1ULL);
v___x_7347_ = lean_usize_add(v_i_7336_, v___x_7346_);
v_i_7336_ = v___x_7347_;
v_b_7338_ = v_a_7345_;
goto _start;
}
}
else
{
lean_object* v___x_7349_; 
v___x_7349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7349_, 0, v_b_7338_);
return v___x_7349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1___boxed(lean_object* v_as_7350_, lean_object* v_i_7351_, lean_object* v_stop_7352_, lean_object* v_b_7353_){
_start:
{
size_t v_i_boxed_7354_; size_t v_stop_boxed_7355_; lean_object* v_res_7356_; 
v_i_boxed_7354_ = lean_unbox_usize(v_i_7351_);
lean_dec(v_i_7351_);
v_stop_boxed_7355_ = lean_unbox_usize(v_stop_7352_);
lean_dec(v_stop_7352_);
v_res_7356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(v_as_7350_, v_i_boxed_7354_, v_stop_boxed_7355_, v_b_7353_);
lean_dec_ref(v_as_7350_);
return v_res_7356_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(lean_object* v_libs_7363_, lean_object* v_a_7364_){
_start:
{
lean_object* v_snd_7367_; lean_object* v___y_7370_; lean_object* v___x_7394_; lean_object* v___x_7395_; lean_object* v___x_7396_; uint8_t v___x_7397_; 
v___x_7394_ = lean_unsigned_to_nat(0u);
v___x_7395_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1));
v___x_7396_ = lean_array_get_size(v_libs_7363_);
v___x_7397_ = lean_nat_dec_lt(v___x_7394_, v___x_7396_);
if (v___x_7397_ == 0)
{
v_snd_7367_ = v___x_7395_;
goto v___jp_7366_;
}
else
{
lean_object* v___x_7398_; uint8_t v___x_7399_; 
v___x_7398_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2));
v___x_7399_ = lean_nat_dec_le(v___x_7396_, v___x_7396_);
if (v___x_7399_ == 0)
{
if (v___x_7397_ == 0)
{
v_snd_7367_ = v___x_7395_;
goto v___jp_7366_;
}
else
{
size_t v___x_7400_; size_t v___x_7401_; lean_object* v___x_7402_; 
v___x_7400_ = ((size_t)0ULL);
v___x_7401_ = lean_usize_of_nat(v___x_7396_);
v___x_7402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(v_libs_7363_, v___x_7400_, v___x_7401_, v___x_7398_);
v___y_7370_ = v___x_7402_;
goto v___jp_7369_;
}
}
else
{
size_t v___x_7403_; size_t v___x_7404_; lean_object* v___x_7405_; 
v___x_7403_ = ((size_t)0ULL);
v___x_7404_ = lean_usize_of_nat(v___x_7396_);
v___x_7405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(v_libs_7363_, v___x_7403_, v___x_7404_, v___x_7398_);
v___y_7370_ = v___x_7405_;
goto v___jp_7369_;
}
}
v___jp_7366_:
{
lean_object* v___x_7368_; 
v___x_7368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7368_, 0, v_snd_7367_);
lean_ctor_set(v___x_7368_, 1, v_a_7364_);
return v___x_7368_;
}
v___jp_7369_:
{
if (lean_obj_tag(v___y_7370_) == 0)
{
lean_object* v_a_7371_; lean_object* v_log_7372_; uint8_t v_action_7373_; uint8_t v_wantsRebuild_7374_; lean_object* v_trace_7375_; lean_object* v_buildTime_7376_; lean_object* v___x_7378_; uint8_t v_isShared_7379_; uint8_t v_isSharedCheck_7391_; 
v_a_7371_ = lean_ctor_get(v___y_7370_, 0);
lean_inc(v_a_7371_);
lean_dec_ref(v___y_7370_);
v_log_7372_ = lean_ctor_get(v_a_7364_, 0);
v_action_7373_ = lean_ctor_get_uint8(v_a_7364_, sizeof(void*)*3);
v_wantsRebuild_7374_ = lean_ctor_get_uint8(v_a_7364_, sizeof(void*)*3 + 1);
v_trace_7375_ = lean_ctor_get(v_a_7364_, 1);
v_buildTime_7376_ = lean_ctor_get(v_a_7364_, 2);
v_isSharedCheck_7391_ = !lean_is_exclusive(v_a_7364_);
if (v_isSharedCheck_7391_ == 0)
{
v___x_7378_ = v_a_7364_;
v_isShared_7379_ = v_isSharedCheck_7391_;
goto v_resetjp_7377_;
}
else
{
lean_inc(v_buildTime_7376_);
lean_inc(v_trace_7375_);
lean_inc(v_log_7372_);
lean_dec(v_a_7364_);
v___x_7378_ = lean_box(0);
v_isShared_7379_ = v_isSharedCheck_7391_;
goto v_resetjp_7377_;
}
v_resetjp_7377_:
{
lean_object* v___x_7380_; lean_object* v___x_7381_; lean_object* v___x_7382_; uint8_t v___x_7383_; lean_object* v___x_7384_; lean_object* v___x_7385_; lean_object* v___x_7386_; lean_object* v___x_7388_; 
v___x_7380_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0));
v___x_7381_ = l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(v_a_7371_);
v___x_7382_ = lean_string_append(v___x_7380_, v___x_7381_);
lean_dec_ref(v___x_7381_);
v___x_7383_ = 3;
v___x_7384_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7384_, 0, v___x_7382_);
lean_ctor_set_uint8(v___x_7384_, sizeof(void*)*1, v___x_7383_);
v___x_7385_ = lean_array_get_size(v_log_7372_);
v___x_7386_ = lean_array_push(v_log_7372_, v___x_7384_);
if (v_isShared_7379_ == 0)
{
lean_ctor_set(v___x_7378_, 0, v___x_7386_);
v___x_7388_ = v___x_7378_;
goto v_reusejp_7387_;
}
else
{
lean_object* v_reuseFailAlloc_7390_; 
v_reuseFailAlloc_7390_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7390_, 0, v___x_7386_);
lean_ctor_set(v_reuseFailAlloc_7390_, 1, v_trace_7375_);
lean_ctor_set(v_reuseFailAlloc_7390_, 2, v_buildTime_7376_);
lean_ctor_set_uint8(v_reuseFailAlloc_7390_, sizeof(void*)*3, v_action_7373_);
lean_ctor_set_uint8(v_reuseFailAlloc_7390_, sizeof(void*)*3 + 1, v_wantsRebuild_7374_);
v___x_7388_ = v_reuseFailAlloc_7390_;
goto v_reusejp_7387_;
}
v_reusejp_7387_:
{
lean_object* v___x_7389_; 
v___x_7389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7389_, 0, v___x_7385_);
lean_ctor_set(v___x_7389_, 1, v___x_7388_);
return v___x_7389_;
}
}
}
else
{
lean_object* v_a_7392_; lean_object* v_snd_7393_; 
v_a_7392_ = lean_ctor_get(v___y_7370_, 0);
lean_inc(v_a_7392_);
lean_dec_ref(v___y_7370_);
v_snd_7393_ = lean_ctor_get(v_a_7392_, 1);
lean_inc(v_snd_7393_);
lean_dec(v_a_7392_);
v_snd_7367_ = v_snd_7393_;
goto v___jp_7366_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___boxed(lean_object* v_libs_7406_, lean_object* v_a_7407_, lean_object* v_a_7408_){
_start:
{
lean_object* v_res_7409_; 
v_res_7409_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7406_, v_a_7407_);
lean_dec_ref(v_libs_7406_);
return v_res_7409_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder(lean_object* v_libs_7410_, lean_object* v_a_7411_, lean_object* v_a_7412_, lean_object* v_a_7413_, lean_object* v_a_7414_, lean_object* v_a_7415_, lean_object* v_a_7416_){
_start:
{
lean_object* v___x_7418_; 
v___x_7418_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7410_, v_a_7416_);
return v___x_7418_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___boxed(lean_object* v_libs_7419_, lean_object* v_a_7420_, lean_object* v_a_7421_, lean_object* v_a_7422_, lean_object* v_a_7423_, lean_object* v_a_7424_, lean_object* v_a_7425_, lean_object* v_a_7426_){
_start:
{
lean_object* v_res_7427_; 
v_res_7427_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder(v_libs_7419_, v_a_7420_, v_a_7421_, v_a_7422_, v_a_7423_, v_a_7424_, v_a_7425_);
lean_dec_ref(v_a_7424_);
lean_dec(v_a_7423_);
lean_dec(v_a_7422_);
lean_dec(v_a_7421_);
lean_dec_ref(v_a_7420_);
lean_dec_ref(v_libs_7419_);
return v_res_7427_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0(lean_object* v_objs_7428_, lean_object* v_weakArgs_7429_, lean_object* v_traceArgs_7430_, lean_object* v_libFile_7431_, lean_object* v_linker_7432_, lean_object* v_libs_7433_, lean_object* v___y_7434_, lean_object* v___y_7435_, lean_object* v___y_7436_, lean_object* v___y_7437_, lean_object* v___y_7438_, lean_object* v___y_7439_){
_start:
{
lean_object* v_log_7441_; uint8_t v_action_7442_; uint8_t v_wantsRebuild_7443_; lean_object* v_trace_7444_; lean_object* v_buildTime_7445_; lean_object* v___x_7447_; uint8_t v_isShared_7448_; uint8_t v_isSharedCheck_7477_; 
v_log_7441_ = lean_ctor_get(v___y_7439_, 0);
v_action_7442_ = lean_ctor_get_uint8(v___y_7439_, sizeof(void*)*3);
v_wantsRebuild_7443_ = lean_ctor_get_uint8(v___y_7439_, sizeof(void*)*3 + 1);
v_trace_7444_ = lean_ctor_get(v___y_7439_, 1);
v_buildTime_7445_ = lean_ctor_get(v___y_7439_, 2);
v_isSharedCheck_7477_ = !lean_is_exclusive(v___y_7439_);
if (v_isSharedCheck_7477_ == 0)
{
v___x_7447_ = v___y_7439_;
v_isShared_7448_ = v_isSharedCheck_7477_;
goto v_resetjp_7446_;
}
else
{
lean_inc(v_buildTime_7445_);
lean_inc(v_trace_7444_);
lean_inc(v_log_7441_);
lean_dec(v___y_7439_);
v___x_7447_ = lean_box(0);
v_isShared_7448_ = v_isSharedCheck_7477_;
goto v_resetjp_7446_;
}
v_resetjp_7446_:
{
lean_object* v___x_7449_; lean_object* v___x_7450_; lean_object* v___x_7451_; lean_object* v___x_7452_; 
v___x_7449_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7428_, v_libs_7433_);
v___x_7450_ = l_Array_append___redArg(v___x_7449_, v_weakArgs_7429_);
v___x_7451_ = l_Array_append___redArg(v___x_7450_, v_traceArgs_7430_);
v___x_7452_ = l_Lake_compileSharedLib(v_libFile_7431_, v___x_7451_, v_linker_7432_, v_log_7441_);
lean_dec_ref(v___x_7451_);
if (lean_obj_tag(v___x_7452_) == 0)
{
lean_object* v_a_7453_; lean_object* v_a_7454_; lean_object* v___x_7456_; uint8_t v_isShared_7457_; uint8_t v_isSharedCheck_7464_; 
v_a_7453_ = lean_ctor_get(v___x_7452_, 0);
v_a_7454_ = lean_ctor_get(v___x_7452_, 1);
v_isSharedCheck_7464_ = !lean_is_exclusive(v___x_7452_);
if (v_isSharedCheck_7464_ == 0)
{
v___x_7456_ = v___x_7452_;
v_isShared_7457_ = v_isSharedCheck_7464_;
goto v_resetjp_7455_;
}
else
{
lean_inc(v_a_7454_);
lean_inc(v_a_7453_);
lean_dec(v___x_7452_);
v___x_7456_ = lean_box(0);
v_isShared_7457_ = v_isSharedCheck_7464_;
goto v_resetjp_7455_;
}
v_resetjp_7455_:
{
lean_object* v___x_7459_; 
if (v_isShared_7448_ == 0)
{
lean_ctor_set(v___x_7447_, 0, v_a_7454_);
v___x_7459_ = v___x_7447_;
goto v_reusejp_7458_;
}
else
{
lean_object* v_reuseFailAlloc_7463_; 
v_reuseFailAlloc_7463_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7463_, 0, v_a_7454_);
lean_ctor_set(v_reuseFailAlloc_7463_, 1, v_trace_7444_);
lean_ctor_set(v_reuseFailAlloc_7463_, 2, v_buildTime_7445_);
lean_ctor_set_uint8(v_reuseFailAlloc_7463_, sizeof(void*)*3, v_action_7442_);
lean_ctor_set_uint8(v_reuseFailAlloc_7463_, sizeof(void*)*3 + 1, v_wantsRebuild_7443_);
v___x_7459_ = v_reuseFailAlloc_7463_;
goto v_reusejp_7458_;
}
v_reusejp_7458_:
{
lean_object* v___x_7461_; 
if (v_isShared_7457_ == 0)
{
lean_ctor_set(v___x_7456_, 1, v___x_7459_);
v___x_7461_ = v___x_7456_;
goto v_reusejp_7460_;
}
else
{
lean_object* v_reuseFailAlloc_7462_; 
v_reuseFailAlloc_7462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7462_, 0, v_a_7453_);
lean_ctor_set(v_reuseFailAlloc_7462_, 1, v___x_7459_);
v___x_7461_ = v_reuseFailAlloc_7462_;
goto v_reusejp_7460_;
}
v_reusejp_7460_:
{
return v___x_7461_;
}
}
}
}
else
{
lean_object* v_a_7465_; lean_object* v_a_7466_; lean_object* v___x_7468_; uint8_t v_isShared_7469_; uint8_t v_isSharedCheck_7476_; 
v_a_7465_ = lean_ctor_get(v___x_7452_, 0);
v_a_7466_ = lean_ctor_get(v___x_7452_, 1);
v_isSharedCheck_7476_ = !lean_is_exclusive(v___x_7452_);
if (v_isSharedCheck_7476_ == 0)
{
v___x_7468_ = v___x_7452_;
v_isShared_7469_ = v_isSharedCheck_7476_;
goto v_resetjp_7467_;
}
else
{
lean_inc(v_a_7466_);
lean_inc(v_a_7465_);
lean_dec(v___x_7452_);
v___x_7468_ = lean_box(0);
v_isShared_7469_ = v_isSharedCheck_7476_;
goto v_resetjp_7467_;
}
v_resetjp_7467_:
{
lean_object* v___x_7471_; 
if (v_isShared_7448_ == 0)
{
lean_ctor_set(v___x_7447_, 0, v_a_7466_);
v___x_7471_ = v___x_7447_;
goto v_reusejp_7470_;
}
else
{
lean_object* v_reuseFailAlloc_7475_; 
v_reuseFailAlloc_7475_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7475_, 0, v_a_7466_);
lean_ctor_set(v_reuseFailAlloc_7475_, 1, v_trace_7444_);
lean_ctor_set(v_reuseFailAlloc_7475_, 2, v_buildTime_7445_);
lean_ctor_set_uint8(v_reuseFailAlloc_7475_, sizeof(void*)*3, v_action_7442_);
lean_ctor_set_uint8(v_reuseFailAlloc_7475_, sizeof(void*)*3 + 1, v_wantsRebuild_7443_);
v___x_7471_ = v_reuseFailAlloc_7475_;
goto v_reusejp_7470_;
}
v_reusejp_7470_:
{
lean_object* v___x_7473_; 
if (v_isShared_7469_ == 0)
{
lean_ctor_set(v___x_7468_, 1, v___x_7471_);
v___x_7473_ = v___x_7468_;
goto v_reusejp_7472_;
}
else
{
lean_object* v_reuseFailAlloc_7474_; 
v_reuseFailAlloc_7474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7474_, 0, v_a_7465_);
lean_ctor_set(v_reuseFailAlloc_7474_, 1, v___x_7471_);
v___x_7473_ = v_reuseFailAlloc_7474_;
goto v_reusejp_7472_;
}
v_reusejp_7472_:
{
return v___x_7473_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object* v_objs_7478_, lean_object* v_weakArgs_7479_, lean_object* v_traceArgs_7480_, lean_object* v_libFile_7481_, lean_object* v_linker_7482_, lean_object* v_libs_7483_, lean_object* v___y_7484_, lean_object* v___y_7485_, lean_object* v___y_7486_, lean_object* v___y_7487_, lean_object* v___y_7488_, lean_object* v___y_7489_, lean_object* v___y_7490_){
_start:
{
lean_object* v_res_7491_; 
v_res_7491_ = l_Lake_buildSharedLib___lam__0(v_objs_7478_, v_weakArgs_7479_, v_traceArgs_7480_, v_libFile_7481_, v_linker_7482_, v_libs_7483_, v___y_7484_, v___y_7485_, v___y_7486_, v___y_7487_, v___y_7488_, v___y_7489_);
lean_dec_ref(v___y_7488_);
lean_dec(v___y_7487_);
lean_dec(v___y_7486_);
lean_dec(v___y_7485_);
lean_dec_ref(v___y_7484_);
lean_dec_ref(v_libs_7483_);
lean_dec_ref(v_traceArgs_7480_);
lean_dec_ref(v_weakArgs_7479_);
lean_dec_ref(v_objs_7478_);
return v_res_7491_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1(uint8_t v_linkDeps_7492_, lean_object* v___x_7493_, lean_object* v___f_7494_, lean_object* v_libs_7495_, lean_object* v___y_7496_, lean_object* v___y_7497_, lean_object* v___y_7498_, lean_object* v___y_7499_, lean_object* v___y_7500_, lean_object* v___y_7501_){
_start:
{
if (v_linkDeps_7492_ == 0)
{
lean_object* v___x_7503_; lean_object* v___x_7504_; 
v___x_7503_ = lean_mk_empty_array_with_capacity(v___x_7493_);
lean_inc_ref(v___y_7500_);
lean_inc(v___y_7499_);
lean_inc(v___y_7498_);
lean_inc(v___y_7497_);
v___x_7504_ = lean_apply_8(v___f_7494_, v___x_7503_, v___y_7496_, v___y_7497_, v___y_7498_, v___y_7499_, v___y_7500_, v___y_7501_, lean_box(0));
return v___x_7504_;
}
else
{
lean_object* v___x_7505_; 
v___x_7505_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7495_, v___y_7501_);
if (lean_obj_tag(v___x_7505_) == 0)
{
lean_object* v_a_7506_; lean_object* v_a_7507_; lean_object* v___x_7508_; 
v_a_7506_ = lean_ctor_get(v___x_7505_, 0);
lean_inc(v_a_7506_);
v_a_7507_ = lean_ctor_get(v___x_7505_, 1);
lean_inc(v_a_7507_);
lean_dec_ref(v___x_7505_);
lean_inc_ref(v___y_7500_);
lean_inc(v___y_7499_);
lean_inc(v___y_7498_);
lean_inc(v___y_7497_);
v___x_7508_ = lean_apply_8(v___f_7494_, v_a_7506_, v___y_7496_, v___y_7497_, v___y_7498_, v___y_7499_, v___y_7500_, v_a_7507_, lean_box(0));
return v___x_7508_;
}
else
{
lean_object* v_a_7509_; lean_object* v_a_7510_; lean_object* v___x_7512_; uint8_t v_isShared_7513_; uint8_t v_isSharedCheck_7517_; 
lean_dec_ref(v___y_7496_);
lean_dec_ref(v___f_7494_);
v_a_7509_ = lean_ctor_get(v___x_7505_, 0);
v_a_7510_ = lean_ctor_get(v___x_7505_, 1);
v_isSharedCheck_7517_ = !lean_is_exclusive(v___x_7505_);
if (v_isSharedCheck_7517_ == 0)
{
v___x_7512_ = v___x_7505_;
v_isShared_7513_ = v_isSharedCheck_7517_;
goto v_resetjp_7511_;
}
else
{
lean_inc(v_a_7510_);
lean_inc(v_a_7509_);
lean_dec(v___x_7505_);
v___x_7512_ = lean_box(0);
v_isShared_7513_ = v_isSharedCheck_7517_;
goto v_resetjp_7511_;
}
v_resetjp_7511_:
{
lean_object* v___x_7515_; 
if (v_isShared_7513_ == 0)
{
v___x_7515_ = v___x_7512_;
goto v_reusejp_7514_;
}
else
{
lean_object* v_reuseFailAlloc_7516_; 
v_reuseFailAlloc_7516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7516_, 0, v_a_7509_);
lean_ctor_set(v_reuseFailAlloc_7516_, 1, v_a_7510_);
v___x_7515_ = v_reuseFailAlloc_7516_;
goto v_reusejp_7514_;
}
v_reusejp_7514_:
{
return v___x_7515_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1___boxed(lean_object* v_linkDeps_7518_, lean_object* v___x_7519_, lean_object* v___f_7520_, lean_object* v_libs_7521_, lean_object* v___y_7522_, lean_object* v___y_7523_, lean_object* v___y_7524_, lean_object* v___y_7525_, lean_object* v___y_7526_, lean_object* v___y_7527_, lean_object* v___y_7528_){
_start:
{
uint8_t v_linkDeps_boxed_7529_; lean_object* v_res_7530_; 
v_linkDeps_boxed_7529_ = lean_unbox(v_linkDeps_7518_);
v_res_7530_ = l_Lake_buildSharedLib___lam__1(v_linkDeps_boxed_7529_, v___x_7519_, v___f_7520_, v_libs_7521_, v___y_7522_, v___y_7523_, v___y_7524_, v___y_7525_, v___y_7526_, v___y_7527_);
lean_dec_ref(v___y_7526_);
lean_dec(v___y_7525_);
lean_dec(v___y_7524_);
lean_dec(v___y_7523_);
lean_dec_ref(v_libs_7521_);
lean_dec(v___x_7519_);
return v_res_7530_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2(lean_object* v_traceArgs_7531_, lean_object* v_extraDepTrace_7532_, uint8_t v_linkDeps_7533_, lean_object* v___f_7534_, lean_object* v_libFile_7535_, lean_object* v_libName_7536_, uint8_t v_plugin_7537_, lean_object* v_libs_7538_, lean_object* v___y_7539_, lean_object* v___y_7540_, lean_object* v___y_7541_, lean_object* v___y_7542_, lean_object* v___y_7543_, lean_object* v___y_7544_){
_start:
{
uint64_t v___y_7547_; uint64_t v___x_7624_; lean_object* v___x_7625_; lean_object* v___x_7626_; uint8_t v___x_7627_; 
v___x_7624_ = l_Lake_Hash_nil;
v___x_7625_ = lean_unsigned_to_nat(0u);
v___x_7626_ = lean_array_get_size(v_traceArgs_7531_);
v___x_7627_ = lean_nat_dec_lt(v___x_7625_, v___x_7626_);
if (v___x_7627_ == 0)
{
v___y_7547_ = v___x_7624_;
goto v___jp_7546_;
}
else
{
uint8_t v___x_7628_; 
v___x_7628_ = lean_nat_dec_le(v___x_7626_, v___x_7626_);
if (v___x_7628_ == 0)
{
if (v___x_7627_ == 0)
{
v___y_7547_ = v___x_7624_;
goto v___jp_7546_;
}
else
{
size_t v___x_7629_; size_t v___x_7630_; uint64_t v___x_7631_; 
v___x_7629_ = ((size_t)0ULL);
v___x_7630_ = lean_usize_of_nat(v___x_7626_);
v___x_7631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7531_, v___x_7629_, v___x_7630_, v___x_7624_);
v___y_7547_ = v___x_7631_;
goto v___jp_7546_;
}
}
else
{
size_t v___x_7632_; size_t v___x_7633_; uint64_t v___x_7634_; 
v___x_7632_ = ((size_t)0ULL);
v___x_7633_ = lean_usize_of_nat(v___x_7626_);
v___x_7634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7531_, v___x_7632_, v___x_7633_, v___x_7624_);
v___y_7547_ = v___x_7634_;
goto v___jp_7546_;
}
}
v___jp_7546_:
{
lean_object* v_log_7548_; uint8_t v_action_7549_; uint8_t v_wantsRebuild_7550_; lean_object* v_trace_7551_; lean_object* v_buildTime_7552_; lean_object* v___x_7554_; uint8_t v_isShared_7555_; uint8_t v_isSharedCheck_7623_; 
v_log_7548_ = lean_ctor_get(v___y_7544_, 0);
v_action_7549_ = lean_ctor_get_uint8(v___y_7544_, sizeof(void*)*3);
v_wantsRebuild_7550_ = lean_ctor_get_uint8(v___y_7544_, sizeof(void*)*3 + 1);
v_trace_7551_ = lean_ctor_get(v___y_7544_, 1);
v_buildTime_7552_ = lean_ctor_get(v___y_7544_, 2);
v_isSharedCheck_7623_ = !lean_is_exclusive(v___y_7544_);
if (v_isSharedCheck_7623_ == 0)
{
v___x_7554_ = v___y_7544_;
v_isShared_7555_ = v_isSharedCheck_7623_;
goto v_resetjp_7553_;
}
else
{
lean_inc(v_buildTime_7552_);
lean_inc(v_trace_7551_);
lean_inc(v_log_7548_);
lean_dec(v___y_7544_);
v___x_7554_ = lean_box(0);
v_isShared_7555_ = v_isSharedCheck_7623_;
goto v_resetjp_7553_;
}
v_resetjp_7553_:
{
lean_object* v___x_7556_; lean_object* v___x_7557_; lean_object* v___x_7558_; lean_object* v___x_7559_; lean_object* v___x_7560_; lean_object* v___x_7561_; lean_object* v___x_7562_; lean_object* v___x_7563_; lean_object* v___x_7564_; lean_object* v___x_7565_; lean_object* v___x_7566_; lean_object* v___x_7567_; lean_object* v___x_7568_; lean_object* v___x_7570_; 
v___x_7556_ = lean_unsigned_to_nat(0u);
v___x_7557_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_7558_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_7559_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_7560_ = lean_array_to_list(v_traceArgs_7531_);
v___x_7561_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_7560_);
lean_dec(v___x_7560_);
v___x_7562_ = lean_string_append(v___x_7559_, v___x_7561_);
lean_dec_ref(v___x_7561_);
v___x_7563_ = lean_string_append(v___x_7558_, v___x_7562_);
lean_dec_ref(v___x_7562_);
v___x_7564_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_7565_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_7565_, 0, v___x_7563_);
lean_ctor_set(v___x_7565_, 1, v___x_7557_);
lean_ctor_set(v___x_7565_, 2, v___x_7564_);
lean_ctor_set_uint64(v___x_7565_, sizeof(void*)*3, v___y_7547_);
v___x_7566_ = l_Lake_BuildTrace_mix(v_trace_7551_, v___x_7565_);
v___x_7567_ = l_Lake_platformTrace;
v___x_7568_ = l_Lake_BuildTrace_mix(v___x_7566_, v___x_7567_);
if (v_isShared_7555_ == 0)
{
lean_ctor_set(v___x_7554_, 1, v___x_7568_);
v___x_7570_ = v___x_7554_;
goto v_reusejp_7569_;
}
else
{
lean_object* v_reuseFailAlloc_7622_; 
v_reuseFailAlloc_7622_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7622_, 0, v_log_7548_);
lean_ctor_set(v_reuseFailAlloc_7622_, 1, v___x_7568_);
lean_ctor_set(v_reuseFailAlloc_7622_, 2, v_buildTime_7552_);
lean_ctor_set_uint8(v_reuseFailAlloc_7622_, sizeof(void*)*3, v_action_7549_);
lean_ctor_set_uint8(v_reuseFailAlloc_7622_, sizeof(void*)*3 + 1, v_wantsRebuild_7550_);
v___x_7570_ = v_reuseFailAlloc_7622_;
goto v_reusejp_7569_;
}
v_reusejp_7569_:
{
lean_object* v___x_7571_; 
lean_inc_ref(v___y_7543_);
lean_inc(v___y_7542_);
lean_inc(v___y_7541_);
lean_inc(v___y_7540_);
lean_inc_ref(v___y_7539_);
v___x_7571_ = lean_apply_7(v_extraDepTrace_7532_, v___y_7539_, v___y_7540_, v___y_7541_, v___y_7542_, v___y_7543_, v___x_7570_, lean_box(0));
if (lean_obj_tag(v___x_7571_) == 0)
{
lean_object* v_a_7572_; lean_object* v_a_7573_; lean_object* v_log_7574_; uint8_t v_action_7575_; uint8_t v_wantsRebuild_7576_; lean_object* v_trace_7577_; lean_object* v_buildTime_7578_; lean_object* v___x_7580_; uint8_t v_isShared_7581_; uint8_t v_isSharedCheck_7612_; 
v_a_7572_ = lean_ctor_get(v___x_7571_, 1);
lean_inc(v_a_7572_);
v_a_7573_ = lean_ctor_get(v___x_7571_, 0);
lean_inc(v_a_7573_);
lean_dec_ref(v___x_7571_);
v_log_7574_ = lean_ctor_get(v_a_7572_, 0);
v_action_7575_ = lean_ctor_get_uint8(v_a_7572_, sizeof(void*)*3);
v_wantsRebuild_7576_ = lean_ctor_get_uint8(v_a_7572_, sizeof(void*)*3 + 1);
v_trace_7577_ = lean_ctor_get(v_a_7572_, 1);
v_buildTime_7578_ = lean_ctor_get(v_a_7572_, 2);
v_isSharedCheck_7612_ = !lean_is_exclusive(v_a_7572_);
if (v_isSharedCheck_7612_ == 0)
{
v___x_7580_ = v_a_7572_;
v_isShared_7581_ = v_isSharedCheck_7612_;
goto v_resetjp_7579_;
}
else
{
lean_inc(v_buildTime_7578_);
lean_inc(v_trace_7577_);
lean_inc(v_log_7574_);
lean_dec(v_a_7572_);
v___x_7580_ = lean_box(0);
v_isShared_7581_ = v_isSharedCheck_7612_;
goto v_resetjp_7579_;
}
v_resetjp_7579_:
{
lean_object* v___x_7582_; lean_object* v___y_7583_; lean_object* v___x_7584_; lean_object* v___x_7586_; 
v___x_7582_ = lean_box(v_linkDeps_7533_);
lean_inc_ref(v_libs_7538_);
v___y_7583_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__1___boxed), 11, 4);
lean_closure_set(v___y_7583_, 0, v___x_7582_);
lean_closure_set(v___y_7583_, 1, v___x_7556_);
lean_closure_set(v___y_7583_, 2, v___f_7534_);
lean_closure_set(v___y_7583_, 3, v_libs_7538_);
v___x_7584_ = l_Lake_BuildTrace_mix(v_trace_7577_, v_a_7573_);
if (v_isShared_7581_ == 0)
{
lean_ctor_set(v___x_7580_, 1, v___x_7584_);
v___x_7586_ = v___x_7580_;
goto v_reusejp_7585_;
}
else
{
lean_object* v_reuseFailAlloc_7611_; 
v_reuseFailAlloc_7611_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7611_, 0, v_log_7574_);
lean_ctor_set(v_reuseFailAlloc_7611_, 1, v___x_7584_);
lean_ctor_set(v_reuseFailAlloc_7611_, 2, v_buildTime_7578_);
lean_ctor_set_uint8(v_reuseFailAlloc_7611_, sizeof(void*)*3, v_action_7575_);
lean_ctor_set_uint8(v_reuseFailAlloc_7611_, sizeof(void*)*3 + 1, v_wantsRebuild_7576_);
v___x_7586_ = v_reuseFailAlloc_7611_;
goto v_reusejp_7585_;
}
v_reusejp_7585_:
{
uint8_t v___x_7587_; uint8_t v___x_7588_; lean_object* v___x_7589_; lean_object* v___x_7590_; 
v___x_7587_ = 1;
v___x_7588_ = 0;
v___x_7589_ = l_Lake_sharedLibExt;
lean_inc(v___y_7540_);
v___x_7590_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_7535_, v___y_7583_, v___x_7588_, v___x_7589_, v___x_7587_, v___x_7588_, v___x_7588_, v___y_7539_, v___y_7540_, v___y_7541_, v___y_7542_, v___y_7543_, v___x_7586_);
if (lean_obj_tag(v___x_7590_) == 0)
{
lean_object* v_a_7591_; lean_object* v_a_7592_; lean_object* v___x_7594_; uint8_t v_isShared_7595_; uint8_t v_isSharedCheck_7601_; 
v_a_7591_ = lean_ctor_get(v___x_7590_, 0);
v_a_7592_ = lean_ctor_get(v___x_7590_, 1);
v_isSharedCheck_7601_ = !lean_is_exclusive(v___x_7590_);
if (v_isSharedCheck_7601_ == 0)
{
v___x_7594_ = v___x_7590_;
v_isShared_7595_ = v_isSharedCheck_7601_;
goto v_resetjp_7593_;
}
else
{
lean_inc(v_a_7592_);
lean_inc(v_a_7591_);
lean_dec(v___x_7590_);
v___x_7594_ = lean_box(0);
v_isShared_7595_ = v_isSharedCheck_7601_;
goto v_resetjp_7593_;
}
v_resetjp_7593_:
{
lean_object* v_path_7596_; lean_object* v___x_7597_; lean_object* v___x_7599_; 
v_path_7596_ = lean_ctor_get(v_a_7591_, 1);
lean_inc_ref(v_path_7596_);
lean_dec(v_a_7591_);
v___x_7597_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_7597_, 0, v_path_7596_);
lean_ctor_set(v___x_7597_, 1, v_libName_7536_);
lean_ctor_set(v___x_7597_, 2, v_libs_7538_);
lean_ctor_set_uint8(v___x_7597_, sizeof(void*)*3, v_plugin_7537_);
if (v_isShared_7595_ == 0)
{
lean_ctor_set(v___x_7594_, 0, v___x_7597_);
v___x_7599_ = v___x_7594_;
goto v_reusejp_7598_;
}
else
{
lean_object* v_reuseFailAlloc_7600_; 
v_reuseFailAlloc_7600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7600_, 0, v___x_7597_);
lean_ctor_set(v_reuseFailAlloc_7600_, 1, v_a_7592_);
v___x_7599_ = v_reuseFailAlloc_7600_;
goto v_reusejp_7598_;
}
v_reusejp_7598_:
{
return v___x_7599_;
}
}
}
else
{
lean_object* v_a_7602_; lean_object* v_a_7603_; lean_object* v___x_7605_; uint8_t v_isShared_7606_; uint8_t v_isSharedCheck_7610_; 
lean_dec_ref(v_libs_7538_);
lean_dec_ref(v_libName_7536_);
v_a_7602_ = lean_ctor_get(v___x_7590_, 0);
v_a_7603_ = lean_ctor_get(v___x_7590_, 1);
v_isSharedCheck_7610_ = !lean_is_exclusive(v___x_7590_);
if (v_isSharedCheck_7610_ == 0)
{
v___x_7605_ = v___x_7590_;
v_isShared_7606_ = v_isSharedCheck_7610_;
goto v_resetjp_7604_;
}
else
{
lean_inc(v_a_7603_);
lean_inc(v_a_7602_);
lean_dec(v___x_7590_);
v___x_7605_ = lean_box(0);
v_isShared_7606_ = v_isSharedCheck_7610_;
goto v_resetjp_7604_;
}
v_resetjp_7604_:
{
lean_object* v___x_7608_; 
if (v_isShared_7606_ == 0)
{
v___x_7608_ = v___x_7605_;
goto v_reusejp_7607_;
}
else
{
lean_object* v_reuseFailAlloc_7609_; 
v_reuseFailAlloc_7609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7609_, 0, v_a_7602_);
lean_ctor_set(v_reuseFailAlloc_7609_, 1, v_a_7603_);
v___x_7608_ = v_reuseFailAlloc_7609_;
goto v_reusejp_7607_;
}
v_reusejp_7607_:
{
return v___x_7608_;
}
}
}
}
}
}
else
{
lean_object* v_a_7613_; lean_object* v_a_7614_; lean_object* v___x_7616_; uint8_t v_isShared_7617_; uint8_t v_isSharedCheck_7621_; 
lean_dec_ref(v___y_7539_);
lean_dec_ref(v_libs_7538_);
lean_dec_ref(v_libName_7536_);
lean_dec_ref(v_libFile_7535_);
lean_dec_ref(v___f_7534_);
v_a_7613_ = lean_ctor_get(v___x_7571_, 0);
v_a_7614_ = lean_ctor_get(v___x_7571_, 1);
v_isSharedCheck_7621_ = !lean_is_exclusive(v___x_7571_);
if (v_isSharedCheck_7621_ == 0)
{
v___x_7616_ = v___x_7571_;
v_isShared_7617_ = v_isSharedCheck_7621_;
goto v_resetjp_7615_;
}
else
{
lean_inc(v_a_7614_);
lean_inc(v_a_7613_);
lean_dec(v___x_7571_);
v___x_7616_ = lean_box(0);
v_isShared_7617_ = v_isSharedCheck_7621_;
goto v_resetjp_7615_;
}
v_resetjp_7615_:
{
lean_object* v___x_7619_; 
if (v_isShared_7617_ == 0)
{
v___x_7619_ = v___x_7616_;
goto v_reusejp_7618_;
}
else
{
lean_object* v_reuseFailAlloc_7620_; 
v_reuseFailAlloc_7620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7620_, 0, v_a_7613_);
lean_ctor_set(v_reuseFailAlloc_7620_, 1, v_a_7614_);
v___x_7619_ = v_reuseFailAlloc_7620_;
goto v_reusejp_7618_;
}
v_reusejp_7618_:
{
return v___x_7619_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2___boxed(lean_object* v_traceArgs_7635_, lean_object* v_extraDepTrace_7636_, lean_object* v_linkDeps_7637_, lean_object* v___f_7638_, lean_object* v_libFile_7639_, lean_object* v_libName_7640_, lean_object* v_plugin_7641_, lean_object* v_libs_7642_, lean_object* v___y_7643_, lean_object* v___y_7644_, lean_object* v___y_7645_, lean_object* v___y_7646_, lean_object* v___y_7647_, lean_object* v___y_7648_, lean_object* v___y_7649_){
_start:
{
uint8_t v_linkDeps_boxed_7650_; uint8_t v_plugin_boxed_7651_; lean_object* v_res_7652_; 
v_linkDeps_boxed_7650_ = lean_unbox(v_linkDeps_7637_);
v_plugin_boxed_7651_ = lean_unbox(v_plugin_7641_);
v_res_7652_ = l_Lake_buildSharedLib___lam__2(v_traceArgs_7635_, v_extraDepTrace_7636_, v_linkDeps_boxed_7650_, v___f_7638_, v_libFile_7639_, v_libName_7640_, v_plugin_boxed_7651_, v_libs_7642_, v___y_7643_, v___y_7644_, v___y_7645_, v___y_7646_, v___y_7647_, v___y_7648_);
lean_dec_ref(v___y_7647_);
lean_dec(v___y_7646_);
lean_dec(v___y_7645_);
lean_dec(v___y_7644_);
return v_res_7652_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3(lean_object* v_weakArgs_7654_, lean_object* v_traceArgs_7655_, lean_object* v_libFile_7656_, lean_object* v_linker_7657_, lean_object* v_extraDepTrace_7658_, uint8_t v_linkDeps_7659_, lean_object* v_libName_7660_, uint8_t v_plugin_7661_, lean_object* v_linkLibs_7662_, lean_object* v___x_7663_, lean_object* v_objs_7664_, lean_object* v___y_7665_, lean_object* v___y_7666_, lean_object* v___y_7667_, lean_object* v___y_7668_, lean_object* v___y_7669_, lean_object* v___y_7670_){
_start:
{
lean_object* v_trace_7672_; lean_object* v___f_7673_; lean_object* v___x_7674_; lean_object* v___x_7675_; lean_object* v___f_7676_; lean_object* v___x_7677_; lean_object* v___x_7678_; lean_object* v___x_7679_; uint8_t v___x_7680_; lean_object* v___x_7681_; lean_object* v___x_7682_; 
v_trace_7672_ = lean_ctor_get(v___y_7670_, 1);
lean_inc_ref(v_libFile_7656_);
lean_inc_ref(v_traceArgs_7655_);
v___f_7673_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__0___boxed), 13, 5);
lean_closure_set(v___f_7673_, 0, v_objs_7664_);
lean_closure_set(v___f_7673_, 1, v_weakArgs_7654_);
lean_closure_set(v___f_7673_, 2, v_traceArgs_7655_);
lean_closure_set(v___f_7673_, 3, v_libFile_7656_);
lean_closure_set(v___f_7673_, 4, v_linker_7657_);
v___x_7674_ = lean_box(v_linkDeps_7659_);
v___x_7675_ = lean_box(v_plugin_7661_);
v___f_7676_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__2___boxed), 15, 7);
lean_closure_set(v___f_7676_, 0, v_traceArgs_7655_);
lean_closure_set(v___f_7676_, 1, v_extraDepTrace_7658_);
lean_closure_set(v___f_7676_, 2, v___x_7674_);
lean_closure_set(v___f_7676_, 3, v___f_7673_);
lean_closure_set(v___f_7676_, 4, v_libFile_7656_);
lean_closure_set(v___f_7676_, 5, v_libName_7660_);
lean_closure_set(v___f_7676_, 6, v___x_7675_);
v___x_7677_ = ((lean_object*)(l_Lake_buildSharedLib___lam__3___closed__0));
v___x_7678_ = l_Lake_Job_collectArray___redArg(v_linkLibs_7662_, v___x_7677_);
v___x_7679_ = lean_unsigned_to_nat(0u);
v___x_7680_ = 0;
v___x_7681_ = l_Lake_Job_mapM___redArg(v___x_7663_, v___x_7678_, v___f_7676_, v___x_7679_, v___x_7680_, v___y_7665_, v___y_7666_, v___y_7667_, v___y_7668_, v___y_7669_, v_trace_7672_);
v___x_7682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7682_, 0, v___x_7681_);
lean_ctor_set(v___x_7682_, 1, v___y_7670_);
return v___x_7682_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3___boxed(lean_object** _args){
lean_object* v_weakArgs_7683_ = _args[0];
lean_object* v_traceArgs_7684_ = _args[1];
lean_object* v_libFile_7685_ = _args[2];
lean_object* v_linker_7686_ = _args[3];
lean_object* v_extraDepTrace_7687_ = _args[4];
lean_object* v_linkDeps_7688_ = _args[5];
lean_object* v_libName_7689_ = _args[6];
lean_object* v_plugin_7690_ = _args[7];
lean_object* v_linkLibs_7691_ = _args[8];
lean_object* v___x_7692_ = _args[9];
lean_object* v_objs_7693_ = _args[10];
lean_object* v___y_7694_ = _args[11];
lean_object* v___y_7695_ = _args[12];
lean_object* v___y_7696_ = _args[13];
lean_object* v___y_7697_ = _args[14];
lean_object* v___y_7698_ = _args[15];
lean_object* v___y_7699_ = _args[16];
lean_object* v___y_7700_ = _args[17];
_start:
{
uint8_t v_linkDeps_boxed_7701_; uint8_t v_plugin_boxed_7702_; lean_object* v_res_7703_; 
v_linkDeps_boxed_7701_ = lean_unbox(v_linkDeps_7688_);
v_plugin_boxed_7702_ = lean_unbox(v_plugin_7690_);
v_res_7703_ = l_Lake_buildSharedLib___lam__3(v_weakArgs_7683_, v_traceArgs_7684_, v_libFile_7685_, v_linker_7686_, v_extraDepTrace_7687_, v_linkDeps_boxed_7701_, v_libName_7689_, v_plugin_boxed_7702_, v_linkLibs_7691_, v___x_7692_, v_objs_7693_, v___y_7694_, v___y_7695_, v___y_7696_, v___y_7697_, v___y_7698_, v___y_7699_);
lean_dec_ref(v___y_7698_);
lean_dec(v___y_7697_);
lean_dec(v___y_7696_);
lean_dec(v___y_7695_);
lean_dec_ref(v_linkLibs_7691_);
return v_res_7703_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib(lean_object* v_libName_7705_, lean_object* v_libFile_7706_, lean_object* v_linkObjs_7707_, lean_object* v_linkLibs_7708_, lean_object* v_weakArgs_7709_, lean_object* v_traceArgs_7710_, lean_object* v_linker_7711_, lean_object* v_extraDepTrace_7712_, uint8_t v_plugin_7713_, uint8_t v_linkDeps_7714_, lean_object* v_a_7715_, lean_object* v_a_7716_, lean_object* v_a_7717_, lean_object* v_a_7718_, lean_object* v_a_7719_, lean_object* v_a_7720_){
_start:
{
lean_object* v___x_7722_; lean_object* v___x_7723_; lean_object* v___x_7724_; lean_object* v___f_7725_; lean_object* v___x_7726_; lean_object* v___x_7727_; lean_object* v___x_7728_; uint8_t v___x_7729_; lean_object* v___x_7730_; 
v___x_7722_ = l_Lake_instDataKindDynlib;
v___x_7723_ = lean_box(v_linkDeps_7714_);
v___x_7724_ = lean_box(v_plugin_7713_);
v___f_7725_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__3___boxed), 18, 10);
lean_closure_set(v___f_7725_, 0, v_weakArgs_7709_);
lean_closure_set(v___f_7725_, 1, v_traceArgs_7710_);
lean_closure_set(v___f_7725_, 2, v_libFile_7706_);
lean_closure_set(v___f_7725_, 3, v_linker_7711_);
lean_closure_set(v___f_7725_, 4, v_extraDepTrace_7712_);
lean_closure_set(v___f_7725_, 5, v___x_7723_);
lean_closure_set(v___f_7725_, 6, v_libName_7705_);
lean_closure_set(v___f_7725_, 7, v___x_7724_);
lean_closure_set(v___f_7725_, 8, v_linkLibs_7708_);
lean_closure_set(v___f_7725_, 9, v___x_7722_);
v___x_7726_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_7727_ = l_Lake_Job_collectArray___redArg(v_linkObjs_7707_, v___x_7726_);
v___x_7728_ = lean_unsigned_to_nat(0u);
v___x_7729_ = 1;
v___x_7730_ = l_Lake_Job_bindM___redArg(v___x_7722_, v___x_7727_, v___f_7725_, v___x_7728_, v___x_7729_, v_a_7715_, v_a_7716_, v_a_7717_, v_a_7718_, v_a_7719_, v_a_7720_);
return v___x_7730_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___boxed(lean_object** _args){
lean_object* v_libName_7731_ = _args[0];
lean_object* v_libFile_7732_ = _args[1];
lean_object* v_linkObjs_7733_ = _args[2];
lean_object* v_linkLibs_7734_ = _args[3];
lean_object* v_weakArgs_7735_ = _args[4];
lean_object* v_traceArgs_7736_ = _args[5];
lean_object* v_linker_7737_ = _args[6];
lean_object* v_extraDepTrace_7738_ = _args[7];
lean_object* v_plugin_7739_ = _args[8];
lean_object* v_linkDeps_7740_ = _args[9];
lean_object* v_a_7741_ = _args[10];
lean_object* v_a_7742_ = _args[11];
lean_object* v_a_7743_ = _args[12];
lean_object* v_a_7744_ = _args[13];
lean_object* v_a_7745_ = _args[14];
lean_object* v_a_7746_ = _args[15];
lean_object* v_a_7747_ = _args[16];
_start:
{
uint8_t v_plugin_boxed_7748_; uint8_t v_linkDeps_boxed_7749_; lean_object* v_res_7750_; 
v_plugin_boxed_7748_ = lean_unbox(v_plugin_7739_);
v_linkDeps_boxed_7749_ = lean_unbox(v_linkDeps_7740_);
v_res_7750_ = l_Lake_buildSharedLib(v_libName_7731_, v_libFile_7732_, v_linkObjs_7733_, v_linkLibs_7734_, v_weakArgs_7735_, v_traceArgs_7736_, v_linker_7737_, v_extraDepTrace_7738_, v_plugin_boxed_7748_, v_linkDeps_boxed_7749_, v_a_7741_, v_a_7742_, v_a_7743_, v_a_7744_, v_a_7745_, v_a_7746_);
lean_dec_ref(v_a_7746_);
lean_dec_ref(v_a_7745_);
lean_dec(v_a_7744_);
lean_dec(v_a_7743_);
lean_dec(v_a_7742_);
lean_dec_ref(v_linkObjs_7733_);
return v_res_7750_;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLib___lam__0___closed__0(void){
_start:
{
lean_object* v___x_7751_; lean_object* v___x_7752_; lean_object* v___x_7753_; lean_object* v___x_7754_; 
v___x_7751_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
v___x_7752_ = lean_unsigned_to_nat(2u);
v___x_7753_ = lean_mk_empty_array_with_capacity(v___x_7752_);
v___x_7754_ = lean_array_push(v___x_7753_, v___x_7751_);
return v___x_7754_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object* v_objs_7755_, lean_object* v_weakArgs_7756_, lean_object* v_traceArgs_7757_, lean_object* v_libFile_7758_, uint8_t v_linkDeps_7759_, lean_object* v_libs_7760_, lean_object* v___y_7761_, lean_object* v___y_7762_, lean_object* v___y_7763_, lean_object* v___y_7764_, lean_object* v___y_7765_, lean_object* v___y_7766_){
_start:
{
lean_object* v_toContext_7768_; lean_object* v_lakeEnv_7769_; lean_object* v_lean_7770_; lean_object* v_libs_7772_; lean_object* v___y_7773_; 
v_toContext_7768_ = lean_ctor_get(v___y_7765_, 1);
lean_inc(v_toContext_7768_);
lean_dec_ref(v___y_7765_);
v_lakeEnv_7769_ = lean_ctor_get(v_toContext_7768_, 1);
lean_inc_ref(v_lakeEnv_7769_);
lean_dec(v_toContext_7768_);
v_lean_7770_ = lean_ctor_get(v_lakeEnv_7769_, 1);
lean_inc_ref(v_lean_7770_);
lean_dec_ref(v_lakeEnv_7769_);
if (v_linkDeps_7759_ == 0)
{
lean_object* v___x_7818_; 
v___x_7818_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1));
v_libs_7772_ = v___x_7818_;
v___y_7773_ = v___y_7766_;
goto v___jp_7771_;
}
else
{
lean_object* v___x_7819_; 
v___x_7819_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7760_, v___y_7766_);
if (lean_obj_tag(v___x_7819_) == 0)
{
lean_object* v_a_7820_; lean_object* v_a_7821_; 
v_a_7820_ = lean_ctor_get(v___x_7819_, 0);
lean_inc(v_a_7820_);
v_a_7821_ = lean_ctor_get(v___x_7819_, 1);
lean_inc(v_a_7821_);
lean_dec_ref(v___x_7819_);
v_libs_7772_ = v_a_7820_;
v___y_7773_ = v_a_7821_;
goto v___jp_7771_;
}
else
{
lean_object* v_a_7822_; lean_object* v_a_7823_; lean_object* v___x_7825_; uint8_t v_isShared_7826_; uint8_t v_isSharedCheck_7830_; 
lean_dec_ref(v_lean_7770_);
lean_dec_ref(v_libFile_7758_);
v_a_7822_ = lean_ctor_get(v___x_7819_, 0);
v_a_7823_ = lean_ctor_get(v___x_7819_, 1);
v_isSharedCheck_7830_ = !lean_is_exclusive(v___x_7819_);
if (v_isSharedCheck_7830_ == 0)
{
v___x_7825_ = v___x_7819_;
v_isShared_7826_ = v_isSharedCheck_7830_;
goto v_resetjp_7824_;
}
else
{
lean_inc(v_a_7823_);
lean_inc(v_a_7822_);
lean_dec(v___x_7819_);
v___x_7825_ = lean_box(0);
v_isShared_7826_ = v_isSharedCheck_7830_;
goto v_resetjp_7824_;
}
v_resetjp_7824_:
{
lean_object* v___x_7828_; 
if (v_isShared_7826_ == 0)
{
v___x_7828_ = v___x_7825_;
goto v_reusejp_7827_;
}
else
{
lean_object* v_reuseFailAlloc_7829_; 
v_reuseFailAlloc_7829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7829_, 0, v_a_7822_);
lean_ctor_set(v_reuseFailAlloc_7829_, 1, v_a_7823_);
v___x_7828_ = v_reuseFailAlloc_7829_;
goto v_reusejp_7827_;
}
v_reusejp_7827_:
{
return v___x_7828_;
}
}
}
}
v___jp_7771_:
{
lean_object* v_leanLibDir_7774_; lean_object* v_cc_7775_; lean_object* v_ccLinkSharedFlags_7776_; lean_object* v_log_7777_; uint8_t v_action_7778_; uint8_t v_wantsRebuild_7779_; lean_object* v_trace_7780_; lean_object* v_buildTime_7781_; lean_object* v___x_7783_; uint8_t v_isShared_7784_; uint8_t v_isSharedCheck_7817_; 
v_leanLibDir_7774_ = lean_ctor_get(v_lean_7770_, 3);
lean_inc_ref(v_leanLibDir_7774_);
v_cc_7775_ = lean_ctor_get(v_lean_7770_, 14);
lean_inc_ref(v_cc_7775_);
v_ccLinkSharedFlags_7776_ = lean_ctor_get(v_lean_7770_, 20);
lean_inc_ref(v_ccLinkSharedFlags_7776_);
lean_dec_ref(v_lean_7770_);
v_log_7777_ = lean_ctor_get(v___y_7773_, 0);
v_action_7778_ = lean_ctor_get_uint8(v___y_7773_, sizeof(void*)*3);
v_wantsRebuild_7779_ = lean_ctor_get_uint8(v___y_7773_, sizeof(void*)*3 + 1);
v_trace_7780_ = lean_ctor_get(v___y_7773_, 1);
v_buildTime_7781_ = lean_ctor_get(v___y_7773_, 2);
v_isSharedCheck_7817_ = !lean_is_exclusive(v___y_7773_);
if (v_isSharedCheck_7817_ == 0)
{
v___x_7783_ = v___y_7773_;
v_isShared_7784_ = v_isSharedCheck_7817_;
goto v_resetjp_7782_;
}
else
{
lean_inc(v_buildTime_7781_);
lean_inc(v_trace_7780_);
lean_inc(v_log_7777_);
lean_dec(v___y_7773_);
v___x_7783_ = lean_box(0);
v_isShared_7784_ = v_isSharedCheck_7817_;
goto v_resetjp_7782_;
}
v_resetjp_7782_:
{
lean_object* v___x_7785_; lean_object* v___x_7786_; lean_object* v___x_7787_; lean_object* v___x_7788_; lean_object* v___x_7789_; lean_object* v___x_7790_; lean_object* v___x_7791_; lean_object* v___x_7792_; 
v___x_7785_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7755_, v_libs_7772_);
lean_dec_ref(v_libs_7772_);
v___x_7786_ = l_Array_append___redArg(v___x_7785_, v_weakArgs_7756_);
v___x_7787_ = l_Array_append___redArg(v___x_7786_, v_traceArgs_7757_);
v___x_7788_ = lean_obj_once(&l_Lake_buildLeanSharedLib___lam__0___closed__0, &l_Lake_buildLeanSharedLib___lam__0___closed__0_once, _init_l_Lake_buildLeanSharedLib___lam__0___closed__0);
v___x_7789_ = lean_array_push(v___x_7788_, v_leanLibDir_7774_);
v___x_7790_ = l_Array_append___redArg(v___x_7787_, v___x_7789_);
lean_dec_ref(v___x_7789_);
v___x_7791_ = l_Array_append___redArg(v___x_7790_, v_ccLinkSharedFlags_7776_);
lean_dec_ref(v_ccLinkSharedFlags_7776_);
v___x_7792_ = l_Lake_compileSharedLib(v_libFile_7758_, v___x_7791_, v_cc_7775_, v_log_7777_);
lean_dec_ref(v___x_7791_);
if (lean_obj_tag(v___x_7792_) == 0)
{
lean_object* v_a_7793_; lean_object* v_a_7794_; lean_object* v___x_7796_; uint8_t v_isShared_7797_; uint8_t v_isSharedCheck_7804_; 
v_a_7793_ = lean_ctor_get(v___x_7792_, 0);
v_a_7794_ = lean_ctor_get(v___x_7792_, 1);
v_isSharedCheck_7804_ = !lean_is_exclusive(v___x_7792_);
if (v_isSharedCheck_7804_ == 0)
{
v___x_7796_ = v___x_7792_;
v_isShared_7797_ = v_isSharedCheck_7804_;
goto v_resetjp_7795_;
}
else
{
lean_inc(v_a_7794_);
lean_inc(v_a_7793_);
lean_dec(v___x_7792_);
v___x_7796_ = lean_box(0);
v_isShared_7797_ = v_isSharedCheck_7804_;
goto v_resetjp_7795_;
}
v_resetjp_7795_:
{
lean_object* v___x_7799_; 
if (v_isShared_7784_ == 0)
{
lean_ctor_set(v___x_7783_, 0, v_a_7794_);
v___x_7799_ = v___x_7783_;
goto v_reusejp_7798_;
}
else
{
lean_object* v_reuseFailAlloc_7803_; 
v_reuseFailAlloc_7803_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7803_, 0, v_a_7794_);
lean_ctor_set(v_reuseFailAlloc_7803_, 1, v_trace_7780_);
lean_ctor_set(v_reuseFailAlloc_7803_, 2, v_buildTime_7781_);
lean_ctor_set_uint8(v_reuseFailAlloc_7803_, sizeof(void*)*3, v_action_7778_);
lean_ctor_set_uint8(v_reuseFailAlloc_7803_, sizeof(void*)*3 + 1, v_wantsRebuild_7779_);
v___x_7799_ = v_reuseFailAlloc_7803_;
goto v_reusejp_7798_;
}
v_reusejp_7798_:
{
lean_object* v___x_7801_; 
if (v_isShared_7797_ == 0)
{
lean_ctor_set(v___x_7796_, 1, v___x_7799_);
v___x_7801_ = v___x_7796_;
goto v_reusejp_7800_;
}
else
{
lean_object* v_reuseFailAlloc_7802_; 
v_reuseFailAlloc_7802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7802_, 0, v_a_7793_);
lean_ctor_set(v_reuseFailAlloc_7802_, 1, v___x_7799_);
v___x_7801_ = v_reuseFailAlloc_7802_;
goto v_reusejp_7800_;
}
v_reusejp_7800_:
{
return v___x_7801_;
}
}
}
}
else
{
lean_object* v_a_7805_; lean_object* v_a_7806_; lean_object* v___x_7808_; uint8_t v_isShared_7809_; uint8_t v_isSharedCheck_7816_; 
v_a_7805_ = lean_ctor_get(v___x_7792_, 0);
v_a_7806_ = lean_ctor_get(v___x_7792_, 1);
v_isSharedCheck_7816_ = !lean_is_exclusive(v___x_7792_);
if (v_isSharedCheck_7816_ == 0)
{
v___x_7808_ = v___x_7792_;
v_isShared_7809_ = v_isSharedCheck_7816_;
goto v_resetjp_7807_;
}
else
{
lean_inc(v_a_7806_);
lean_inc(v_a_7805_);
lean_dec(v___x_7792_);
v___x_7808_ = lean_box(0);
v_isShared_7809_ = v_isSharedCheck_7816_;
goto v_resetjp_7807_;
}
v_resetjp_7807_:
{
lean_object* v___x_7811_; 
if (v_isShared_7784_ == 0)
{
lean_ctor_set(v___x_7783_, 0, v_a_7806_);
v___x_7811_ = v___x_7783_;
goto v_reusejp_7810_;
}
else
{
lean_object* v_reuseFailAlloc_7815_; 
v_reuseFailAlloc_7815_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7815_, 0, v_a_7806_);
lean_ctor_set(v_reuseFailAlloc_7815_, 1, v_trace_7780_);
lean_ctor_set(v_reuseFailAlloc_7815_, 2, v_buildTime_7781_);
lean_ctor_set_uint8(v_reuseFailAlloc_7815_, sizeof(void*)*3, v_action_7778_);
lean_ctor_set_uint8(v_reuseFailAlloc_7815_, sizeof(void*)*3 + 1, v_wantsRebuild_7779_);
v___x_7811_ = v_reuseFailAlloc_7815_;
goto v_reusejp_7810_;
}
v_reusejp_7810_:
{
lean_object* v___x_7813_; 
if (v_isShared_7809_ == 0)
{
lean_ctor_set(v___x_7808_, 1, v___x_7811_);
v___x_7813_ = v___x_7808_;
goto v_reusejp_7812_;
}
else
{
lean_object* v_reuseFailAlloc_7814_; 
v_reuseFailAlloc_7814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7814_, 0, v_a_7805_);
lean_ctor_set(v_reuseFailAlloc_7814_, 1, v___x_7811_);
v___x_7813_ = v_reuseFailAlloc_7814_;
goto v_reusejp_7812_;
}
v_reusejp_7812_:
{
return v___x_7813_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object* v_objs_7831_, lean_object* v_weakArgs_7832_, lean_object* v_traceArgs_7833_, lean_object* v_libFile_7834_, lean_object* v_linkDeps_7835_, lean_object* v_libs_7836_, lean_object* v___y_7837_, lean_object* v___y_7838_, lean_object* v___y_7839_, lean_object* v___y_7840_, lean_object* v___y_7841_, lean_object* v___y_7842_, lean_object* v___y_7843_){
_start:
{
uint8_t v_linkDeps_boxed_7844_; lean_object* v_res_7845_; 
v_linkDeps_boxed_7844_ = lean_unbox(v_linkDeps_7835_);
v_res_7845_ = l_Lake_buildLeanSharedLib___lam__0(v_objs_7831_, v_weakArgs_7832_, v_traceArgs_7833_, v_libFile_7834_, v_linkDeps_boxed_7844_, v_libs_7836_, v___y_7837_, v___y_7838_, v___y_7839_, v___y_7840_, v___y_7841_, v___y_7842_);
lean_dec(v___y_7840_);
lean_dec(v___y_7839_);
lean_dec(v___y_7838_);
lean_dec_ref(v___y_7837_);
lean_dec_ref(v_libs_7836_);
lean_dec_ref(v_traceArgs_7833_);
lean_dec_ref(v_weakArgs_7832_);
lean_dec_ref(v_objs_7831_);
return v_res_7845_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object* v_objs_7846_, lean_object* v_weakArgs_7847_, lean_object* v_traceArgs_7848_, lean_object* v_libFile_7849_, uint8_t v_linkDeps_7850_, lean_object* v_libName_7851_, uint8_t v_plugin_7852_, lean_object* v_libs_7853_, lean_object* v___y_7854_, lean_object* v___y_7855_, lean_object* v___y_7856_, lean_object* v___y_7857_, lean_object* v___y_7858_, lean_object* v___y_7859_){
_start:
{
lean_object* v_log_7861_; uint8_t v_action_7862_; uint8_t v_wantsRebuild_7863_; lean_object* v_trace_7864_; lean_object* v_buildTime_7865_; lean_object* v___x_7867_; uint8_t v_isShared_7868_; uint8_t v_isSharedCheck_7925_; 
v_log_7861_ = lean_ctor_get(v___y_7859_, 0);
v_action_7862_ = lean_ctor_get_uint8(v___y_7859_, sizeof(void*)*3);
v_wantsRebuild_7863_ = lean_ctor_get_uint8(v___y_7859_, sizeof(void*)*3 + 1);
v_trace_7864_ = lean_ctor_get(v___y_7859_, 1);
v_buildTime_7865_ = lean_ctor_get(v___y_7859_, 2);
v_isSharedCheck_7925_ = !lean_is_exclusive(v___y_7859_);
if (v_isSharedCheck_7925_ == 0)
{
v___x_7867_ = v___y_7859_;
v_isShared_7868_ = v_isSharedCheck_7925_;
goto v_resetjp_7866_;
}
else
{
lean_inc(v_buildTime_7865_);
lean_inc(v_trace_7864_);
lean_inc(v_log_7861_);
lean_dec(v___y_7859_);
v___x_7867_ = lean_box(0);
v_isShared_7868_ = v_isSharedCheck_7925_;
goto v_resetjp_7866_;
}
v_resetjp_7866_:
{
lean_object* v_leanTrace_7869_; lean_object* v___x_7870_; lean_object* v___f_7871_; lean_object* v___x_7872_; uint64_t v___y_7874_; uint64_t v___x_7914_; lean_object* v___x_7915_; lean_object* v___x_7916_; uint8_t v___x_7917_; 
v_leanTrace_7869_ = lean_ctor_get(v___y_7858_, 2);
v___x_7870_ = lean_box(v_linkDeps_7850_);
lean_inc_ref(v_libs_7853_);
lean_inc_ref(v_libFile_7849_);
lean_inc_ref(v_traceArgs_7848_);
v___f_7871_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__0___boxed), 13, 6);
lean_closure_set(v___f_7871_, 0, v_objs_7846_);
lean_closure_set(v___f_7871_, 1, v_weakArgs_7847_);
lean_closure_set(v___f_7871_, 2, v_traceArgs_7848_);
lean_closure_set(v___f_7871_, 3, v_libFile_7849_);
lean_closure_set(v___f_7871_, 4, v___x_7870_);
lean_closure_set(v___f_7871_, 5, v_libs_7853_);
lean_inc_ref(v_leanTrace_7869_);
v___x_7872_ = l_Lake_BuildTrace_mix(v_trace_7864_, v_leanTrace_7869_);
v___x_7914_ = l_Lake_Hash_nil;
v___x_7915_ = lean_unsigned_to_nat(0u);
v___x_7916_ = lean_array_get_size(v_traceArgs_7848_);
v___x_7917_ = lean_nat_dec_lt(v___x_7915_, v___x_7916_);
if (v___x_7917_ == 0)
{
v___y_7874_ = v___x_7914_;
goto v___jp_7873_;
}
else
{
uint8_t v___x_7918_; 
v___x_7918_ = lean_nat_dec_le(v___x_7916_, v___x_7916_);
if (v___x_7918_ == 0)
{
if (v___x_7917_ == 0)
{
v___y_7874_ = v___x_7914_;
goto v___jp_7873_;
}
else
{
size_t v___x_7919_; size_t v___x_7920_; uint64_t v___x_7921_; 
v___x_7919_ = ((size_t)0ULL);
v___x_7920_ = lean_usize_of_nat(v___x_7916_);
v___x_7921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7848_, v___x_7919_, v___x_7920_, v___x_7914_);
v___y_7874_ = v___x_7921_;
goto v___jp_7873_;
}
}
else
{
size_t v___x_7922_; size_t v___x_7923_; uint64_t v___x_7924_; 
v___x_7922_ = ((size_t)0ULL);
v___x_7923_ = lean_usize_of_nat(v___x_7916_);
v___x_7924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7848_, v___x_7922_, v___x_7923_, v___x_7914_);
v___y_7874_ = v___x_7924_;
goto v___jp_7873_;
}
}
v___jp_7873_:
{
lean_object* v___x_7875_; lean_object* v___x_7876_; lean_object* v___x_7877_; lean_object* v___x_7878_; lean_object* v___x_7879_; lean_object* v___x_7880_; lean_object* v___x_7881_; lean_object* v___x_7882_; lean_object* v___x_7883_; lean_object* v___x_7884_; lean_object* v___x_7885_; lean_object* v___x_7886_; lean_object* v___x_7888_; 
v___x_7875_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_7876_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_7877_ = lean_array_to_list(v_traceArgs_7848_);
v___x_7878_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_7877_);
lean_dec(v___x_7877_);
v___x_7879_ = lean_string_append(v___x_7876_, v___x_7878_);
lean_dec_ref(v___x_7878_);
v___x_7880_ = lean_string_append(v___x_7875_, v___x_7879_);
lean_dec_ref(v___x_7879_);
v___x_7881_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_7882_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_7883_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_7883_, 0, v___x_7880_);
lean_ctor_set(v___x_7883_, 1, v___x_7881_);
lean_ctor_set(v___x_7883_, 2, v___x_7882_);
lean_ctor_set_uint64(v___x_7883_, sizeof(void*)*3, v___y_7874_);
v___x_7884_ = l_Lake_BuildTrace_mix(v___x_7872_, v___x_7883_);
v___x_7885_ = l_Lake_platformTrace;
v___x_7886_ = l_Lake_BuildTrace_mix(v___x_7884_, v___x_7885_);
if (v_isShared_7868_ == 0)
{
lean_ctor_set(v___x_7867_, 1, v___x_7886_);
v___x_7888_ = v___x_7867_;
goto v_reusejp_7887_;
}
else
{
lean_object* v_reuseFailAlloc_7913_; 
v_reuseFailAlloc_7913_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7913_, 0, v_log_7861_);
lean_ctor_set(v_reuseFailAlloc_7913_, 1, v___x_7886_);
lean_ctor_set(v_reuseFailAlloc_7913_, 2, v_buildTime_7865_);
lean_ctor_set_uint8(v_reuseFailAlloc_7913_, sizeof(void*)*3, v_action_7862_);
lean_ctor_set_uint8(v_reuseFailAlloc_7913_, sizeof(void*)*3 + 1, v_wantsRebuild_7863_);
v___x_7888_ = v_reuseFailAlloc_7913_;
goto v_reusejp_7887_;
}
v_reusejp_7887_:
{
uint8_t v___x_7889_; lean_object* v___x_7890_; uint8_t v___x_7891_; lean_object* v___x_7892_; 
v___x_7889_ = 0;
v___x_7890_ = l_Lake_sharedLibExt;
v___x_7891_ = 1;
lean_inc(v___y_7855_);
v___x_7892_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_7849_, v___f_7871_, v___x_7889_, v___x_7890_, v___x_7891_, v___x_7889_, v___x_7889_, v___y_7854_, v___y_7855_, v___y_7856_, v___y_7857_, v___y_7858_, v___x_7888_);
lean_dec_ref(v___y_7858_);
if (lean_obj_tag(v___x_7892_) == 0)
{
lean_object* v_a_7893_; lean_object* v_a_7894_; lean_object* v___x_7896_; uint8_t v_isShared_7897_; uint8_t v_isSharedCheck_7903_; 
v_a_7893_ = lean_ctor_get(v___x_7892_, 0);
v_a_7894_ = lean_ctor_get(v___x_7892_, 1);
v_isSharedCheck_7903_ = !lean_is_exclusive(v___x_7892_);
if (v_isSharedCheck_7903_ == 0)
{
v___x_7896_ = v___x_7892_;
v_isShared_7897_ = v_isSharedCheck_7903_;
goto v_resetjp_7895_;
}
else
{
lean_inc(v_a_7894_);
lean_inc(v_a_7893_);
lean_dec(v___x_7892_);
v___x_7896_ = lean_box(0);
v_isShared_7897_ = v_isSharedCheck_7903_;
goto v_resetjp_7895_;
}
v_resetjp_7895_:
{
lean_object* v_path_7898_; lean_object* v___x_7899_; lean_object* v___x_7901_; 
v_path_7898_ = lean_ctor_get(v_a_7893_, 1);
lean_inc_ref(v_path_7898_);
lean_dec(v_a_7893_);
v___x_7899_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_7899_, 0, v_path_7898_);
lean_ctor_set(v___x_7899_, 1, v_libName_7851_);
lean_ctor_set(v___x_7899_, 2, v_libs_7853_);
lean_ctor_set_uint8(v___x_7899_, sizeof(void*)*3, v_plugin_7852_);
if (v_isShared_7897_ == 0)
{
lean_ctor_set(v___x_7896_, 0, v___x_7899_);
v___x_7901_ = v___x_7896_;
goto v_reusejp_7900_;
}
else
{
lean_object* v_reuseFailAlloc_7902_; 
v_reuseFailAlloc_7902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7902_, 0, v___x_7899_);
lean_ctor_set(v_reuseFailAlloc_7902_, 1, v_a_7894_);
v___x_7901_ = v_reuseFailAlloc_7902_;
goto v_reusejp_7900_;
}
v_reusejp_7900_:
{
return v___x_7901_;
}
}
}
else
{
lean_object* v_a_7904_; lean_object* v_a_7905_; lean_object* v___x_7907_; uint8_t v_isShared_7908_; uint8_t v_isSharedCheck_7912_; 
lean_dec_ref(v_libs_7853_);
lean_dec_ref(v_libName_7851_);
v_a_7904_ = lean_ctor_get(v___x_7892_, 0);
v_a_7905_ = lean_ctor_get(v___x_7892_, 1);
v_isSharedCheck_7912_ = !lean_is_exclusive(v___x_7892_);
if (v_isSharedCheck_7912_ == 0)
{
v___x_7907_ = v___x_7892_;
v_isShared_7908_ = v_isSharedCheck_7912_;
goto v_resetjp_7906_;
}
else
{
lean_inc(v_a_7905_);
lean_inc(v_a_7904_);
lean_dec(v___x_7892_);
v___x_7907_ = lean_box(0);
v_isShared_7908_ = v_isSharedCheck_7912_;
goto v_resetjp_7906_;
}
v_resetjp_7906_:
{
lean_object* v___x_7910_; 
if (v_isShared_7908_ == 0)
{
v___x_7910_ = v___x_7907_;
goto v_reusejp_7909_;
}
else
{
lean_object* v_reuseFailAlloc_7911_; 
v_reuseFailAlloc_7911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7911_, 0, v_a_7904_);
lean_ctor_set(v_reuseFailAlloc_7911_, 1, v_a_7905_);
v___x_7910_ = v_reuseFailAlloc_7911_;
goto v_reusejp_7909_;
}
v_reusejp_7909_:
{
return v___x_7910_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1___boxed(lean_object* v_objs_7926_, lean_object* v_weakArgs_7927_, lean_object* v_traceArgs_7928_, lean_object* v_libFile_7929_, lean_object* v_linkDeps_7930_, lean_object* v_libName_7931_, lean_object* v_plugin_7932_, lean_object* v_libs_7933_, lean_object* v___y_7934_, lean_object* v___y_7935_, lean_object* v___y_7936_, lean_object* v___y_7937_, lean_object* v___y_7938_, lean_object* v___y_7939_, lean_object* v___y_7940_){
_start:
{
uint8_t v_linkDeps_boxed_7941_; uint8_t v_plugin_boxed_7942_; lean_object* v_res_7943_; 
v_linkDeps_boxed_7941_ = lean_unbox(v_linkDeps_7930_);
v_plugin_boxed_7942_ = lean_unbox(v_plugin_7932_);
v_res_7943_ = l_Lake_buildLeanSharedLib___lam__1(v_objs_7926_, v_weakArgs_7927_, v_traceArgs_7928_, v_libFile_7929_, v_linkDeps_boxed_7941_, v_libName_7931_, v_plugin_boxed_7942_, v_libs_7933_, v___y_7934_, v___y_7935_, v___y_7936_, v___y_7937_, v___y_7938_, v___y_7939_);
lean_dec(v___y_7937_);
lean_dec(v___y_7936_);
lean_dec(v___y_7935_);
return v_res_7943_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2(lean_object* v_weakArgs_7944_, lean_object* v_traceArgs_7945_, lean_object* v_libFile_7946_, uint8_t v_linkDeps_7947_, lean_object* v_libName_7948_, uint8_t v_plugin_7949_, lean_object* v_linkLibs_7950_, lean_object* v___x_7951_, lean_object* v_objs_7952_, lean_object* v___y_7953_, lean_object* v___y_7954_, lean_object* v___y_7955_, lean_object* v___y_7956_, lean_object* v___y_7957_, lean_object* v___y_7958_){
_start:
{
lean_object* v_trace_7960_; lean_object* v___x_7961_; lean_object* v___x_7962_; lean_object* v___f_7963_; lean_object* v___x_7964_; lean_object* v___x_7965_; lean_object* v___x_7966_; uint8_t v___x_7967_; lean_object* v___x_7968_; lean_object* v___x_7969_; 
v_trace_7960_ = lean_ctor_get(v___y_7958_, 1);
v___x_7961_ = lean_box(v_linkDeps_7947_);
v___x_7962_ = lean_box(v_plugin_7949_);
v___f_7963_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__1___boxed), 15, 7);
lean_closure_set(v___f_7963_, 0, v_objs_7952_);
lean_closure_set(v___f_7963_, 1, v_weakArgs_7944_);
lean_closure_set(v___f_7963_, 2, v_traceArgs_7945_);
lean_closure_set(v___f_7963_, 3, v_libFile_7946_);
lean_closure_set(v___f_7963_, 4, v___x_7961_);
lean_closure_set(v___f_7963_, 5, v_libName_7948_);
lean_closure_set(v___f_7963_, 6, v___x_7962_);
v___x_7964_ = ((lean_object*)(l_Lake_buildSharedLib___lam__3___closed__0));
v___x_7965_ = l_Lake_Job_collectArray___redArg(v_linkLibs_7950_, v___x_7964_);
v___x_7966_ = lean_unsigned_to_nat(0u);
v___x_7967_ = 0;
v___x_7968_ = l_Lake_Job_mapM___redArg(v___x_7951_, v___x_7965_, v___f_7963_, v___x_7966_, v___x_7967_, v___y_7953_, v___y_7954_, v___y_7955_, v___y_7956_, v___y_7957_, v_trace_7960_);
v___x_7969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7969_, 0, v___x_7968_);
lean_ctor_set(v___x_7969_, 1, v___y_7958_);
return v___x_7969_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2___boxed(lean_object* v_weakArgs_7970_, lean_object* v_traceArgs_7971_, lean_object* v_libFile_7972_, lean_object* v_linkDeps_7973_, lean_object* v_libName_7974_, lean_object* v_plugin_7975_, lean_object* v_linkLibs_7976_, lean_object* v___x_7977_, lean_object* v_objs_7978_, lean_object* v___y_7979_, lean_object* v___y_7980_, lean_object* v___y_7981_, lean_object* v___y_7982_, lean_object* v___y_7983_, lean_object* v___y_7984_, lean_object* v___y_7985_){
_start:
{
uint8_t v_linkDeps_boxed_7986_; uint8_t v_plugin_boxed_7987_; lean_object* v_res_7988_; 
v_linkDeps_boxed_7986_ = lean_unbox(v_linkDeps_7973_);
v_plugin_boxed_7987_ = lean_unbox(v_plugin_7975_);
v_res_7988_ = l_Lake_buildLeanSharedLib___lam__2(v_weakArgs_7970_, v_traceArgs_7971_, v_libFile_7972_, v_linkDeps_boxed_7986_, v_libName_7974_, v_plugin_boxed_7987_, v_linkLibs_7976_, v___x_7977_, v_objs_7978_, v___y_7979_, v___y_7980_, v___y_7981_, v___y_7982_, v___y_7983_, v___y_7984_);
lean_dec_ref(v___y_7983_);
lean_dec(v___y_7982_);
lean_dec(v___y_7981_);
lean_dec(v___y_7980_);
lean_dec_ref(v_linkLibs_7976_);
return v_res_7988_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object* v_libName_7989_, lean_object* v_libFile_7990_, lean_object* v_linkObjs_7991_, lean_object* v_linkLibs_7992_, lean_object* v_weakArgs_7993_, lean_object* v_traceArgs_7994_, uint8_t v_plugin_7995_, uint8_t v_linkDeps_7996_, lean_object* v_a_7997_, lean_object* v_a_7998_, lean_object* v_a_7999_, lean_object* v_a_8000_, lean_object* v_a_8001_, lean_object* v_a_8002_){
_start:
{
lean_object* v___x_8004_; lean_object* v___x_8005_; lean_object* v___x_8006_; lean_object* v___f_8007_; lean_object* v___x_8008_; lean_object* v___x_8009_; lean_object* v___x_8010_; uint8_t v___x_8011_; lean_object* v___x_8012_; 
v___x_8004_ = l_Lake_instDataKindDynlib;
v___x_8005_ = lean_box(v_linkDeps_7996_);
v___x_8006_ = lean_box(v_plugin_7995_);
v___f_8007_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__2___boxed), 16, 8);
lean_closure_set(v___f_8007_, 0, v_weakArgs_7993_);
lean_closure_set(v___f_8007_, 1, v_traceArgs_7994_);
lean_closure_set(v___f_8007_, 2, v_libFile_7990_);
lean_closure_set(v___f_8007_, 3, v___x_8005_);
lean_closure_set(v___f_8007_, 4, v_libName_7989_);
lean_closure_set(v___f_8007_, 5, v___x_8006_);
lean_closure_set(v___f_8007_, 6, v_linkLibs_7992_);
lean_closure_set(v___f_8007_, 7, v___x_8004_);
v___x_8008_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8009_ = l_Lake_Job_collectArray___redArg(v_linkObjs_7991_, v___x_8008_);
v___x_8010_ = lean_unsigned_to_nat(0u);
v___x_8011_ = 1;
v___x_8012_ = l_Lake_Job_bindM___redArg(v___x_8004_, v___x_8009_, v___f_8007_, v___x_8010_, v___x_8011_, v_a_7997_, v_a_7998_, v_a_7999_, v_a_8000_, v_a_8001_, v_a_8002_);
return v___x_8012_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object* v_libName_8013_, lean_object* v_libFile_8014_, lean_object* v_linkObjs_8015_, lean_object* v_linkLibs_8016_, lean_object* v_weakArgs_8017_, lean_object* v_traceArgs_8018_, lean_object* v_plugin_8019_, lean_object* v_linkDeps_8020_, lean_object* v_a_8021_, lean_object* v_a_8022_, lean_object* v_a_8023_, lean_object* v_a_8024_, lean_object* v_a_8025_, lean_object* v_a_8026_, lean_object* v_a_8027_){
_start:
{
uint8_t v_plugin_boxed_8028_; uint8_t v_linkDeps_boxed_8029_; lean_object* v_res_8030_; 
v_plugin_boxed_8028_ = lean_unbox(v_plugin_8019_);
v_linkDeps_boxed_8029_ = lean_unbox(v_linkDeps_8020_);
v_res_8030_ = l_Lake_buildLeanSharedLib(v_libName_8013_, v_libFile_8014_, v_linkObjs_8015_, v_linkLibs_8016_, v_weakArgs_8017_, v_traceArgs_8018_, v_plugin_boxed_8028_, v_linkDeps_boxed_8029_, v_a_8021_, v_a_8022_, v_a_8023_, v_a_8024_, v_a_8025_, v_a_8026_);
lean_dec_ref(v_a_8026_);
lean_dec_ref(v_a_8025_);
lean_dec(v_a_8024_);
lean_dec(v_a_8023_);
lean_dec(v_a_8022_);
lean_dec_ref(v_linkObjs_8015_);
return v_res_8030_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0(lean_object* v_libs_8031_, lean_object* v_objs_8032_, lean_object* v_weakArgs_8033_, lean_object* v_traceArgs_8034_, uint8_t v_sharedLean_8035_, lean_object* v_exeFile_8036_, lean_object* v___y_8037_, lean_object* v___y_8038_, lean_object* v___y_8039_, lean_object* v___y_8040_, lean_object* v___y_8041_, lean_object* v___y_8042_){
_start:
{
lean_object* v___x_8044_; 
v___x_8044_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_8031_, v___y_8042_);
if (lean_obj_tag(v___x_8044_) == 0)
{
lean_object* v_toContext_8045_; lean_object* v_lakeEnv_8046_; lean_object* v_lean_8047_; lean_object* v_a_8048_; lean_object* v_a_8049_; lean_object* v_leanLibDir_8050_; lean_object* v_cc_8051_; lean_object* v_log_8052_; uint8_t v_action_8053_; uint8_t v_wantsRebuild_8054_; lean_object* v_trace_8055_; lean_object* v_buildTime_8056_; lean_object* v___x_8058_; uint8_t v_isShared_8059_; uint8_t v_isSharedCheck_8095_; 
v_toContext_8045_ = lean_ctor_get(v___y_8041_, 1);
lean_inc(v_toContext_8045_);
lean_dec_ref(v___y_8041_);
v_lakeEnv_8046_ = lean_ctor_get(v_toContext_8045_, 1);
lean_inc_ref(v_lakeEnv_8046_);
lean_dec(v_toContext_8045_);
v_lean_8047_ = lean_ctor_get(v_lakeEnv_8046_, 1);
lean_inc_ref(v_lean_8047_);
lean_dec_ref(v_lakeEnv_8046_);
v_a_8048_ = lean_ctor_get(v___x_8044_, 1);
lean_inc(v_a_8048_);
v_a_8049_ = lean_ctor_get(v___x_8044_, 0);
lean_inc(v_a_8049_);
lean_dec_ref(v___x_8044_);
v_leanLibDir_8050_ = lean_ctor_get(v_lean_8047_, 3);
v_cc_8051_ = lean_ctor_get(v_lean_8047_, 14);
lean_inc_ref(v_cc_8051_);
v_log_8052_ = lean_ctor_get(v_a_8048_, 0);
v_action_8053_ = lean_ctor_get_uint8(v_a_8048_, sizeof(void*)*3);
v_wantsRebuild_8054_ = lean_ctor_get_uint8(v_a_8048_, sizeof(void*)*3 + 1);
v_trace_8055_ = lean_ctor_get(v_a_8048_, 1);
v_buildTime_8056_ = lean_ctor_get(v_a_8048_, 2);
v_isSharedCheck_8095_ = !lean_is_exclusive(v_a_8048_);
if (v_isSharedCheck_8095_ == 0)
{
v___x_8058_ = v_a_8048_;
v_isShared_8059_ = v_isSharedCheck_8095_;
goto v_resetjp_8057_;
}
else
{
lean_inc(v_buildTime_8056_);
lean_inc(v_trace_8055_);
lean_inc(v_log_8052_);
lean_dec(v_a_8048_);
v___x_8058_ = lean_box(0);
v_isShared_8059_ = v_isSharedCheck_8095_;
goto v_resetjp_8057_;
}
v_resetjp_8057_:
{
lean_object* v___x_8060_; lean_object* v___x_8061_; lean_object* v___x_8062_; lean_object* v___x_8063_; lean_object* v___x_8064_; lean_object* v___x_8065_; lean_object* v___x_8066_; lean_object* v___x_8067_; lean_object* v___x_8068_; lean_object* v___x_8069_; lean_object* v___x_8070_; 
v___x_8060_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_8032_, v_a_8049_);
lean_dec(v_a_8049_);
v___x_8061_ = l_Array_append___redArg(v___x_8060_, v_weakArgs_8033_);
v___x_8062_ = l_Array_append___redArg(v___x_8061_, v_traceArgs_8034_);
v___x_8063_ = lean_unsigned_to_nat(2u);
v___x_8064_ = lean_mk_empty_array_with_capacity(v___x_8063_);
lean_dec_ref(v___x_8064_);
v___x_8065_ = lean_obj_once(&l_Lake_buildLeanSharedLib___lam__0___closed__0, &l_Lake_buildLeanSharedLib___lam__0___closed__0_once, _init_l_Lake_buildLeanSharedLib___lam__0___closed__0);
lean_inc_ref(v_leanLibDir_8050_);
v___x_8066_ = lean_array_push(v___x_8065_, v_leanLibDir_8050_);
v___x_8067_ = l_Array_append___redArg(v___x_8062_, v___x_8066_);
lean_dec_ref(v___x_8066_);
v___x_8068_ = l_Lake_LeanInstall_ccLinkFlags(v_sharedLean_8035_, v_lean_8047_);
lean_dec_ref(v_lean_8047_);
v___x_8069_ = l_Array_append___redArg(v___x_8067_, v___x_8068_);
lean_dec_ref(v___x_8068_);
v___x_8070_ = l_Lake_compileExe(v_exeFile_8036_, v___x_8069_, v_cc_8051_, v_log_8052_);
lean_dec_ref(v___x_8069_);
if (lean_obj_tag(v___x_8070_) == 0)
{
lean_object* v_a_8071_; lean_object* v_a_8072_; lean_object* v___x_8074_; uint8_t v_isShared_8075_; uint8_t v_isSharedCheck_8082_; 
v_a_8071_ = lean_ctor_get(v___x_8070_, 0);
v_a_8072_ = lean_ctor_get(v___x_8070_, 1);
v_isSharedCheck_8082_ = !lean_is_exclusive(v___x_8070_);
if (v_isSharedCheck_8082_ == 0)
{
v___x_8074_ = v___x_8070_;
v_isShared_8075_ = v_isSharedCheck_8082_;
goto v_resetjp_8073_;
}
else
{
lean_inc(v_a_8072_);
lean_inc(v_a_8071_);
lean_dec(v___x_8070_);
v___x_8074_ = lean_box(0);
v_isShared_8075_ = v_isSharedCheck_8082_;
goto v_resetjp_8073_;
}
v_resetjp_8073_:
{
lean_object* v___x_8077_; 
if (v_isShared_8059_ == 0)
{
lean_ctor_set(v___x_8058_, 0, v_a_8072_);
v___x_8077_ = v___x_8058_;
goto v_reusejp_8076_;
}
else
{
lean_object* v_reuseFailAlloc_8081_; 
v_reuseFailAlloc_8081_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8081_, 0, v_a_8072_);
lean_ctor_set(v_reuseFailAlloc_8081_, 1, v_trace_8055_);
lean_ctor_set(v_reuseFailAlloc_8081_, 2, v_buildTime_8056_);
lean_ctor_set_uint8(v_reuseFailAlloc_8081_, sizeof(void*)*3, v_action_8053_);
lean_ctor_set_uint8(v_reuseFailAlloc_8081_, sizeof(void*)*3 + 1, v_wantsRebuild_8054_);
v___x_8077_ = v_reuseFailAlloc_8081_;
goto v_reusejp_8076_;
}
v_reusejp_8076_:
{
lean_object* v___x_8079_; 
if (v_isShared_8075_ == 0)
{
lean_ctor_set(v___x_8074_, 1, v___x_8077_);
v___x_8079_ = v___x_8074_;
goto v_reusejp_8078_;
}
else
{
lean_object* v_reuseFailAlloc_8080_; 
v_reuseFailAlloc_8080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8080_, 0, v_a_8071_);
lean_ctor_set(v_reuseFailAlloc_8080_, 1, v___x_8077_);
v___x_8079_ = v_reuseFailAlloc_8080_;
goto v_reusejp_8078_;
}
v_reusejp_8078_:
{
return v___x_8079_;
}
}
}
}
else
{
lean_object* v_a_8083_; lean_object* v_a_8084_; lean_object* v___x_8086_; uint8_t v_isShared_8087_; uint8_t v_isSharedCheck_8094_; 
v_a_8083_ = lean_ctor_get(v___x_8070_, 0);
v_a_8084_ = lean_ctor_get(v___x_8070_, 1);
v_isSharedCheck_8094_ = !lean_is_exclusive(v___x_8070_);
if (v_isSharedCheck_8094_ == 0)
{
v___x_8086_ = v___x_8070_;
v_isShared_8087_ = v_isSharedCheck_8094_;
goto v_resetjp_8085_;
}
else
{
lean_inc(v_a_8084_);
lean_inc(v_a_8083_);
lean_dec(v___x_8070_);
v___x_8086_ = lean_box(0);
v_isShared_8087_ = v_isSharedCheck_8094_;
goto v_resetjp_8085_;
}
v_resetjp_8085_:
{
lean_object* v___x_8089_; 
if (v_isShared_8059_ == 0)
{
lean_ctor_set(v___x_8058_, 0, v_a_8084_);
v___x_8089_ = v___x_8058_;
goto v_reusejp_8088_;
}
else
{
lean_object* v_reuseFailAlloc_8093_; 
v_reuseFailAlloc_8093_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8093_, 0, v_a_8084_);
lean_ctor_set(v_reuseFailAlloc_8093_, 1, v_trace_8055_);
lean_ctor_set(v_reuseFailAlloc_8093_, 2, v_buildTime_8056_);
lean_ctor_set_uint8(v_reuseFailAlloc_8093_, sizeof(void*)*3, v_action_8053_);
lean_ctor_set_uint8(v_reuseFailAlloc_8093_, sizeof(void*)*3 + 1, v_wantsRebuild_8054_);
v___x_8089_ = v_reuseFailAlloc_8093_;
goto v_reusejp_8088_;
}
v_reusejp_8088_:
{
lean_object* v___x_8091_; 
if (v_isShared_8087_ == 0)
{
lean_ctor_set(v___x_8086_, 1, v___x_8089_);
v___x_8091_ = v___x_8086_;
goto v_reusejp_8090_;
}
else
{
lean_object* v_reuseFailAlloc_8092_; 
v_reuseFailAlloc_8092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8092_, 0, v_a_8083_);
lean_ctor_set(v_reuseFailAlloc_8092_, 1, v___x_8089_);
v___x_8091_ = v_reuseFailAlloc_8092_;
goto v_reusejp_8090_;
}
v_reusejp_8090_:
{
return v___x_8091_;
}
}
}
}
}
}
else
{
lean_object* v_a_8096_; lean_object* v_a_8097_; lean_object* v___x_8099_; uint8_t v_isShared_8100_; uint8_t v_isSharedCheck_8104_; 
lean_dec_ref(v___y_8041_);
lean_dec_ref(v_exeFile_8036_);
v_a_8096_ = lean_ctor_get(v___x_8044_, 0);
v_a_8097_ = lean_ctor_get(v___x_8044_, 1);
v_isSharedCheck_8104_ = !lean_is_exclusive(v___x_8044_);
if (v_isSharedCheck_8104_ == 0)
{
v___x_8099_ = v___x_8044_;
v_isShared_8100_ = v_isSharedCheck_8104_;
goto v_resetjp_8098_;
}
else
{
lean_inc(v_a_8097_);
lean_inc(v_a_8096_);
lean_dec(v___x_8044_);
v___x_8099_ = lean_box(0);
v_isShared_8100_ = v_isSharedCheck_8104_;
goto v_resetjp_8098_;
}
v_resetjp_8098_:
{
lean_object* v___x_8102_; 
if (v_isShared_8100_ == 0)
{
v___x_8102_ = v___x_8099_;
goto v_reusejp_8101_;
}
else
{
lean_object* v_reuseFailAlloc_8103_; 
v_reuseFailAlloc_8103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8103_, 0, v_a_8096_);
lean_ctor_set(v_reuseFailAlloc_8103_, 1, v_a_8097_);
v___x_8102_ = v_reuseFailAlloc_8103_;
goto v_reusejp_8101_;
}
v_reusejp_8101_:
{
return v___x_8102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object* v_libs_8105_, lean_object* v_objs_8106_, lean_object* v_weakArgs_8107_, lean_object* v_traceArgs_8108_, lean_object* v_sharedLean_8109_, lean_object* v_exeFile_8110_, lean_object* v___y_8111_, lean_object* v___y_8112_, lean_object* v___y_8113_, lean_object* v___y_8114_, lean_object* v___y_8115_, lean_object* v___y_8116_, lean_object* v___y_8117_){
_start:
{
uint8_t v_sharedLean_boxed_8118_; lean_object* v_res_8119_; 
v_sharedLean_boxed_8118_ = lean_unbox(v_sharedLean_8109_);
v_res_8119_ = l_Lake_buildLeanExe___lam__0(v_libs_8105_, v_objs_8106_, v_weakArgs_8107_, v_traceArgs_8108_, v_sharedLean_boxed_8118_, v_exeFile_8110_, v___y_8111_, v___y_8112_, v___y_8113_, v___y_8114_, v___y_8115_, v___y_8116_);
lean_dec(v___y_8114_);
lean_dec(v___y_8113_);
lean_dec(v___y_8112_);
lean_dec_ref(v___y_8111_);
lean_dec_ref(v_traceArgs_8108_);
lean_dec_ref(v_weakArgs_8107_);
lean_dec_ref(v_objs_8106_);
lean_dec_ref(v_libs_8105_);
return v_res_8119_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object* v_objs_8120_, lean_object* v_weakArgs_8121_, lean_object* v_traceArgs_8122_, uint8_t v_sharedLean_8123_, lean_object* v_exeFile_8124_, lean_object* v_libs_8125_, lean_object* v___y_8126_, lean_object* v___y_8127_, lean_object* v___y_8128_, lean_object* v___y_8129_, lean_object* v___y_8130_, lean_object* v___y_8131_){
_start:
{
lean_object* v_log_8133_; uint8_t v_action_8134_; uint8_t v_wantsRebuild_8135_; lean_object* v_trace_8136_; lean_object* v_buildTime_8137_; lean_object* v___x_8139_; uint8_t v_isShared_8140_; uint8_t v_isSharedCheck_8196_; 
v_log_8133_ = lean_ctor_get(v___y_8131_, 0);
v_action_8134_ = lean_ctor_get_uint8(v___y_8131_, sizeof(void*)*3);
v_wantsRebuild_8135_ = lean_ctor_get_uint8(v___y_8131_, sizeof(void*)*3 + 1);
v_trace_8136_ = lean_ctor_get(v___y_8131_, 1);
v_buildTime_8137_ = lean_ctor_get(v___y_8131_, 2);
v_isSharedCheck_8196_ = !lean_is_exclusive(v___y_8131_);
if (v_isSharedCheck_8196_ == 0)
{
v___x_8139_ = v___y_8131_;
v_isShared_8140_ = v_isSharedCheck_8196_;
goto v_resetjp_8138_;
}
else
{
lean_inc(v_buildTime_8137_);
lean_inc(v_trace_8136_);
lean_inc(v_log_8133_);
lean_dec(v___y_8131_);
v___x_8139_ = lean_box(0);
v_isShared_8140_ = v_isSharedCheck_8196_;
goto v_resetjp_8138_;
}
v_resetjp_8138_:
{
lean_object* v_leanTrace_8141_; lean_object* v___x_8142_; lean_object* v___f_8143_; lean_object* v___x_8144_; uint64_t v___y_8146_; uint64_t v___x_8185_; lean_object* v___x_8186_; lean_object* v___x_8187_; uint8_t v___x_8188_; 
v_leanTrace_8141_ = lean_ctor_get(v___y_8130_, 2);
v___x_8142_ = lean_box(v_sharedLean_8123_);
lean_inc_ref(v_exeFile_8124_);
lean_inc_ref(v_traceArgs_8122_);
v___f_8143_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__0___boxed), 13, 6);
lean_closure_set(v___f_8143_, 0, v_libs_8125_);
lean_closure_set(v___f_8143_, 1, v_objs_8120_);
lean_closure_set(v___f_8143_, 2, v_weakArgs_8121_);
lean_closure_set(v___f_8143_, 3, v_traceArgs_8122_);
lean_closure_set(v___f_8143_, 4, v___x_8142_);
lean_closure_set(v___f_8143_, 5, v_exeFile_8124_);
lean_inc_ref(v_leanTrace_8141_);
v___x_8144_ = l_Lake_BuildTrace_mix(v_trace_8136_, v_leanTrace_8141_);
v___x_8185_ = l_Lake_Hash_nil;
v___x_8186_ = lean_unsigned_to_nat(0u);
v___x_8187_ = lean_array_get_size(v_traceArgs_8122_);
v___x_8188_ = lean_nat_dec_lt(v___x_8186_, v___x_8187_);
if (v___x_8188_ == 0)
{
v___y_8146_ = v___x_8185_;
goto v___jp_8145_;
}
else
{
uint8_t v___x_8189_; 
v___x_8189_ = lean_nat_dec_le(v___x_8187_, v___x_8187_);
if (v___x_8189_ == 0)
{
if (v___x_8188_ == 0)
{
v___y_8146_ = v___x_8185_;
goto v___jp_8145_;
}
else
{
size_t v___x_8190_; size_t v___x_8191_; uint64_t v___x_8192_; 
v___x_8190_ = ((size_t)0ULL);
v___x_8191_ = lean_usize_of_nat(v___x_8187_);
v___x_8192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8122_, v___x_8190_, v___x_8191_, v___x_8185_);
v___y_8146_ = v___x_8192_;
goto v___jp_8145_;
}
}
else
{
size_t v___x_8193_; size_t v___x_8194_; uint64_t v___x_8195_; 
v___x_8193_ = ((size_t)0ULL);
v___x_8194_ = lean_usize_of_nat(v___x_8187_);
v___x_8195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8122_, v___x_8193_, v___x_8194_, v___x_8185_);
v___y_8146_ = v___x_8195_;
goto v___jp_8145_;
}
}
v___jp_8145_:
{
lean_object* v___x_8147_; lean_object* v___x_8148_; lean_object* v___x_8149_; lean_object* v___x_8150_; lean_object* v___x_8151_; lean_object* v___x_8152_; lean_object* v___x_8153_; lean_object* v___x_8154_; lean_object* v___x_8155_; lean_object* v___x_8156_; lean_object* v___x_8157_; lean_object* v___x_8158_; lean_object* v___x_8160_; 
v___x_8147_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_8148_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_8149_ = lean_array_to_list(v_traceArgs_8122_);
v___x_8150_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_8149_);
lean_dec(v___x_8149_);
v___x_8151_ = lean_string_append(v___x_8148_, v___x_8150_);
lean_dec_ref(v___x_8150_);
v___x_8152_ = lean_string_append(v___x_8147_, v___x_8151_);
lean_dec_ref(v___x_8151_);
v___x_8153_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_8154_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_8155_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_8155_, 0, v___x_8152_);
lean_ctor_set(v___x_8155_, 1, v___x_8153_);
lean_ctor_set(v___x_8155_, 2, v___x_8154_);
lean_ctor_set_uint64(v___x_8155_, sizeof(void*)*3, v___y_8146_);
v___x_8156_ = l_Lake_BuildTrace_mix(v___x_8144_, v___x_8155_);
v___x_8157_ = l_Lake_platformTrace;
v___x_8158_ = l_Lake_BuildTrace_mix(v___x_8156_, v___x_8157_);
if (v_isShared_8140_ == 0)
{
lean_ctor_set(v___x_8139_, 1, v___x_8158_);
v___x_8160_ = v___x_8139_;
goto v_reusejp_8159_;
}
else
{
lean_object* v_reuseFailAlloc_8184_; 
v_reuseFailAlloc_8184_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8184_, 0, v_log_8133_);
lean_ctor_set(v_reuseFailAlloc_8184_, 1, v___x_8158_);
lean_ctor_set(v_reuseFailAlloc_8184_, 2, v_buildTime_8137_);
lean_ctor_set_uint8(v_reuseFailAlloc_8184_, sizeof(void*)*3, v_action_8134_);
lean_ctor_set_uint8(v_reuseFailAlloc_8184_, sizeof(void*)*3 + 1, v_wantsRebuild_8135_);
v___x_8160_ = v_reuseFailAlloc_8184_;
goto v_reusejp_8159_;
}
v_reusejp_8159_:
{
uint8_t v___x_8161_; lean_object* v___x_8162_; uint8_t v___x_8163_; lean_object* v___x_8164_; 
v___x_8161_ = 0;
v___x_8162_ = l_System_FilePath_exeExtension;
v___x_8163_ = 1;
lean_inc(v___y_8127_);
v___x_8164_ = l_Lake_buildArtifactUnlessUpToDate(v_exeFile_8124_, v___f_8143_, v___x_8161_, v___x_8162_, v___x_8163_, v___x_8163_, v___x_8161_, v___y_8126_, v___y_8127_, v___y_8128_, v___y_8129_, v___y_8130_, v___x_8160_);
lean_dec_ref(v___y_8130_);
if (lean_obj_tag(v___x_8164_) == 0)
{
lean_object* v_a_8165_; lean_object* v_a_8166_; lean_object* v___x_8168_; uint8_t v_isShared_8169_; uint8_t v_isSharedCheck_8174_; 
v_a_8165_ = lean_ctor_get(v___x_8164_, 0);
v_a_8166_ = lean_ctor_get(v___x_8164_, 1);
v_isSharedCheck_8174_ = !lean_is_exclusive(v___x_8164_);
if (v_isSharedCheck_8174_ == 0)
{
v___x_8168_ = v___x_8164_;
v_isShared_8169_ = v_isSharedCheck_8174_;
goto v_resetjp_8167_;
}
else
{
lean_inc(v_a_8166_);
lean_inc(v_a_8165_);
lean_dec(v___x_8164_);
v___x_8168_ = lean_box(0);
v_isShared_8169_ = v_isSharedCheck_8174_;
goto v_resetjp_8167_;
}
v_resetjp_8167_:
{
lean_object* v_path_8170_; lean_object* v___x_8172_; 
v_path_8170_ = lean_ctor_get(v_a_8165_, 1);
lean_inc_ref(v_path_8170_);
lean_dec(v_a_8165_);
if (v_isShared_8169_ == 0)
{
lean_ctor_set(v___x_8168_, 0, v_path_8170_);
v___x_8172_ = v___x_8168_;
goto v_reusejp_8171_;
}
else
{
lean_object* v_reuseFailAlloc_8173_; 
v_reuseFailAlloc_8173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8173_, 0, v_path_8170_);
lean_ctor_set(v_reuseFailAlloc_8173_, 1, v_a_8166_);
v___x_8172_ = v_reuseFailAlloc_8173_;
goto v_reusejp_8171_;
}
v_reusejp_8171_:
{
return v___x_8172_;
}
}
}
else
{
lean_object* v_a_8175_; lean_object* v_a_8176_; lean_object* v___x_8178_; uint8_t v_isShared_8179_; uint8_t v_isSharedCheck_8183_; 
v_a_8175_ = lean_ctor_get(v___x_8164_, 0);
v_a_8176_ = lean_ctor_get(v___x_8164_, 1);
v_isSharedCheck_8183_ = !lean_is_exclusive(v___x_8164_);
if (v_isSharedCheck_8183_ == 0)
{
v___x_8178_ = v___x_8164_;
v_isShared_8179_ = v_isSharedCheck_8183_;
goto v_resetjp_8177_;
}
else
{
lean_inc(v_a_8176_);
lean_inc(v_a_8175_);
lean_dec(v___x_8164_);
v___x_8178_ = lean_box(0);
v_isShared_8179_ = v_isSharedCheck_8183_;
goto v_resetjp_8177_;
}
v_resetjp_8177_:
{
lean_object* v___x_8181_; 
if (v_isShared_8179_ == 0)
{
v___x_8181_ = v___x_8178_;
goto v_reusejp_8180_;
}
else
{
lean_object* v_reuseFailAlloc_8182_; 
v_reuseFailAlloc_8182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8182_, 0, v_a_8175_);
lean_ctor_set(v_reuseFailAlloc_8182_, 1, v_a_8176_);
v___x_8181_ = v_reuseFailAlloc_8182_;
goto v_reusejp_8180_;
}
v_reusejp_8180_:
{
return v___x_8181_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object* v_objs_8197_, lean_object* v_weakArgs_8198_, lean_object* v_traceArgs_8199_, lean_object* v_sharedLean_8200_, lean_object* v_exeFile_8201_, lean_object* v_libs_8202_, lean_object* v___y_8203_, lean_object* v___y_8204_, lean_object* v___y_8205_, lean_object* v___y_8206_, lean_object* v___y_8207_, lean_object* v___y_8208_, lean_object* v___y_8209_){
_start:
{
uint8_t v_sharedLean_boxed_8210_; lean_object* v_res_8211_; 
v_sharedLean_boxed_8210_ = lean_unbox(v_sharedLean_8200_);
v_res_8211_ = l_Lake_buildLeanExe___lam__1(v_objs_8197_, v_weakArgs_8198_, v_traceArgs_8199_, v_sharedLean_boxed_8210_, v_exeFile_8201_, v_libs_8202_, v___y_8203_, v___y_8204_, v___y_8205_, v___y_8206_, v___y_8207_, v___y_8208_);
lean_dec(v___y_8206_);
lean_dec(v___y_8205_);
lean_dec(v___y_8204_);
return v_res_8211_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2(lean_object* v_weakArgs_8212_, lean_object* v_traceArgs_8213_, uint8_t v_sharedLean_8214_, lean_object* v_exeFile_8215_, lean_object* v_linkLibs_8216_, lean_object* v___x_8217_, lean_object* v_objs_8218_, lean_object* v___y_8219_, lean_object* v___y_8220_, lean_object* v___y_8221_, lean_object* v___y_8222_, lean_object* v___y_8223_, lean_object* v___y_8224_){
_start:
{
lean_object* v_trace_8226_; lean_object* v___x_8227_; lean_object* v___f_8228_; lean_object* v___x_8229_; lean_object* v___x_8230_; lean_object* v___x_8231_; uint8_t v___x_8232_; lean_object* v___x_8233_; lean_object* v___x_8234_; 
v_trace_8226_ = lean_ctor_get(v___y_8224_, 1);
v___x_8227_ = lean_box(v_sharedLean_8214_);
v___f_8228_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__1___boxed), 13, 5);
lean_closure_set(v___f_8228_, 0, v_objs_8218_);
lean_closure_set(v___f_8228_, 1, v_weakArgs_8212_);
lean_closure_set(v___f_8228_, 2, v_traceArgs_8213_);
lean_closure_set(v___f_8228_, 3, v___x_8227_);
lean_closure_set(v___f_8228_, 4, v_exeFile_8215_);
v___x_8229_ = ((lean_object*)(l_Lake_buildSharedLib___lam__3___closed__0));
v___x_8230_ = l_Lake_Job_collectArray___redArg(v_linkLibs_8216_, v___x_8229_);
v___x_8231_ = lean_unsigned_to_nat(0u);
v___x_8232_ = 0;
v___x_8233_ = l_Lake_Job_mapM___redArg(v___x_8217_, v___x_8230_, v___f_8228_, v___x_8231_, v___x_8232_, v___y_8219_, v___y_8220_, v___y_8221_, v___y_8222_, v___y_8223_, v_trace_8226_);
v___x_8234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8234_, 0, v___x_8233_);
lean_ctor_set(v___x_8234_, 1, v___y_8224_);
return v___x_8234_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2___boxed(lean_object* v_weakArgs_8235_, lean_object* v_traceArgs_8236_, lean_object* v_sharedLean_8237_, lean_object* v_exeFile_8238_, lean_object* v_linkLibs_8239_, lean_object* v___x_8240_, lean_object* v_objs_8241_, lean_object* v___y_8242_, lean_object* v___y_8243_, lean_object* v___y_8244_, lean_object* v___y_8245_, lean_object* v___y_8246_, lean_object* v___y_8247_, lean_object* v___y_8248_){
_start:
{
uint8_t v_sharedLean_boxed_8249_; lean_object* v_res_8250_; 
v_sharedLean_boxed_8249_ = lean_unbox(v_sharedLean_8237_);
v_res_8250_ = l_Lake_buildLeanExe___lam__2(v_weakArgs_8235_, v_traceArgs_8236_, v_sharedLean_boxed_8249_, v_exeFile_8238_, v_linkLibs_8239_, v___x_8240_, v_objs_8241_, v___y_8242_, v___y_8243_, v___y_8244_, v___y_8245_, v___y_8246_, v___y_8247_);
lean_dec_ref(v___y_8246_);
lean_dec(v___y_8245_);
lean_dec(v___y_8244_);
lean_dec(v___y_8243_);
lean_dec_ref(v_linkLibs_8239_);
return v_res_8250_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object* v_exeFile_8251_, lean_object* v_linkObjs_8252_, lean_object* v_linkLibs_8253_, lean_object* v_weakArgs_8254_, lean_object* v_traceArgs_8255_, uint8_t v_sharedLean_8256_, lean_object* v_a_8257_, lean_object* v_a_8258_, lean_object* v_a_8259_, lean_object* v_a_8260_, lean_object* v_a_8261_, lean_object* v_a_8262_){
_start:
{
lean_object* v___x_8264_; lean_object* v___x_8265_; lean_object* v___f_8266_; lean_object* v___x_8267_; lean_object* v___x_8268_; lean_object* v___x_8269_; uint8_t v___x_8270_; lean_object* v___x_8271_; 
v___x_8264_ = l_Lake_instDataKindFilePath;
v___x_8265_ = lean_box(v_sharedLean_8256_);
v___f_8266_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__2___boxed), 14, 6);
lean_closure_set(v___f_8266_, 0, v_weakArgs_8254_);
lean_closure_set(v___f_8266_, 1, v_traceArgs_8255_);
lean_closure_set(v___f_8266_, 2, v___x_8265_);
lean_closure_set(v___f_8266_, 3, v_exeFile_8251_);
lean_closure_set(v___f_8266_, 4, v_linkLibs_8253_);
lean_closure_set(v___f_8266_, 5, v___x_8264_);
v___x_8267_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8268_ = l_Lake_Job_collectArray___redArg(v_linkObjs_8252_, v___x_8267_);
v___x_8269_ = lean_unsigned_to_nat(0u);
v___x_8270_ = 1;
v___x_8271_ = l_Lake_Job_bindM___redArg(v___x_8264_, v___x_8268_, v___f_8266_, v___x_8269_, v___x_8270_, v_a_8257_, v_a_8258_, v_a_8259_, v_a_8260_, v_a_8261_, v_a_8262_);
return v___x_8271_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object* v_exeFile_8272_, lean_object* v_linkObjs_8273_, lean_object* v_linkLibs_8274_, lean_object* v_weakArgs_8275_, lean_object* v_traceArgs_8276_, lean_object* v_sharedLean_8277_, lean_object* v_a_8278_, lean_object* v_a_8279_, lean_object* v_a_8280_, lean_object* v_a_8281_, lean_object* v_a_8282_, lean_object* v_a_8283_, lean_object* v_a_8284_){
_start:
{
uint8_t v_sharedLean_boxed_8285_; lean_object* v_res_8286_; 
v_sharedLean_boxed_8285_ = lean_unbox(v_sharedLean_8277_);
v_res_8286_ = l_Lake_buildLeanExe(v_exeFile_8272_, v_linkObjs_8273_, v_linkLibs_8274_, v_weakArgs_8275_, v_traceArgs_8276_, v_sharedLean_boxed_8285_, v_a_8278_, v_a_8279_, v_a_8280_, v_a_8281_, v_a_8282_, v_a_8283_);
lean_dec_ref(v_a_8283_);
lean_dec_ref(v_a_8282_);
lean_dec(v_a_8281_);
lean_dec(v_a_8280_);
lean_dec(v_a_8279_);
lean_dec_ref(v_linkObjs_8273_);
return v_res_8286_;
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
