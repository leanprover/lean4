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
lean_object* l_Lake_writeBinFileIfNew(lean_object*, lean_object*);
lean_object* l_String_crlfToLf(lean_object*);
lean_object* l_Lake_writeFileIfNew(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Cache_saveArtifact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "failed to cache artifact: "};
static const lean_object* l_Lake_Cache_saveArtifact___closed__0 = (const lean_object*)&l_Lake_Cache_saveArtifact___closed__0_value;
static const lean_string_object l_Lake_Cache_saveArtifact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "artifacts"};
static const lean_object* l_Lake_Cache_saveArtifact___closed__1 = (const lean_object*)&l_Lake_Cache_saveArtifact___closed__1_value;
static const lean_ctor_object l_Lake_Cache_saveArtifact___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_Cache_saveArtifact___closed__2 = (const lean_object*)&l_Lake_Cache_saveArtifact___closed__2_value;
static const lean_ctor_object l_Lake_Cache_saveArtifact___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Cache_saveArtifact___closed__2_value),((lean_object*)&l_Lake_Cache_saveArtifact___closed__2_value),((lean_object*)&l_Lake_Cache_saveArtifact___closed__2_value)}};
static const lean_object* l_Lake_Cache_saveArtifact___closed__3 = (const lean_object*)&l_Lake_Cache_saveArtifact___closed__3_value;
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
lean_object* v___x_43_; lean_object* v_toApplicative_44_; lean_object* v_toBind_45_; lean_object* v_toFunctor_46_; lean_object* v_toPure_47_; lean_object* v___f_48_; lean_object* v___f_49_; lean_object* v___f_50_; lean_object* v___f_51_; lean_object* v___x_52_; lean_object* v___f_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___f_56_; lean_object* v___f_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v_toApplicative_63_; lean_object* v_toFunctor_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v_toApplicative_68_; lean_object* v_toFunctor_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___f_73_; lean_object* v___f_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v_toApplicative_77_; lean_object* v_toFunctor_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___f_84_; lean_object* v___f_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v_toApplicative_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_106_; 
v___x_43_ = l_instMonadBaseIO;
v_toApplicative_44_ = lean_ctor_get(v___x_43_, 0);
v_toBind_45_ = lean_ctor_get(v___x_43_, 1);
v_toFunctor_46_ = lean_ctor_get(v_toApplicative_44_, 0);
v_toPure_47_ = lean_ctor_get(v_toApplicative_44_, 1);
lean_inc_n(v_toBind_45_, 3);
lean_inc_n(v_toPure_47_, 5);
v___f_48_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_48_, 0, v_toPure_47_);
lean_closure_set(v___f_48_, 1, v_toBind_45_);
v___f_49_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_49_, 0, v_toPure_47_);
lean_closure_set(v___f_49_, 1, v_toBind_45_);
lean_inc_ref(v___f_48_);
v___f_50_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_50_, 0, v_toPure_47_);
lean_closure_set(v___f_50_, 1, v___f_48_);
lean_inc_ref_n(v_toFunctor_46_, 2);
v___f_51_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_51_, 0, v_toFunctor_46_);
lean_closure_set(v___f_51_, 1, v_toPure_47_);
lean_closure_set(v___f_51_, 2, v_toBind_45_);
v___x_52_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_46_);
v___f_53_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_53_, 0, v_toPure_47_);
lean_inc_ref_n(v___x_52_, 2);
v___x_54_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_54_, 0, v___x_52_);
lean_ctor_set(v___x_54_, 1, v___f_53_);
lean_ctor_set(v___x_54_, 2, v___f_51_);
lean_ctor_set(v___x_54_, 3, v___f_50_);
lean_ctor_set(v___x_54_, 4, v___f_49_);
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___f_48_);
v___f_56_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_56_, 0, v___x_52_);
v___f_57_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_57_, 0, v___x_52_);
v___x_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_58_, 0, v___f_56_);
lean_ctor_set(v___x_58_, 1, v___f_57_);
v___x_59_ = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__15, &l_Lake_instMonadWorkspaceJobM___closed__15_once, _init_l_Lake_instMonadWorkspaceJobM___closed__15);
lean_inc_ref(v___x_55_);
v___x_60_ = l_ReaderT_instAlternativeOfMonad___redArg(v___x_59_, v___x_55_);
v___x_61_ = l_ReaderT_instMonad___redArg(v___x_55_);
lean_inc_ref(v___x_61_);
v___x_62_ = l_StateRefT_x27_instAlternativeOfMonad___redArg(v___x_60_, v___x_61_);
v_toApplicative_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc_ref(v_toApplicative_63_);
lean_dec_ref(v___x_62_);
v_toFunctor_64_ = lean_ctor_get(v_toApplicative_63_, 0);
lean_inc_ref_n(v_toFunctor_64_, 2);
lean_dec_ref(v_toApplicative_63_);
v___x_65_ = lean_obj_once(&l_Lake_instMonadWorkspaceJobM___closed__19, &l_Lake_instMonadWorkspaceJobM___closed__19_once, _init_l_Lake_instMonadWorkspaceJobM___closed__19);
lean_inc_ref(v___x_58_);
v___x_66_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_65_, v___x_58_);
v___x_67_ = l_StateRefT_x27_instMonad___redArg(v___x_61_);
v_toApplicative_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc_ref(v_toApplicative_68_);
v_toFunctor_69_ = lean_ctor_get(v_toApplicative_68_, 0);
lean_inc_ref_n(v_toFunctor_69_, 2);
lean_dec_ref(v_toApplicative_68_);
v___x_70_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v___x_66_, v___x_58_);
v___x_71_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_71_, 0, lean_box(0));
lean_closure_set(v___x_71_, 1, lean_box(0));
lean_closure_set(v___x_71_, 2, lean_box(0));
lean_closure_set(v___x_71_, 3, lean_box(0));
lean_closure_set(v___x_71_, 4, v___x_70_);
v___x_72_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_71_, v_toFunctor_64_);
v___f_73_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_73_, 0, v_toFunctor_69_);
v___f_74_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_74_, 0, v_toFunctor_69_);
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v___f_73_);
lean_ctor_set(v___x_75_, 1, v___f_74_);
v___x_76_ = l_ReaderT_instMonad___redArg(v___x_67_);
v_toApplicative_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc_ref(v_toApplicative_77_);
v_toFunctor_78_ = lean_ctor_get(v_toApplicative_77_, 0);
lean_inc_ref_n(v_toFunctor_78_, 2);
lean_dec_ref(v_toApplicative_77_);
v___x_79_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v___x_72_, v_toFunctor_64_);
v___x_80_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(v___x_80_, 0, lean_box(0));
lean_closure_set(v___x_80_, 1, v___x_79_);
lean_inc_ref(v___x_75_);
v___x_81_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_80_, v___x_75_);
v___x_82_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v___x_81_, v___x_75_);
v___x_83_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(v___x_83_, 0, lean_box(0));
lean_closure_set(v___x_83_, 1, v___x_82_);
v___f_84_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_84_, 0, v_toFunctor_78_);
v___f_85_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_85_, 0, v_toFunctor_78_);
v___x_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_86_, 0, v___f_84_);
lean_ctor_set(v___x_86_, 1, v___f_85_);
lean_inc_ref_n(v___x_86_, 2);
v___x_87_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_83_, v___x_86_);
v___x_88_ = l_Lake_EquipT_instFunctor___redArg(v___x_86_);
v_toApplicative_89_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_106_ == 0)
{
lean_object* v_unused_107_; 
v_unused_107_ = lean_ctor_get(v___x_76_, 1);
lean_dec(v_unused_107_);
v___x_91_ = v___x_76_;
v_isShared_92_ = v_isSharedCheck_106_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_toApplicative_89_);
lean_dec(v___x_76_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_106_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v_toFunctor_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___f_99_; lean_object* v___f_100_; lean_object* v___x_102_; 
v_toFunctor_93_ = lean_ctor_get(v_toApplicative_89_, 0);
lean_inc_ref_n(v_toFunctor_93_, 2);
lean_dec_ref(v_toApplicative_89_);
v___x_94_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v___x_87_, v___x_86_);
v___x_95_ = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(v___x_95_, 0, lean_box(0));
lean_closure_set(v___x_95_, 1, lean_box(0));
lean_closure_set(v___x_95_, 2, lean_box(0));
lean_closure_set(v___x_95_, 3, v___x_94_);
lean_inc_ref(v___x_88_);
v___x_96_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_95_, v___x_88_);
v___x_97_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v___x_96_, v___x_88_);
v___x_98_ = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM___boxed), 9, 2);
lean_closure_set(v___x_98_, 0, lean_box(0));
lean_closure_set(v___x_98_, 1, v___x_97_);
v___f_99_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_99_, 0, v_toFunctor_93_);
v___f_100_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_100_, 0, v_toFunctor_93_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 1, v___f_100_);
lean_ctor_set(v___x_91_, 0, v___f_99_);
v___x_102_ = v___x_91_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___f_99_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v___f_100_);
v___x_102_ = v_reuseFailAlloc_105_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = l_Lake_EquipT_instFunctor___redArg(v___x_102_);
v___x_104_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_98_, v___x_103_);
return v___x_104_;
}
}
}
}
static uint64_t _init_l_Lake_platformTrace___closed__0(void){
_start:
{
lean_object* v___x_108_; uint64_t v___x_109_; 
v___x_108_ = l_System_Platform_target;
v___x_109_ = lean_string_hash(v___x_108_);
return v___x_109_;
}
}
static uint64_t _init_l_Lake_platformTrace___closed__1(void){
_start:
{
uint64_t v___x_110_; uint64_t v___x_111_; uint64_t v___x_112_; 
v___x_110_ = lean_uint64_once(&l_Lake_platformTrace___closed__0, &l_Lake_platformTrace___closed__0_once, _init_l_Lake_platformTrace___closed__0);
v___x_111_ = l_Lake_Hash_nil;
v___x_112_ = lean_uint64_mix_hash(v___x_111_, v___x_110_);
return v___x_112_;
}
}
static lean_object* _init_l_Lake_platformTrace___closed__3(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = lean_nat_to_int(v___x_115_);
return v___x_116_;
}
}
static lean_object* _init_l_Lake_platformTrace___closed__4(void){
_start:
{
uint32_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = 0;
v___x_118_ = lean_obj_once(&l_Lake_platformTrace___closed__3, &l_Lake_platformTrace___closed__3_once, _init_l_Lake_platformTrace___closed__3);
v___x_119_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set_uint32(v___x_119_, sizeof(void*)*1, v___x_117_);
return v___x_119_;
}
}
static lean_object* _init_l_Lake_platformTrace___closed__5(void){
_start:
{
lean_object* v___x_120_; uint64_t v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_120_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_121_ = lean_uint64_once(&l_Lake_platformTrace___closed__1, &l_Lake_platformTrace___closed__1_once, _init_l_Lake_platformTrace___closed__1);
v___x_122_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_123_ = l_System_Platform_target;
v___x_124_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set(v___x_124_, 1, v___x_122_);
lean_ctor_set(v___x_124_, 2, v___x_120_);
lean_ctor_set_uint64(v___x_124_, sizeof(void*)*3, v___x_121_);
return v___x_124_;
}
}
static lean_object* _init_l_Lake_platformTrace(void){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = lean_obj_once(&l_Lake_platformTrace___closed__5, &l_Lake_platformTrace___closed__5_once, _init_l_Lake_platformTrace___closed__5);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg(lean_object* v_a_126_){
_start:
{
lean_object* v_log_128_; uint8_t v_action_129_; uint8_t v_wantsRebuild_130_; lean_object* v_trace_131_; lean_object* v_buildTime_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_143_; 
v_log_128_ = lean_ctor_get(v_a_126_, 0);
v_action_129_ = lean_ctor_get_uint8(v_a_126_, sizeof(void*)*3);
v_wantsRebuild_130_ = lean_ctor_get_uint8(v_a_126_, sizeof(void*)*3 + 1);
v_trace_131_ = lean_ctor_get(v_a_126_, 1);
v_buildTime_132_ = lean_ctor_get(v_a_126_, 2);
v_isSharedCheck_143_ = !lean_is_exclusive(v_a_126_);
if (v_isSharedCheck_143_ == 0)
{
v___x_134_ = v_a_126_;
v_isShared_135_ = v_isSharedCheck_143_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_buildTime_132_);
lean_inc(v_trace_131_);
lean_inc(v_log_128_);
lean_dec(v_a_126_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_143_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_140_; 
v___x_136_ = l_Lake_platformTrace;
v___x_137_ = lean_box(0);
v___x_138_ = l_Lake_BuildTrace_mix(v_trace_131_, v___x_136_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 1, v___x_138_);
v___x_140_ = v___x_134_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_log_128_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_142_, 2, v_buildTime_132_);
lean_ctor_set_uint8(v_reuseFailAlloc_142_, sizeof(void*)*3, v_action_129_);
lean_ctor_set_uint8(v_reuseFailAlloc_142_, sizeof(void*)*3 + 1, v_wantsRebuild_130_);
v___x_140_ = v_reuseFailAlloc_142_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_141_; 
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_137_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
return v___x_141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg___boxed(lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lake_addPlatformTrace___redArg(v_a_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace(lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_log_154_; uint8_t v_action_155_; uint8_t v_wantsRebuild_156_; lean_object* v_trace_157_; lean_object* v_buildTime_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_169_; 
v_log_154_ = lean_ctor_get(v_a_152_, 0);
v_action_155_ = lean_ctor_get_uint8(v_a_152_, sizeof(void*)*3);
v_wantsRebuild_156_ = lean_ctor_get_uint8(v_a_152_, sizeof(void*)*3 + 1);
v_trace_157_ = lean_ctor_get(v_a_152_, 1);
v_buildTime_158_ = lean_ctor_get(v_a_152_, 2);
v_isSharedCheck_169_ = !lean_is_exclusive(v_a_152_);
if (v_isSharedCheck_169_ == 0)
{
v___x_160_ = v_a_152_;
v_isShared_161_ = v_isSharedCheck_169_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_buildTime_158_);
lean_inc(v_trace_157_);
lean_inc(v_log_154_);
lean_dec(v_a_152_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_169_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_162_ = l_Lake_platformTrace;
v___x_163_ = lean_box(0);
v___x_164_ = l_Lake_BuildTrace_mix(v_trace_157_, v___x_162_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v___x_164_);
v___x_166_ = v___x_160_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_log_154_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_168_, 2, v_buildTime_158_);
lean_ctor_set_uint8(v_reuseFailAlloc_168_, sizeof(void*)*3, v_action_155_);
lean_ctor_set_uint8(v_reuseFailAlloc_168_, sizeof(void*)*3 + 1, v_wantsRebuild_156_);
v___x_166_ = v_reuseFailAlloc_168_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_167_; 
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_163_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
return v___x_167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___boxed(lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lake_addPlatformTrace(v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
lean_dec_ref(v_a_174_);
lean_dec(v_a_173_);
lean_dec(v_a_172_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg(lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_log_181_; uint8_t v_action_182_; uint8_t v_wantsRebuild_183_; lean_object* v_trace_184_; lean_object* v_buildTime_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_196_; 
v_log_181_ = lean_ctor_get(v_a_179_, 0);
v_action_182_ = lean_ctor_get_uint8(v_a_179_, sizeof(void*)*3);
v_wantsRebuild_183_ = lean_ctor_get_uint8(v_a_179_, sizeof(void*)*3 + 1);
v_trace_184_ = lean_ctor_get(v_a_179_, 1);
v_buildTime_185_ = lean_ctor_get(v_a_179_, 2);
v_isSharedCheck_196_ = !lean_is_exclusive(v_a_179_);
if (v_isSharedCheck_196_ == 0)
{
v___x_187_ = v_a_179_;
v_isShared_188_ = v_isSharedCheck_196_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_buildTime_185_);
lean_inc(v_trace_184_);
lean_inc(v_log_181_);
lean_dec(v_a_179_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_196_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v_leanTrace_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v_leanTrace_189_ = lean_ctor_get(v_a_178_, 2);
v___x_190_ = lean_box(0);
lean_inc_ref(v_leanTrace_189_);
v___x_191_ = l_Lake_BuildTrace_mix(v_trace_184_, v_leanTrace_189_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 1, v___x_191_);
v___x_193_ = v___x_187_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_log_181_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_195_, 2, v_buildTime_185_);
lean_ctor_set_uint8(v_reuseFailAlloc_195_, sizeof(void*)*3, v_action_182_);
lean_ctor_set_uint8(v_reuseFailAlloc_195_, sizeof(void*)*3 + 1, v_wantsRebuild_183_);
v___x_193_ = v_reuseFailAlloc_195_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_194_; 
v___x_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_190_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
return v___x_194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg___boxed(lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lake_addLeanTrace___redArg(v_a_197_, v_a_198_);
lean_dec_ref(v_a_197_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace(lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_log_208_; uint8_t v_action_209_; uint8_t v_wantsRebuild_210_; lean_object* v_trace_211_; lean_object* v_buildTime_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_223_; 
v_log_208_ = lean_ctor_get(v_a_206_, 0);
v_action_209_ = lean_ctor_get_uint8(v_a_206_, sizeof(void*)*3);
v_wantsRebuild_210_ = lean_ctor_get_uint8(v_a_206_, sizeof(void*)*3 + 1);
v_trace_211_ = lean_ctor_get(v_a_206_, 1);
v_buildTime_212_ = lean_ctor_get(v_a_206_, 2);
v_isSharedCheck_223_ = !lean_is_exclusive(v_a_206_);
if (v_isSharedCheck_223_ == 0)
{
v___x_214_ = v_a_206_;
v_isShared_215_ = v_isSharedCheck_223_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_buildTime_212_);
lean_inc(v_trace_211_);
lean_inc(v_log_208_);
lean_dec(v_a_206_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_223_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v_leanTrace_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_220_; 
v_leanTrace_216_ = lean_ctor_get(v_a_205_, 2);
v___x_217_ = lean_box(0);
lean_inc_ref(v_leanTrace_216_);
v___x_218_ = l_Lake_BuildTrace_mix(v_trace_211_, v_leanTrace_216_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 1, v___x_218_);
v___x_220_ = v___x_214_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_log_208_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_222_, 2, v_buildTime_212_);
lean_ctor_set_uint8(v_reuseFailAlloc_222_, sizeof(void*)*3, v_action_209_);
lean_ctor_set_uint8(v_reuseFailAlloc_222_, sizeof(void*)*3 + 1, v_wantsRebuild_210_);
v___x_220_ = v_reuseFailAlloc_222_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
lean_object* v___x_221_; 
v___x_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_217_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
return v___x_221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___boxed(lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lake_addLeanTrace(v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
lean_dec(v_a_226_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg(lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_a_235_, lean_object* v_caption_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_log_239_; uint8_t v_action_240_; uint8_t v_wantsRebuild_241_; lean_object* v_trace_242_; lean_object* v_buildTime_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_262_; 
v_log_239_ = lean_ctor_get(v_a_237_, 0);
v_action_240_ = lean_ctor_get_uint8(v_a_237_, sizeof(void*)*3);
v_wantsRebuild_241_ = lean_ctor_get_uint8(v_a_237_, sizeof(void*)*3 + 1);
v_trace_242_ = lean_ctor_get(v_a_237_, 1);
v_buildTime_243_ = lean_ctor_get(v_a_237_, 2);
v_isSharedCheck_262_ = !lean_is_exclusive(v_a_237_);
if (v_isSharedCheck_262_ == 0)
{
v___x_245_ = v_a_237_;
v_isShared_246_ = v_isSharedCheck_262_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_buildTime_243_);
lean_inc(v_trace_242_);
lean_inc(v_log_239_);
lean_dec(v_a_237_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_262_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; uint64_t v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
lean_inc(v_a_235_);
v___x_247_ = lean_apply_1(v_inst_234_, v_a_235_);
v___x_248_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_249_ = ((lean_object*)(l_Lake_addPureTrace___redArg___closed__0));
v___x_250_ = lean_string_append(v_caption_236_, v___x_249_);
v___x_251_ = lean_apply_1(v_inst_233_, v_a_235_);
v___x_252_ = lean_string_append(v___x_250_, v___x_251_);
lean_dec_ref(v___x_251_);
v___x_253_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_254_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set(v___x_254_, 1, v___x_248_);
lean_ctor_set(v___x_254_, 2, v___x_253_);
v___x_255_ = lean_unbox_uint64(v___x_247_);
lean_dec_ref(v___x_247_);
lean_ctor_set_uint64(v___x_254_, sizeof(void*)*3, v___x_255_);
v___x_256_ = lean_box(0);
v___x_257_ = l_Lake_BuildTrace_mix(v_trace_242_, v___x_254_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 1, v___x_257_);
v___x_259_ = v___x_245_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_log_239_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_buildTime_243_);
lean_ctor_set_uint8(v_reuseFailAlloc_261_, sizeof(void*)*3, v_action_240_);
lean_ctor_set_uint8(v_reuseFailAlloc_261_, sizeof(void*)*3 + 1, v_wantsRebuild_241_);
v___x_259_ = v_reuseFailAlloc_261_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; 
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_256_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
return v___x_260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg___boxed(lean_object* v_inst_263_, lean_object* v_inst_264_, lean_object* v_a_265_, lean_object* v_caption_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lake_addPureTrace___redArg(v_inst_263_, v_inst_264_, v_a_265_, v_caption_266_, v_a_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace(lean_object* v_00_u03b1_270_, lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_a_273_, lean_object* v_caption_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
lean_object* v_log_282_; uint8_t v_action_283_; uint8_t v_wantsRebuild_284_; lean_object* v_trace_285_; lean_object* v_buildTime_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_305_; 
v_log_282_ = lean_ctor_get(v_a_280_, 0);
v_action_283_ = lean_ctor_get_uint8(v_a_280_, sizeof(void*)*3);
v_wantsRebuild_284_ = lean_ctor_get_uint8(v_a_280_, sizeof(void*)*3 + 1);
v_trace_285_ = lean_ctor_get(v_a_280_, 1);
v_buildTime_286_ = lean_ctor_get(v_a_280_, 2);
v_isSharedCheck_305_ = !lean_is_exclusive(v_a_280_);
if (v_isSharedCheck_305_ == 0)
{
v___x_288_ = v_a_280_;
v_isShared_289_ = v_isSharedCheck_305_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_buildTime_286_);
lean_inc(v_trace_285_);
lean_inc(v_log_282_);
lean_dec(v_a_280_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_305_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; uint64_t v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_302_; 
lean_inc(v_a_273_);
v___x_290_ = lean_apply_1(v_inst_272_, v_a_273_);
v___x_291_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_292_ = ((lean_object*)(l_Lake_addPureTrace___redArg___closed__0));
v___x_293_ = lean_string_append(v_caption_274_, v___x_292_);
v___x_294_ = lean_apply_1(v_inst_271_, v_a_273_);
v___x_295_ = lean_string_append(v___x_293_, v___x_294_);
lean_dec_ref(v___x_294_);
v___x_296_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_297_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_297_, 0, v___x_295_);
lean_ctor_set(v___x_297_, 1, v___x_291_);
lean_ctor_set(v___x_297_, 2, v___x_296_);
v___x_298_ = lean_unbox_uint64(v___x_290_);
lean_dec_ref(v___x_290_);
lean_ctor_set_uint64(v___x_297_, sizeof(void*)*3, v___x_298_);
v___x_299_ = lean_box(0);
v___x_300_ = l_Lake_BuildTrace_mix(v_trace_285_, v___x_297_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 1, v___x_300_);
v___x_302_ = v___x_288_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_log_282_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_304_, 2, v_buildTime_286_);
lean_ctor_set_uint8(v_reuseFailAlloc_304_, sizeof(void*)*3, v_action_283_);
lean_ctor_set_uint8(v_reuseFailAlloc_304_, sizeof(void*)*3 + 1, v_wantsRebuild_284_);
v___x_302_ = v_reuseFailAlloc_304_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_303_; 
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_299_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
return v___x_303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace___boxed(lean_object* v_00_u03b1_306_, lean_object* v_inst_307_, lean_object* v_inst_308_, lean_object* v_a_309_, lean_object* v_caption_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lake_addPureTrace(v_00_u03b1_306_, v_inst_307_, v_inst_308_, v_a_309_, v_caption_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
lean_dec_ref(v_a_315_);
lean_dec(v_a_314_);
lean_dec(v_a_313_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(lean_object* v_x_321_){
_start:
{
if (lean_obj_tag(v_x_321_) == 0)
{
lean_object* v___x_322_; 
v___x_322_ = lean_box(0);
return v___x_322_;
}
else
{
lean_object* v_val_323_; 
v_val_323_ = lean_ctor_get(v_x_321_, 0);
lean_inc(v_val_323_);
return v_val_323_;
}
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1___boxed(lean_object* v_x_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(v_x_324_);
lean_dec(v_x_324_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0(lean_object* v_x_326_){
_start:
{
lean_object* v_fst_327_; lean_object* v_snd_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_fst_327_ = lean_ctor_get(v_x_326_, 0);
lean_inc(v_fst_327_);
v_snd_328_ = lean_ctor_get(v_x_326_, 1);
lean_inc(v_snd_328_);
lean_dec_ref(v_x_326_);
v___x_329_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_329_, 0, v_fst_327_);
v___x_330_ = lean_unsigned_to_nat(2u);
v___x_331_ = lean_mk_empty_array_with_capacity(v___x_330_);
v___x_332_ = lean_array_push(v___x_331_, v___x_329_);
v___x_333_ = lean_array_push(v___x_332_, v_snd_328_);
v___x_334_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(size_t v_sz_335_, size_t v_i_336_, lean_object* v_bs_337_){
_start:
{
uint8_t v___x_338_; 
v___x_338_ = lean_usize_dec_lt(v_i_336_, v_sz_335_);
if (v___x_338_ == 0)
{
return v_bs_337_;
}
else
{
lean_object* v_v_339_; lean_object* v___x_340_; lean_object* v_bs_x27_341_; lean_object* v___x_342_; size_t v___x_343_; size_t v___x_344_; lean_object* v___x_345_; 
v_v_339_ = lean_array_uget(v_bs_337_, v_i_336_);
v___x_340_ = lean_unsigned_to_nat(0u);
v_bs_x27_341_ = lean_array_uset(v_bs_337_, v_i_336_, v___x_340_);
v___x_342_ = l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0(v_v_339_);
v___x_343_ = ((size_t)1ULL);
v___x_344_ = lean_usize_add(v_i_336_, v___x_343_);
v___x_345_ = lean_array_uset(v_bs_x27_341_, v_i_336_, v___x_342_);
v_i_336_ = v___x_344_;
v_bs_337_ = v___x_345_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1___boxed(lean_object* v_sz_347_, lean_object* v_i_348_, lean_object* v_bs_349_){
_start:
{
size_t v_sz_boxed_350_; size_t v_i_boxed_351_; lean_object* v_res_352_; 
v_sz_boxed_350_ = lean_unbox_usize(v_sz_347_);
lean_dec(v_sz_347_);
v_i_boxed_351_ = lean_unbox_usize(v_i_348_);
lean_dec(v_i_348_);
v_res_352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(v_sz_boxed_350_, v_i_boxed_351_, v_bs_349_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(lean_object* v_a_353_){
_start:
{
size_t v_sz_354_; size_t v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v_sz_354_ = lean_array_size(v_a_353_);
v___x_355_ = ((size_t)0ULL);
v___x_356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(v_sz_354_, v___x_355_, v_a_353_);
v___x_357_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(size_t v_sz_358_, size_t v_i_359_, lean_object* v_bs_360_){
_start:
{
uint8_t v___x_361_; 
v___x_361_ = lean_usize_dec_lt(v_i_359_, v_sz_358_);
if (v___x_361_ == 0)
{
return v_bs_360_;
}
else
{
lean_object* v_v_362_; lean_object* v___x_363_; lean_object* v_bs_x27_364_; lean_object* v___x_365_; size_t v___x_366_; size_t v___x_367_; lean_object* v___x_368_; 
v_v_362_ = lean_array_uget(v_bs_360_, v_i_359_);
v___x_363_ = lean_unsigned_to_nat(0u);
v_bs_x27_364_ = lean_array_uset(v_bs_360_, v_i_359_, v___x_363_);
v___x_365_ = l_Lake_instToJsonLogEntry_toJson(v_v_362_);
lean_dec(v_v_362_);
v___x_366_ = ((size_t)1ULL);
v___x_367_ = lean_usize_add(v_i_359_, v___x_366_);
v___x_368_ = lean_array_uset(v_bs_x27_364_, v_i_359_, v___x_365_);
v_i_359_ = v___x_367_;
v_bs_360_ = v___x_368_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4___boxed(lean_object* v_sz_370_, lean_object* v_i_371_, lean_object* v_bs_372_){
_start:
{
size_t v_sz_boxed_373_; size_t v_i_boxed_374_; lean_object* v_res_375_; 
v_sz_boxed_373_ = lean_unbox_usize(v_sz_370_);
lean_dec(v_sz_370_);
v_i_boxed_374_ = lean_unbox_usize(v_i_371_);
lean_dec(v_i_371_);
v_res_375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(v_sz_boxed_373_, v_i_boxed_374_, v_bs_372_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2(lean_object* v_a_376_){
_start:
{
size_t v_sz_377_; size_t v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_sz_377_ = lean_array_size(v_a_376_);
v___x_378_ = ((size_t)0ULL);
v___x_379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(v_sz_377_, v___x_378_, v_a_376_);
v___x_380_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
return v___x_380_;
}
}
static lean_object* _init_l_Lake_BuildMetadata_toJson___closed__2(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_384_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__1));
v___x_385_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__0));
v___x_386_ = lean_box(1);
v___x_387_ = l_Lake_JsonObject_insertJson(v___x_386_, v___x_385_, v___x_384_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_toJson(lean_object* v_self_393_){
_start:
{
uint64_t v_depHash_394_; lean_object* v_inputs_395_; lean_object* v_outputs_x3f_396_; lean_object* v_log_397_; uint8_t v_synthetic_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v_depHash_394_ = lean_ctor_get_uint64(v_self_393_, sizeof(void*)*3);
v_inputs_395_ = lean_ctor_get(v_self_393_, 0);
lean_inc_ref(v_inputs_395_);
v_outputs_x3f_396_ = lean_ctor_get(v_self_393_, 1);
lean_inc(v_outputs_x3f_396_);
v_log_397_ = lean_ctor_get(v_self_393_, 2);
lean_inc_ref(v_log_397_);
v_synthetic_398_ = lean_ctor_get_uint8(v_self_393_, sizeof(void*)*3 + 8);
lean_dec_ref(v_self_393_);
v___x_399_ = lean_obj_once(&l_Lake_BuildMetadata_toJson___closed__2, &l_Lake_BuildMetadata_toJson___closed__2_once, _init_l_Lake_BuildMetadata_toJson___closed__2);
v___x_400_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__3));
v___x_401_ = l_Lake_Hash_hex(v_depHash_394_);
v___x_402_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
v___x_403_ = l_Lake_JsonObject_insertJson(v___x_399_, v___x_400_, v___x_402_);
v___x_404_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__4));
v___x_405_ = l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(v_inputs_395_);
v___x_406_ = l_Lake_JsonObject_insertJson(v___x_403_, v___x_404_, v___x_405_);
v___x_407_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__5));
v___x_408_ = l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(v_outputs_x3f_396_);
lean_dec(v_outputs_x3f_396_);
v___x_409_ = l_Lake_JsonObject_insertJson(v___x_406_, v___x_407_, v___x_408_);
v___x_410_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__6));
v___x_411_ = l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2(v_log_397_);
v___x_412_ = l_Lake_JsonObject_insertJson(v___x_409_, v___x_410_, v___x_411_);
v___x_413_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__7));
v___x_414_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_414_, 0, v_synthetic_398_);
v___x_415_ = l_Lake_JsonObject_insertJson(v___x_412_, v___x_413_, v___x_414_);
v___x_416_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub(uint64_t v_hash_421_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; lean_object* v___x_425_; 
v___x_422_ = ((lean_object*)(l_Lake_BuildMetadata_ofStub___closed__0));
v___x_423_ = lean_box(0);
v___x_424_ = 0;
v___x_425_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_425_, 0, v___x_422_);
lean_ctor_set(v___x_425_, 1, v___x_423_);
lean_ctor_set(v___x_425_, 2, v___x_422_);
lean_ctor_set_uint64(v___x_425_, sizeof(void*)*3, v_hash_421_);
lean_ctor_set_uint8(v___x_425_, sizeof(void*)*3 + 8, v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub___boxed(lean_object* v_hash_426_){
_start:
{
uint64_t v_hash_boxed_427_; lean_object* v_res_428_; 
v_hash_boxed_427_ = lean_unbox_uint64(v_hash_426_);
lean_dec_ref(v_hash_426_);
v_res_428_ = l_Lake_BuildMetadata_ofStub(v_hash_boxed_427_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(lean_object* v_x_431_){
_start:
{
if (lean_obj_tag(v_x_431_) == 0)
{
lean_object* v___x_432_; 
v___x_432_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0));
return v___x_432_;
}
else
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Json_getBool_x3f(v_x_431_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_450_; 
v_a_442_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_450_ == 0)
{
v___x_444_ = v___x_433_;
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_433_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_446_, 0, v_a_442_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_446_);
v___x_448_ = v___x_444_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___boxed(lean_object* v_x_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(v_x_451_);
lean_dec(v_x_451_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3(lean_object* v_x_455_){
_start:
{
if (lean_obj_tag(v_x_455_) == 0)
{
lean_object* v___x_456_; 
v___x_456_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0));
return v___x_456_;
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_457_, 0, v_x_455_);
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2(lean_object* v_x_461_){
_start:
{
if (lean_obj_tag(v_x_461_) == 0)
{
lean_object* v___x_462_; 
v___x_462_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0));
return v___x_462_;
}
else
{
lean_object* v___x_463_; lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_472_; 
v___x_463_ = l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3(v_x_461_);
v_a_464_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_472_ == 0)
{
v___x_466_ = v___x_463_;
v_isShared_467_ = v_isSharedCheck_472_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_463_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_472_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_468_, 0, v_a_464_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___x_468_);
v___x_470_ = v___x_466_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(size_t v_sz_473_, size_t v_i_474_, lean_object* v_bs_475_){
_start:
{
uint8_t v___x_476_; 
v___x_476_ = lean_usize_dec_lt(v_i_474_, v_sz_473_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; 
v___x_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_477_, 0, v_bs_475_);
return v___x_477_;
}
else
{
lean_object* v_v_478_; lean_object* v___x_479_; 
v_v_478_ = lean_array_uget_borrowed(v_bs_475_, v_i_474_);
lean_inc(v_v_478_);
v___x_479_ = l_Lake_instFromJsonLogEntry_fromJson(v_v_478_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec_ref(v_bs_475_);
v_a_480_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_479_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_489_; lean_object* v_bs_x27_490_; size_t v___x_491_; size_t v___x_492_; lean_object* v___x_493_; 
v_a_488_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_488_);
lean_dec_ref(v___x_479_);
v___x_489_ = lean_unsigned_to_nat(0u);
v_bs_x27_490_ = lean_array_uset(v_bs_475_, v_i_474_, v___x_489_);
v___x_491_ = ((size_t)1ULL);
v___x_492_ = lean_usize_add(v_i_474_, v___x_491_);
v___x_493_ = lean_array_uset(v_bs_x27_490_, v_i_474_, v_a_488_);
v_i_474_ = v___x_492_;
v_bs_475_ = v___x_493_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_495_, lean_object* v_i_496_, lean_object* v_bs_497_){
_start:
{
size_t v_sz_boxed_498_; size_t v_i_boxed_499_; lean_object* v_res_500_; 
v_sz_boxed_498_ = lean_unbox_usize(v_sz_495_);
lean_dec(v_sz_495_);
v_i_boxed_499_ = lean_unbox_usize(v_i_496_);
lean_dec(v_i_496_);
v_res_500_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(v_sz_boxed_498_, v_i_boxed_499_, v_bs_497_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(lean_object* v_x_503_){
_start:
{
if (lean_obj_tag(v_x_503_) == 4)
{
lean_object* v_elems_504_; size_t v_sz_505_; size_t v___x_506_; lean_object* v___x_507_; 
v_elems_504_ = lean_ctor_get(v_x_503_, 0);
lean_inc_ref(v_elems_504_);
lean_dec_ref(v_x_503_);
v_sz_505_ = lean_array_size(v_elems_504_);
v___x_506_ = ((size_t)0ULL);
v___x_507_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(v_sz_505_, v___x_506_, v_elems_504_);
return v___x_507_;
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_508_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0));
v___x_509_ = lean_unsigned_to_nat(80u);
v___x_510_ = l_Lean_Json_pretty(v_x_503_, v___x_509_);
v___x_511_ = lean_string_append(v___x_508_, v___x_510_);
lean_dec_ref(v___x_510_);
v___x_512_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1));
v___x_513_ = lean_string_append(v___x_511_, v___x_512_);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1(lean_object* v_x_517_){
_start:
{
if (lean_obj_tag(v_x_517_) == 0)
{
lean_object* v___x_518_; 
v___x_518_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0));
return v___x_518_;
}
else
{
lean_object* v___x_519_; 
v___x_519_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(v_x_517_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_519_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_519_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_536_; 
v_a_528_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_536_ == 0)
{
v___x_530_ = v___x_519_;
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_519_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_532_, 0, v_a_528_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_532_);
v___x_534_ = v___x_530_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7(lean_object* v_x_538_){
_start:
{
lean_object* v_j_540_; 
if (lean_obj_tag(v_x_538_) == 4)
{
lean_object* v_elems_548_; lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v_elems_548_ = lean_ctor_get(v_x_538_, 0);
v___x_549_ = lean_array_get_size(v_elems_548_);
v___x_550_ = lean_unsigned_to_nat(2u);
v___x_551_ = lean_nat_dec_eq(v___x_549_, v___x_550_);
if (v___x_551_ == 0)
{
v_j_540_ = v_x_538_;
goto v___jp_539_;
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
lean_inc_ref(v_elems_548_);
lean_dec_ref(v_x_538_);
v___x_552_ = lean_unsigned_to_nat(0u);
v___x_553_ = lean_array_fget_borrowed(v_elems_548_, v___x_552_);
lean_inc(v___x_553_);
v___x_554_ = l_Lean_Json_getStr_x3f(v___x_553_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_dec_ref(v_elems_548_);
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_573_; 
v_a_563_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_573_ == 0)
{
v___x_565_ = v___x_554_;
v_isShared_566_ = v_isSharedCheck_573_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_554_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_573_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_567_ = lean_unsigned_to_nat(1u);
v___x_568_ = lean_array_fget(v_elems_548_, v___x_567_);
lean_dec_ref(v_elems_548_);
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v_a_563_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_569_);
v___x_571_ = v___x_565_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
else
{
v_j_540_ = v_x_538_;
goto v___jp_539_;
}
v___jp_539_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_541_ = ((lean_object*)(l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0));
v___x_542_ = lean_unsigned_to_nat(80u);
v___x_543_ = l_Lean_Json_pretty(v_j_540_, v___x_542_);
v___x_544_ = lean_string_append(v___x_541_, v___x_543_);
lean_dec_ref(v___x_543_);
v___x_545_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1));
v___x_546_ = lean_string_append(v___x_544_, v___x_545_);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(size_t v_sz_574_, size_t v_i_575_, lean_object* v_bs_576_){
_start:
{
uint8_t v___x_577_; 
v___x_577_ = lean_usize_dec_lt(v_i_575_, v_sz_574_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
v___x_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_578_, 0, v_bs_576_);
return v___x_578_;
}
else
{
lean_object* v_v_579_; lean_object* v___x_580_; 
v_v_579_ = lean_array_uget_borrowed(v_bs_576_, v_i_575_);
lean_inc(v_v_579_);
v___x_580_ = l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7(v_v_579_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec_ref(v_bs_576_);
v_a_581_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_580_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_580_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_590_; lean_object* v_bs_x27_591_; size_t v___x_592_; size_t v___x_593_; lean_object* v___x_594_; 
v_a_589_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_589_);
lean_dec_ref(v___x_580_);
v___x_590_ = lean_unsigned_to_nat(0u);
v_bs_x27_591_ = lean_array_uset(v_bs_576_, v_i_575_, v___x_590_);
v___x_592_ = ((size_t)1ULL);
v___x_593_ = lean_usize_add(v_i_575_, v___x_592_);
v___x_594_ = lean_array_uset(v_bs_x27_591_, v_i_575_, v_a_589_);
v_i_575_ = v___x_593_;
v_bs_576_ = v___x_594_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8___boxed(lean_object* v_sz_596_, lean_object* v_i_597_, lean_object* v_bs_598_){
_start:
{
size_t v_sz_boxed_599_; size_t v_i_boxed_600_; lean_object* v_res_601_; 
v_sz_boxed_599_ = lean_unbox_usize(v_sz_596_);
lean_dec(v_sz_596_);
v_i_boxed_600_ = lean_unbox_usize(v_i_597_);
lean_dec(v_i_597_);
v_res_601_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(v_sz_boxed_599_, v_i_boxed_600_, v_bs_598_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5(lean_object* v_x_602_){
_start:
{
if (lean_obj_tag(v_x_602_) == 4)
{
lean_object* v_elems_603_; size_t v_sz_604_; size_t v___x_605_; lean_object* v___x_606_; 
v_elems_603_ = lean_ctor_get(v_x_602_, 0);
lean_inc_ref(v_elems_603_);
lean_dec_ref(v_x_602_);
v_sz_604_ = lean_array_size(v_elems_603_);
v___x_605_ = ((size_t)0ULL);
v___x_606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(v_sz_604_, v___x_605_, v_elems_603_);
return v___x_606_;
}
else
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_607_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0));
v___x_608_ = lean_unsigned_to_nat(80u);
v___x_609_ = l_Lean_Json_pretty(v_x_602_, v___x_608_);
v___x_610_ = lean_string_append(v___x_607_, v___x_609_);
lean_dec_ref(v___x_609_);
v___x_611_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1));
v___x_612_ = lean_string_append(v___x_610_, v___x_611_);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3(lean_object* v_x_616_){
_start:
{
if (lean_obj_tag(v_x_616_) == 0)
{
lean_object* v___x_617_; 
v___x_617_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0));
return v___x_617_;
}
else
{
lean_object* v___x_618_; 
v___x_618_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5(v_x_616_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_618_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_618_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_635_; 
v_a_627_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_635_ == 0)
{
v___x_629_ = v___x_618_;
v_isShared_630_ = v_isSharedCheck_635_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_618_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_635_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_631_, 0, v_a_627_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v___x_631_);
v___x_633_ = v___x_629_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f(lean_object* v_obj_651_){
_start:
{
lean_object* v___y_653_; uint64_t v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; uint8_t v_a_657_; lean_object* v___y_661_; uint64_t v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_667_; uint64_t v___y_668_; lean_object* v___y_669_; lean_object* v_a_670_; lean_object* v___y_697_; uint64_t v___y_698_; lean_object* v___y_699_; uint64_t v___y_702_; lean_object* v___y_703_; lean_object* v_a_704_; uint64_t v___y_730_; lean_object* v___y_731_; uint64_t v___y_734_; lean_object* v_a_735_; uint64_t v___y_761_; uint64_t v_depHash_764_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__0));
v___x_790_ = l_Lake_JsonObject_getJson_x3f(v_obj_651_, v___x_789_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__3));
v___x_792_ = l_Lake_JsonObject_getJson_x3f(v_obj_651_, v___x_791_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v___x_793_; 
v___x_793_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7));
return v___x_793_;
}
else
{
lean_object* v_val_794_; lean_object* v___x_795_; 
v_val_794_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_val_794_);
lean_dec_ref(v___x_792_);
v___x_795_ = l_Lean_Json_getStr_x3f(v_val_794_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_805_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_805_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_805_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_805_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_800_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8));
v___x_801_ = lean_string_append(v___x_800_, v_a_796_);
lean_dec(v_a_796_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_801_);
v___x_803_ = v___x_798_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
else
{
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
v_a_806_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_795_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_795_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set_tag(v___x_808_, 0);
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_815_; 
v_a_814_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_814_);
lean_dec_ref(v___x_795_);
v___x_815_ = l_Lake_Hash_ofDecimal_x3f(v_a_814_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v___x_816_; 
v___x_816_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__10));
return v___x_816_;
}
else
{
lean_object* v_val_817_; uint64_t v___x_818_; 
v_val_817_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_val_817_);
lean_dec_ref(v___x_815_);
v___x_818_ = lean_unbox_uint64(v_val_817_);
lean_dec(v_val_817_);
v_depHash_764_ = v___x_818_;
goto v___jp_763_;
}
}
}
}
}
else
{
lean_object* v___x_819_; lean_object* v___x_820_; 
lean_dec_ref(v___x_790_);
v___x_819_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__3));
v___x_820_ = l_Lake_JsonObject_getJson_x3f(v_obj_651_, v___x_819_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v___x_821_; 
v___x_821_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7));
return v___x_821_;
}
else
{
lean_object* v_val_822_; lean_object* v___x_823_; 
v_val_822_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_val_822_);
lean_dec_ref(v___x_820_);
v___x_823_ = l_Lake_Hash_fromJson_x3f(v_val_822_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_833_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_833_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_833_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_833_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_831_; 
v___x_828_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8));
v___x_829_ = lean_string_append(v___x_828_, v_a_824_);
lean_dec(v_a_824_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_829_);
v___x_831_ = v___x_826_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
else
{
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
v_a_834_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_823_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_823_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set_tag(v___x_836_, 0);
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
else
{
lean_object* v_a_842_; uint64_t v___x_843_; 
v_a_842_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_842_);
lean_dec_ref(v___x_823_);
v___x_843_ = lean_unbox_uint64(v_a_842_);
lean_dec(v_a_842_);
v_depHash_764_ = v___x_843_;
goto v___jp_763_;
}
}
}
}
v___jp_652_:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_658_, 0, v___y_655_);
lean_ctor_set(v___x_658_, 1, v___y_653_);
lean_ctor_set(v___x_658_, 2, v___y_656_);
lean_ctor_set_uint64(v___x_658_, sizeof(void*)*3, v___y_654_);
lean_ctor_set_uint8(v___x_658_, sizeof(void*)*3 + 8, v_a_657_);
v___x_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
return v___x_659_;
}
v___jp_660_:
{
uint8_t v___x_665_; 
v___x_665_ = 0;
v___y_653_ = v___y_661_;
v___y_654_ = v___y_662_;
v___y_655_ = v___y_663_;
v___y_656_ = v___y_664_;
v_a_657_ = v___x_665_;
goto v___jp_652_;
}
v___jp_666_:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__7));
v___x_672_ = l_Lake_JsonObject_getJson_x3f(v_obj_651_, v___x_671_);
if (lean_obj_tag(v___x_672_) == 0)
{
v___y_661_ = v___y_667_;
v___y_662_ = v___y_668_;
v___y_663_ = v___y_669_;
v___y_664_ = v_a_670_;
goto v___jp_660_;
}
else
{
lean_object* v_val_673_; lean_object* v___x_674_; 
v_val_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_val_673_);
lean_dec_ref(v___x_672_);
v___x_674_ = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(v_val_673_);
lean_dec(v_val_673_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_684_; 
lean_dec_ref(v_a_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_667_);
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_684_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_684_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_684_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_682_; 
v___x_679_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__0));
v___x_680_ = lean_string_append(v___x_679_, v_a_675_);
lean_dec(v_a_675_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_680_);
v___x_682_ = v___x_677_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
else
{
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_692_; 
lean_dec_ref(v_a_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_667_);
v_a_685_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_692_ == 0)
{
v___x_687_ = v___x_674_;
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_674_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_690_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set_tag(v___x_687_, 0);
v___x_690_ = v___x_687_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_685_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
else
{
lean_object* v_a_693_; 
v_a_693_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_693_);
lean_dec_ref(v___x_674_);
if (lean_obj_tag(v_a_693_) == 0)
{
v___y_661_ = v___y_667_;
v___y_662_ = v___y_668_;
v___y_663_ = v___y_669_;
v___y_664_ = v_a_670_;
goto v___jp_660_;
}
else
{
lean_object* v_val_694_; uint8_t v___x_695_; 
v_val_694_ = lean_ctor_get(v_a_693_, 0);
lean_inc(v_val_694_);
lean_dec_ref(v_a_693_);
v___x_695_ = lean_unbox(v_val_694_);
lean_dec(v_val_694_);
v___y_653_ = v___y_667_;
v___y_654_ = v___y_668_;
v___y_655_ = v___y_669_;
v___y_656_ = v_a_670_;
v_a_657_ = v___x_695_;
goto v___jp_652_;
}
}
}
}
}
v___jp_696_:
{
lean_object* v___x_700_; 
v___x_700_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___y_667_ = v___y_697_;
v___y_668_ = v___y_698_;
v___y_669_ = v___y_699_;
v_a_670_ = v___x_700_;
goto v___jp_666_;
}
v___jp_701_:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__6));
v___x_706_ = l_Lake_JsonObject_getJson_x3f(v_obj_651_, v___x_705_);
if (lean_obj_tag(v___x_706_) == 0)
{
v___y_697_ = v_a_704_;
v___y_698_ = v___y_702_;
v___y_699_ = v___y_703_;
goto v___jp_696_;
}
else
{
lean_object* v_val_707_; lean_object* v___x_708_; 
v_val_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_val_707_);
lean_dec_ref(v___x_706_);
v___x_708_ = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1(v_val_707_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_718_; 
lean_dec(v_a_704_);
lean_dec_ref(v___y_703_);
v_a_709_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_718_ == 0)
{
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_718_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_718_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_713_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2));
v___x_714_ = lean_string_append(v___x_713_, v_a_709_);
lean_dec(v_a_709_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___x_714_);
v___x_716_ = v___x_711_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
else
{
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec(v_a_704_);
lean_dec_ref(v___y_703_);
v_a_719_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_708_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_708_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
lean_ctor_set_tag(v___x_721_, 0);
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
else
{
lean_object* v_a_727_; 
v_a_727_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_727_);
lean_dec_ref(v___x_708_);
if (lean_obj_tag(v_a_727_) == 0)
{
v___y_697_ = v_a_704_;
v___y_698_ = v___y_702_;
v___y_699_ = v___y_703_;
goto v___jp_696_;
}
else
{
lean_object* v_val_728_; 
v_val_728_ = lean_ctor_get(v_a_727_, 0);
lean_inc(v_val_728_);
lean_dec_ref(v_a_727_);
v___y_667_ = v_a_704_;
v___y_668_ = v___y_702_;
v___y_669_ = v___y_703_;
v_a_670_ = v_val_728_;
goto v___jp_666_;
}
}
}
}
}
v___jp_729_:
{
lean_object* v___x_732_; 
v___x_732_ = lean_box(0);
v___y_702_ = v___y_730_;
v___y_703_ = v___y_731_;
v_a_704_ = v___x_732_;
goto v___jp_701_;
}
v___jp_733_:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__5));
v___x_737_ = l_Lake_JsonObject_getJson_x3f(v_obj_651_, v___x_736_);
if (lean_obj_tag(v___x_737_) == 0)
{
v___y_730_ = v___y_734_;
v___y_731_ = v_a_735_;
goto v___jp_729_;
}
else
{
lean_object* v_val_738_; lean_object* v___x_739_; 
v_val_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_val_738_);
lean_dec_ref(v___x_737_);
v___x_739_ = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2(v_val_738_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_749_; 
lean_dec_ref(v_a_735_);
v_a_740_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_749_ == 0)
{
v___x_742_ = v___x_739_;
v_isShared_743_ = v_isSharedCheck_749_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_749_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_744_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3));
v___x_745_ = lean_string_append(v___x_744_, v_a_740_);
lean_dec(v_a_740_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_745_);
v___x_747_ = v___x_742_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
else
{
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_dec_ref(v_a_735_);
v_a_750_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_739_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_739_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
lean_ctor_set_tag(v___x_752_, 0);
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
else
{
lean_object* v_a_758_; 
v_a_758_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_758_);
lean_dec_ref(v___x_739_);
if (lean_obj_tag(v_a_758_) == 0)
{
v___y_730_ = v___y_734_;
v___y_731_ = v_a_735_;
goto v___jp_729_;
}
else
{
lean_object* v_val_759_; 
v_val_759_ = lean_ctor_get(v_a_758_, 0);
lean_inc(v_val_759_);
lean_dec_ref(v_a_758_);
v___y_702_ = v___y_734_;
v___y_703_ = v_a_735_;
v_a_704_ = v_val_759_;
goto v___jp_701_;
}
}
}
}
}
v___jp_760_:
{
lean_object* v___x_762_; 
v___x_762_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4));
v___y_734_ = v___y_761_;
v_a_735_ = v___x_762_;
goto v___jp_733_;
}
v___jp_763_:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__4));
v___x_766_ = l_Lake_JsonObject_getJson_x3f(v_obj_651_, v___x_765_);
if (lean_obj_tag(v___x_766_) == 0)
{
v___y_761_ = v_depHash_764_;
goto v___jp_760_;
}
else
{
lean_object* v_val_767_; lean_object* v___x_768_; 
v_val_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_val_767_);
lean_dec_ref(v___x_766_);
v___x_768_ = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3(v_val_767_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_778_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_778_ == 0)
{
v___x_771_ = v___x_768_;
v_isShared_772_ = v_isSharedCheck_778_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_768_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_778_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_773_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5));
v___x_774_ = lean_string_append(v___x_773_, v_a_769_);
lean_dec(v_a_769_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_774_);
v___x_776_ = v___x_771_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
else
{
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
v_a_779_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_768_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_768_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
lean_ctor_set_tag(v___x_781_, 0);
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
else
{
lean_object* v_a_787_; 
v_a_787_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_787_);
lean_dec_ref(v___x_768_);
if (lean_obj_tag(v_a_787_) == 0)
{
v___y_761_ = v_depHash_764_;
goto v___jp_760_;
}
else
{
lean_object* v_val_788_; 
v_val_788_ = lean_ctor_get(v_a_787_, 0);
lean_inc(v_val_788_);
lean_dec_ref(v_a_787_);
v___y_734_ = v_depHash_764_;
v_a_735_ = v_val_788_;
goto v___jp_733_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___boxed(lean_object* v_obj_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lake_BuildMetadata_fromJsonObject_x3f(v_obj_844_);
lean_dec(v_obj_844_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f(lean_object* v_json_852_){
_start:
{
switch(lean_obj_tag(v_json_852_))
{
case 2:
{
lean_object* v_n_853_; lean_object* v___x_854_; 
v_n_853_ = lean_ctor_get(v_json_852_, 0);
v___x_854_ = l_Lake_Hash_ofJsonNumber_x3f(v_n_853_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_864_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_864_ == 0)
{
v___x_857_ = v___x_854_;
v_isShared_858_ = v_isSharedCheck_864_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_854_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_864_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_862_; 
v___x_859_ = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__0));
v___x_860_ = lean_string_append(v___x_859_, v_a_855_);
lean_dec(v_a_855_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_860_);
v___x_862_ = v___x_857_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_874_; 
v_a_865_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_874_ == 0)
{
v___x_867_ = v___x_854_;
v_isShared_868_ = v_isSharedCheck_874_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_854_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_874_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
uint64_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_869_ = lean_unbox_uint64(v_a_865_);
lean_dec(v_a_865_);
v___x_870_ = l_Lake_BuildMetadata_ofStub(v___x_869_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_870_);
v___x_872_ = v___x_867_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
case 5:
{
lean_object* v_kvPairs_875_; lean_object* v___x_876_; 
v_kvPairs_875_ = lean_ctor_get(v_json_852_, 0);
v___x_876_ = l_Lake_BuildMetadata_fromJsonObject_x3f(v_kvPairs_875_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_902_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_902_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_902_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_902_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__0));
v___x_888_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_875_, v___x_887_);
if (lean_obj_tag(v___x_888_) == 1)
{
lean_object* v_val_889_; 
v_val_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_val_889_);
lean_dec_ref(v___x_888_);
if (lean_obj_tag(v_val_889_) == 3)
{
lean_object* v_s_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_901_; 
v_s_890_ = lean_ctor_get(v_val_889_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v_val_889_);
if (v_isSharedCheck_901_ == 0)
{
v___x_892_ = v_val_889_;
v_isShared_893_ = v_isSharedCheck_901_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_s_890_);
lean_dec(v_val_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_901_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_894_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0));
v___x_895_ = lean_string_dec_eq(v_s_890_, v___x_894_);
lean_dec_ref(v_s_890_);
if (v___x_895_ == 0)
{
lean_del_object(v___x_892_);
goto v___jp_881_;
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
lean_del_object(v___x_879_);
v___x_896_ = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__2));
v___x_897_ = lean_string_append(v___x_896_, v_a_877_);
lean_dec(v_a_877_);
if (v_isShared_893_ == 0)
{
lean_ctor_set_tag(v___x_892_, 0);
lean_ctor_set(v___x_892_, 0, v___x_897_);
v___x_899_ = v___x_892_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
else
{
lean_dec(v_val_889_);
goto v___jp_881_;
}
}
else
{
lean_dec(v___x_888_);
goto v___jp_881_;
}
v___jp_881_:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_882_ = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__1));
v___x_883_ = lean_string_append(v___x_882_, v_a_877_);
lean_dec(v_a_877_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_883_);
v___x_885_ = v___x_879_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
else
{
return v___x_876_;
}
}
default: 
{
lean_object* v___x_903_; 
v___x_903_ = ((lean_object*)(l_Lake_BuildMetadata_fromJson_x3f___closed__4));
return v___x_903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f___boxed(lean_object* v_json_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lake_BuildMetadata_fromJson_x3f(v_json_904_);
lean_dec(v_json_904_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_parse(lean_object* v_contents_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_Json_parse(v_contents_908_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
else
{
lean_object* v_a_918_; lean_object* v___x_919_; 
v_a_918_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_918_);
lean_dec_ref(v___x_909_);
v___x_919_ = l_Lake_BuildMetadata_fromJson_x3f(v_a_918_);
lean_dec(v_a_918_);
return v___x_919_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch(uint64_t v_inputHash_920_, lean_object* v_outputs_921_){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; uint8_t v___x_924_; lean_object* v___x_925_; 
v___x_922_ = ((lean_object*)(l_Lake_BuildMetadata_ofStub___closed__0));
v___x_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_923_, 0, v_outputs_921_);
v___x_924_ = 1;
v___x_925_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_925_, 0, v___x_922_);
lean_ctor_set(v___x_925_, 1, v___x_923_);
lean_ctor_set(v___x_925_, 2, v___x_922_);
lean_ctor_set_uint64(v___x_925_, sizeof(void*)*3, v_inputHash_920_);
lean_ctor_set_uint8(v___x_925_, sizeof(void*)*3 + 8, v___x_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch___boxed(lean_object* v_inputHash_926_, lean_object* v_outputs_927_){
_start:
{
uint64_t v_inputHash_boxed_928_; lean_object* v_res_929_; 
v_inputHash_boxed_928_ = lean_unbox_uint64(v_inputHash_926_);
lean_dec_ref(v_inputHash_926_);
v_res_929_ = l_Lake_BuildMetadata_ofFetch(v_inputHash_boxed_928_, v_outputs_927_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(lean_object* v_as_930_, size_t v_i_931_, size_t v_stop_932_, lean_object* v_b_933_){
_start:
{
uint8_t v___x_934_; 
v___x_934_ = lean_usize_dec_eq(v_i_931_, v_stop_932_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; lean_object* v___y_937_; lean_object* v_inputs_944_; uint64_t v_hash_945_; lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_935_ = lean_array_uget_borrowed(v_as_930_, v_i_931_);
v_inputs_944_ = lean_ctor_get(v___x_935_, 1);
v_hash_945_ = lean_ctor_get_uint64(v___x_935_, sizeof(void*)*3);
v___x_946_ = lean_array_get_size(v_inputs_944_);
v___x_947_ = lean_unsigned_to_nat(0u);
v___x_948_ = lean_nat_dec_eq(v___x_946_, v___x_947_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = l___private_Lake_Build_Common_0__Lake_serializeInputs(v_inputs_944_);
v___x_950_ = l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(v___x_949_);
v___y_937_ = v___x_950_;
goto v___jp_936_;
}
else
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = l_Lake_Hash_hex(v_hash_945_);
v___x_952_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
v___y_937_ = v___x_952_;
goto v___jp_936_;
}
v___jp_936_:
{
lean_object* v_caption_938_; lean_object* v___x_939_; lean_object* v___x_940_; size_t v___x_941_; size_t v___x_942_; 
v_caption_938_ = lean_ctor_get(v___x_935_, 0);
lean_inc_ref(v_caption_938_);
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v_caption_938_);
lean_ctor_set(v___x_939_, 1, v___y_937_);
v___x_940_ = lean_array_push(v_b_933_, v___x_939_);
v___x_941_ = ((size_t)1ULL);
v___x_942_ = lean_usize_add(v_i_931_, v___x_941_);
v_i_931_ = v___x_942_;
v_b_933_ = v___x_940_;
goto _start;
}
}
else
{
return v_b_933_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs(lean_object* v_inputs_953_){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; uint8_t v___x_957_; 
v___x_954_ = lean_unsigned_to_nat(0u);
v___x_955_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4));
v___x_956_ = lean_array_get_size(v_inputs_953_);
v___x_957_ = lean_nat_dec_lt(v___x_954_, v___x_956_);
if (v___x_957_ == 0)
{
return v___x_955_;
}
else
{
uint8_t v___x_958_; 
v___x_958_ = lean_nat_dec_le(v___x_956_, v___x_956_);
if (v___x_958_ == 0)
{
if (v___x_957_ == 0)
{
return v___x_955_;
}
else
{
size_t v___x_959_; size_t v___x_960_; lean_object* v___x_961_; 
v___x_959_ = ((size_t)0ULL);
v___x_960_ = lean_usize_of_nat(v___x_956_);
v___x_961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(v_inputs_953_, v___x_959_, v___x_960_, v___x_955_);
return v___x_961_;
}
}
else
{
size_t v___x_962_; size_t v___x_963_; lean_object* v___x_964_; 
v___x_962_ = ((size_t)0ULL);
v___x_963_ = lean_usize_of_nat(v___x_956_);
v___x_964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(v_inputs_953_, v___x_962_, v___x_963_, v___x_955_);
return v___x_964_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs___boxed(lean_object* v_inputs_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l___private_Lake_Build_Common_0__Lake_serializeInputs(v_inputs_965_);
lean_dec_ref(v_inputs_965_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0___boxed(lean_object* v_as_967_, lean_object* v_i_968_, lean_object* v_stop_969_, lean_object* v_b_970_){
_start:
{
size_t v_i_boxed_971_; size_t v_stop_boxed_972_; lean_object* v_res_973_; 
v_i_boxed_971_ = lean_unbox_usize(v_i_968_);
lean_dec(v_i_968_);
v_stop_boxed_972_ = lean_unbox_usize(v_stop_969_);
lean_dec(v_stop_969_);
v_res_973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(v_as_967_, v_i_boxed_971_, v_stop_boxed_972_, v_b_970_);
lean_dec_ref(v_as_967_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(lean_object* v_depTrace_974_, lean_object* v_outputs_975_, lean_object* v_log_976_){
_start:
{
lean_object* v_inputs_977_; uint64_t v_hash_978_; lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; lean_object* v___x_982_; 
v_inputs_977_ = lean_ctor_get(v_depTrace_974_, 1);
v_hash_978_ = lean_ctor_get_uint64(v_depTrace_974_, sizeof(void*)*3);
v___x_979_ = l___private_Lake_Build_Common_0__Lake_serializeInputs(v_inputs_977_);
v___x_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_980_, 0, v_outputs_975_);
v___x_981_ = 0;
v___x_982_ = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(v___x_982_, 0, v___x_979_);
lean_ctor_set(v___x_982_, 1, v___x_980_);
lean_ctor_set(v___x_982_, 2, v_log_976_);
lean_ctor_set_uint64(v___x_982_, sizeof(void*)*3, v_hash_978_);
lean_ctor_set_uint8(v___x_982_, sizeof(void*)*3 + 8, v___x_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore___boxed(lean_object* v_depTrace_983_, lean_object* v_outputs_984_, lean_object* v_log_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_983_, v_outputs_984_, v_log_985_);
lean_dec_ref(v_depTrace_983_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg(lean_object* v_inst_987_, lean_object* v_depTrace_988_, lean_object* v_outputs_989_, lean_object* v_log_990_){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = lean_apply_1(v_inst_987_, v_outputs_989_);
v___x_992_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_988_, v___x_991_, v_log_990_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg___boxed(lean_object* v_inst_993_, lean_object* v_depTrace_994_, lean_object* v_outputs_995_, lean_object* v_log_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lake_BuildMetadata_ofBuild___redArg(v_inst_993_, v_depTrace_994_, v_outputs_995_, v_log_996_);
lean_dec_ref(v_depTrace_994_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild(lean_object* v_00_u03b1_998_, lean_object* v_inst_999_, lean_object* v_depTrace_1000_, lean_object* v_outputs_1001_, lean_object* v_log_1002_){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_apply_1(v_inst_999_, v_outputs_1001_);
v___x_1004_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1000_, v___x_1003_, v_log_1002_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___boxed(lean_object* v_00_u03b1_1005_, lean_object* v_inst_1006_, lean_object* v_depTrace_1007_, lean_object* v_outputs_1008_, lean_object* v_log_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lake_BuildMetadata_ofBuild(v_00_u03b1_1005_, v_inst_1006_, v_depTrace_1007_, v_outputs_1008_, v_log_1009_);
lean_dec_ref(v_depTrace_1007_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorIdx(lean_object* v_x_1011_){
_start:
{
switch(lean_obj_tag(v_x_1011_))
{
case 0:
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_unsigned_to_nat(0u);
return v___x_1012_;
}
case 1:
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_unsigned_to_nat(1u);
return v___x_1013_;
}
default: 
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_unsigned_to_nat(2u);
return v___x_1014_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorIdx___boxed(lean_object* v_x_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lake_SavedTrace_ctorIdx(v_x_1015_);
lean_dec(v_x_1015_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim___redArg(lean_object* v_t_1017_, lean_object* v_k_1018_){
_start:
{
if (lean_obj_tag(v_t_1017_) == 2)
{
lean_object* v_data_1019_; lean_object* v___x_1020_; 
v_data_1019_ = lean_ctor_get(v_t_1017_, 0);
lean_inc_ref(v_data_1019_);
lean_dec_ref(v_t_1017_);
v___x_1020_ = lean_apply_1(v_k_1018_, v_data_1019_);
return v___x_1020_;
}
else
{
lean_dec(v_t_1017_);
return v_k_1018_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim(lean_object* v_motive_1021_, lean_object* v_ctorIdx_1022_, lean_object* v_t_1023_, lean_object* v_h_1024_, lean_object* v_k_1025_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1023_, v_k_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim___boxed(lean_object* v_motive_1027_, lean_object* v_ctorIdx_1028_, lean_object* v_t_1029_, lean_object* v_h_1030_, lean_object* v_k_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lake_SavedTrace_ctorElim(v_motive_1027_, v_ctorIdx_1028_, v_t_1029_, v_h_1030_, v_k_1031_);
lean_dec(v_ctorIdx_1028_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_missing_elim___redArg(lean_object* v_t_1033_, lean_object* v_missing_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1033_, v_missing_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_missing_elim(lean_object* v_motive_1036_, lean_object* v_t_1037_, lean_object* v_h_1038_, lean_object* v_missing_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1037_, v_missing_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_invalid_elim___redArg(lean_object* v_t_1041_, lean_object* v_invalid_1042_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1041_, v_invalid_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_invalid_elim(lean_object* v_motive_1044_, lean_object* v_t_1045_, lean_object* v_h_1046_, lean_object* v_invalid_1047_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1045_, v_invalid_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ok_elim___redArg(lean_object* v_t_1049_, lean_object* v_ok_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1049_, v_ok_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ok_elim(lean_object* v_motive_1052_, lean_object* v_t_1053_, lean_object* v_h_1054_, lean_object* v_ok_1055_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lake_SavedTrace_ctorElim___redArg(v_t_1053_, v_ok_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lake_readTraceFile(lean_object* v_path_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_IO_FS_readFile(v_path_1058_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v_a_1064_; lean_object* v___x_1073_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_a_1062_);
lean_dec_ref(v___x_1061_);
v___x_1073_ = l_Lean_Json_parse(v_a_1062_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1074_);
lean_dec_ref(v___x_1073_);
v_a_1064_ = v_a_1074_;
goto v___jp_1063_;
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1076_; 
v_a_1075_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1075_);
lean_dec_ref(v___x_1073_);
v___x_1076_ = l_Lake_BuildMetadata_fromJson_x3f(v_a_1075_);
lean_dec(v_a_1075_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref(v___x_1076_);
v_a_1064_ = v_a_1077_;
goto v___jp_1063_;
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1086_; 
lean_dec_ref(v_path_1058_);
v_a_1078_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1080_ = v___x_1076_;
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1076_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
lean_ctor_set_tag(v___x_1080_, 2);
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v_a_1059_);
return v___x_1084_;
}
}
}
}
v___jp_1063_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1065_ = ((lean_object*)(l_Lake_addPureTrace___redArg___closed__0));
v___x_1066_ = lean_string_append(v_path_1058_, v___x_1065_);
v___x_1067_ = lean_string_append(v___x_1066_, v_a_1064_);
lean_dec_ref(v_a_1064_);
v___x_1068_ = 2;
v___x_1069_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set_uint8(v___x_1069_, sizeof(void*)*1, v___x_1068_);
v___x_1070_ = lean_array_push(v_a_1059_, v___x_1069_);
v___x_1071_ = lean_box(1);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
lean_ctor_set(v___x_1072_, 1, v___x_1070_);
return v___x_1072_;
}
}
else
{
lean_object* v_a_1087_; 
v_a_1087_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_a_1087_);
lean_dec_ref(v___x_1061_);
if (lean_obj_tag(v_a_1087_) == 11)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_dec_ref(v_a_1087_);
lean_dec_ref(v_path_1058_);
v___x_1088_ = lean_box(0);
v___x_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
lean_ctor_set(v___x_1089_, 1, v_a_1059_);
return v___x_1089_;
}
else
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1090_ = ((lean_object*)(l_Lake_readTraceFile___closed__0));
v___x_1091_ = lean_string_append(v_path_1058_, v___x_1090_);
v___x_1092_ = lean_io_error_to_string(v_a_1087_);
v___x_1093_ = lean_string_append(v___x_1091_, v___x_1092_);
lean_dec_ref(v___x_1092_);
v___x_1094_ = 3;
v___x_1095_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*1, v___x_1094_);
v___x_1096_ = lean_array_get_size(v_a_1059_);
v___x_1097_ = lean_array_push(v_a_1059_, v___x_1095_);
v___x_1098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
return v___x_1098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_readTraceFile___boxed(lean_object* v_path_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lake_readTraceFile(v_path_1099_, v_a_1100_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile(lean_object* v_path_1103_, lean_object* v_data_1104_){
_start:
{
lean_object* v___x_1106_; 
lean_inc_ref(v_path_1103_);
v___x_1106_ = l_Lake_createParentDirs(v_path_1103_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
lean_dec_ref(v___x_1106_);
v___x_1107_ = l_Lake_BuildMetadata_toJson(v_data_1104_);
v___x_1108_ = lean_unsigned_to_nat(80u);
v___x_1109_ = l_Lean_Json_pretty(v___x_1107_, v___x_1108_);
v___x_1110_ = l_IO_FS_writeFile(v_path_1103_, v___x_1109_);
lean_dec_ref(v___x_1109_);
lean_dec_ref(v_path_1103_);
return v___x_1110_;
}
else
{
lean_dec_ref(v_data_1104_);
lean_dec_ref(v_path_1103_);
return v___x_1106_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile___boxed(lean_object* v_path_1111_, lean_object* v_data_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lake_BuildMetadata_writeFile(v_path_1111_, v_data_1112_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace(lean_object* v_path_1115_, uint64_t v_inputHash_1116_, lean_object* v_outputs_1117_){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = l_Lake_BuildMetadata_ofFetch(v_inputHash_1116_, v_outputs_1117_);
v___x_1120_ = l_Lake_BuildMetadata_writeFile(v_path_1115_, v___x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace___boxed(lean_object* v_path_1121_, lean_object* v_inputHash_1122_, lean_object* v_outputs_1123_, lean_object* v_a_1124_){
_start:
{
uint64_t v_inputHash_boxed_1125_; lean_object* v_res_1126_; 
v_inputHash_boxed_1125_ = lean_unbox_uint64(v_inputHash_1122_);
lean_dec_ref(v_inputHash_1122_);
v_res_1126_ = l_Lake_writeFetchTrace(v_path_1121_, v_inputHash_boxed_1125_, v_outputs_1123_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg(lean_object* v_inst_1127_, lean_object* v_path_1128_, lean_object* v_depTrace_1129_, lean_object* v_outputs_1130_, lean_object* v_log_1131_){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1133_ = lean_apply_1(v_inst_1127_, v_outputs_1130_);
v___x_1134_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1129_, v___x_1133_, v_log_1131_);
v___x_1135_ = l_Lake_BuildMetadata_writeFile(v_path_1128_, v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg___boxed(lean_object* v_inst_1136_, lean_object* v_path_1137_, lean_object* v_depTrace_1138_, lean_object* v_outputs_1139_, lean_object* v_log_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lake_writeBuildTrace___redArg(v_inst_1136_, v_path_1137_, v_depTrace_1138_, v_outputs_1139_, v_log_1140_);
lean_dec_ref(v_depTrace_1138_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace(lean_object* v_00_u03b1_1143_, lean_object* v_inst_1144_, lean_object* v_path_1145_, lean_object* v_depTrace_1146_, lean_object* v_outputs_1147_, lean_object* v_log_1148_){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1150_ = lean_apply_1(v_inst_1144_, v_outputs_1147_);
v___x_1151_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1146_, v___x_1150_, v_log_1148_);
v___x_1152_ = l_Lake_BuildMetadata_writeFile(v_path_1145_, v___x_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___boxed(lean_object* v_00_u03b1_1153_, lean_object* v_inst_1154_, lean_object* v_path_1155_, lean_object* v_depTrace_1156_, lean_object* v_outputs_1157_, lean_object* v_log_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Lake_writeBuildTrace(v_00_u03b1_1153_, v_inst_1154_, v_path_1155_, v_depTrace_1156_, v_outputs_1157_, v_log_1158_);
lean_dec_ref(v_depTrace_1156_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorIdx(uint8_t v_x_1161_){
_start:
{
switch(v_x_1161_)
{
case 0:
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_unsigned_to_nat(0u);
return v___x_1162_;
}
case 1:
{
lean_object* v___x_1163_; 
v___x_1163_ = lean_unsigned_to_nat(1u);
return v___x_1163_;
}
default: 
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_unsigned_to_nat(2u);
return v___x_1164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorIdx___boxed(lean_object* v_x_1165_){
_start:
{
uint8_t v_x_boxed_1166_; lean_object* v_res_1167_; 
v_x_boxed_1166_ = lean_unbox(v_x_1165_);
v_res_1167_ = l_Lake_OutputStatus_ctorIdx(v_x_boxed_1166_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_toCtorIdx(uint8_t v_x_1168_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Lake_OutputStatus_ctorIdx(v_x_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_toCtorIdx___boxed(lean_object* v_x_1170_){
_start:
{
uint8_t v_x_4__boxed_1171_; lean_object* v_res_1172_; 
v_x_4__boxed_1171_ = lean_unbox(v_x_1170_);
v_res_1172_ = l_Lake_OutputStatus_toCtorIdx(v_x_4__boxed_1171_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg(lean_object* v_k_1173_){
_start:
{
lean_inc(v_k_1173_);
return v_k_1173_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg___boxed(lean_object* v_k_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lake_OutputStatus_ctorElim___redArg(v_k_1174_);
lean_dec(v_k_1174_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim(lean_object* v_motive_1176_, lean_object* v_ctorIdx_1177_, uint8_t v_t_1178_, lean_object* v_h_1179_, lean_object* v_k_1180_){
_start:
{
lean_inc(v_k_1180_);
return v_k_1180_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___boxed(lean_object* v_motive_1181_, lean_object* v_ctorIdx_1182_, lean_object* v_t_1183_, lean_object* v_h_1184_, lean_object* v_k_1185_){
_start:
{
uint8_t v_t_boxed_1186_; lean_object* v_res_1187_; 
v_t_boxed_1186_ = lean_unbox(v_t_1183_);
v_res_1187_ = l_Lake_OutputStatus_ctorElim(v_motive_1181_, v_ctorIdx_1182_, v_t_boxed_1186_, v_h_1184_, v_k_1185_);
lean_dec(v_k_1185_);
lean_dec(v_ctorIdx_1182_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg(lean_object* v_outOfDate_1188_){
_start:
{
lean_inc(v_outOfDate_1188_);
return v_outOfDate_1188_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg___boxed(lean_object* v_outOfDate_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lake_OutputStatus_outOfDate_elim___redArg(v_outOfDate_1189_);
lean_dec(v_outOfDate_1189_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim(lean_object* v_motive_1191_, uint8_t v_t_1192_, lean_object* v_h_1193_, lean_object* v_outOfDate_1194_){
_start:
{
lean_inc(v_outOfDate_1194_);
return v_outOfDate_1194_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___boxed(lean_object* v_motive_1195_, lean_object* v_t_1196_, lean_object* v_h_1197_, lean_object* v_outOfDate_1198_){
_start:
{
uint8_t v_t_boxed_1199_; lean_object* v_res_1200_; 
v_t_boxed_1199_ = lean_unbox(v_t_1196_);
v_res_1200_ = l_Lake_OutputStatus_outOfDate_elim(v_motive_1195_, v_t_boxed_1199_, v_h_1197_, v_outOfDate_1198_);
lean_dec(v_outOfDate_1198_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg(lean_object* v_mtimeUpToDate_1201_){
_start:
{
lean_inc(v_mtimeUpToDate_1201_);
return v_mtimeUpToDate_1201_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg___boxed(lean_object* v_mtimeUpToDate_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lake_OutputStatus_mtimeUpToDate_elim___redArg(v_mtimeUpToDate_1202_);
lean_dec(v_mtimeUpToDate_1202_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim(lean_object* v_motive_1204_, uint8_t v_t_1205_, lean_object* v_h_1206_, lean_object* v_mtimeUpToDate_1207_){
_start:
{
lean_inc(v_mtimeUpToDate_1207_);
return v_mtimeUpToDate_1207_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___boxed(lean_object* v_motive_1208_, lean_object* v_t_1209_, lean_object* v_h_1210_, lean_object* v_mtimeUpToDate_1211_){
_start:
{
uint8_t v_t_boxed_1212_; lean_object* v_res_1213_; 
v_t_boxed_1212_ = lean_unbox(v_t_1209_);
v_res_1213_ = l_Lake_OutputStatus_mtimeUpToDate_elim(v_motive_1208_, v_t_boxed_1212_, v_h_1210_, v_mtimeUpToDate_1211_);
lean_dec(v_mtimeUpToDate_1211_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg(lean_object* v_hashUpToDate_1214_){
_start:
{
lean_inc(v_hashUpToDate_1214_);
return v_hashUpToDate_1214_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg___boxed(lean_object* v_hashUpToDate_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lake_OutputStatus_hashUpToDate_elim___redArg(v_hashUpToDate_1215_);
lean_dec(v_hashUpToDate_1215_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim(lean_object* v_motive_1217_, uint8_t v_t_1218_, lean_object* v_h_1219_, lean_object* v_hashUpToDate_1220_){
_start:
{
lean_inc(v_hashUpToDate_1220_);
return v_hashUpToDate_1220_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___boxed(lean_object* v_motive_1221_, lean_object* v_t_1222_, lean_object* v_h_1223_, lean_object* v_hashUpToDate_1224_){
_start:
{
uint8_t v_t_boxed_1225_; lean_object* v_res_1226_; 
v_t_boxed_1225_ = lean_unbox(v_t_1222_);
v_res_1226_ = l_Lake_OutputStatus_hashUpToDate_elim(v_motive_1221_, v_t_boxed_1225_, v_h_1223_, v_hashUpToDate_1224_);
lean_dec(v_hashUpToDate_1224_);
return v_res_1226_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofNat(lean_object* v_n_1227_){
_start:
{
lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = lean_unsigned_to_nat(0u);
v___x_1229_ = lean_nat_dec_le(v_n_1227_, v___x_1228_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1230_ = lean_unsigned_to_nat(1u);
v___x_1231_ = lean_nat_dec_le(v_n_1227_, v___x_1230_);
if (v___x_1231_ == 0)
{
uint8_t v___x_1232_; 
v___x_1232_ = 2;
return v___x_1232_;
}
else
{
uint8_t v___x_1233_; 
v___x_1233_ = 1;
return v___x_1233_;
}
}
else
{
uint8_t v___x_1234_; 
v___x_1234_ = 0;
return v___x_1234_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofNat___boxed(lean_object* v_n_1235_){
_start:
{
uint8_t v_res_1236_; lean_object* v_r_1237_; 
v_res_1236_ = l_Lake_OutputStatus_ofNat(v_n_1235_);
lean_dec(v_n_1235_);
v_r_1237_ = lean_box(v_res_1236_);
return v_r_1237_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqOutputStatus(uint8_t v_x_1238_, uint8_t v_y_1239_){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1240_ = l_Lake_OutputStatus_ctorIdx(v_x_1238_);
v___x_1241_ = l_Lake_OutputStatus_ctorIdx(v_y_1239_);
v___x_1242_ = lean_nat_dec_eq(v___x_1240_, v___x_1241_);
lean_dec(v___x_1241_);
lean_dec(v___x_1240_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqOutputStatus___boxed(lean_object* v_x_1243_, lean_object* v_y_1244_){
_start:
{
uint8_t v_x_13__boxed_1245_; uint8_t v_y_14__boxed_1246_; uint8_t v_res_1247_; lean_object* v_r_1248_; 
v_x_13__boxed_1245_ = lean_unbox(v_x_1243_);
v_y_14__boxed_1246_ = lean_unbox(v_y_1244_);
v_res_1247_ = l_Lake_instDecidableEqOutputStatus(v_x_13__boxed_1245_, v_y_14__boxed_1246_);
v_r_1248_ = lean_box(v_res_1247_);
return v_r_1248_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofHashCheck(uint8_t v_upToDate_1249_){
_start:
{
if (v_upToDate_1249_ == 0)
{
uint8_t v___x_1250_; 
v___x_1250_ = 0;
return v___x_1250_;
}
else
{
uint8_t v___x_1251_; 
v___x_1251_ = 2;
return v___x_1251_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofHashCheck___boxed(lean_object* v_upToDate_1252_){
_start:
{
uint8_t v_upToDate_boxed_1253_; uint8_t v_res_1254_; lean_object* v_r_1255_; 
v_upToDate_boxed_1253_ = lean_unbox(v_upToDate_1252_);
v_res_1254_ = l_Lake_OutputStatus_ofHashCheck(v_upToDate_boxed_1253_);
v_r_1255_ = lean_box(v_res_1254_);
return v_r_1255_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofMTimeCheck(uint8_t v_upToDate_1256_){
_start:
{
if (v_upToDate_1256_ == 0)
{
uint8_t v___x_1257_; 
v___x_1257_ = 0;
return v___x_1257_;
}
else
{
uint8_t v___x_1258_; 
v___x_1258_ = 1;
return v___x_1258_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofMTimeCheck___boxed(lean_object* v_upToDate_1259_){
_start:
{
uint8_t v_upToDate_boxed_1260_; uint8_t v_res_1261_; lean_object* v_r_1262_; 
v_upToDate_boxed_1260_ = lean_unbox(v_upToDate_1259_);
v_res_1261_ = l_Lake_OutputStatus_ofMTimeCheck(v_upToDate_boxed_1260_);
v_r_1262_ = lean_box(v_res_1261_);
return v_r_1262_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isUpToDate(uint8_t v_status_1263_){
_start:
{
uint8_t v___x_1264_; uint8_t v___x_1265_; 
v___x_1264_ = 0;
v___x_1265_ = l_Lake_instDecidableEqOutputStatus(v_status_1263_, v___x_1264_);
if (v___x_1265_ == 0)
{
uint8_t v___x_1266_; 
v___x_1266_ = 1;
return v___x_1266_;
}
else
{
uint8_t v___x_1267_; 
v___x_1267_ = 0;
return v___x_1267_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isUpToDate___boxed(lean_object* v_status_1268_){
_start:
{
uint8_t v_status_boxed_1269_; uint8_t v_res_1270_; lean_object* v_r_1271_; 
v_status_boxed_1269_ = lean_unbox(v_status_1268_);
v_res_1270_ = l_Lake_OutputStatus_isUpToDate(v_status_boxed_1269_);
v_r_1271_ = lean_box(v_res_1270_);
return v_r_1271_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isCacheable(uint8_t v_status_1272_){
_start:
{
uint8_t v___x_1273_; uint8_t v___x_1274_; 
v___x_1273_ = 1;
v___x_1274_ = l_Lake_instDecidableEqOutputStatus(v_status_1272_, v___x_1273_);
if (v___x_1274_ == 0)
{
uint8_t v___x_1275_; 
v___x_1275_ = 1;
return v___x_1275_;
}
else
{
uint8_t v___x_1276_; 
v___x_1276_ = 0;
return v___x_1276_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isCacheable___boxed(lean_object* v_status_1277_){
_start:
{
uint8_t v_status_boxed_1278_; uint8_t v_res_1279_; lean_object* v_r_1280_; 
v_status_boxed_1278_ = lean_unbox(v_status_1277_);
v_res_1279_ = l_Lake_OutputStatus_isCacheable(v_status_boxed_1278_);
v_r_1280_ = lean_box(v_res_1279_);
return v_r_1280_;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___f_1282_; 
v___x_1281_ = lean_alloc_closure((void*)(l_Lake_instDecidableEqHash___boxed), 2, 0);
v___f_1282_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1282_, 0, v___x_1281_);
return v___f_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(lean_object* v_inst_1283_, lean_object* v_inst_1284_, lean_object* v_info_1285_, lean_object* v_depTrace_1286_, lean_object* v_depHash_1287_, lean_object* v_oldTrace_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
uint64_t v_hash_1292_; lean_object* v___f_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; 
v_hash_1292_ = lean_ctor_get_uint64(v_depTrace_1286_, sizeof(void*)*3);
v___f_1293_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0);
v___x_1294_ = lean_box_uint64(v_hash_1292_);
v___x_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
v___x_1296_ = l_Option_instBEq_beq___redArg(v___f_1293_, v___x_1295_, v_depHash_1287_);
if (v___x_1296_ == 0)
{
lean_object* v_toBuildConfig_1297_; uint8_t v_oldMode_1298_; 
lean_dec_ref(v_inst_1283_);
v_toBuildConfig_1297_ = lean_ctor_get(v_a_1289_, 0);
v_oldMode_1298_ = lean_ctor_get_uint8(v_toBuildConfig_1297_, sizeof(void*)*2);
if (v_oldMode_1298_ == 0)
{
uint8_t v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_dec(v_info_1285_);
lean_dec_ref(v_inst_1284_);
v___x_1299_ = 0;
v___x_1300_ = lean_box(v___x_1299_);
v___x_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
lean_ctor_set(v___x_1301_, 1, v_a_1290_);
return v___x_1301_;
}
else
{
uint8_t v___x_1302_; 
v___x_1302_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1284_, v_info_1285_, v_oldTrace_1288_);
if (v___x_1302_ == 0)
{
uint8_t v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1303_ = 0;
v___x_1304_ = lean_box(v___x_1303_);
v___x_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
lean_ctor_set(v___x_1305_, 1, v_a_1290_);
return v___x_1305_;
}
else
{
uint8_t v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = 1;
v___x_1307_ = lean_box(v___x_1306_);
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
lean_ctor_set(v___x_1308_, 1, v_a_1290_);
return v___x_1308_;
}
}
}
else
{
lean_object* v___x_1309_; uint8_t v___x_1310_; 
lean_dec_ref(v_inst_1284_);
v___x_1309_ = lean_apply_2(v_inst_1283_, v_info_1285_, lean_box(0));
v___x_1310_ = lean_unbox(v___x_1309_);
if (v___x_1310_ == 0)
{
uint8_t v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = 0;
v___x_1312_ = lean_box(v___x_1311_);
v___x_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
lean_ctor_set(v___x_1313_, 1, v_a_1290_);
return v___x_1313_;
}
else
{
uint8_t v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1314_ = 2;
v___x_1315_ = lean_box(v___x_1314_);
v___x_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
lean_ctor_set(v___x_1316_, 1, v_a_1290_);
return v___x_1316_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___boxed(lean_object* v_inst_1317_, lean_object* v_inst_1318_, lean_object* v_info_1319_, lean_object* v_depTrace_1320_, lean_object* v_depHash_1321_, lean_object* v_oldTrace_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1317_, v_inst_1318_, v_info_1319_, v_depTrace_1320_, v_depHash_1321_, v_oldTrace_1322_, v_a_1323_, v_a_1324_);
lean_dec_ref(v_a_1323_);
lean_dec_ref(v_oldTrace_1322_);
lean_dec_ref(v_depTrace_1320_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27(lean_object* v_00_u03b9_1327_, lean_object* v_inst_1328_, lean_object* v_inst_1329_, lean_object* v_info_1330_, lean_object* v_depTrace_1331_, lean_object* v_depHash_1332_, lean_object* v_oldTrace_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1328_, v_inst_1329_, v_info_1330_, v_depTrace_1331_, v_depHash_1332_, v_oldTrace_1333_, v_a_1338_, v_a_1339_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___boxed(lean_object* v_00_u03b9_1342_, lean_object* v_inst_1343_, lean_object* v_inst_1344_, lean_object* v_info_1345_, lean_object* v_depTrace_1346_, lean_object* v_depHash_1347_, lean_object* v_oldTrace_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27(v_00_u03b9_1342_, v_inst_1343_, v_inst_1344_, v_info_1345_, v_depTrace_1346_, v_depHash_1347_, v_oldTrace_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
lean_dec_ref(v_a_1353_);
lean_dec(v_a_1352_);
lean_dec(v_a_1351_);
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1349_);
lean_dec_ref(v_oldTrace_1348_);
lean_dec_ref(v_depTrace_1346_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg(lean_object* v_inst_1357_, lean_object* v_inst_1358_, lean_object* v_info_1359_, lean_object* v_depTrace_1360_, lean_object* v_depHash_1361_, lean_object* v_oldTrace_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_){
_start:
{
lean_object* v___x_1366_; lean_object* v_a_1367_; lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1385_; 
v___x_1366_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1357_, v_inst_1358_, v_info_1359_, v_depTrace_1360_, v_depHash_1361_, v_oldTrace_1362_, v_a_1363_, v_a_1364_);
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
v_a_1368_ = lean_ctor_get(v___x_1366_, 1);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1370_ = v___x_1366_;
v_isShared_1371_ = v_isSharedCheck_1385_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_inc(v_a_1367_);
lean_dec(v___x_1366_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1385_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
uint8_t v___x_1372_; uint8_t v___x_1373_; uint8_t v___x_1374_; 
v___x_1372_ = 0;
v___x_1373_ = lean_unbox(v_a_1367_);
lean_dec(v_a_1367_);
v___x_1374_ = l_Lake_instDecidableEqOutputStatus(v___x_1373_, v___x_1372_);
if (v___x_1374_ == 0)
{
uint8_t v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1375_ = 1;
v___x_1376_ = lean_box(v___x_1375_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1376_);
v___x_1378_ = v___x_1370_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_a_1368_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
else
{
uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1383_; 
v___x_1380_ = 0;
v___x_1381_ = lean_box(v___x_1380_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1381_);
v___x_1383_ = v___x_1370_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_a_1368_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg___boxed(lean_object* v_inst_1386_, lean_object* v_inst_1387_, lean_object* v_info_1388_, lean_object* v_depTrace_1389_, lean_object* v_depHash_1390_, lean_object* v_oldTrace_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lake_checkHashUpToDate___redArg(v_inst_1386_, v_inst_1387_, v_info_1388_, v_depTrace_1389_, v_depHash_1390_, v_oldTrace_1391_, v_a_1392_, v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec_ref(v_oldTrace_1391_);
lean_dec_ref(v_depTrace_1389_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate(lean_object* v_00_u03b9_1396_, lean_object* v_inst_1397_, lean_object* v_inst_1398_, lean_object* v_info_1399_, lean_object* v_depTrace_1400_, lean_object* v_depHash_1401_, lean_object* v_oldTrace_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_){
_start:
{
lean_object* v___x_1410_; lean_object* v_a_1411_; lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1429_; 
v___x_1410_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1397_, v_inst_1398_, v_info_1399_, v_depTrace_1400_, v_depHash_1401_, v_oldTrace_1402_, v_a_1407_, v_a_1408_);
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
v_a_1412_ = lean_ctor_get(v___x_1410_, 1);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1414_ = v___x_1410_;
v_isShared_1415_ = v_isSharedCheck_1429_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_inc(v_a_1411_);
lean_dec(v___x_1410_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1429_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
uint8_t v___x_1416_; uint8_t v___x_1417_; uint8_t v___x_1418_; 
v___x_1416_ = 0;
v___x_1417_ = lean_unbox(v_a_1411_);
lean_dec(v_a_1411_);
v___x_1418_ = l_Lake_instDecidableEqOutputStatus(v___x_1417_, v___x_1416_);
if (v___x_1418_ == 0)
{
uint8_t v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1419_ = 1;
v___x_1420_ = lean_box(v___x_1419_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 0, v___x_1420_);
v___x_1422_ = v___x_1414_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_a_1412_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
else
{
uint8_t v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1424_ = 0;
v___x_1425_ = lean_box(v___x_1424_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 0, v___x_1425_);
v___x_1427_ = v___x_1414_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_a_1412_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___boxed(lean_object* v_00_u03b9_1430_, lean_object* v_inst_1431_, lean_object* v_inst_1432_, lean_object* v_info_1433_, lean_object* v_depTrace_1434_, lean_object* v_depHash_1435_, lean_object* v_oldTrace_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lake_checkHashUpToDate(v_00_u03b9_1430_, v_inst_1431_, v_inst_1432_, v_info_1433_, v_depTrace_1434_, v_depHash_1435_, v_oldTrace_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
lean_dec_ref(v_a_1441_);
lean_dec(v_a_1440_);
lean_dec(v_a_1439_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v_oldTrace_1436_);
lean_dec_ref(v_depTrace_1434_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(lean_object* v_as_1445_, size_t v_i_1446_, size_t v_stop_1447_, lean_object* v_b_1448_, lean_object* v___y_1449_){
_start:
{
uint8_t v___x_1451_; 
v___x_1451_ = lean_usize_dec_eq(v_i_1446_, v_stop_1447_);
if (v___x_1451_ == 0)
{
lean_object* v_log_1452_; uint8_t v_action_1453_; uint8_t v_wantsRebuild_1454_; lean_object* v_trace_1455_; lean_object* v_buildTime_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1469_; 
v_log_1452_ = lean_ctor_get(v___y_1449_, 0);
v_action_1453_ = lean_ctor_get_uint8(v___y_1449_, sizeof(void*)*3);
v_wantsRebuild_1454_ = lean_ctor_get_uint8(v___y_1449_, sizeof(void*)*3 + 1);
v_trace_1455_ = lean_ctor_get(v___y_1449_, 1);
v_buildTime_1456_ = lean_ctor_get(v___y_1449_, 2);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___y_1449_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1458_ = v___y_1449_;
v_isShared_1459_ = v_isSharedCheck_1469_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_buildTime_1456_);
lean_inc(v_trace_1455_);
lean_inc(v_log_1452_);
lean_dec(v___y_1449_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1469_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1464_; 
v___x_1460_ = lean_array_uget_borrowed(v_as_1445_, v_i_1446_);
v___x_1461_ = lean_box(0);
lean_inc(v___x_1460_);
v___x_1462_ = lean_array_push(v_log_1452_, v___x_1460_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 0, v___x_1462_);
v___x_1464_ = v___x_1458_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_trace_1455_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_buildTime_1456_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*3, v_action_1453_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*3 + 1, v_wantsRebuild_1454_);
v___x_1464_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
size_t v___x_1465_; size_t v___x_1466_; 
v___x_1465_ = ((size_t)1ULL);
v___x_1466_ = lean_usize_add(v_i_1446_, v___x_1465_);
v_i_1446_ = v___x_1466_;
v_b_1448_ = v___x_1461_;
v___y_1449_ = v___x_1464_;
goto _start;
}
}
}
else
{
lean_object* v___x_1470_; 
v___x_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1470_, 0, v_b_1448_);
lean_ctor_set(v___x_1470_, 1, v___y_1449_);
return v___x_1470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg___boxed(lean_object* v_as_1471_, lean_object* v_i_1472_, lean_object* v_stop_1473_, lean_object* v_b_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
size_t v_i_boxed_1477_; size_t v_stop_boxed_1478_; lean_object* v_res_1479_; 
v_i_boxed_1477_ = lean_unbox_usize(v_i_1472_);
lean_dec(v_i_1472_);
v_stop_boxed_1478_ = lean_unbox_usize(v_stop_1473_);
lean_dec(v_stop_1473_);
v_res_1479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_as_1471_, v_i_boxed_1477_, v_stop_boxed_1478_, v_b_1474_, v___y_1475_);
lean_dec_ref(v_as_1471_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(lean_object* v_log_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; uint8_t v___x_1491_; 
v___x_1488_ = lean_unsigned_to_nat(0u);
v___x_1489_ = lean_array_get_size(v_log_1480_);
v___x_1490_ = lean_box(0);
v___x_1491_ = lean_nat_dec_lt(v___x_1488_, v___x_1489_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; 
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1490_);
lean_ctor_set(v___x_1492_, 1, v_a_1486_);
return v___x_1492_;
}
else
{
uint8_t v___x_1493_; 
v___x_1493_ = lean_nat_dec_le(v___x_1489_, v___x_1489_);
if (v___x_1493_ == 0)
{
if (v___x_1491_ == 0)
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1490_);
lean_ctor_set(v___x_1494_, 1, v_a_1486_);
return v___x_1494_;
}
else
{
size_t v___x_1495_; size_t v___x_1496_; lean_object* v___x_1497_; 
v___x_1495_ = ((size_t)0ULL);
v___x_1496_ = lean_usize_of_nat(v___x_1489_);
v___x_1497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1480_, v___x_1495_, v___x_1496_, v___x_1490_, v_a_1486_);
return v___x_1497_;
}
}
else
{
size_t v___x_1498_; size_t v___x_1499_; lean_object* v___x_1500_; 
v___x_1498_ = ((size_t)0ULL);
v___x_1499_ = lean_usize_of_nat(v___x_1489_);
v___x_1500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1480_, v___x_1498_, v___x_1499_, v___x_1490_, v_a_1486_);
return v___x_1500_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay___boxed(lean_object* v_log_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
lean_dec(v_a_1504_);
lean_dec(v_a_1503_);
lean_dec_ref(v_a_1502_);
lean_dec_ref(v_log_1501_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(lean_object* v_as_1510_, size_t v_i_1511_, size_t v_stop_1512_, lean_object* v_b_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_as_1510_, v_i_1511_, v_stop_1512_, v_b_1513_, v___y_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___boxed(lean_object* v_as_1522_, lean_object* v_i_1523_, lean_object* v_stop_1524_, lean_object* v_b_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
size_t v_i_boxed_1533_; size_t v_stop_boxed_1534_; lean_object* v_res_1535_; 
v_i_boxed_1533_ = lean_unbox_usize(v_i_1523_);
lean_dec(v_i_1523_);
v_stop_boxed_1534_ = lean_unbox_usize(v_stop_1524_);
lean_dec(v_stop_1524_);
v_res_1535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(v_as_1522_, v_i_boxed_1533_, v_stop_boxed_1534_, v_b_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec_ref(v_as_1522_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(lean_object* v_inst_1536_, lean_object* v_inst_1537_, lean_object* v_info_1538_, lean_object* v_depTrace_1539_, lean_object* v_savedTrace_1540_, lean_object* v_oldTrace_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
if (lean_obj_tag(v_savedTrace_1540_) == 2)
{
lean_object* v_data_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1599_; 
v_data_1549_ = lean_ctor_get(v_savedTrace_1540_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v_savedTrace_1540_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1551_ = v_savedTrace_1540_;
v_isShared_1552_ = v_isSharedCheck_1599_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_data_1549_);
lean_dec(v_savedTrace_1540_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1599_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
uint64_t v_depHash_1553_; lean_object* v_log_1554_; lean_object* v___x_1555_; lean_object* v___x_1557_; 
v_depHash_1553_ = lean_ctor_get_uint64(v_data_1549_, sizeof(void*)*3);
v_log_1554_ = lean_ctor_get(v_data_1549_, 2);
lean_inc_ref(v_log_1554_);
lean_dec_ref(v_data_1549_);
v___x_1555_ = lean_box_uint64(v_depHash_1553_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set_tag(v___x_1551_, 1);
lean_ctor_set(v___x_1551_, 0, v___x_1555_);
v___x_1557_ = v___x_1551_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
lean_object* v___x_1558_; lean_object* v_a_1559_; lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1597_; 
v___x_1558_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1536_, v_inst_1537_, v_info_1538_, v_depTrace_1539_, v___x_1557_, v_oldTrace_1541_, v_a_1546_, v_a_1547_);
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_a_1560_ = lean_ctor_get(v___x_1558_, 1);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1562_ = v___x_1558_;
v_isShared_1563_ = v_isSharedCheck_1597_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1597_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___y_1565_; uint8_t v___x_1569_; uint8_t v___x_1570_; uint8_t v___x_1571_; 
v___x_1569_ = 0;
v___x_1570_ = lean_unbox(v_a_1559_);
v___x_1571_ = l_Lake_instDecidableEqOutputStatus(v___x_1570_, v___x_1569_);
if (v___x_1571_ == 0)
{
lean_object* v_log_1572_; uint8_t v_action_1573_; uint8_t v_wantsRebuild_1574_; lean_object* v_trace_1575_; lean_object* v_buildTime_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1596_; 
v_log_1572_ = lean_ctor_get(v_a_1560_, 0);
v_action_1573_ = lean_ctor_get_uint8(v_a_1560_, sizeof(void*)*3);
v_wantsRebuild_1574_ = lean_ctor_get_uint8(v_a_1560_, sizeof(void*)*3 + 1);
v_trace_1575_ = lean_ctor_get(v_a_1560_, 1);
v_buildTime_1576_ = lean_ctor_get(v_a_1560_, 2);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_a_1560_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1578_ = v_a_1560_;
v_isShared_1579_ = v_isSharedCheck_1596_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_buildTime_1576_);
lean_inc(v_trace_1575_);
lean_inc(v_log_1572_);
lean_dec(v_a_1560_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1596_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
uint8_t v___x_1580_; uint8_t v___x_1581_; lean_object* v___x_1583_; 
v___x_1580_ = 1;
v___x_1581_ = l_Lake_JobAction_merge(v_action_1573_, v___x_1580_);
if (v_isShared_1579_ == 0)
{
v___x_1583_ = v___x_1578_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_log_1572_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_trace_1575_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_buildTime_1576_);
lean_ctor_set_uint8(v_reuseFailAlloc_1595_, sizeof(void*)*3 + 1, v_wantsRebuild_1574_);
v___x_1583_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1584_; 
lean_ctor_set_uint8(v___x_1583_, sizeof(void*)*3, v___x_1581_);
v___x_1584_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_1554_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v___x_1583_);
lean_dec_ref(v_log_1554_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 1);
lean_inc(v_a_1585_);
lean_dec_ref(v___x_1584_);
v___y_1565_ = v_a_1585_;
goto v___jp_1564_;
}
else
{
lean_object* v_a_1586_; lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_del_object(v___x_1562_);
lean_dec(v_a_1559_);
v_a_1586_ = lean_ctor_get(v___x_1584_, 0);
v_a_1587_ = lean_ctor_get(v___x_1584_, 1);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1584_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_inc(v_a_1586_);
lean_dec(v___x_1584_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1586_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_log_1554_);
v___y_1565_ = v_a_1560_;
goto v___jp_1564_;
}
v___jp_1564_:
{
lean_object* v___x_1567_; 
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 1, v___y_1565_);
v___x_1567_ = v___x_1562_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1559_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v___y_1565_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
}
}
else
{
lean_object* v_toBuildConfig_1600_; uint8_t v_oldMode_1601_; 
lean_dec(v_savedTrace_1540_);
lean_dec_ref(v_inst_1536_);
v_toBuildConfig_1600_ = lean_ctor_get(v_a_1546_, 0);
v_oldMode_1601_ = lean_ctor_get_uint8(v_toBuildConfig_1600_, sizeof(void*)*2);
if (v_oldMode_1601_ == 0)
{
uint8_t v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_dec(v_info_1538_);
lean_dec_ref(v_inst_1537_);
v___x_1602_ = 0;
v___x_1603_ = lean_box(v___x_1602_);
v___x_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set(v___x_1604_, 1, v_a_1547_);
return v___x_1604_;
}
else
{
uint8_t v___x_1605_; 
v___x_1605_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1537_, v_info_1538_, v_oldTrace_1541_);
if (v___x_1605_ == 0)
{
uint8_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1606_ = 0;
v___x_1607_ = lean_box(v___x_1606_);
v___x_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
lean_ctor_set(v___x_1608_, 1, v_a_1547_);
return v___x_1608_;
}
else
{
uint8_t v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1609_ = 1;
v___x_1610_ = lean_box(v___x_1609_);
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
lean_ctor_set(v___x_1611_, 1, v_a_1547_);
return v___x_1611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg___boxed(lean_object* v_inst_1612_, lean_object* v_inst_1613_, lean_object* v_info_1614_, lean_object* v_depTrace_1615_, lean_object* v_savedTrace_1616_, lean_object* v_oldTrace_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1612_, v_inst_1613_, v_info_1614_, v_depTrace_1615_, v_savedTrace_1616_, v_oldTrace_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
lean_dec_ref(v_oldTrace_1617_);
lean_dec_ref(v_depTrace_1615_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27(lean_object* v_00_u03b9_1626_, lean_object* v_inst_1627_, lean_object* v_inst_1628_, lean_object* v_info_1629_, lean_object* v_depTrace_1630_, lean_object* v_savedTrace_1631_, lean_object* v_oldTrace_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1627_, v_inst_1628_, v_info_1629_, v_depTrace_1630_, v_savedTrace_1631_, v_oldTrace_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___boxed(lean_object* v_00_u03b9_1641_, lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_info_1644_, lean_object* v_depTrace_1645_, lean_object* v_savedTrace_1646_, lean_object* v_oldTrace_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lake_SavedTrace_replayIfUpToDate_x27(v_00_u03b9_1641_, v_inst_1642_, v_inst_1643_, v_info_1644_, v_depTrace_1645_, v_savedTrace_1646_, v_oldTrace_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec_ref(v_oldTrace_1647_);
lean_dec_ref(v_depTrace_1645_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg(lean_object* v_inst_1656_, lean_object* v_inst_1657_, lean_object* v_info_1658_, lean_object* v_depTrace_1659_, lean_object* v_savedTrace_1660_, lean_object* v_oldTrace_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1656_, v_inst_1657_, v_info_1658_, v_depTrace_1659_, v_savedTrace_1660_, v_oldTrace_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1688_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
v_a_1671_ = lean_ctor_get(v___x_1669_, 1);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1673_ = v___x_1669_;
v_isShared_1674_ = v_isSharedCheck_1688_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_inc(v_a_1670_);
lean_dec(v___x_1669_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1688_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
uint8_t v___x_1675_; uint8_t v___x_1676_; uint8_t v___x_1677_; 
v___x_1675_ = 0;
v___x_1676_ = lean_unbox(v_a_1670_);
lean_dec(v_a_1670_);
v___x_1677_ = l_Lake_instDecidableEqOutputStatus(v___x_1676_, v___x_1675_);
if (v___x_1677_ == 0)
{
uint8_t v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1678_ = 1;
v___x_1679_ = lean_box(v___x_1678_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1679_);
v___x_1681_ = v___x_1673_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_a_1671_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
else
{
uint8_t v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1683_ = 0;
v___x_1684_ = lean_box(v___x_1683_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1684_);
v___x_1686_ = v___x_1673_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_a_1671_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
v_a_1689_ = lean_ctor_get(v___x_1669_, 0);
v_a_1690_ = lean_ctor_get(v___x_1669_, 1);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1669_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_inc(v_a_1689_);
lean_dec(v___x_1669_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1689_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg___boxed(lean_object* v_inst_1698_, lean_object* v_inst_1699_, lean_object* v_info_1700_, lean_object* v_depTrace_1701_, lean_object* v_savedTrace_1702_, lean_object* v_oldTrace_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lake_SavedTrace_replayIfUpToDate___redArg(v_inst_1698_, v_inst_1699_, v_info_1700_, v_depTrace_1701_, v_savedTrace_1702_, v_oldTrace_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec(v_a_1706_);
lean_dec(v_a_1705_);
lean_dec_ref(v_a_1704_);
lean_dec_ref(v_oldTrace_1703_);
lean_dec_ref(v_depTrace_1701_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate(lean_object* v_00_u03b9_1712_, lean_object* v_inst_1713_, lean_object* v_inst_1714_, lean_object* v_info_1715_, lean_object* v_depTrace_1716_, lean_object* v_savedTrace_1717_, lean_object* v_oldTrace_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1713_, v_inst_1714_, v_info_1715_, v_depTrace_1716_, v_savedTrace_1717_, v_oldTrace_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1745_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
v_a_1728_ = lean_ctor_get(v___x_1726_, 1);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1730_ = v___x_1726_;
v_isShared_1731_ = v_isSharedCheck_1745_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_inc(v_a_1727_);
lean_dec(v___x_1726_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1745_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
uint8_t v___x_1732_; uint8_t v___x_1733_; uint8_t v___x_1734_; 
v___x_1732_ = 0;
v___x_1733_ = lean_unbox(v_a_1727_);
lean_dec(v_a_1727_);
v___x_1734_ = l_Lake_instDecidableEqOutputStatus(v___x_1733_, v___x_1732_);
if (v___x_1734_ == 0)
{
uint8_t v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1738_; 
v___x_1735_ = 1;
v___x_1736_ = lean_box(v___x_1735_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1736_);
v___x_1738_ = v___x_1730_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_a_1728_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
else
{
uint8_t v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1743_; 
v___x_1740_ = 0;
v___x_1741_ = lean_box(v___x_1740_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1741_);
v___x_1743_ = v___x_1730_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1741_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_a_1728_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
else
{
lean_object* v_a_1746_; lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
v_a_1746_ = lean_ctor_get(v___x_1726_, 0);
v_a_1747_ = lean_ctor_get(v___x_1726_, 1);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1726_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_inc(v_a_1746_);
lean_dec(v___x_1726_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1746_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___boxed(lean_object* v_00_u03b9_1755_, lean_object* v_inst_1756_, lean_object* v_inst_1757_, lean_object* v_info_1758_, lean_object* v_depTrace_1759_, lean_object* v_savedTrace_1760_, lean_object* v_oldTrace_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lake_SavedTrace_replayIfUpToDate(v_00_u03b9_1755_, v_inst_1756_, v_inst_1757_, v_info_1758_, v_depTrace_1759_, v_savedTrace_1760_, v_oldTrace_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_);
lean_dec_ref(v_a_1766_);
lean_dec(v_a_1765_);
lean_dec(v_a_1764_);
lean_dec(v_a_1763_);
lean_dec_ref(v_a_1762_);
lean_dec_ref(v_oldTrace_1761_);
lean_dec_ref(v_depTrace_1759_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(uint64_t v_inputHash_1770_, lean_object* v_self_1771_, lean_object* v_a_1772_){
_start:
{
lean_object* v___y_1775_; 
if (lean_obj_tag(v_self_1771_) == 2)
{
lean_object* v_data_1793_; uint64_t v_depHash_1794_; lean_object* v_log_1795_; uint8_t v_synthetic_1796_; uint8_t v___x_1797_; lean_object* v___y_1799_; lean_object* v___y_1803_; 
v_data_1793_ = lean_ctor_get(v_self_1771_, 0);
v_depHash_1794_ = lean_ctor_get_uint64(v_data_1793_, sizeof(void*)*3);
v_log_1795_ = lean_ctor_get(v_data_1793_, 2);
v_synthetic_1796_ = lean_ctor_get_uint8(v_data_1793_, sizeof(void*)*3 + 8);
v___x_1797_ = lean_uint64_dec_eq(v_depHash_1794_, v_inputHash_1770_);
if (v___x_1797_ == 0)
{
v___y_1775_ = v_a_1772_;
goto v___jp_1774_;
}
else
{
if (v_synthetic_1796_ == 0)
{
goto v___jp_1814_;
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1840_ = lean_array_get_size(v_log_1795_);
v___x_1841_ = lean_unsigned_to_nat(0u);
v___x_1842_ = lean_nat_dec_eq(v___x_1840_, v___x_1841_);
if (v___x_1842_ == 0)
{
goto v___jp_1814_;
}
else
{
lean_object* v_log_1843_; uint8_t v_action_1844_; uint8_t v_wantsRebuild_1845_; lean_object* v_trace_1846_; lean_object* v_buildTime_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1856_; 
v_log_1843_ = lean_ctor_get(v_a_1772_, 0);
v_action_1844_ = lean_ctor_get_uint8(v_a_1772_, sizeof(void*)*3);
v_wantsRebuild_1845_ = lean_ctor_get_uint8(v_a_1772_, sizeof(void*)*3 + 1);
v_trace_1846_ = lean_ctor_get(v_a_1772_, 1);
v_buildTime_1847_ = lean_ctor_get(v_a_1772_, 2);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_a_1772_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1849_ = v_a_1772_;
v_isShared_1850_ = v_isSharedCheck_1856_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_buildTime_1847_);
lean_inc(v_trace_1846_);
lean_inc(v_log_1843_);
lean_dec(v_a_1772_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1856_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
uint8_t v___x_1851_; uint8_t v___x_1852_; lean_object* v___x_1854_; 
v___x_1851_ = 2;
v___x_1852_ = l_Lake_JobAction_merge(v_action_1844_, v___x_1851_);
if (v_isShared_1850_ == 0)
{
v___x_1854_ = v___x_1849_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_log_1843_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v_trace_1846_);
lean_ctor_set(v_reuseFailAlloc_1855_, 2, v_buildTime_1847_);
lean_ctor_set_uint8(v_reuseFailAlloc_1855_, sizeof(void*)*3 + 1, v_wantsRebuild_1845_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_ctor_set_uint8(v___x_1854_, sizeof(void*)*3, v___x_1852_);
v___y_1799_ = v___x_1854_;
goto v___jp_1798_;
}
}
}
}
}
v___jp_1798_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = lean_box(v___x_1797_);
v___x_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v___y_1799_);
return v___x_1801_;
}
v___jp_1802_:
{
if (lean_obj_tag(v___y_1803_) == 0)
{
lean_object* v_a_1804_; 
v_a_1804_ = lean_ctor_get(v___y_1803_, 1);
lean_inc(v_a_1804_);
lean_dec_ref(v___y_1803_);
v___y_1799_ = v_a_1804_;
goto v___jp_1798_;
}
else
{
lean_object* v_a_1805_; lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
v_a_1805_ = lean_ctor_get(v___y_1803_, 0);
v_a_1806_ = lean_ctor_get(v___y_1803_, 1);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___y_1803_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___y_1803_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_inc(v_a_1805_);
lean_dec(v___y_1803_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1805_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
v___jp_1814_:
{
lean_object* v_log_1815_; uint8_t v_action_1816_; uint8_t v_wantsRebuild_1817_; lean_object* v_trace_1818_; lean_object* v_buildTime_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1839_; 
v_log_1815_ = lean_ctor_get(v_a_1772_, 0);
v_action_1816_ = lean_ctor_get_uint8(v_a_1772_, sizeof(void*)*3);
v_wantsRebuild_1817_ = lean_ctor_get_uint8(v_a_1772_, sizeof(void*)*3 + 1);
v_trace_1818_ = lean_ctor_get(v_a_1772_, 1);
v_buildTime_1819_ = lean_ctor_get(v_a_1772_, 2);
v_isSharedCheck_1839_ = !lean_is_exclusive(v_a_1772_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1821_ = v_a_1772_;
v_isShared_1822_ = v_isSharedCheck_1839_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_buildTime_1819_);
lean_inc(v_trace_1818_);
lean_inc(v_log_1815_);
lean_dec(v_a_1772_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1839_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
uint8_t v___x_1823_; uint8_t v___x_1824_; lean_object* v___x_1826_; 
v___x_1823_ = 1;
v___x_1824_ = l_Lake_JobAction_merge(v_action_1816_, v___x_1823_);
if (v_isShared_1822_ == 0)
{
v___x_1826_ = v___x_1821_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_log_1815_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_trace_1818_);
lean_ctor_set(v_reuseFailAlloc_1838_, 2, v_buildTime_1819_);
lean_ctor_set_uint8(v_reuseFailAlloc_1838_, sizeof(void*)*3 + 1, v_wantsRebuild_1817_);
v___x_1826_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
lean_ctor_set_uint8(v___x_1826_, sizeof(void*)*3, v___x_1824_);
v___x_1827_ = lean_unsigned_to_nat(0u);
v___x_1828_ = lean_array_get_size(v_log_1795_);
v___x_1829_ = lean_nat_dec_lt(v___x_1827_, v___x_1828_);
if (v___x_1829_ == 0)
{
v___y_1799_ = v___x_1826_;
goto v___jp_1798_;
}
else
{
lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1830_ = lean_box(0);
v___x_1831_ = lean_nat_dec_le(v___x_1828_, v___x_1828_);
if (v___x_1831_ == 0)
{
if (v___x_1829_ == 0)
{
v___y_1799_ = v___x_1826_;
goto v___jp_1798_;
}
else
{
size_t v___x_1832_; size_t v___x_1833_; lean_object* v___x_1834_; 
v___x_1832_ = ((size_t)0ULL);
v___x_1833_ = lean_usize_of_nat(v___x_1828_);
v___x_1834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1795_, v___x_1832_, v___x_1833_, v___x_1830_, v___x_1826_);
v___y_1803_ = v___x_1834_;
goto v___jp_1802_;
}
}
else
{
size_t v___x_1835_; size_t v___x_1836_; lean_object* v___x_1837_; 
v___x_1835_ = ((size_t)0ULL);
v___x_1836_ = lean_usize_of_nat(v___x_1828_);
v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1795_, v___x_1835_, v___x_1836_, v___x_1830_, v___x_1826_);
v___y_1803_ = v___x_1837_;
goto v___jp_1802_;
}
}
}
}
}
}
else
{
v___y_1775_ = v_a_1772_;
goto v___jp_1774_;
}
v___jp_1774_:
{
lean_object* v_log_1776_; uint8_t v_action_1777_; uint8_t v_wantsRebuild_1778_; lean_object* v_trace_1779_; lean_object* v_buildTime_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1792_; 
v_log_1776_ = lean_ctor_get(v___y_1775_, 0);
v_action_1777_ = lean_ctor_get_uint8(v___y_1775_, sizeof(void*)*3);
v_wantsRebuild_1778_ = lean_ctor_get_uint8(v___y_1775_, sizeof(void*)*3 + 1);
v_trace_1779_ = lean_ctor_get(v___y_1775_, 1);
v_buildTime_1780_ = lean_ctor_get(v___y_1775_, 2);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___y_1775_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1782_ = v___y_1775_;
v_isShared_1783_ = v_isSharedCheck_1792_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_buildTime_1780_);
lean_inc(v_trace_1779_);
lean_inc(v_log_1776_);
lean_dec(v___y_1775_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1792_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
uint8_t v___x_1784_; uint8_t v___x_1785_; lean_object* v___x_1787_; 
v___x_1784_ = 2;
v___x_1785_ = l_Lake_JobAction_merge(v_action_1777_, v___x_1784_);
if (v_isShared_1783_ == 0)
{
v___x_1787_ = v___x_1782_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_log_1776_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_trace_1779_);
lean_ctor_set(v_reuseFailAlloc_1791_, 2, v_buildTime_1780_);
lean_ctor_set_uint8(v_reuseFailAlloc_1791_, sizeof(void*)*3 + 1, v_wantsRebuild_1778_);
v___x_1787_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
uint8_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_ctor_set_uint8(v___x_1787_, sizeof(void*)*3, v___x_1785_);
v___x_1788_ = 0;
v___x_1789_ = lean_box(v___x_1788_);
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
lean_ctor_set(v___x_1790_, 1, v___x_1787_);
return v___x_1790_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg___boxed(lean_object* v_inputHash_1857_, lean_object* v_self_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
uint64_t v_inputHash_boxed_1861_; lean_object* v_res_1862_; 
v_inputHash_boxed_1861_ = lean_unbox_uint64(v_inputHash_1857_);
lean_dec_ref(v_inputHash_1857_);
v_res_1862_ = l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(v_inputHash_boxed_1861_, v_self_1858_, v_a_1859_);
lean_dec(v_self_1858_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate(uint64_t v_inputHash_1863_, lean_object* v_self_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(v_inputHash_1863_, v_self_1864_, v_a_1870_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___boxed(lean_object* v_inputHash_1873_, lean_object* v_self_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_){
_start:
{
uint64_t v_inputHash_boxed_1882_; lean_object* v_res_1883_; 
v_inputHash_boxed_1882_ = lean_unbox_uint64(v_inputHash_1873_);
lean_dec_ref(v_inputHash_1873_);
v_res_1883_ = l_Lake_SavedTrace_replayOrFetchIfUpToDate(v_inputHash_boxed_1882_, v_self_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
lean_dec_ref(v_a_1879_);
lean_dec(v_a_1878_);
lean_dec(v_a_1877_);
lean_dec(v_a_1876_);
lean_dec_ref(v_a_1875_);
lean_dec(v_self_1874_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonPUnit___lam__0(lean_object* v_x_1884_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_box(0);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0(lean_object* v_x_1889_){
_start:
{
lean_object* v_descr_1890_; uint64_t v_hash_1891_; lean_object* v_ext_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; 
v_descr_1890_ = lean_ctor_get(v_x_1889_, 0);
v_hash_1891_ = lean_ctor_get_uint64(v_descr_1890_, sizeof(void*)*1);
v_ext_1892_ = lean_ctor_get(v_descr_1890_, 0);
v___x_1893_ = lean_string_utf8_byte_size(v_ext_1892_);
v___x_1894_ = lean_unsigned_to_nat(0u);
v___x_1895_ = lean_nat_dec_eq(v___x_1893_, v___x_1894_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1896_ = l_Lake_Hash_hex(v_hash_1891_);
v___x_1897_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_1898_ = lean_string_append(v___x_1896_, v___x_1897_);
v___x_1899_ = lean_string_append(v___x_1898_, v_ext_1892_);
v___x_1900_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
return v___x_1900_;
}
else
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = l_Lake_Hash_hex(v_hash_1891_);
v___x_1902_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
return v___x_1902_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0___boxed(lean_object* v_x_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Lake_instToOutputJsonArtifact___lam__0(v_x_1903_);
lean_dec_ref(v_x_1903_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0(lean_object* v_val_1907_, lean_object* v_a_x3f_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v___x_1911_; lean_object* v_log_1912_; uint8_t v_action_1913_; uint8_t v_wantsRebuild_1914_; lean_object* v_trace_1915_; lean_object* v_buildTime_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1927_; 
v___x_1911_ = lean_io_mono_ms_now();
v_log_1912_ = lean_ctor_get(v___y_1909_, 0);
v_action_1913_ = lean_ctor_get_uint8(v___y_1909_, sizeof(void*)*3);
v_wantsRebuild_1914_ = lean_ctor_get_uint8(v___y_1909_, sizeof(void*)*3 + 1);
v_trace_1915_ = lean_ctor_get(v___y_1909_, 1);
v_buildTime_1916_ = lean_ctor_get(v___y_1909_, 2);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___y_1909_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1918_ = v___y_1909_;
v_isShared_1919_ = v_isSharedCheck_1927_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_buildTime_1916_);
lean_inc(v_trace_1915_);
lean_inc(v_log_1912_);
lean_dec(v___y_1909_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1927_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1924_; 
v___x_1920_ = lean_nat_sub(v___x_1911_, v_val_1907_);
lean_dec(v___x_1911_);
v___x_1921_ = lean_box(0);
v___x_1922_ = lean_nat_add(v_buildTime_1916_, v___x_1920_);
lean_dec(v___x_1920_);
lean_dec(v_buildTime_1916_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 2, v___x_1922_);
v___x_1924_ = v___x_1918_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_log_1912_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v_trace_1915_);
lean_ctor_set(v_reuseFailAlloc_1926_, 2, v___x_1922_);
lean_ctor_set_uint8(v_reuseFailAlloc_1926_, sizeof(void*)*3, v_action_1913_);
lean_ctor_set_uint8(v_reuseFailAlloc_1926_, sizeof(void*)*3 + 1, v_wantsRebuild_1914_);
v___x_1924_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_object* v___x_1925_; 
v___x_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1921_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
return v___x_1925_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0___boxed(lean_object* v_val_1928_, lean_object* v_a_x3f_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lake_buildAction___redArg___lam__0(v_val_1928_, v_a_x3f_1929_, v___y_1930_);
lean_dec(v_a_x3f_1929_);
lean_dec(v_val_1928_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg(lean_object* v_inst_1938_, lean_object* v_depTrace_1939_, lean_object* v_traceFile_1940_, lean_object* v_build_1941_, uint8_t v_action_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v_a_1951_; lean_object* v_a_1952_; lean_object* v_log_1955_; uint8_t v_action_1956_; uint8_t v_wantsRebuild_1957_; lean_object* v_trace_1958_; lean_object* v_buildTime_1959_; lean_object* v_toBuildConfig_1965_; lean_object* v_log_1966_; uint8_t v_action_1967_; uint8_t v_wantsRebuild_1968_; lean_object* v_trace_1969_; lean_object* v_buildTime_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2076_; 
v_toBuildConfig_1965_ = lean_ctor_get(v_a_1947_, 0);
v_log_1966_ = lean_ctor_get(v_a_1948_, 0);
v_action_1967_ = lean_ctor_get_uint8(v_a_1948_, sizeof(void*)*3);
v_wantsRebuild_1968_ = lean_ctor_get_uint8(v_a_1948_, sizeof(void*)*3 + 1);
v_trace_1969_ = lean_ctor_get(v_a_1948_, 1);
v_buildTime_1970_ = lean_ctor_get(v_a_1948_, 2);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_a_1948_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_1972_ = v_a_1948_;
v_isShared_1973_ = v_isSharedCheck_2076_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_buildTime_1970_);
lean_inc(v_trace_1969_);
lean_inc(v_log_1966_);
lean_dec(v_a_1948_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2076_;
goto v_resetjp_1971_;
}
v___jp_1950_:
{
lean_object* v___x_1953_; 
v___x_1953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1953_, 0, v_a_1951_);
lean_ctor_set(v___x_1953_, 1, v_a_1952_);
return v___x_1953_;
}
v___jp_1954_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1960_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_1961_ = lean_array_get_size(v_log_1955_);
v___x_1962_ = lean_array_push(v_log_1955_, v___x_1960_);
v___x_1963_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
lean_ctor_set(v___x_1963_, 1, v_trace_1958_);
lean_ctor_set(v___x_1963_, 2, v_buildTime_1959_);
lean_ctor_set_uint8(v___x_1963_, sizeof(void*)*3, v_action_1956_);
lean_ctor_set_uint8(v___x_1963_, sizeof(void*)*3 + 1, v_wantsRebuild_1957_);
v___x_1964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1961_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
return v___x_1964_;
}
v_resetjp_1971_:
{
uint8_t v_noBuild_1974_; uint8_t v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v_noBuild_1974_ = lean_ctor_get_uint8(v_toBuildConfig_1965_, sizeof(void*)*2 + 2);
v___x_1975_ = l_Lake_JobAction_merge(v_action_1967_, v_action_1942_);
v___x_1976_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_1940_);
v___x_1977_ = l_System_FilePath_addExtension(v_traceFile_1940_, v___x_1976_);
if (v_noBuild_1974_ == 0)
{
lean_object* v___x_1978_; lean_object* v___x_1980_; 
v___x_1978_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_1966_);
if (v_isShared_1973_ == 0)
{
v___x_1980_ = v___x_1972_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_log_1966_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v_trace_1969_);
lean_ctor_set(v_reuseFailAlloc_2060_, 2, v_buildTime_1970_);
lean_ctor_set_uint8(v_reuseFailAlloc_2060_, sizeof(void*)*3 + 1, v_wantsRebuild_1968_);
v___x_1980_ = v_reuseFailAlloc_2060_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
lean_object* v___x_1981_; lean_object* v_a_1983_; lean_object* v_a_1984_; 
lean_ctor_set_uint8(v___x_1980_, sizeof(void*)*3, v___x_1975_);
lean_inc_ref(v_a_1947_);
lean_inc(v_a_1946_);
lean_inc(v_a_1945_);
lean_inc(v_a_1944_);
v___x_1981_ = lean_apply_7(v_build_1941_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v___x_1980_, lean_box(0));
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1988_; lean_object* v_a_1989_; lean_object* v_log_1990_; uint8_t v_action_1991_; uint8_t v_wantsRebuild_1992_; lean_object* v_trace_1993_; lean_object* v_buildTime_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v_a_1988_ = lean_ctor_get(v___x_1981_, 1);
lean_inc(v_a_1988_);
v_a_1989_ = lean_ctor_get(v___x_1981_, 0);
lean_inc_n(v_a_1989_, 2);
lean_dec_ref(v___x_1981_);
v_log_1990_ = lean_ctor_get(v_a_1988_, 0);
v_action_1991_ = lean_ctor_get_uint8(v_a_1988_, sizeof(void*)*3);
v_wantsRebuild_1992_ = lean_ctor_get_uint8(v_a_1988_, sizeof(void*)*3 + 1);
v_trace_1993_ = lean_ctor_get(v_a_1988_, 1);
v_buildTime_1994_ = lean_ctor_get(v_a_1988_, 2);
v___x_1995_ = lean_array_get_size(v_log_1966_);
lean_dec_ref(v_log_1966_);
v___x_1996_ = lean_array_get_size(v_log_1990_);
v___x_1997_ = l_Array_extract___redArg(v_log_1990_, v___x_1995_, v___x_1996_);
v___x_1998_ = lean_apply_1(v_inst_1938_, v_a_1989_);
v___x_1999_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1939_, v___x_1998_, v___x_1997_);
v___x_2000_ = l_Lake_BuildMetadata_writeFile(v_traceFile_1940_, v___x_1999_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2041_; 
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2041_ == 0)
{
lean_object* v_unused_2042_; 
v_unused_2042_ = lean_ctor_get(v___x_2000_, 0);
lean_dec(v_unused_2042_);
v___x_2002_ = v___x_2000_;
v_isShared_2003_ = v_isSharedCheck_2041_;
goto v_resetjp_2001_;
}
else
{
lean_dec(v___x_2000_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2041_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lake_removeFileIfExists(v___x_1977_);
lean_dec_ref(v___x_1977_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2024_; 
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2024_ == 0)
{
lean_object* v_unused_2025_; 
v_unused_2025_ = lean_ctor_get(v___x_2004_, 0);
lean_dec(v_unused_2025_);
v___x_2006_ = v___x_2004_;
v_isShared_2007_ = v_isSharedCheck_2024_;
goto v_resetjp_2005_;
}
else
{
lean_dec(v___x_2004_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2024_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
lean_inc(v_a_1989_);
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 0, v_a_1989_);
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_1989_);
v___x_2009_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2011_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set_tag(v___x_2002_, 1);
lean_ctor_set(v___x_2002_, 0, v___x_2009_);
v___x_2011_ = v___x_2002_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2009_);
v___x_2011_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2012_; lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
v___x_2012_ = l_Lake_buildAction___redArg___lam__0(v___x_1978_, v___x_2011_, v_a_1988_);
lean_dec_ref(v___x_2011_);
lean_dec(v___x_1978_);
v_a_2013_ = lean_ctor_get(v___x_2012_, 1);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2020_ == 0)
{
lean_object* v_unused_2021_; 
v_unused_2021_ = lean_ctor_get(v___x_2012_, 0);
lean_dec(v_unused_2021_);
v___x_2015_ = v___x_2012_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2012_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v_a_1989_);
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_1989_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
}
else
{
lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2037_; 
lean_inc(v_buildTime_1994_);
lean_inc_ref(v_trace_1993_);
lean_inc_ref(v_log_1990_);
lean_del_object(v___x_2002_);
lean_dec(v_a_1989_);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_a_1988_);
if (v_isSharedCheck_2037_ == 0)
{
lean_object* v_unused_2038_; lean_object* v_unused_2039_; lean_object* v_unused_2040_; 
v_unused_2038_ = lean_ctor_get(v_a_1988_, 2);
lean_dec(v_unused_2038_);
v_unused_2039_ = lean_ctor_get(v_a_1988_, 1);
lean_dec(v_unused_2039_);
v_unused_2040_ = lean_ctor_get(v_a_1988_, 0);
lean_dec(v_unused_2040_);
v___x_2027_ = v_a_1988_;
v_isShared_2028_ = v_isSharedCheck_2037_;
goto v_resetjp_2026_;
}
else
{
lean_dec(v_a_1988_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2037_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v_a_2029_; lean_object* v___x_2030_; uint8_t v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2035_; 
v_a_2029_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2029_);
lean_dec_ref(v___x_2004_);
v___x_2030_ = lean_io_error_to_string(v_a_2029_);
v___x_2031_ = 3;
v___x_2032_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2032_, 0, v___x_2030_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*1, v___x_2031_);
v___x_2033_ = lean_array_push(v_log_1990_, v___x_2032_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 0, v___x_2033_);
v___x_2035_ = v___x_2027_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2033_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v_trace_1993_);
lean_ctor_set(v_reuseFailAlloc_2036_, 2, v_buildTime_1994_);
lean_ctor_set_uint8(v_reuseFailAlloc_2036_, sizeof(void*)*3, v_action_1991_);
lean_ctor_set_uint8(v_reuseFailAlloc_2036_, sizeof(void*)*3 + 1, v_wantsRebuild_1992_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
v_a_1983_ = v___x_1996_;
v_a_1984_ = v___x_2035_;
goto v___jp_1982_;
}
}
}
}
}
else
{
lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2054_; 
lean_inc(v_buildTime_1994_);
lean_inc_ref(v_trace_1993_);
lean_inc_ref(v_log_1990_);
lean_dec(v_a_1989_);
lean_dec_ref(v___x_1977_);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_a_1988_);
if (v_isSharedCheck_2054_ == 0)
{
lean_object* v_unused_2055_; lean_object* v_unused_2056_; lean_object* v_unused_2057_; 
v_unused_2055_ = lean_ctor_get(v_a_1988_, 2);
lean_dec(v_unused_2055_);
v_unused_2056_ = lean_ctor_get(v_a_1988_, 1);
lean_dec(v_unused_2056_);
v_unused_2057_ = lean_ctor_get(v_a_1988_, 0);
lean_dec(v_unused_2057_);
v___x_2044_ = v_a_1988_;
v_isShared_2045_ = v_isSharedCheck_2054_;
goto v_resetjp_2043_;
}
else
{
lean_dec(v_a_1988_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2054_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v_a_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2052_; 
v_a_2046_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2046_);
lean_dec_ref(v___x_2000_);
v___x_2047_ = lean_io_error_to_string(v_a_2046_);
v___x_2048_ = 3;
v___x_2049_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2049_, 0, v___x_2047_);
lean_ctor_set_uint8(v___x_2049_, sizeof(void*)*1, v___x_2048_);
v___x_2050_ = lean_array_push(v_log_1990_, v___x_2049_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 0, v___x_2050_);
v___x_2052_ = v___x_2044_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_trace_1993_);
lean_ctor_set(v_reuseFailAlloc_2053_, 2, v_buildTime_1994_);
lean_ctor_set_uint8(v_reuseFailAlloc_2053_, sizeof(void*)*3, v_action_1991_);
lean_ctor_set_uint8(v_reuseFailAlloc_2053_, sizeof(void*)*3 + 1, v_wantsRebuild_1992_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
v_a_1983_ = v___x_1996_;
v_a_1984_ = v___x_2052_;
goto v___jp_1982_;
}
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v_a_2059_; 
lean_dec_ref(v___x_1977_);
lean_dec_ref(v_log_1966_);
lean_dec_ref(v_traceFile_1940_);
lean_dec_ref(v_inst_1938_);
v_a_2058_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_2058_);
v_a_2059_ = lean_ctor_get(v___x_1981_, 1);
lean_inc(v_a_2059_);
lean_dec_ref(v___x_1981_);
v_a_1983_ = v_a_2058_;
v_a_1984_ = v_a_2059_;
goto v___jp_1982_;
}
v___jp_1982_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v_a_1987_; 
v___x_1985_ = lean_box(0);
v___x_1986_ = l_Lake_buildAction___redArg___lam__0(v___x_1978_, v___x_1985_, v_a_1984_);
lean_dec(v___x_1978_);
v_a_1987_ = lean_ctor_get(v___x_1986_, 1);
lean_inc(v_a_1987_);
lean_dec_ref(v___x_1986_);
v_a_1951_ = v_a_1983_;
v_a_1952_ = v_a_1987_;
goto v___jp_1950_;
}
}
}
else
{
uint8_t v___x_2061_; 
lean_dec_ref(v_a_1943_);
lean_dec_ref(v_build_1941_);
lean_dec_ref(v_inst_1938_);
v___x_2061_ = l_System_FilePath_pathExists(v_traceFile_1940_);
lean_dec_ref(v_traceFile_1940_);
if (v___x_2061_ == 0)
{
lean_dec_ref(v___x_1977_);
lean_del_object(v___x_1972_);
v_log_1955_ = v_log_1966_;
v_action_1956_ = v___x_1975_;
v_wantsRebuild_1957_ = v_noBuild_1974_;
v_trace_1958_ = v_trace_1969_;
v_buildTime_1959_ = v_buildTime_1970_;
goto v___jp_1954_;
}
else
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2062_ = lean_box(0);
v___x_2063_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_2064_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1939_, v___x_2062_, v___x_2063_);
v___x_2065_ = l_Lake_BuildMetadata_writeFile(v___x_1977_, v___x_2064_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_dec_ref(v___x_2065_);
lean_del_object(v___x_1972_);
v_log_1955_ = v_log_1966_;
v_action_1956_ = v___x_1975_;
v_wantsRebuild_1957_ = v_noBuild_1974_;
v_trace_1958_ = v_trace_1969_;
v_buildTime_1959_ = v_buildTime_1970_;
goto v___jp_1954_;
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2073_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
lean_dec_ref(v___x_2065_);
v___x_2067_ = lean_io_error_to_string(v_a_2066_);
v___x_2068_ = 3;
v___x_2069_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2069_, 0, v___x_2067_);
lean_ctor_set_uint8(v___x_2069_, sizeof(void*)*1, v___x_2068_);
v___x_2070_ = lean_array_get_size(v_log_1966_);
v___x_2071_ = lean_array_push(v_log_1966_, v___x_2069_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_2071_);
v___x_2073_ = v___x_1972_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2071_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_trace_1969_);
lean_ctor_set(v_reuseFailAlloc_2075_, 2, v_buildTime_1970_);
v___x_2073_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
lean_object* v___x_2074_; 
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3, v___x_1975_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 1, v_noBuild_1974_);
v___x_2074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2070_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
return v___x_2074_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___boxed(lean_object* v_inst_2077_, lean_object* v_depTrace_2078_, lean_object* v_traceFile_2079_, lean_object* v_build_2080_, lean_object* v_action_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_){
_start:
{
uint8_t v_action_boxed_2089_; lean_object* v_res_2090_; 
v_action_boxed_2089_ = lean_unbox(v_action_2081_);
v_res_2090_ = l_Lake_buildAction___redArg(v_inst_2077_, v_depTrace_2078_, v_traceFile_2079_, v_build_2080_, v_action_boxed_2089_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
lean_dec_ref(v_a_2086_);
lean_dec(v_a_2085_);
lean_dec(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec_ref(v_depTrace_2078_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction(lean_object* v_00_u03b1_2091_, lean_object* v_inst_2092_, lean_object* v_depTrace_2093_, lean_object* v_traceFile_2094_, lean_object* v_build_2095_, uint8_t v_action_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = l_Lake_buildAction___redArg(v_inst_2092_, v_depTrace_2093_, v_traceFile_2094_, v_build_2095_, v_action_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___boxed(lean_object* v_00_u03b1_2105_, lean_object* v_inst_2106_, lean_object* v_depTrace_2107_, lean_object* v_traceFile_2108_, lean_object* v_build_2109_, lean_object* v_action_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_){
_start:
{
uint8_t v_action_boxed_2118_; lean_object* v_res_2119_; 
v_action_boxed_2118_ = lean_unbox(v_action_2110_);
v_res_2119_ = l_Lake_buildAction(v_00_u03b1_2105_, v_inst_2106_, v_depTrace_2107_, v_traceFile_2108_, v_build_2109_, v_action_boxed_2118_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
lean_dec_ref(v_a_2115_);
lean_dec(v_a_2114_);
lean_dec(v_a_2113_);
lean_dec(v_a_2112_);
lean_dec_ref(v_depTrace_2107_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg(lean_object* v_inst_2120_, lean_object* v_inst_2121_, lean_object* v_info_2122_, lean_object* v_depTrace_2123_, lean_object* v_traceFile_2124_, lean_object* v_build_2125_, uint8_t v_action_2126_, lean_object* v_oldTrace_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_){
_start:
{
lean_object* v_log_2135_; uint8_t v_action_2136_; uint8_t v_wantsRebuild_2137_; lean_object* v_trace_2138_; lean_object* v_buildTime_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2207_; 
v_log_2135_ = lean_ctor_get(v_a_2133_, 0);
v_action_2136_ = lean_ctor_get_uint8(v_a_2133_, sizeof(void*)*3);
v_wantsRebuild_2137_ = lean_ctor_get_uint8(v_a_2133_, sizeof(void*)*3 + 1);
v_trace_2138_ = lean_ctor_get(v_a_2133_, 1);
v_buildTime_2139_ = lean_ctor_get(v_a_2133_, 2);
v_isSharedCheck_2207_ = !lean_is_exclusive(v_a_2133_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2141_ = v_a_2133_;
v_isShared_2142_ = v_isSharedCheck_2207_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_buildTime_2139_);
lean_inc(v_trace_2138_);
lean_inc(v_log_2135_);
lean_dec(v_a_2133_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2207_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2143_; 
lean_inc_ref(v_traceFile_2124_);
v___x_2143_ = l_Lake_readTraceFile(v_traceFile_2124_, v_log_2135_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v_a_2145_; lean_object* v___x_2147_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
v_a_2145_ = lean_ctor_get(v___x_2143_, 1);
lean_inc(v_a_2145_);
lean_dec_ref(v___x_2143_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 0, v_a_2145_);
v___x_2147_ = v___x_2141_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2145_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v_trace_2138_);
lean_ctor_set(v_reuseFailAlloc_2194_, 2, v_buildTime_2139_);
lean_ctor_set_uint8(v_reuseFailAlloc_2194_, sizeof(void*)*3, v_action_2136_);
lean_ctor_set_uint8(v_reuseFailAlloc_2194_, sizeof(void*)*3 + 1, v_wantsRebuild_2137_);
v___x_2147_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
lean_object* v___x_2148_; 
v___x_2148_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2120_, v_inst_2121_, v_info_2122_, v_depTrace_2123_, v_a_2144_, v_oldTrace_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v___x_2147_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2184_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
v_a_2150_ = lean_ctor_get(v___x_2148_, 1);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2152_ = v___x_2148_;
v_isShared_2153_ = v_isSharedCheck_2184_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_inc(v_a_2149_);
lean_dec(v___x_2148_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2184_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
uint8_t v___x_2154_; uint8_t v___x_2155_; uint8_t v___x_2156_; 
v___x_2154_ = 0;
v___x_2155_ = lean_unbox(v_a_2149_);
lean_dec(v_a_2149_);
v___x_2156_ = l_Lake_instDecidableEqOutputStatus(v___x_2155_, v___x_2154_);
if (v___x_2156_ == 0)
{
uint8_t v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2160_; 
lean_dec_ref(v_a_2128_);
lean_dec_ref(v_build_2125_);
lean_dec_ref(v_traceFile_2124_);
v___x_2157_ = 1;
v___x_2158_ = lean_box(v___x_2157_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2158_);
v___x_2160_ = v___x_2152_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_a_2150_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
else
{
lean_object* v___f_2162_; lean_object* v___x_2163_; 
lean_del_object(v___x_2152_);
v___f_2162_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2163_ = l_Lake_buildAction___redArg(v___f_2162_, v_depTrace_2123_, v_traceFile_2124_, v_build_2125_, v_action_2126_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2150_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2173_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 1);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2173_ == 0)
{
lean_object* v_unused_2174_; 
v_unused_2174_ = lean_ctor_get(v___x_2163_, 0);
lean_dec(v_unused_2174_);
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2173_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2173_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
uint8_t v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2171_; 
v___x_2168_ = 0;
v___x_2169_ = lean_box(v___x_2168_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2169_);
v___x_2171_ = v___x_2166_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_a_2164_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
else
{
lean_object* v_a_2175_; lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
v_a_2175_ = lean_ctor_get(v___x_2163_, 0);
v_a_2176_ = lean_ctor_get(v___x_2163_, 1);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2163_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_inc(v_a_2175_);
lean_dec(v___x_2163_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2175_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
}
}
else
{
lean_object* v_a_2185_; lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec_ref(v_a_2128_);
lean_dec_ref(v_build_2125_);
lean_dec_ref(v_traceFile_2124_);
v_a_2185_ = lean_ctor_get(v___x_2148_, 0);
v_a_2186_ = lean_ctor_get(v___x_2148_, 1);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2148_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_inc(v_a_2185_);
lean_dec(v___x_2148_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2185_);
lean_ctor_set(v_reuseFailAlloc_2192_, 1, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
}
else
{
lean_object* v_a_2195_; lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2206_; 
lean_dec_ref(v_a_2128_);
lean_dec_ref(v_build_2125_);
lean_dec_ref(v_traceFile_2124_);
lean_dec(v_info_2122_);
lean_dec_ref(v_inst_2121_);
lean_dec_ref(v_inst_2120_);
v_a_2195_ = lean_ctor_get(v___x_2143_, 0);
v_a_2196_ = lean_ctor_get(v___x_2143_, 1);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2198_ = v___x_2143_;
v_isShared_2199_ = v_isSharedCheck_2206_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_inc(v_a_2195_);
lean_dec(v___x_2143_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2206_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 0, v_a_2196_);
v___x_2201_ = v___x_2141_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2196_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v_trace_2138_);
lean_ctor_set(v_reuseFailAlloc_2205_, 2, v_buildTime_2139_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, sizeof(void*)*3, v_action_2136_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, sizeof(void*)*3 + 1, v_wantsRebuild_2137_);
v___x_2201_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2203_; 
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 1, v___x_2201_);
v___x_2203_ = v___x_2198_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2195_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v___x_2201_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg___boxed(lean_object* v_inst_2208_, lean_object* v_inst_2209_, lean_object* v_info_2210_, lean_object* v_depTrace_2211_, lean_object* v_traceFile_2212_, lean_object* v_build_2213_, lean_object* v_action_2214_, lean_object* v_oldTrace_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_){
_start:
{
uint8_t v_action_boxed_2223_; lean_object* v_res_2224_; 
v_action_boxed_2223_ = lean_unbox(v_action_2214_);
v_res_2224_ = l_Lake_buildUnlessUpToDate_x3f___redArg(v_inst_2208_, v_inst_2209_, v_info_2210_, v_depTrace_2211_, v_traceFile_2212_, v_build_2213_, v_action_boxed_2223_, v_oldTrace_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec_ref(v_oldTrace_2215_);
lean_dec_ref(v_depTrace_2211_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f(lean_object* v_00_u03b9_2225_, lean_object* v_inst_2226_, lean_object* v_inst_2227_, lean_object* v_info_2228_, lean_object* v_depTrace_2229_, lean_object* v_traceFile_2230_, lean_object* v_build_2231_, uint8_t v_action_2232_, lean_object* v_oldTrace_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_){
_start:
{
lean_object* v_log_2241_; uint8_t v_action_2242_; uint8_t v_wantsRebuild_2243_; lean_object* v_trace_2244_; lean_object* v_buildTime_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2313_; 
v_log_2241_ = lean_ctor_get(v_a_2239_, 0);
v_action_2242_ = lean_ctor_get_uint8(v_a_2239_, sizeof(void*)*3);
v_wantsRebuild_2243_ = lean_ctor_get_uint8(v_a_2239_, sizeof(void*)*3 + 1);
v_trace_2244_ = lean_ctor_get(v_a_2239_, 1);
v_buildTime_2245_ = lean_ctor_get(v_a_2239_, 2);
v_isSharedCheck_2313_ = !lean_is_exclusive(v_a_2239_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2247_ = v_a_2239_;
v_isShared_2248_ = v_isSharedCheck_2313_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_buildTime_2245_);
lean_inc(v_trace_2244_);
lean_inc(v_log_2241_);
lean_dec(v_a_2239_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2313_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2249_; 
lean_inc_ref(v_traceFile_2230_);
v___x_2249_ = l_Lake_readTraceFile(v_traceFile_2230_, v_log_2241_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v_a_2251_; lean_object* v___x_2253_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_a_2250_);
v_a_2251_ = lean_ctor_get(v___x_2249_, 1);
lean_inc(v_a_2251_);
lean_dec_ref(v___x_2249_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v_a_2251_);
v___x_2253_ = v___x_2247_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2251_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_trace_2244_);
lean_ctor_set(v_reuseFailAlloc_2300_, 2, v_buildTime_2245_);
lean_ctor_set_uint8(v_reuseFailAlloc_2300_, sizeof(void*)*3, v_action_2242_);
lean_ctor_set_uint8(v_reuseFailAlloc_2300_, sizeof(void*)*3 + 1, v_wantsRebuild_2243_);
v___x_2253_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
lean_object* v___x_2254_; 
v___x_2254_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2226_, v_inst_2227_, v_info_2228_, v_depTrace_2229_, v_a_2250_, v_oldTrace_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v___x_2253_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2290_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
v_a_2256_ = lean_ctor_get(v___x_2254_, 1);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2258_ = v___x_2254_;
v_isShared_2259_ = v_isSharedCheck_2290_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_inc(v_a_2255_);
lean_dec(v___x_2254_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2290_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
uint8_t v___x_2260_; uint8_t v___x_2261_; uint8_t v___x_2262_; 
v___x_2260_ = 0;
v___x_2261_ = lean_unbox(v_a_2255_);
lean_dec(v_a_2255_);
v___x_2262_ = l_Lake_instDecidableEqOutputStatus(v___x_2261_, v___x_2260_);
if (v___x_2262_ == 0)
{
uint8_t v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2266_; 
lean_dec_ref(v_a_2234_);
lean_dec_ref(v_build_2231_);
lean_dec_ref(v_traceFile_2230_);
v___x_2263_ = 1;
v___x_2264_ = lean_box(v___x_2263_);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 0, v___x_2264_);
v___x_2266_ = v___x_2258_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2264_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v_a_2256_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
else
{
lean_object* v___f_2268_; lean_object* v___x_2269_; 
lean_del_object(v___x_2258_);
v___f_2268_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2269_ = l_Lake_buildAction___redArg(v___f_2268_, v_depTrace_2229_, v_traceFile_2230_, v_build_2231_, v_action_2232_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2256_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2279_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 1);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2279_ == 0)
{
lean_object* v_unused_2280_; 
v_unused_2280_ = lean_ctor_get(v___x_2269_, 0);
lean_dec(v_unused_2280_);
v___x_2272_ = v___x_2269_;
v_isShared_2273_ = v_isSharedCheck_2279_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2269_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2279_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
uint8_t v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2277_; 
v___x_2274_ = 0;
v___x_2275_ = lean_box(v___x_2274_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 0, v___x_2275_);
v___x_2277_ = v___x_2272_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2275_);
lean_ctor_set(v_reuseFailAlloc_2278_, 1, v_a_2270_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
else
{
lean_object* v_a_2281_; lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
v_a_2281_ = lean_ctor_get(v___x_2269_, 0);
v_a_2282_ = lean_ctor_get(v___x_2269_, 1);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2269_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_inc(v_a_2281_);
lean_dec(v___x_2269_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2281_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
}
}
else
{
lean_object* v_a_2291_; lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec_ref(v_a_2234_);
lean_dec_ref(v_build_2231_);
lean_dec_ref(v_traceFile_2230_);
v_a_2291_ = lean_ctor_get(v___x_2254_, 0);
v_a_2292_ = lean_ctor_get(v___x_2254_, 1);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2254_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_inc(v_a_2291_);
lean_dec(v___x_2254_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2291_);
lean_ctor_set(v_reuseFailAlloc_2298_, 1, v_a_2292_);
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
lean_object* v_a_2301_; lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2312_; 
lean_dec_ref(v_a_2234_);
lean_dec_ref(v_build_2231_);
lean_dec_ref(v_traceFile_2230_);
lean_dec(v_info_2228_);
lean_dec_ref(v_inst_2227_);
lean_dec_ref(v_inst_2226_);
v_a_2301_ = lean_ctor_get(v___x_2249_, 0);
v_a_2302_ = lean_ctor_get(v___x_2249_, 1);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2304_ = v___x_2249_;
v_isShared_2305_ = v_isSharedCheck_2312_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_inc(v_a_2301_);
lean_dec(v___x_2249_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2312_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v_a_2302_);
v___x_2307_ = v___x_2247_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2302_);
lean_ctor_set(v_reuseFailAlloc_2311_, 1, v_trace_2244_);
lean_ctor_set(v_reuseFailAlloc_2311_, 2, v_buildTime_2245_);
lean_ctor_set_uint8(v_reuseFailAlloc_2311_, sizeof(void*)*3, v_action_2242_);
lean_ctor_set_uint8(v_reuseFailAlloc_2311_, sizeof(void*)*3 + 1, v_wantsRebuild_2243_);
v___x_2307_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
lean_object* v___x_2309_; 
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 1, v___x_2307_);
v___x_2309_ = v___x_2304_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2301_);
lean_ctor_set(v_reuseFailAlloc_2310_, 1, v___x_2307_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___boxed(lean_object* v_00_u03b9_2314_, lean_object* v_inst_2315_, lean_object* v_inst_2316_, lean_object* v_info_2317_, lean_object* v_depTrace_2318_, lean_object* v_traceFile_2319_, lean_object* v_build_2320_, lean_object* v_action_2321_, lean_object* v_oldTrace_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_){
_start:
{
uint8_t v_action_boxed_2330_; lean_object* v_res_2331_; 
v_action_boxed_2330_ = lean_unbox(v_action_2321_);
v_res_2331_ = l_Lake_buildUnlessUpToDate_x3f(v_00_u03b9_2314_, v_inst_2315_, v_inst_2316_, v_info_2317_, v_depTrace_2318_, v_traceFile_2319_, v_build_2320_, v_action_boxed_2330_, v_oldTrace_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec_ref(v_a_2327_);
lean_dec(v_a_2326_);
lean_dec(v_a_2325_);
lean_dec(v_a_2324_);
lean_dec_ref(v_oldTrace_2322_);
lean_dec_ref(v_depTrace_2318_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg(lean_object* v_inst_2332_, lean_object* v_inst_2333_, lean_object* v_info_2334_, lean_object* v_depTrace_2335_, lean_object* v_traceFile_2336_, lean_object* v_build_2337_, uint8_t v_action_2338_, lean_object* v_oldTrace_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_){
_start:
{
lean_object* v_a_2348_; lean_object* v_a_2349_; lean_object* v_log_2351_; uint8_t v_action_2352_; uint8_t v_wantsRebuild_2353_; lean_object* v_trace_2354_; lean_object* v_buildTime_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2393_; 
v_log_2351_ = lean_ctor_get(v_a_2345_, 0);
v_action_2352_ = lean_ctor_get_uint8(v_a_2345_, sizeof(void*)*3);
v_wantsRebuild_2353_ = lean_ctor_get_uint8(v_a_2345_, sizeof(void*)*3 + 1);
v_trace_2354_ = lean_ctor_get(v_a_2345_, 1);
v_buildTime_2355_ = lean_ctor_get(v_a_2345_, 2);
v_isSharedCheck_2393_ = !lean_is_exclusive(v_a_2345_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2357_ = v_a_2345_;
v_isShared_2358_ = v_isSharedCheck_2393_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_buildTime_2355_);
lean_inc(v_trace_2354_);
lean_inc(v_log_2351_);
lean_dec(v_a_2345_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2393_;
goto v_resetjp_2356_;
}
v___jp_2347_:
{
lean_object* v___x_2350_; 
v___x_2350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2350_, 0, v_a_2348_);
lean_ctor_set(v___x_2350_, 1, v_a_2349_);
return v___x_2350_;
}
v_resetjp_2356_:
{
lean_object* v___x_2359_; 
lean_inc_ref(v_traceFile_2336_);
v___x_2359_ = l_Lake_readTraceFile(v_traceFile_2336_, v_log_2351_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v_a_2361_; lean_object* v___x_2363_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2360_);
v_a_2361_ = lean_ctor_get(v___x_2359_, 1);
lean_inc(v_a_2361_);
lean_dec_ref(v___x_2359_);
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v_a_2361_);
v___x_2363_ = v___x_2357_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2361_);
lean_ctor_set(v_reuseFailAlloc_2387_, 1, v_trace_2354_);
lean_ctor_set(v_reuseFailAlloc_2387_, 2, v_buildTime_2355_);
lean_ctor_set_uint8(v_reuseFailAlloc_2387_, sizeof(void*)*3, v_action_2352_);
lean_ctor_set_uint8(v_reuseFailAlloc_2387_, sizeof(void*)*3 + 1, v_wantsRebuild_2353_);
v___x_2363_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2364_; 
v___x_2364_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2332_, v_inst_2333_, v_info_2334_, v_depTrace_2335_, v_a_2360_, v_oldTrace_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v___x_2363_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2384_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
v_a_2366_ = lean_ctor_get(v___x_2364_, 1);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2368_ = v___x_2364_;
v_isShared_2369_ = v_isSharedCheck_2384_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_inc(v_a_2365_);
lean_dec(v___x_2364_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2384_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2370_; lean_object* v_a_2372_; uint8_t v___x_2376_; uint8_t v___x_2377_; uint8_t v___x_2378_; 
v___x_2370_ = lean_box(0);
v___x_2376_ = 0;
v___x_2377_ = lean_unbox(v_a_2365_);
lean_dec(v_a_2365_);
v___x_2378_ = l_Lake_instDecidableEqOutputStatus(v___x_2377_, v___x_2376_);
if (v___x_2378_ == 0)
{
lean_dec_ref(v_a_2340_);
lean_dec_ref(v_build_2337_);
lean_dec_ref(v_traceFile_2336_);
v_a_2372_ = v_a_2366_;
goto v___jp_2371_;
}
else
{
lean_object* v___f_2379_; lean_object* v___x_2380_; 
v___f_2379_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2380_ = l_Lake_buildAction___redArg(v___f_2379_, v_depTrace_2335_, v_traceFile_2336_, v_build_2337_, v_action_2338_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2366_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 1);
lean_inc(v_a_2381_);
lean_dec_ref(v___x_2380_);
v_a_2372_ = v_a_2381_;
goto v___jp_2371_;
}
else
{
lean_object* v_a_2382_; lean_object* v_a_2383_; 
lean_del_object(v___x_2368_);
v_a_2382_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2382_);
v_a_2383_ = lean_ctor_get(v___x_2380_, 1);
lean_inc(v_a_2383_);
lean_dec_ref(v___x_2380_);
v_a_2348_ = v_a_2382_;
v_a_2349_ = v_a_2383_;
goto v___jp_2347_;
}
}
v___jp_2371_:
{
lean_object* v___x_2374_; 
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 1, v_a_2372_);
lean_ctor_set(v___x_2368_, 0, v___x_2370_);
v___x_2374_ = v___x_2368_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2370_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v_a_2372_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
else
{
lean_object* v_a_2385_; lean_object* v_a_2386_; 
lean_dec_ref(v_a_2340_);
lean_dec_ref(v_build_2337_);
lean_dec_ref(v_traceFile_2336_);
v_a_2385_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_a_2385_);
v_a_2386_ = lean_ctor_get(v___x_2364_, 1);
lean_inc(v_a_2386_);
lean_dec_ref(v___x_2364_);
v_a_2348_ = v_a_2385_;
v_a_2349_ = v_a_2386_;
goto v___jp_2347_;
}
}
}
else
{
lean_object* v_a_2388_; lean_object* v_a_2389_; lean_object* v___x_2391_; 
lean_dec_ref(v_a_2340_);
lean_dec_ref(v_build_2337_);
lean_dec_ref(v_traceFile_2336_);
lean_dec(v_info_2334_);
lean_dec_ref(v_inst_2333_);
lean_dec_ref(v_inst_2332_);
v_a_2388_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2388_);
v_a_2389_ = lean_ctor_get(v___x_2359_, 1);
lean_inc(v_a_2389_);
lean_dec_ref(v___x_2359_);
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v_a_2389_);
v___x_2391_ = v___x_2357_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2389_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v_trace_2354_);
lean_ctor_set(v_reuseFailAlloc_2392_, 2, v_buildTime_2355_);
lean_ctor_set_uint8(v_reuseFailAlloc_2392_, sizeof(void*)*3, v_action_2352_);
lean_ctor_set_uint8(v_reuseFailAlloc_2392_, sizeof(void*)*3 + 1, v_wantsRebuild_2353_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
v_a_2348_ = v_a_2388_;
v_a_2349_ = v___x_2391_;
goto v___jp_2347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg___boxed(lean_object* v_inst_2394_, lean_object* v_inst_2395_, lean_object* v_info_2396_, lean_object* v_depTrace_2397_, lean_object* v_traceFile_2398_, lean_object* v_build_2399_, lean_object* v_action_2400_, lean_object* v_oldTrace_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
uint8_t v_action_boxed_2409_; lean_object* v_res_2410_; 
v_action_boxed_2409_ = lean_unbox(v_action_2400_);
v_res_2410_ = l_Lake_buildUnlessUpToDate___redArg(v_inst_2394_, v_inst_2395_, v_info_2396_, v_depTrace_2397_, v_traceFile_2398_, v_build_2399_, v_action_boxed_2409_, v_oldTrace_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
lean_dec_ref(v_a_2406_);
lean_dec(v_a_2405_);
lean_dec(v_a_2404_);
lean_dec(v_a_2403_);
lean_dec_ref(v_oldTrace_2401_);
lean_dec_ref(v_depTrace_2397_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate(lean_object* v_00_u03b9_2411_, lean_object* v_inst_2412_, lean_object* v_inst_2413_, lean_object* v_info_2414_, lean_object* v_depTrace_2415_, lean_object* v_traceFile_2416_, lean_object* v_build_2417_, uint8_t v_action_2418_, lean_object* v_oldTrace_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v_a_2428_; lean_object* v_a_2429_; lean_object* v_log_2431_; uint8_t v_action_2432_; uint8_t v_wantsRebuild_2433_; lean_object* v_trace_2434_; lean_object* v_buildTime_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2473_; 
v_log_2431_ = lean_ctor_get(v_a_2425_, 0);
v_action_2432_ = lean_ctor_get_uint8(v_a_2425_, sizeof(void*)*3);
v_wantsRebuild_2433_ = lean_ctor_get_uint8(v_a_2425_, sizeof(void*)*3 + 1);
v_trace_2434_ = lean_ctor_get(v_a_2425_, 1);
v_buildTime_2435_ = lean_ctor_get(v_a_2425_, 2);
v_isSharedCheck_2473_ = !lean_is_exclusive(v_a_2425_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2437_ = v_a_2425_;
v_isShared_2438_ = v_isSharedCheck_2473_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_buildTime_2435_);
lean_inc(v_trace_2434_);
lean_inc(v_log_2431_);
lean_dec(v_a_2425_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2473_;
goto v_resetjp_2436_;
}
v___jp_2427_:
{
lean_object* v___x_2430_; 
v___x_2430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2430_, 0, v_a_2428_);
lean_ctor_set(v___x_2430_, 1, v_a_2429_);
return v___x_2430_;
}
v_resetjp_2436_:
{
lean_object* v___x_2439_; 
lean_inc_ref(v_traceFile_2416_);
v___x_2439_ = l_Lake_readTraceFile(v_traceFile_2416_, v_log_2431_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v_a_2440_; lean_object* v_a_2441_; lean_object* v___x_2443_; 
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_a_2440_);
v_a_2441_ = lean_ctor_get(v___x_2439_, 1);
lean_inc(v_a_2441_);
lean_dec_ref(v___x_2439_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 0, v_a_2441_);
v___x_2443_ = v___x_2437_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2441_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v_trace_2434_);
lean_ctor_set(v_reuseFailAlloc_2467_, 2, v_buildTime_2435_);
lean_ctor_set_uint8(v_reuseFailAlloc_2467_, sizeof(void*)*3, v_action_2432_);
lean_ctor_set_uint8(v_reuseFailAlloc_2467_, sizeof(void*)*3 + 1, v_wantsRebuild_2433_);
v___x_2443_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2412_, v_inst_2413_, v_info_2414_, v_depTrace_2415_, v_a_2440_, v_oldTrace_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v___x_2443_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v_a_2445_; lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2464_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
v_a_2446_ = lean_ctor_get(v___x_2444_, 1);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2448_ = v___x_2444_;
v_isShared_2449_ = v_isSharedCheck_2464_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_inc(v_a_2445_);
lean_dec(v___x_2444_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2464_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2450_; lean_object* v_a_2452_; uint8_t v___x_2456_; uint8_t v___x_2457_; uint8_t v___x_2458_; 
v___x_2450_ = lean_box(0);
v___x_2456_ = 0;
v___x_2457_ = lean_unbox(v_a_2445_);
lean_dec(v_a_2445_);
v___x_2458_ = l_Lake_instDecidableEqOutputStatus(v___x_2457_, v___x_2456_);
if (v___x_2458_ == 0)
{
lean_dec_ref(v_a_2420_);
lean_dec_ref(v_build_2417_);
lean_dec_ref(v_traceFile_2416_);
v_a_2452_ = v_a_2446_;
goto v___jp_2451_;
}
else
{
lean_object* v___f_2459_; lean_object* v___x_2460_; 
v___f_2459_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2460_ = l_Lake_buildAction___redArg(v___f_2459_, v_depTrace_2415_, v_traceFile_2416_, v_build_2417_, v_action_2418_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2446_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 1);
lean_inc(v_a_2461_);
lean_dec_ref(v___x_2460_);
v_a_2452_ = v_a_2461_;
goto v___jp_2451_;
}
else
{
lean_object* v_a_2462_; lean_object* v_a_2463_; 
lean_del_object(v___x_2448_);
v_a_2462_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_a_2462_);
v_a_2463_ = lean_ctor_get(v___x_2460_, 1);
lean_inc(v_a_2463_);
lean_dec_ref(v___x_2460_);
v_a_2428_ = v_a_2462_;
v_a_2429_ = v_a_2463_;
goto v___jp_2427_;
}
}
v___jp_2451_:
{
lean_object* v___x_2454_; 
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 1, v_a_2452_);
lean_ctor_set(v___x_2448_, 0, v___x_2450_);
v___x_2454_ = v___x_2448_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v___x_2450_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v_a_2452_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
else
{
lean_object* v_a_2465_; lean_object* v_a_2466_; 
lean_dec_ref(v_a_2420_);
lean_dec_ref(v_build_2417_);
lean_dec_ref(v_traceFile_2416_);
v_a_2465_ = lean_ctor_get(v___x_2444_, 0);
lean_inc(v_a_2465_);
v_a_2466_ = lean_ctor_get(v___x_2444_, 1);
lean_inc(v_a_2466_);
lean_dec_ref(v___x_2444_);
v_a_2428_ = v_a_2465_;
v_a_2429_ = v_a_2466_;
goto v___jp_2427_;
}
}
}
else
{
lean_object* v_a_2468_; lean_object* v_a_2469_; lean_object* v___x_2471_; 
lean_dec_ref(v_a_2420_);
lean_dec_ref(v_build_2417_);
lean_dec_ref(v_traceFile_2416_);
lean_dec(v_info_2414_);
lean_dec_ref(v_inst_2413_);
lean_dec_ref(v_inst_2412_);
v_a_2468_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_a_2468_);
v_a_2469_ = lean_ctor_get(v___x_2439_, 1);
lean_inc(v_a_2469_);
lean_dec_ref(v___x_2439_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 0, v_a_2469_);
v___x_2471_ = v___x_2437_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2469_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v_trace_2434_);
lean_ctor_set(v_reuseFailAlloc_2472_, 2, v_buildTime_2435_);
lean_ctor_set_uint8(v_reuseFailAlloc_2472_, sizeof(void*)*3, v_action_2432_);
lean_ctor_set_uint8(v_reuseFailAlloc_2472_, sizeof(void*)*3 + 1, v_wantsRebuild_2433_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
v_a_2428_ = v_a_2468_;
v_a_2429_ = v___x_2471_;
goto v___jp_2427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___boxed(lean_object* v_00_u03b9_2474_, lean_object* v_inst_2475_, lean_object* v_inst_2476_, lean_object* v_info_2477_, lean_object* v_depTrace_2478_, lean_object* v_traceFile_2479_, lean_object* v_build_2480_, lean_object* v_action_2481_, lean_object* v_oldTrace_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_){
_start:
{
uint8_t v_action_boxed_2490_; lean_object* v_res_2491_; 
v_action_boxed_2490_ = lean_unbox(v_action_2481_);
v_res_2491_ = l_Lake_buildUnlessUpToDate(v_00_u03b9_2474_, v_inst_2475_, v_inst_2476_, v_info_2477_, v_depTrace_2478_, v_traceFile_2479_, v_build_2480_, v_action_boxed_2490_, v_oldTrace_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
lean_dec_ref(v_a_2487_);
lean_dec(v_a_2486_);
lean_dec(v_a_2485_);
lean_dec(v_a_2484_);
lean_dec_ref(v_oldTrace_2482_);
lean_dec_ref(v_depTrace_2478_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFileHash(lean_object* v_file_2493_, uint64_t v_hash_2494_){
_start:
{
lean_object* v___x_2496_; lean_object* v_hashFile_2497_; lean_object* v___x_2498_; 
v___x_2496_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
v_hashFile_2497_ = lean_string_append(v_file_2493_, v___x_2496_);
lean_inc_ref(v_hashFile_2497_);
v___x_2498_ = l_Lake_createParentDirs(v_hashFile_2497_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
lean_dec_ref(v___x_2498_);
v___x_2499_ = l_Lake_Hash_hex(v_hash_2494_);
v___x_2500_ = l_IO_FS_writeFile(v_hashFile_2497_, v___x_2499_);
lean_dec_ref(v___x_2499_);
lean_dec_ref(v_hashFile_2497_);
return v___x_2500_;
}
else
{
lean_dec_ref(v_hashFile_2497_);
return v___x_2498_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_writeFileHash___boxed(lean_object* v_file_2501_, lean_object* v_hash_2502_, lean_object* v_a_2503_){
_start:
{
uint64_t v_hash_boxed_2504_; lean_object* v_res_2505_; 
v_hash_boxed_2504_ = lean_unbox_uint64(v_hash_2502_);
lean_dec_ref(v_hash_2502_);
v_res_2505_ = l_Lake_writeFileHash(v_file_2501_, v_hash_boxed_2504_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object* v_file_2506_, uint8_t v_text_2507_){
_start:
{
lean_object* v___y_2510_; 
if (v_text_2507_ == 0)
{
lean_object* v___x_2522_; 
v___x_2522_ = l_Lake_computeBinFileHash(v_file_2506_);
v___y_2510_ = v___x_2522_;
goto v___jp_2509_;
}
else
{
lean_object* v___x_2523_; 
v___x_2523_ = l_Lake_computeTextFileHash(v_file_2506_);
v___y_2510_ = v___x_2523_;
goto v___jp_2509_;
}
v___jp_2509_:
{
if (lean_obj_tag(v___y_2510_) == 0)
{
lean_object* v_a_2511_; uint64_t v___x_2512_; lean_object* v___x_2513_; 
v_a_2511_ = lean_ctor_get(v___y_2510_, 0);
lean_inc(v_a_2511_);
lean_dec_ref(v___y_2510_);
v___x_2512_ = lean_unbox_uint64(v_a_2511_);
lean_dec(v_a_2511_);
v___x_2513_ = l_Lake_writeFileHash(v_file_2506_, v___x_2512_);
return v___x_2513_;
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_dec_ref(v_file_2506_);
v_a_2514_ = lean_ctor_get(v___y_2510_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___y_2510_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___y_2510_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___y_2510_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash___boxed(lean_object* v_file_2524_, lean_object* v_text_2525_, lean_object* v_a_2526_){
_start:
{
uint8_t v_text_boxed_2527_; lean_object* v_res_2528_; 
v_text_boxed_2527_ = lean_unbox(v_text_2525_);
v_res_2528_ = l_Lake_cacheFileHash(v_file_2524_, v_text_boxed_2527_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l_Lake_clearFileHash(lean_object* v_file_2529_){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
v___x_2532_ = lean_string_append(v_file_2529_, v___x_2531_);
v___x_2533_ = l_Lake_removeFileIfExists(v___x_2532_);
lean_dec_ref(v___x_2532_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_Lake_clearFileHash___boxed(lean_object* v_file_2534_, lean_object* v_a_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Lake_clearFileHash(v_file_2534_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg(lean_object* v_file_2537_, uint8_t v_text_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_){
_start:
{
lean_object* v_toBuildConfig_2542_; uint8_t v_trustHash_2543_; lean_object* v___x_2544_; lean_object* v_hashFile_2545_; lean_object* v___y_2547_; lean_object* v___y_2548_; uint8_t v___y_2549_; lean_object* v___y_2550_; uint8_t v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2585_; 
v_toBuildConfig_2542_ = lean_ctor_get(v_a_2539_, 0);
v_trustHash_2543_ = lean_ctor_get_uint8(v_toBuildConfig_2542_, sizeof(void*)*2 + 1);
v___x_2544_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
lean_inc_ref(v_file_2537_);
v_hashFile_2545_ = lean_string_append(v_file_2537_, v___x_2544_);
if (v_trustHash_2543_ == 0)
{
v___y_2585_ = v_a_2540_;
goto v___jp_2584_;
}
else
{
lean_object* v___x_2598_; 
v___x_2598_ = l_Lake_Hash_load_x3f(v_hashFile_2545_);
if (lean_obj_tag(v___x_2598_) == 1)
{
lean_object* v_val_2599_; lean_object* v___x_2600_; 
lean_dec_ref(v_hashFile_2545_);
lean_dec_ref(v_file_2537_);
v_val_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_val_2599_);
lean_dec_ref(v___x_2598_);
v___x_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2600_, 0, v_val_2599_);
lean_ctor_set(v___x_2600_, 1, v_a_2540_);
return v___x_2600_;
}
else
{
lean_dec(v___x_2598_);
v___y_2585_ = v_a_2540_;
goto v___jp_2584_;
}
}
v___jp_2546_:
{
if (lean_obj_tag(v___y_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2554_; 
v_a_2553_ = lean_ctor_get(v___y_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref(v___y_2552_);
lean_inc_ref(v_hashFile_2545_);
v___x_2554_ = l_Lake_createParentDirs(v_hashFile_2545_);
if (lean_obj_tag(v___x_2554_) == 0)
{
uint64_t v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
lean_dec_ref(v___x_2554_);
v___x_2555_ = lean_unbox_uint64(v_a_2553_);
v___x_2556_ = l_Lake_Hash_hex(v___x_2555_);
v___x_2557_ = l_IO_FS_writeFile(v_hashFile_2545_, v___x_2556_);
lean_dec_ref(v___x_2556_);
lean_dec_ref(v_hashFile_2545_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
lean_dec_ref(v___x_2557_);
v___x_2558_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2558_, 0, v___y_2548_);
lean_ctor_set(v___x_2558_, 1, v___y_2547_);
lean_ctor_set(v___x_2558_, 2, v___y_2550_);
lean_ctor_set_uint8(v___x_2558_, sizeof(void*)*3, v___y_2551_);
lean_ctor_set_uint8(v___x_2558_, sizeof(void*)*3 + 1, v___y_2549_);
v___x_2559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2559_, 0, v_a_2553_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
return v___x_2559_;
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2561_; uint8_t v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
lean_dec(v_a_2553_);
v_a_2560_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_a_2560_);
lean_dec_ref(v___x_2557_);
v___x_2561_ = lean_io_error_to_string(v_a_2560_);
v___x_2562_ = 3;
v___x_2563_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2563_, 0, v___x_2561_);
lean_ctor_set_uint8(v___x_2563_, sizeof(void*)*1, v___x_2562_);
v___x_2564_ = lean_array_get_size(v___y_2548_);
v___x_2565_ = lean_array_push(v___y_2548_, v___x_2563_);
v___x_2566_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
lean_ctor_set(v___x_2566_, 1, v___y_2547_);
lean_ctor_set(v___x_2566_, 2, v___y_2550_);
lean_ctor_set_uint8(v___x_2566_, sizeof(void*)*3, v___y_2551_);
lean_ctor_set_uint8(v___x_2566_, sizeof(void*)*3 + 1, v___y_2549_);
v___x_2567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2564_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
return v___x_2567_;
}
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2569_; uint8_t v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
lean_dec(v_a_2553_);
lean_dec_ref(v_hashFile_2545_);
v_a_2568_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_a_2568_);
lean_dec_ref(v___x_2554_);
v___x_2569_ = lean_io_error_to_string(v_a_2568_);
v___x_2570_ = 3;
v___x_2571_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2571_, 0, v___x_2569_);
lean_ctor_set_uint8(v___x_2571_, sizeof(void*)*1, v___x_2570_);
v___x_2572_ = lean_array_get_size(v___y_2548_);
v___x_2573_ = lean_array_push(v___y_2548_, v___x_2571_);
v___x_2574_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2574_, 0, v___x_2573_);
lean_ctor_set(v___x_2574_, 1, v___y_2547_);
lean_ctor_set(v___x_2574_, 2, v___y_2550_);
lean_ctor_set_uint8(v___x_2574_, sizeof(void*)*3, v___y_2551_);
lean_ctor_set_uint8(v___x_2574_, sizeof(void*)*3 + 1, v___y_2549_);
v___x_2575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2572_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
return v___x_2575_;
}
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
lean_dec_ref(v_hashFile_2545_);
v_a_2576_ = lean_ctor_get(v___y_2552_, 0);
lean_inc(v_a_2576_);
lean_dec_ref(v___y_2552_);
v___x_2577_ = lean_io_error_to_string(v_a_2576_);
v___x_2578_ = 3;
v___x_2579_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2579_, 0, v___x_2577_);
lean_ctor_set_uint8(v___x_2579_, sizeof(void*)*1, v___x_2578_);
v___x_2580_ = lean_array_get_size(v___y_2548_);
v___x_2581_ = lean_array_push(v___y_2548_, v___x_2579_);
v___x_2582_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2582_, 0, v___x_2581_);
lean_ctor_set(v___x_2582_, 1, v___y_2547_);
lean_ctor_set(v___x_2582_, 2, v___y_2550_);
lean_ctor_set_uint8(v___x_2582_, sizeof(void*)*3, v___y_2551_);
lean_ctor_set_uint8(v___x_2582_, sizeof(void*)*3 + 1, v___y_2549_);
v___x_2583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2580_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
return v___x_2583_;
}
}
v___jp_2584_:
{
if (v_text_2538_ == 0)
{
lean_object* v_log_2586_; uint8_t v_action_2587_; uint8_t v_wantsRebuild_2588_; lean_object* v_trace_2589_; lean_object* v_buildTime_2590_; lean_object* v___x_2591_; 
v_log_2586_ = lean_ctor_get(v___y_2585_, 0);
lean_inc_ref(v_log_2586_);
v_action_2587_ = lean_ctor_get_uint8(v___y_2585_, sizeof(void*)*3);
v_wantsRebuild_2588_ = lean_ctor_get_uint8(v___y_2585_, sizeof(void*)*3 + 1);
v_trace_2589_ = lean_ctor_get(v___y_2585_, 1);
lean_inc_ref(v_trace_2589_);
v_buildTime_2590_ = lean_ctor_get(v___y_2585_, 2);
lean_inc(v_buildTime_2590_);
lean_dec_ref(v___y_2585_);
v___x_2591_ = l_Lake_computeBinFileHash(v_file_2537_);
lean_dec_ref(v_file_2537_);
v___y_2547_ = v_trace_2589_;
v___y_2548_ = v_log_2586_;
v___y_2549_ = v_wantsRebuild_2588_;
v___y_2550_ = v_buildTime_2590_;
v___y_2551_ = v_action_2587_;
v___y_2552_ = v___x_2591_;
goto v___jp_2546_;
}
else
{
lean_object* v_log_2592_; uint8_t v_action_2593_; uint8_t v_wantsRebuild_2594_; lean_object* v_trace_2595_; lean_object* v_buildTime_2596_; lean_object* v___x_2597_; 
v_log_2592_ = lean_ctor_get(v___y_2585_, 0);
lean_inc_ref(v_log_2592_);
v_action_2593_ = lean_ctor_get_uint8(v___y_2585_, sizeof(void*)*3);
v_wantsRebuild_2594_ = lean_ctor_get_uint8(v___y_2585_, sizeof(void*)*3 + 1);
v_trace_2595_ = lean_ctor_get(v___y_2585_, 1);
lean_inc_ref(v_trace_2595_);
v_buildTime_2596_ = lean_ctor_get(v___y_2585_, 2);
lean_inc(v_buildTime_2596_);
lean_dec_ref(v___y_2585_);
v___x_2597_ = l_Lake_computeTextFileHash(v_file_2537_);
lean_dec_ref(v_file_2537_);
v___y_2547_ = v_trace_2595_;
v___y_2548_ = v_log_2592_;
v___y_2549_ = v_wantsRebuild_2594_;
v___y_2550_ = v_buildTime_2596_;
v___y_2551_ = v_action_2593_;
v___y_2552_ = v___x_2597_;
goto v___jp_2546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg___boxed(lean_object* v_file_2601_, lean_object* v_text_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_){
_start:
{
uint8_t v_text_boxed_2606_; lean_object* v_res_2607_; 
v_text_boxed_2606_ = lean_unbox(v_text_2602_);
v_res_2607_ = l_Lake_fetchFileHash___redArg(v_file_2601_, v_text_boxed_2606_, v_a_2603_, v_a_2604_);
lean_dec_ref(v_a_2603_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash(lean_object* v_file_2608_, uint8_t v_text_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_){
_start:
{
lean_object* v___x_2617_; 
v___x_2617_ = l_Lake_fetchFileHash___redArg(v_file_2608_, v_text_2609_, v_a_2614_, v_a_2615_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___boxed(lean_object* v_file_2618_, lean_object* v_text_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_){
_start:
{
uint8_t v_text_boxed_2627_; lean_object* v_res_2628_; 
v_text_boxed_2627_ = lean_unbox(v_text_2619_);
v_res_2628_ = l_Lake_fetchFileHash(v_file_2618_, v_text_boxed_2627_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_);
lean_dec_ref(v_a_2624_);
lean_dec(v_a_2623_);
lean_dec(v_a_2622_);
lean_dec(v_a_2621_);
lean_dec_ref(v_a_2620_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg(lean_object* v_file_2629_, uint8_t v_text_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_){
_start:
{
lean_object* v___x_2634_; 
lean_inc_ref(v_file_2629_);
v___x_2634_ = l_Lake_fetchFileHash___redArg(v_file_2629_, v_text_2630_, v_a_2631_, v_a_2632_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2673_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 1);
v_a_2636_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2638_ = v___x_2634_;
v_isShared_2639_ = v_isSharedCheck_2673_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2635_);
lean_inc(v_a_2636_);
lean_dec(v___x_2634_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2673_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v_log_2640_; uint8_t v_action_2641_; uint8_t v_wantsRebuild_2642_; lean_object* v_trace_2643_; lean_object* v_buildTime_2644_; lean_object* v___x_2645_; 
v_log_2640_ = lean_ctor_get(v_a_2635_, 0);
v_action_2641_ = lean_ctor_get_uint8(v_a_2635_, sizeof(void*)*3);
v_wantsRebuild_2642_ = lean_ctor_get_uint8(v_a_2635_, sizeof(void*)*3 + 1);
v_trace_2643_ = lean_ctor_get(v_a_2635_, 1);
v_buildTime_2644_ = lean_ctor_get(v_a_2635_, 2);
v___x_2645_ = lean_io_metadata(v_file_2629_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; lean_object* v_modified_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; uint64_t v___x_2650_; lean_object* v___x_2652_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2646_);
lean_dec_ref(v___x_2645_);
v_modified_2647_ = lean_ctor_get(v_a_2646_, 1);
lean_inc_ref(v_modified_2647_);
lean_dec(v_a_2646_);
v___x_2648_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_2649_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_2649_, 0, v_file_2629_);
lean_ctor_set(v___x_2649_, 1, v___x_2648_);
lean_ctor_set(v___x_2649_, 2, v_modified_2647_);
v___x_2650_ = lean_unbox_uint64(v_a_2636_);
lean_dec(v_a_2636_);
lean_ctor_set_uint64(v___x_2649_, sizeof(void*)*3, v___x_2650_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 0, v___x_2649_);
v___x_2652_ = v___x_2638_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2649_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v_a_2635_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
else
{
lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2669_; 
lean_inc(v_buildTime_2644_);
lean_inc_ref(v_trace_2643_);
lean_inc_ref(v_log_2640_);
lean_dec(v_a_2636_);
lean_dec_ref(v_file_2629_);
v_isSharedCheck_2669_ = !lean_is_exclusive(v_a_2635_);
if (v_isSharedCheck_2669_ == 0)
{
lean_object* v_unused_2670_; lean_object* v_unused_2671_; lean_object* v_unused_2672_; 
v_unused_2670_ = lean_ctor_get(v_a_2635_, 2);
lean_dec(v_unused_2670_);
v_unused_2671_ = lean_ctor_get(v_a_2635_, 1);
lean_dec(v_unused_2671_);
v_unused_2672_ = lean_ctor_get(v_a_2635_, 0);
lean_dec(v_unused_2672_);
v___x_2655_ = v_a_2635_;
v_isShared_2656_ = v_isSharedCheck_2669_;
goto v_resetjp_2654_;
}
else
{
lean_dec(v_a_2635_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2669_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v_a_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2664_; 
v_a_2657_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2657_);
lean_dec_ref(v___x_2645_);
v___x_2658_ = lean_io_error_to_string(v_a_2657_);
v___x_2659_ = 3;
v___x_2660_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2660_, 0, v___x_2658_);
lean_ctor_set_uint8(v___x_2660_, sizeof(void*)*1, v___x_2659_);
v___x_2661_ = lean_array_get_size(v_log_2640_);
v___x_2662_ = lean_array_push(v_log_2640_, v___x_2660_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 0, v___x_2662_);
v___x_2664_ = v___x_2655_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2662_);
lean_ctor_set(v_reuseFailAlloc_2668_, 1, v_trace_2643_);
lean_ctor_set(v_reuseFailAlloc_2668_, 2, v_buildTime_2644_);
lean_ctor_set_uint8(v_reuseFailAlloc_2668_, sizeof(void*)*3, v_action_2641_);
lean_ctor_set_uint8(v_reuseFailAlloc_2668_, sizeof(void*)*3 + 1, v_wantsRebuild_2642_);
v___x_2664_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v___x_2666_; 
if (v_isShared_2639_ == 0)
{
lean_ctor_set_tag(v___x_2638_, 1);
lean_ctor_set(v___x_2638_, 1, v___x_2664_);
lean_ctor_set(v___x_2638_, 0, v___x_2661_);
v___x_2666_ = v___x_2638_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2667_, 1, v___x_2664_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
}
}
else
{
lean_object* v_a_2674_; lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec_ref(v_file_2629_);
v_a_2674_ = lean_ctor_get(v___x_2634_, 0);
v_a_2675_ = lean_ctor_get(v___x_2634_, 1);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2634_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_inc(v_a_2674_);
lean_dec(v___x_2634_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2674_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg___boxed(lean_object* v_file_2683_, lean_object* v_text_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_){
_start:
{
uint8_t v_text_boxed_2688_; lean_object* v_res_2689_; 
v_text_boxed_2688_ = lean_unbox(v_text_2684_);
v_res_2689_ = l_Lake_fetchFileTrace___redArg(v_file_2683_, v_text_boxed_2688_, v_a_2685_, v_a_2686_);
lean_dec_ref(v_a_2685_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object* v_file_2690_, uint8_t v_text_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v___x_2699_; 
v___x_2699_ = l_Lake_fetchFileTrace___redArg(v_file_2690_, v_text_2691_, v_a_2696_, v_a_2697_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object* v_file_2700_, lean_object* v_text_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_){
_start:
{
uint8_t v_text_boxed_2709_; lean_object* v_res_2710_; 
v_text_boxed_2709_ = lean_unbox(v_text_2701_);
v_res_2710_ = l_Lake_fetchFileTrace(v_file_2700_, v_text_boxed_2709_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
lean_dec_ref(v_a_2706_);
lean_dec(v_a_2705_);
lean_dec(v_a_2704_);
lean_dec(v_a_2703_);
lean_dec_ref(v_a_2702_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(lean_object* v_val_2711_, lean_object* v_a_x3f_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v___x_2715_; lean_object* v_log_2716_; uint8_t v_action_2717_; uint8_t v_wantsRebuild_2718_; lean_object* v_trace_2719_; lean_object* v_buildTime_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2731_; 
v___x_2715_ = lean_io_mono_ms_now();
v_log_2716_ = lean_ctor_get(v___y_2713_, 0);
v_action_2717_ = lean_ctor_get_uint8(v___y_2713_, sizeof(void*)*3);
v_wantsRebuild_2718_ = lean_ctor_get_uint8(v___y_2713_, sizeof(void*)*3 + 1);
v_trace_2719_ = lean_ctor_get(v___y_2713_, 1);
v_buildTime_2720_ = lean_ctor_get(v___y_2713_, 2);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___y_2713_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2722_ = v___y_2713_;
v_isShared_2723_ = v_isSharedCheck_2731_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_buildTime_2720_);
lean_inc(v_trace_2719_);
lean_inc(v_log_2716_);
lean_dec(v___y_2713_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2731_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2728_; 
v___x_2724_ = lean_nat_sub(v___x_2715_, v_val_2711_);
lean_dec(v___x_2715_);
v___x_2725_ = lean_box(0);
v___x_2726_ = lean_nat_add(v_buildTime_2720_, v___x_2724_);
lean_dec(v___x_2724_);
lean_dec(v_buildTime_2720_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 2, v___x_2726_);
v___x_2728_ = v___x_2722_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_log_2716_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v_trace_2719_);
lean_ctor_set(v_reuseFailAlloc_2730_, 2, v___x_2726_);
lean_ctor_set_uint8(v_reuseFailAlloc_2730_, sizeof(void*)*3, v_action_2717_);
lean_ctor_set_uint8(v_reuseFailAlloc_2730_, sizeof(void*)*3 + 1, v_wantsRebuild_2718_);
v___x_2728_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
lean_object* v___x_2729_; 
v___x_2729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2725_);
lean_ctor_set(v___x_2729_, 1, v___x_2728_);
return v___x_2729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0___boxed(lean_object* v_val_2732_, lean_object* v_a_x3f_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v_val_2732_, v_a_x3f_2733_, v___y_2734_);
lean_dec(v_a_x3f_2733_);
lean_dec(v_val_2732_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(lean_object* v_build_2737_, lean_object* v_file_2738_, lean_object* v_a_2739_, lean_object* v_depTrace_2740_, lean_object* v_traceFile_2741_, uint8_t v_action_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_){
_start:
{
lean_object* v_a_2750_; lean_object* v_a_2751_; lean_object* v_log_2754_; uint8_t v_action_2755_; uint8_t v_wantsRebuild_2756_; lean_object* v_trace_2757_; lean_object* v_buildTime_2758_; lean_object* v_toBuildConfig_2764_; lean_object* v_log_2765_; uint8_t v_action_2766_; uint8_t v_wantsRebuild_2767_; lean_object* v_trace_2768_; lean_object* v_buildTime_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2892_; 
v_toBuildConfig_2764_ = lean_ctor_get(v_a_2746_, 0);
v_log_2765_ = lean_ctor_get(v_a_2747_, 0);
v_action_2766_ = lean_ctor_get_uint8(v_a_2747_, sizeof(void*)*3);
v_wantsRebuild_2767_ = lean_ctor_get_uint8(v_a_2747_, sizeof(void*)*3 + 1);
v_trace_2768_ = lean_ctor_get(v_a_2747_, 1);
v_buildTime_2769_ = lean_ctor_get(v_a_2747_, 2);
v_isSharedCheck_2892_ = !lean_is_exclusive(v_a_2747_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2771_ = v_a_2747_;
v_isShared_2772_ = v_isSharedCheck_2892_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_buildTime_2769_);
lean_inc(v_trace_2768_);
lean_inc(v_log_2765_);
lean_dec(v_a_2747_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2892_;
goto v_resetjp_2770_;
}
v___jp_2749_:
{
lean_object* v___x_2752_; 
v___x_2752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2752_, 0, v_a_2750_);
lean_ctor_set(v___x_2752_, 1, v_a_2751_);
return v___x_2752_;
}
v___jp_2753_:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2759_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_2760_ = lean_array_get_size(v_log_2754_);
v___x_2761_ = lean_array_push(v_log_2754_, v___x_2759_);
v___x_2762_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2762_, 0, v___x_2761_);
lean_ctor_set(v___x_2762_, 1, v_trace_2757_);
lean_ctor_set(v___x_2762_, 2, v_buildTime_2758_);
lean_ctor_set_uint8(v___x_2762_, sizeof(void*)*3, v_action_2755_);
lean_ctor_set_uint8(v___x_2762_, sizeof(void*)*3 + 1, v_wantsRebuild_2756_);
v___x_2763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2760_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
return v___x_2763_;
}
v_resetjp_2770_:
{
uint8_t v_noBuild_2773_; uint8_t v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v_noBuild_2773_ = lean_ctor_get_uint8(v_toBuildConfig_2764_, sizeof(void*)*2 + 2);
v___x_2774_ = l_Lake_JobAction_merge(v_action_2766_, v_action_2742_);
v___x_2775_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_2741_);
v___x_2776_ = l_System_FilePath_addExtension(v_traceFile_2741_, v___x_2775_);
if (v_noBuild_2773_ == 0)
{
lean_object* v___x_2777_; lean_object* v___x_2779_; 
v___x_2777_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_2765_);
if (v_isShared_2772_ == 0)
{
v___x_2779_ = v___x_2771_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_log_2765_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_trace_2768_);
lean_ctor_set(v_reuseFailAlloc_2876_, 2, v_buildTime_2769_);
lean_ctor_set_uint8(v_reuseFailAlloc_2876_, sizeof(void*)*3 + 1, v_wantsRebuild_2767_);
v___x_2779_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
lean_object* v___x_2780_; lean_object* v_a_2782_; lean_object* v_a_2783_; 
lean_ctor_set_uint8(v___x_2779_, sizeof(void*)*3, v___x_2774_);
lean_inc_ref(v_a_2746_);
lean_inc(v_a_2745_);
lean_inc(v_a_2744_);
lean_inc(v_a_2743_);
v___x_2780_ = lean_apply_7(v_build_2737_, v_a_2739_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v___x_2779_, lean_box(0));
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2787_; lean_object* v_log_2788_; uint8_t v_action_2789_; uint8_t v_wantsRebuild_2790_; lean_object* v_trace_2791_; lean_object* v_buildTime_2792_; lean_object* v___x_2793_; 
v_a_2787_ = lean_ctor_get(v___x_2780_, 1);
lean_inc(v_a_2787_);
lean_dec_ref(v___x_2780_);
v_log_2788_ = lean_ctor_get(v_a_2787_, 0);
v_action_2789_ = lean_ctor_get_uint8(v_a_2787_, sizeof(void*)*3);
v_wantsRebuild_2790_ = lean_ctor_get_uint8(v_a_2787_, sizeof(void*)*3 + 1);
v_trace_2791_ = lean_ctor_get(v_a_2787_, 1);
v_buildTime_2792_ = lean_ctor_get(v_a_2787_, 2);
v___x_2793_ = l_Lake_clearFileHash(v_file_2738_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2794_);
lean_dec_ref(v___x_2793_);
v___x_2795_ = lean_array_get_size(v_log_2765_);
lean_dec_ref(v_log_2765_);
v___x_2796_ = lean_array_get_size(v_log_2788_);
v___x_2797_ = l_Array_extract___redArg(v_log_2788_, v___x_2795_, v___x_2796_);
v___x_2798_ = lean_box(0);
v___x_2799_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_2740_, v___x_2798_, v___x_2797_);
v___x_2800_ = l_Lake_BuildMetadata_writeFile(v_traceFile_2741_, v___x_2799_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2841_; 
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2841_ == 0)
{
lean_object* v_unused_2842_; 
v_unused_2842_ = lean_ctor_get(v___x_2800_, 0);
lean_dec(v_unused_2842_);
v___x_2802_ = v___x_2800_;
v_isShared_2803_ = v_isSharedCheck_2841_;
goto v_resetjp_2801_;
}
else
{
lean_dec(v___x_2800_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2841_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2804_; 
v___x_2804_ = l_Lake_removeFileIfExists(v___x_2776_);
lean_dec_ref(v___x_2776_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2824_; 
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2824_ == 0)
{
lean_object* v_unused_2825_; 
v_unused_2825_ = lean_ctor_get(v___x_2804_, 0);
lean_dec(v_unused_2825_);
v___x_2806_ = v___x_2804_;
v_isShared_2807_ = v_isSharedCheck_2824_;
goto v_resetjp_2805_;
}
else
{
lean_dec(v___x_2804_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2824_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
lean_inc(v_a_2794_);
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 0, v_a_2794_);
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2794_);
v___x_2809_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
lean_object* v___x_2811_; 
if (v_isShared_2803_ == 0)
{
lean_ctor_set_tag(v___x_2802_, 1);
lean_ctor_set(v___x_2802_, 0, v___x_2809_);
v___x_2811_ = v___x_2802_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2809_);
v___x_2811_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
lean_object* v___x_2812_; lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
v___x_2812_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v___x_2777_, v___x_2811_, v_a_2787_);
lean_dec_ref(v___x_2811_);
lean_dec(v___x_2777_);
v_a_2813_ = lean_ctor_get(v___x_2812_, 1);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2820_ == 0)
{
lean_object* v_unused_2821_; 
v_unused_2821_ = lean_ctor_get(v___x_2812_, 0);
lean_dec(v_unused_2821_);
v___x_2815_ = v___x_2812_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2812_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 0, v_a_2794_);
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2794_);
lean_ctor_set(v_reuseFailAlloc_2819_, 1, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
}
}
else
{
lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2837_; 
lean_inc(v_buildTime_2792_);
lean_inc_ref(v_trace_2791_);
lean_inc_ref(v_log_2788_);
lean_del_object(v___x_2802_);
lean_dec(v_a_2794_);
v_isSharedCheck_2837_ = !lean_is_exclusive(v_a_2787_);
if (v_isSharedCheck_2837_ == 0)
{
lean_object* v_unused_2838_; lean_object* v_unused_2839_; lean_object* v_unused_2840_; 
v_unused_2838_ = lean_ctor_get(v_a_2787_, 2);
lean_dec(v_unused_2838_);
v_unused_2839_ = lean_ctor_get(v_a_2787_, 1);
lean_dec(v_unused_2839_);
v_unused_2840_ = lean_ctor_get(v_a_2787_, 0);
lean_dec(v_unused_2840_);
v___x_2827_ = v_a_2787_;
v_isShared_2828_ = v_isSharedCheck_2837_;
goto v_resetjp_2826_;
}
else
{
lean_dec(v_a_2787_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2837_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v_a_2829_; lean_object* v___x_2830_; uint8_t v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2835_; 
v_a_2829_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_a_2829_);
lean_dec_ref(v___x_2804_);
v___x_2830_ = lean_io_error_to_string(v_a_2829_);
v___x_2831_ = 3;
v___x_2832_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2832_, 0, v___x_2830_);
lean_ctor_set_uint8(v___x_2832_, sizeof(void*)*1, v___x_2831_);
v___x_2833_ = lean_array_push(v_log_2788_, v___x_2832_);
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 0, v___x_2833_);
v___x_2835_ = v___x_2827_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___x_2833_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_trace_2791_);
lean_ctor_set(v_reuseFailAlloc_2836_, 2, v_buildTime_2792_);
lean_ctor_set_uint8(v_reuseFailAlloc_2836_, sizeof(void*)*3, v_action_2789_);
lean_ctor_set_uint8(v_reuseFailAlloc_2836_, sizeof(void*)*3 + 1, v_wantsRebuild_2790_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
v_a_2782_ = v___x_2796_;
v_a_2783_ = v___x_2835_;
goto v___jp_2781_;
}
}
}
}
}
else
{
lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2854_; 
lean_inc(v_buildTime_2792_);
lean_inc_ref(v_trace_2791_);
lean_inc_ref(v_log_2788_);
lean_dec(v_a_2794_);
lean_dec_ref(v___x_2776_);
v_isSharedCheck_2854_ = !lean_is_exclusive(v_a_2787_);
if (v_isSharedCheck_2854_ == 0)
{
lean_object* v_unused_2855_; lean_object* v_unused_2856_; lean_object* v_unused_2857_; 
v_unused_2855_ = lean_ctor_get(v_a_2787_, 2);
lean_dec(v_unused_2855_);
v_unused_2856_ = lean_ctor_get(v_a_2787_, 1);
lean_dec(v_unused_2856_);
v_unused_2857_ = lean_ctor_get(v_a_2787_, 0);
lean_dec(v_unused_2857_);
v___x_2844_ = v_a_2787_;
v_isShared_2845_ = v_isSharedCheck_2854_;
goto v_resetjp_2843_;
}
else
{
lean_dec(v_a_2787_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2854_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v_a_2846_; lean_object* v___x_2847_; uint8_t v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2852_; 
v_a_2846_ = lean_ctor_get(v___x_2800_, 0);
lean_inc(v_a_2846_);
lean_dec_ref(v___x_2800_);
v___x_2847_ = lean_io_error_to_string(v_a_2846_);
v___x_2848_ = 3;
v___x_2849_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2849_, 0, v___x_2847_);
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*1, v___x_2848_);
v___x_2850_ = lean_array_push(v_log_2788_, v___x_2849_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v___x_2850_);
v___x_2852_ = v___x_2844_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2850_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v_trace_2791_);
lean_ctor_set(v_reuseFailAlloc_2853_, 2, v_buildTime_2792_);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, sizeof(void*)*3, v_action_2789_);
lean_ctor_set_uint8(v_reuseFailAlloc_2853_, sizeof(void*)*3 + 1, v_wantsRebuild_2790_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
v_a_2782_ = v___x_2796_;
v_a_2783_ = v___x_2852_;
goto v___jp_2781_;
}
}
}
}
else
{
lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2870_; 
lean_inc(v_buildTime_2792_);
lean_inc_ref(v_trace_2791_);
lean_inc_ref(v_log_2788_);
lean_dec_ref(v___x_2776_);
lean_dec_ref(v_log_2765_);
lean_dec_ref(v_traceFile_2741_);
v_isSharedCheck_2870_ = !lean_is_exclusive(v_a_2787_);
if (v_isSharedCheck_2870_ == 0)
{
lean_object* v_unused_2871_; lean_object* v_unused_2872_; lean_object* v_unused_2873_; 
v_unused_2871_ = lean_ctor_get(v_a_2787_, 2);
lean_dec(v_unused_2871_);
v_unused_2872_ = lean_ctor_get(v_a_2787_, 1);
lean_dec(v_unused_2872_);
v_unused_2873_ = lean_ctor_get(v_a_2787_, 0);
lean_dec(v_unused_2873_);
v___x_2859_ = v_a_2787_;
v_isShared_2860_ = v_isSharedCheck_2870_;
goto v_resetjp_2858_;
}
else
{
lean_dec(v_a_2787_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2870_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v_a_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2868_; 
v_a_2861_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2861_);
lean_dec_ref(v___x_2793_);
v___x_2862_ = lean_io_error_to_string(v_a_2861_);
v___x_2863_ = 3;
v___x_2864_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2864_, 0, v___x_2862_);
lean_ctor_set_uint8(v___x_2864_, sizeof(void*)*1, v___x_2863_);
v___x_2865_ = lean_array_get_size(v_log_2788_);
v___x_2866_ = lean_array_push(v_log_2788_, v___x_2864_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v___x_2866_);
v___x_2868_ = v___x_2859_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___x_2866_);
lean_ctor_set(v_reuseFailAlloc_2869_, 1, v_trace_2791_);
lean_ctor_set(v_reuseFailAlloc_2869_, 2, v_buildTime_2792_);
lean_ctor_set_uint8(v_reuseFailAlloc_2869_, sizeof(void*)*3, v_action_2789_);
lean_ctor_set_uint8(v_reuseFailAlloc_2869_, sizeof(void*)*3 + 1, v_wantsRebuild_2790_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
v_a_2782_ = v___x_2865_;
v_a_2783_ = v___x_2868_;
goto v___jp_2781_;
}
}
}
}
else
{
lean_object* v_a_2874_; lean_object* v_a_2875_; 
lean_dec_ref(v___x_2776_);
lean_dec_ref(v_log_2765_);
lean_dec_ref(v_traceFile_2741_);
lean_dec_ref(v_file_2738_);
v_a_2874_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2874_);
v_a_2875_ = lean_ctor_get(v___x_2780_, 1);
lean_inc(v_a_2875_);
lean_dec_ref(v___x_2780_);
v_a_2782_ = v_a_2874_;
v_a_2783_ = v_a_2875_;
goto v___jp_2781_;
}
v___jp_2781_:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v_a_2786_; 
v___x_2784_ = lean_box(0);
v___x_2785_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v___x_2777_, v___x_2784_, v_a_2783_);
lean_dec(v___x_2777_);
v_a_2786_ = lean_ctor_get(v___x_2785_, 1);
lean_inc(v_a_2786_);
lean_dec_ref(v___x_2785_);
v_a_2750_ = v_a_2782_;
v_a_2751_ = v_a_2786_;
goto v___jp_2749_;
}
}
}
else
{
uint8_t v___x_2877_; 
lean_dec_ref(v_a_2739_);
lean_dec_ref(v_file_2738_);
lean_dec_ref(v_build_2737_);
v___x_2877_ = l_System_FilePath_pathExists(v_traceFile_2741_);
lean_dec_ref(v_traceFile_2741_);
if (v___x_2877_ == 0)
{
lean_dec_ref(v___x_2776_);
lean_del_object(v___x_2771_);
v_log_2754_ = v_log_2765_;
v_action_2755_ = v___x_2774_;
v_wantsRebuild_2756_ = v_noBuild_2773_;
v_trace_2757_ = v_trace_2768_;
v_buildTime_2758_ = v_buildTime_2769_;
goto v___jp_2753_;
}
else
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2878_ = lean_box(0);
v___x_2879_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_2880_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_2740_, v___x_2878_, v___x_2879_);
v___x_2881_ = l_Lake_BuildMetadata_writeFile(v___x_2776_, v___x_2880_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_dec_ref(v___x_2881_);
lean_del_object(v___x_2771_);
v_log_2754_ = v_log_2765_;
v_action_2755_ = v___x_2774_;
v_wantsRebuild_2756_ = v_noBuild_2773_;
v_trace_2757_ = v_trace_2768_;
v_buildTime_2758_ = v_buildTime_2769_;
goto v___jp_2753_;
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2883_; uint8_t v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2889_; 
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_a_2882_);
lean_dec_ref(v___x_2881_);
v___x_2883_ = lean_io_error_to_string(v_a_2882_);
v___x_2884_ = 3;
v___x_2885_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2885_, 0, v___x_2883_);
lean_ctor_set_uint8(v___x_2885_, sizeof(void*)*1, v___x_2884_);
v___x_2886_ = lean_array_get_size(v_log_2765_);
v___x_2887_ = lean_array_push(v_log_2765_, v___x_2885_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 0, v___x_2887_);
v___x_2889_ = v___x_2771_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v___x_2887_);
lean_ctor_set(v_reuseFailAlloc_2891_, 1, v_trace_2768_);
lean_ctor_set(v_reuseFailAlloc_2891_, 2, v_buildTime_2769_);
v___x_2889_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
lean_object* v___x_2890_; 
lean_ctor_set_uint8(v___x_2889_, sizeof(void*)*3, v___x_2774_);
lean_ctor_set_uint8(v___x_2889_, sizeof(void*)*3 + 1, v_noBuild_2773_);
v___x_2890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2886_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
return v___x_2890_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___boxed(lean_object* v_build_2893_, lean_object* v_file_2894_, lean_object* v_a_2895_, lean_object* v_depTrace_2896_, lean_object* v_traceFile_2897_, lean_object* v_action_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_){
_start:
{
uint8_t v_action_boxed_2905_; lean_object* v_res_2906_; 
v_action_boxed_2905_ = lean_unbox(v_action_2898_);
v_res_2906_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(v_build_2893_, v_file_2894_, v_a_2895_, v_depTrace_2896_, v_traceFile_2897_, v_action_boxed_2905_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
lean_dec_ref(v_a_2902_);
lean_dec(v_a_2901_);
lean_dec(v_a_2900_);
lean_dec(v_a_2899_);
lean_dec_ref(v_depTrace_2896_);
return v_res_2906_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(lean_object* v_info_2907_, lean_object* v_self_2908_){
_start:
{
lean_object* v___x_2910_; 
v___x_2910_ = lean_io_metadata(v_info_2907_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; lean_object* v_modified_2912_; uint8_t v___x_2913_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_a_2911_);
lean_dec_ref(v___x_2910_);
v_modified_2912_ = lean_ctor_get(v_a_2911_, 1);
lean_inc_ref(v_modified_2912_);
lean_dec(v_a_2911_);
v___x_2913_ = l_IO_FS_instOrdSystemTime_ord(v_self_2908_, v_modified_2912_);
lean_dec_ref(v_modified_2912_);
if (v___x_2913_ == 0)
{
uint8_t v___x_2914_; 
v___x_2914_ = 1;
return v___x_2914_;
}
else
{
uint8_t v___x_2915_; 
v___x_2915_ = 0;
return v___x_2915_;
}
}
else
{
uint8_t v___x_2916_; 
lean_dec_ref(v___x_2910_);
v___x_2916_ = 0;
return v___x_2916_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___boxed(lean_object* v_info_2917_, lean_object* v_self_2918_, lean_object* v_a_2919_){
_start:
{
uint8_t v_res_2920_; lean_object* v_r_2921_; 
v_res_2920_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_2917_, v_self_2918_);
lean_dec_ref(v_self_2918_);
lean_dec_ref(v_info_2917_);
v_r_2921_ = lean_box(v_res_2920_);
return v_r_2921_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(lean_object* v_x_2922_, lean_object* v_x_2923_){
_start:
{
if (lean_obj_tag(v_x_2922_) == 0)
{
if (lean_obj_tag(v_x_2923_) == 0)
{
uint8_t v___x_2924_; 
v___x_2924_ = 1;
return v___x_2924_;
}
else
{
uint8_t v___x_2925_; 
v___x_2925_ = 0;
return v___x_2925_;
}
}
else
{
if (lean_obj_tag(v_x_2923_) == 0)
{
uint8_t v___x_2926_; 
v___x_2926_ = 0;
return v___x_2926_;
}
else
{
lean_object* v_val_2927_; lean_object* v_val_2928_; uint64_t v___x_2929_; uint64_t v___x_2930_; uint8_t v___x_2931_; 
v_val_2927_ = lean_ctor_get(v_x_2922_, 0);
v_val_2928_ = lean_ctor_get(v_x_2923_, 0);
v___x_2929_ = lean_unbox_uint64(v_val_2927_);
v___x_2930_ = lean_unbox_uint64(v_val_2928_);
v___x_2931_ = lean_uint64_dec_eq(v___x_2929_, v___x_2930_);
return v___x_2931_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2932_, lean_object* v_x_2933_){
_start:
{
uint8_t v_res_2934_; lean_object* v_r_2935_; 
v_res_2934_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(v_x_2932_, v_x_2933_);
lean_dec(v_x_2933_);
lean_dec(v_x_2932_);
v_r_2935_ = lean_box(v_res_2934_);
return v_r_2935_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(lean_object* v_info_2936_, lean_object* v_depTrace_2937_, lean_object* v_depHash_2938_, lean_object* v_oldTrace_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_){
_start:
{
uint64_t v_hash_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; uint8_t v___x_2946_; 
v_hash_2943_ = lean_ctor_get_uint64(v_depTrace_2937_, sizeof(void*)*3);
v___x_2944_ = lean_box_uint64(v_hash_2943_);
v___x_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2944_);
v___x_2946_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(v___x_2945_, v_depHash_2938_);
lean_dec_ref(v___x_2945_);
if (v___x_2946_ == 0)
{
lean_object* v_toBuildConfig_2947_; uint8_t v_oldMode_2948_; 
v_toBuildConfig_2947_ = lean_ctor_get(v_a_2940_, 0);
v_oldMode_2948_ = lean_ctor_get_uint8(v_toBuildConfig_2947_, sizeof(void*)*2);
if (v_oldMode_2948_ == 0)
{
uint8_t v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2949_ = 0;
v___x_2950_ = lean_box(v___x_2949_);
v___x_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
lean_ctor_set(v___x_2951_, 1, v_a_2941_);
return v___x_2951_;
}
else
{
uint8_t v___x_2952_; 
v___x_2952_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_2936_, v_oldTrace_2939_);
if (v___x_2952_ == 0)
{
uint8_t v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2953_ = 0;
v___x_2954_ = lean_box(v___x_2953_);
v___x_2955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
lean_ctor_set(v___x_2955_, 1, v_a_2941_);
return v___x_2955_;
}
else
{
uint8_t v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2956_ = 1;
v___x_2957_ = lean_box(v___x_2956_);
v___x_2958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2957_);
lean_ctor_set(v___x_2958_, 1, v_a_2941_);
return v___x_2958_;
}
}
}
else
{
uint8_t v___x_2959_; 
v___x_2959_ = l_System_FilePath_pathExists(v_info_2936_);
if (v___x_2959_ == 0)
{
uint8_t v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2960_ = 0;
v___x_2961_ = lean_box(v___x_2960_);
v___x_2962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
lean_ctor_set(v___x_2962_, 1, v_a_2941_);
return v___x_2962_;
}
else
{
uint8_t v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2963_ = 2;
v___x_2964_ = lean_box(v___x_2963_);
v___x_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
lean_ctor_set(v___x_2965_, 1, v_a_2941_);
return v___x_2965_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg___boxed(lean_object* v_info_2966_, lean_object* v_depTrace_2967_, lean_object* v_depHash_2968_, lean_object* v_oldTrace_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_2966_, v_depTrace_2967_, v_depHash_2968_, v_oldTrace_2969_, v_a_2970_, v_a_2971_);
lean_dec_ref(v_a_2970_);
lean_dec_ref(v_oldTrace_2969_);
lean_dec(v_depHash_2968_);
lean_dec_ref(v_depTrace_2967_);
lean_dec_ref(v_info_2966_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(lean_object* v_a_2974_, lean_object* v_info_2975_, lean_object* v_depTrace_2976_, lean_object* v_savedTrace_2977_, lean_object* v_oldTrace_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_){
_start:
{
if (lean_obj_tag(v_savedTrace_2977_) == 2)
{
lean_object* v_data_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3035_; 
v_data_2985_ = lean_ctor_get(v_savedTrace_2977_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v_savedTrace_2977_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_2987_ = v_savedTrace_2977_;
v_isShared_2988_ = v_isSharedCheck_3035_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_data_2985_);
lean_dec(v_savedTrace_2977_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3035_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
uint64_t v_depHash_2989_; lean_object* v_log_2990_; lean_object* v___x_2991_; lean_object* v___x_2993_; 
v_depHash_2989_ = lean_ctor_get_uint64(v_data_2985_, sizeof(void*)*3);
v_log_2990_ = lean_ctor_get(v_data_2985_, 2);
lean_inc_ref(v_log_2990_);
lean_dec_ref(v_data_2985_);
v___x_2991_ = lean_box_uint64(v_depHash_2989_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set_tag(v___x_2987_, 1);
lean_ctor_set(v___x_2987_, 0, v___x_2991_);
v___x_2993_ = v___x_2987_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_2991_);
v___x_2993_ = v_reuseFailAlloc_3034_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
lean_object* v___x_2994_; lean_object* v_a_2995_; lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3033_; 
v___x_2994_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_2975_, v_depTrace_2976_, v___x_2993_, v_oldTrace_2978_, v_a_2982_, v_a_2983_);
lean_dec_ref(v___x_2993_);
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
v_a_2996_ = lean_ctor_get(v___x_2994_, 1);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_2998_ = v___x_2994_;
v_isShared_2999_ = v_isSharedCheck_3033_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_inc(v_a_2995_);
lean_dec(v___x_2994_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3033_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___y_3001_; uint8_t v___x_3005_; uint8_t v___x_3006_; uint8_t v___x_3007_; 
v___x_3005_ = 0;
v___x_3006_ = lean_unbox(v_a_2995_);
v___x_3007_ = l_Lake_instDecidableEqOutputStatus(v___x_3006_, v___x_3005_);
if (v___x_3007_ == 0)
{
lean_object* v_log_3008_; uint8_t v_action_3009_; uint8_t v_wantsRebuild_3010_; lean_object* v_trace_3011_; lean_object* v_buildTime_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3032_; 
v_log_3008_ = lean_ctor_get(v_a_2996_, 0);
v_action_3009_ = lean_ctor_get_uint8(v_a_2996_, sizeof(void*)*3);
v_wantsRebuild_3010_ = lean_ctor_get_uint8(v_a_2996_, sizeof(void*)*3 + 1);
v_trace_3011_ = lean_ctor_get(v_a_2996_, 1);
v_buildTime_3012_ = lean_ctor_get(v_a_2996_, 2);
v_isSharedCheck_3032_ = !lean_is_exclusive(v_a_2996_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3014_ = v_a_2996_;
v_isShared_3015_ = v_isSharedCheck_3032_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_buildTime_3012_);
lean_inc(v_trace_3011_);
lean_inc(v_log_3008_);
lean_dec(v_a_2996_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3032_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
uint8_t v___x_3016_; uint8_t v___x_3017_; lean_object* v___x_3019_; 
v___x_3016_ = 1;
v___x_3017_ = l_Lake_JobAction_merge(v_action_3009_, v___x_3016_);
if (v_isShared_3015_ == 0)
{
v___x_3019_ = v___x_3014_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_log_3008_);
lean_ctor_set(v_reuseFailAlloc_3031_, 1, v_trace_3011_);
lean_ctor_set(v_reuseFailAlloc_3031_, 2, v_buildTime_3012_);
lean_ctor_set_uint8(v_reuseFailAlloc_3031_, sizeof(void*)*3 + 1, v_wantsRebuild_3010_);
v___x_3019_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
lean_object* v___x_3020_; 
lean_ctor_set_uint8(v___x_3019_, sizeof(void*)*3, v___x_3017_);
v___x_3020_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_2990_, v_a_2974_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v___x_3019_);
lean_dec_ref(v_log_2990_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 1);
lean_inc(v_a_3021_);
lean_dec_ref(v___x_3020_);
v___y_3001_ = v_a_3021_;
goto v___jp_3000_;
}
else
{
lean_object* v_a_3022_; lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_del_object(v___x_2998_);
lean_dec(v_a_2995_);
v_a_3022_ = lean_ctor_get(v___x_3020_, 0);
v_a_3023_ = lean_ctor_get(v___x_3020_, 1);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_3020_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_inc(v_a_3022_);
lean_dec(v___x_3020_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3022_);
lean_ctor_set(v_reuseFailAlloc_3029_, 1, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_log_2990_);
v___y_3001_ = v_a_2996_;
goto v___jp_3000_;
}
v___jp_3000_:
{
lean_object* v___x_3003_; 
if (v_isShared_2999_ == 0)
{
lean_ctor_set(v___x_2998_, 1, v___y_3001_);
v___x_3003_ = v___x_2998_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2995_);
lean_ctor_set(v_reuseFailAlloc_3004_, 1, v___y_3001_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
}
}
else
{
lean_object* v_toBuildConfig_3036_; uint8_t v_oldMode_3037_; 
lean_dec(v_savedTrace_2977_);
v_toBuildConfig_3036_ = lean_ctor_get(v_a_2982_, 0);
v_oldMode_3037_ = lean_ctor_get_uint8(v_toBuildConfig_3036_, sizeof(void*)*2);
if (v_oldMode_3037_ == 0)
{
uint8_t v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3038_ = 0;
v___x_3039_ = lean_box(v___x_3038_);
v___x_3040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
lean_ctor_set(v___x_3040_, 1, v_a_2983_);
return v___x_3040_;
}
else
{
uint8_t v___x_3041_; 
v___x_3041_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_2975_, v_oldTrace_2978_);
if (v___x_3041_ == 0)
{
uint8_t v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3042_ = 0;
v___x_3043_ = lean_box(v___x_3042_);
v___x_3044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3043_);
lean_ctor_set(v___x_3044_, 1, v_a_2983_);
return v___x_3044_;
}
else
{
uint8_t v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3045_ = 1;
v___x_3046_ = lean_box(v___x_3045_);
v___x_3047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3046_);
lean_ctor_set(v___x_3047_, 1, v_a_2983_);
return v___x_3047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0___boxed(lean_object* v_a_3048_, lean_object* v_info_3049_, lean_object* v_depTrace_3050_, lean_object* v_savedTrace_3051_, lean_object* v_oldTrace_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_3048_, v_info_3049_, v_depTrace_3050_, v_savedTrace_3051_, v_oldTrace_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_);
lean_dec_ref(v_a_3056_);
lean_dec(v_a_3055_);
lean_dec(v_a_3054_);
lean_dec(v_a_3053_);
lean_dec_ref(v_oldTrace_3052_);
lean_dec_ref(v_depTrace_3050_);
lean_dec_ref(v_info_3049_);
lean_dec_ref(v_a_3048_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27(lean_object* v_file_3061_, lean_object* v_build_3062_, uint8_t v_text_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v_a_3072_; lean_object* v_a_3073_; lean_object* v_a_3076_; lean_object* v_log_3109_; uint8_t v_action_3110_; uint8_t v_wantsRebuild_3111_; lean_object* v_trace_3112_; lean_object* v_buildTime_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3144_; 
v_log_3109_ = lean_ctor_get(v_a_3069_, 0);
v_action_3110_ = lean_ctor_get_uint8(v_a_3069_, sizeof(void*)*3);
v_wantsRebuild_3111_ = lean_ctor_get_uint8(v_a_3069_, sizeof(void*)*3 + 1);
v_trace_3112_ = lean_ctor_get(v_a_3069_, 1);
v_buildTime_3113_ = lean_ctor_get(v_a_3069_, 2);
v_isSharedCheck_3144_ = !lean_is_exclusive(v_a_3069_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3115_ = v_a_3069_;
v_isShared_3116_ = v_isSharedCheck_3144_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_buildTime_3113_);
lean_inc(v_trace_3112_);
lean_inc(v_log_3109_);
lean_dec(v_a_3069_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3144_;
goto v_resetjp_3114_;
}
v___jp_3071_:
{
lean_object* v___x_3074_; 
v___x_3074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3074_, 0, v_a_3072_);
lean_ctor_set(v___x_3074_, 1, v_a_3073_);
return v___x_3074_;
}
v___jp_3075_:
{
lean_object* v___x_3077_; 
v___x_3077_ = l_Lake_fetchFileTrace___redArg(v_file_3061_, v_text_3063_, v_a_3068_, v_a_3076_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3099_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 1);
v_a_3079_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3081_ = v___x_3077_;
v_isShared_3082_ = v_isSharedCheck_3099_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3078_);
lean_inc(v_a_3079_);
lean_dec(v___x_3077_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3099_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v_log_3083_; uint8_t v_action_3084_; uint8_t v_wantsRebuild_3085_; lean_object* v_buildTime_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3097_; 
v_log_3083_ = lean_ctor_get(v_a_3078_, 0);
v_action_3084_ = lean_ctor_get_uint8(v_a_3078_, sizeof(void*)*3);
v_wantsRebuild_3085_ = lean_ctor_get_uint8(v_a_3078_, sizeof(void*)*3 + 1);
v_buildTime_3086_ = lean_ctor_get(v_a_3078_, 2);
v_isSharedCheck_3097_ = !lean_is_exclusive(v_a_3078_);
if (v_isSharedCheck_3097_ == 0)
{
lean_object* v_unused_3098_; 
v_unused_3098_ = lean_ctor_get(v_a_3078_, 1);
lean_dec(v_unused_3098_);
v___x_3088_ = v_a_3078_;
v_isShared_3089_ = v_isSharedCheck_3097_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_buildTime_3086_);
lean_inc(v_log_3083_);
lean_dec(v_a_3078_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3097_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3090_; lean_object* v___x_3092_; 
v___x_3090_ = lean_box(0);
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 1, v_a_3079_);
v___x_3092_ = v___x_3088_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_log_3083_);
lean_ctor_set(v_reuseFailAlloc_3096_, 1, v_a_3079_);
lean_ctor_set(v_reuseFailAlloc_3096_, 2, v_buildTime_3086_);
lean_ctor_set_uint8(v_reuseFailAlloc_3096_, sizeof(void*)*3, v_action_3084_);
lean_ctor_set_uint8(v_reuseFailAlloc_3096_, sizeof(void*)*3 + 1, v_wantsRebuild_3085_);
v___x_3092_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
lean_object* v___x_3094_; 
if (v_isShared_3082_ == 0)
{
lean_ctor_set(v___x_3081_, 1, v___x_3092_);
lean_ctor_set(v___x_3081_, 0, v___x_3090_);
v___x_3094_ = v___x_3081_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3090_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v___x_3092_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
}
else
{
lean_object* v_a_3100_; lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
v_a_3100_ = lean_ctor_get(v___x_3077_, 0);
v_a_3101_ = lean_ctor_get(v___x_3077_, 1);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_3077_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_inc(v_a_3100_);
lean_dec(v___x_3077_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3100_);
lean_ctor_set(v_reuseFailAlloc_3107_, 1, v_a_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
v_resetjp_3114_:
{
lean_object* v___x_3117_; lean_object* v_traceFile_3118_; lean_object* v___x_3119_; 
v___x_3117_ = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(v_file_3061_);
v_traceFile_3118_ = lean_string_append(v_file_3061_, v___x_3117_);
lean_inc_ref(v_traceFile_3118_);
v___x_3119_ = l_Lake_readTraceFile(v_traceFile_3118_, v_log_3109_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_a_3120_; lean_object* v_a_3121_; lean_object* v_mtime_3122_; lean_object* v___x_3124_; 
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_a_3120_);
v_a_3121_ = lean_ctor_get(v___x_3119_, 1);
lean_inc(v_a_3121_);
lean_dec_ref(v___x_3119_);
v_mtime_3122_ = lean_ctor_get(v_trace_3112_, 2);
lean_inc_ref(v_trace_3112_);
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 0, v_a_3121_);
v___x_3124_ = v___x_3115_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3121_);
lean_ctor_set(v_reuseFailAlloc_3138_, 1, v_trace_3112_);
lean_ctor_set(v_reuseFailAlloc_3138_, 2, v_buildTime_3113_);
lean_ctor_set_uint8(v_reuseFailAlloc_3138_, sizeof(void*)*3, v_action_3110_);
lean_ctor_set_uint8(v_reuseFailAlloc_3138_, sizeof(void*)*3 + 1, v_wantsRebuild_3111_);
v___x_3124_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
lean_object* v___x_3125_; 
v___x_3125_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_3064_, v_file_3061_, v_trace_3112_, v_a_3120_, v_mtime_3122_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v___x_3124_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_object* v_a_3126_; lean_object* v_a_3127_; uint8_t v___x_3128_; uint8_t v___x_3129_; uint8_t v___x_3130_; 
v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_a_3126_);
v_a_3127_ = lean_ctor_get(v___x_3125_, 1);
lean_inc(v_a_3127_);
lean_dec_ref(v___x_3125_);
v___x_3128_ = 0;
v___x_3129_ = lean_unbox(v_a_3126_);
lean_dec(v_a_3126_);
v___x_3130_ = l_Lake_instDecidableEqOutputStatus(v___x_3129_, v___x_3128_);
if (v___x_3130_ == 0)
{
lean_dec_ref(v_traceFile_3118_);
lean_dec_ref(v_trace_3112_);
lean_dec_ref(v_a_3064_);
lean_dec_ref(v_build_3062_);
v_a_3076_ = v_a_3127_;
goto v___jp_3075_;
}
else
{
uint8_t v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = 3;
lean_inc_ref(v_file_3061_);
v___x_3132_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(v_build_3062_, v_file_3061_, v_a_3064_, v_trace_3112_, v_traceFile_3118_, v___x_3131_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3127_);
lean_dec_ref(v_trace_3112_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 1);
lean_inc(v_a_3133_);
lean_dec_ref(v___x_3132_);
v_a_3076_ = v_a_3133_;
goto v___jp_3075_;
}
else
{
lean_object* v_a_3134_; lean_object* v_a_3135_; 
lean_dec_ref(v_file_3061_);
v_a_3134_ = lean_ctor_get(v___x_3132_, 0);
lean_inc(v_a_3134_);
v_a_3135_ = lean_ctor_get(v___x_3132_, 1);
lean_inc(v_a_3135_);
lean_dec_ref(v___x_3132_);
v_a_3072_ = v_a_3134_;
v_a_3073_ = v_a_3135_;
goto v___jp_3071_;
}
}
}
else
{
lean_object* v_a_3136_; lean_object* v_a_3137_; 
lean_dec_ref(v_traceFile_3118_);
lean_dec_ref(v_trace_3112_);
lean_dec_ref(v_a_3064_);
lean_dec_ref(v_build_3062_);
lean_dec_ref(v_file_3061_);
v_a_3136_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_a_3136_);
v_a_3137_ = lean_ctor_get(v___x_3125_, 1);
lean_inc(v_a_3137_);
lean_dec_ref(v___x_3125_);
v_a_3072_ = v_a_3136_;
v_a_3073_ = v_a_3137_;
goto v___jp_3071_;
}
}
}
else
{
lean_object* v_a_3139_; lean_object* v_a_3140_; lean_object* v___x_3142_; 
lean_dec_ref(v_traceFile_3118_);
lean_dec_ref(v_a_3064_);
lean_dec_ref(v_build_3062_);
lean_dec_ref(v_file_3061_);
v_a_3139_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_a_3139_);
v_a_3140_ = lean_ctor_get(v___x_3119_, 1);
lean_inc(v_a_3140_);
lean_dec_ref(v___x_3119_);
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 0, v_a_3140_);
v___x_3142_ = v___x_3115_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3140_);
lean_ctor_set(v_reuseFailAlloc_3143_, 1, v_trace_3112_);
lean_ctor_set(v_reuseFailAlloc_3143_, 2, v_buildTime_3113_);
lean_ctor_set_uint8(v_reuseFailAlloc_3143_, sizeof(void*)*3, v_action_3110_);
lean_ctor_set_uint8(v_reuseFailAlloc_3143_, sizeof(void*)*3 + 1, v_wantsRebuild_3111_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
v_a_3072_ = v_a_3139_;
v_a_3073_ = v___x_3142_;
goto v___jp_3071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27___boxed(lean_object* v_file_3145_, lean_object* v_build_3146_, lean_object* v_text_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_){
_start:
{
uint8_t v_text_boxed_3155_; lean_object* v_res_3156_; 
v_text_boxed_3155_ = lean_unbox(v_text_3147_);
v_res_3156_ = l_Lake_buildFileUnlessUpToDate_x27(v_file_3145_, v_build_3146_, v_text_boxed_3155_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_, v_a_3153_);
lean_dec_ref(v_a_3152_);
lean_dec(v_a_3151_);
lean_dec(v_a_3150_);
lean_dec(v_a_3149_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(lean_object* v_a_3157_, lean_object* v_info_3158_, lean_object* v_depTrace_3159_, lean_object* v_depHash_3160_, lean_object* v_oldTrace_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_){
_start:
{
lean_object* v___x_3168_; 
v___x_3168_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_3158_, v_depTrace_3159_, v_depHash_3160_, v_oldTrace_3161_, v_a_3165_, v_a_3166_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___boxed(lean_object* v_a_3169_, lean_object* v_info_3170_, lean_object* v_depTrace_3171_, lean_object* v_depHash_3172_, lean_object* v_oldTrace_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_){
_start:
{
lean_object* v_res_3180_; 
v_res_3180_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(v_a_3169_, v_info_3170_, v_depTrace_3171_, v_depHash_3172_, v_oldTrace_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_);
lean_dec_ref(v_a_3177_);
lean_dec(v_a_3176_);
lean_dec(v_a_3175_);
lean_dec(v_a_3174_);
lean_dec_ref(v_oldTrace_3173_);
lean_dec(v_depHash_3172_);
lean_dec_ref(v_depTrace_3171_);
lean_dec_ref(v_info_3170_);
lean_dec_ref(v_a_3169_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0(lean_object* v___x_3181_, lean_object* v___x_3182_, lean_object* v_file_3183_, uint64_t v___x_3184_, lean_object* v___x_3185_, uint8_t v_useLocalFile_3186_, lean_object* v_____r_3187_){
_start:
{
lean_object* v___x_3189_; 
v___x_3189_ = l_IO_setAccessRights(v___x_3181_, v___x_3182_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v___x_3190_; 
lean_dec_ref(v___x_3189_);
lean_inc_ref(v_file_3183_);
v___x_3190_ = l_Lake_writeFileHash(v_file_3183_, v___x_3184_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v___x_3191_; 
lean_dec_ref(v___x_3190_);
v___x_3191_ = lean_io_metadata(v___x_3181_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3204_; 
v_a_3192_ = lean_ctor_get(v___x_3191_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3194_ = v___x_3191_;
v_isShared_3195_ = v_isSharedCheck_3204_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_3191_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3204_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v_modified_3196_; lean_object* v___y_3198_; 
v_modified_3196_ = lean_ctor_get(v_a_3192_, 1);
lean_inc_ref(v_modified_3196_);
lean_dec(v_a_3192_);
if (v_useLocalFile_3186_ == 0)
{
v___y_3198_ = v___x_3181_;
goto v___jp_3197_;
}
else
{
lean_dec_ref(v___x_3181_);
lean_inc_ref(v_file_3183_);
v___y_3198_ = v_file_3183_;
goto v___jp_3197_;
}
v___jp_3197_:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3202_; 
v___x_3199_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3185_);
lean_ctor_set(v___x_3199_, 1, v___y_3198_);
lean_ctor_set(v___x_3199_, 2, v_file_3183_);
lean_ctor_set(v___x_3199_, 3, v_modified_3196_);
v___x_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3199_);
if (v_isShared_3195_ == 0)
{
lean_ctor_set(v___x_3194_, 0, v___x_3200_);
v___x_3202_ = v___x_3194_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3200_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
else
{
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
lean_dec_ref(v___x_3185_);
lean_dec_ref(v_file_3183_);
lean_dec_ref(v___x_3181_);
v_a_3205_ = lean_ctor_get(v___x_3191_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_3191_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3191_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
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
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_dec_ref(v___x_3185_);
lean_dec_ref(v_file_3183_);
lean_dec_ref(v___x_3181_);
v_a_3213_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_3190_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3190_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
else
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
lean_dec_ref(v___x_3185_);
lean_dec_ref(v_file_3183_);
lean_dec_ref(v___x_3181_);
v_a_3221_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3223_ = v___x_3189_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3189_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0___boxed(lean_object* v___x_3229_, lean_object* v___x_3230_, lean_object* v_file_3231_, lean_object* v___x_3232_, lean_object* v___x_3233_, lean_object* v_useLocalFile_3234_, lean_object* v_____r_3235_, lean_object* v___y_3236_){
_start:
{
uint64_t v___x_2961__boxed_3237_; uint8_t v_useLocalFile_boxed_3238_; lean_object* v_res_3239_; 
v___x_2961__boxed_3237_ = lean_unbox_uint64(v___x_3232_);
lean_dec_ref(v___x_3232_);
v_useLocalFile_boxed_3238_ = lean_unbox(v_useLocalFile_3234_);
v_res_3239_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3229_, v___x_3230_, v_file_3231_, v___x_2961__boxed_3237_, v___x_3233_, v_useLocalFile_boxed_3238_, v_____r_3235_);
lean_dec_ref(v___x_3230_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact(lean_object* v_cache_3247_, lean_object* v_file_3248_, lean_object* v_ext_3249_, uint8_t v_text_3250_, uint8_t v_exe_3251_, uint8_t v_useLocalFile_3252_){
_start:
{
lean_object* v_a_3255_; lean_object* v___y_3262_; uint8_t v___x_3273_; 
v___x_3273_ = 1;
if (v_text_3250_ == 0)
{
lean_object* v___x_3274_; 
v___x_3274_ = l_IO_FS_readBinFile(v_file_3248_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; uint64_t v___x_3276_; uint64_t v___x_3277_; uint64_t v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___y_3283_; lean_object* v___x_3304_; lean_object* v___x_3305_; uint8_t v___x_3306_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref(v___x_3274_);
v___x_3276_ = l_Lake_Hash_nil;
v___x_3277_ = lean_byte_array_hash(v_a_3275_);
v___x_3278_ = lean_uint64_mix_hash(v___x_3276_, v___x_3277_);
lean_inc_ref(v_ext_3249_);
v___x_3279_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3279_, 0, v_ext_3249_);
lean_ctor_set_uint64(v___x_3279_, sizeof(void*)*1, v___x_3278_);
v___x_3280_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
v___x_3281_ = l_System_FilePath_join(v_cache_3247_, v___x_3280_);
v___x_3304_ = lean_string_utf8_byte_size(v_ext_3249_);
v___x_3305_ = lean_unsigned_to_nat(0u);
v___x_3306_ = lean_nat_dec_eq(v___x_3304_, v___x_3305_);
if (v___x_3306_ == 0)
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3307_ = l_Lake_Hash_hex(v___x_3278_);
v___x_3308_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_3309_ = lean_string_append(v___x_3307_, v___x_3308_);
v___x_3310_ = lean_string_append(v___x_3309_, v_ext_3249_);
lean_dec_ref(v_ext_3249_);
v___y_3283_ = v___x_3310_;
goto v___jp_3282_;
}
else
{
lean_object* v___x_3311_; 
lean_dec_ref(v_ext_3249_);
v___x_3311_ = l_Lake_Hash_hex(v___x_3278_);
v___y_3283_ = v___x_3311_;
goto v___jp_3282_;
}
v___jp_3282_:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3284_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_3284_, 0, v___x_3273_);
lean_ctor_set_uint8(v___x_3284_, 1, v_text_3250_);
lean_ctor_set_uint8(v___x_3284_, 2, v_exe_3251_);
lean_inc_ref_n(v___x_3284_, 2);
v___x_3285_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3284_);
lean_ctor_set(v___x_3285_, 1, v___x_3284_);
lean_ctor_set(v___x_3285_, 2, v___x_3284_);
v___x_3286_ = l_IO_setAccessRights(v_file_3248_, v___x_3285_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v___x_3287_; uint8_t v___x_3288_; 
lean_dec_ref(v___x_3286_);
v___x_3287_ = l_Lake_joinRelative(v___x_3281_, v___y_3283_);
v___x_3288_ = l_System_FilePath_pathExists(v___x_3287_);
if (v___x_3288_ == 0)
{
lean_object* v___x_3289_; 
lean_inc_ref(v___x_3287_);
v___x_3289_ = l_Lake_createParentDirs(v___x_3287_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v___x_3290_; 
lean_dec_ref(v___x_3289_);
v___x_3290_ = lean_io_hard_link(v_file_3248_, v___x_3287_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
lean_dec_ref(v___x_3290_);
lean_dec(v_a_3275_);
v___x_3291_ = lean_box(0);
v___x_3292_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3287_, v___x_3285_, v_file_3248_, v___x_3278_, v___x_3279_, v_useLocalFile_3252_, v___x_3291_);
lean_dec_ref(v___x_3285_);
v___y_3262_ = v___x_3292_;
goto v___jp_3261_;
}
else
{
lean_object* v_a_3293_; 
v_a_3293_ = lean_ctor_get(v___x_3290_, 0);
lean_inc(v_a_3293_);
lean_dec_ref(v___x_3290_);
if (lean_obj_tag(v_a_3293_) == 0)
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
lean_dec_ref(v_a_3293_);
lean_dec(v_a_3275_);
v___x_3294_ = lean_box(0);
v___x_3295_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3287_, v___x_3285_, v_file_3248_, v___x_3278_, v___x_3279_, v_useLocalFile_3252_, v___x_3294_);
lean_dec_ref(v___x_3285_);
v___y_3262_ = v___x_3295_;
goto v___jp_3261_;
}
else
{
lean_object* v___x_3296_; 
lean_dec(v_a_3293_);
v___x_3296_ = l_Lake_writeBinFileIfNew(v___x_3287_, v_a_3275_);
lean_dec(v_a_3275_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; lean_object* v___x_3298_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3297_);
lean_dec_ref(v___x_3296_);
v___x_3298_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3287_, v___x_3285_, v_file_3248_, v___x_3278_, v___x_3279_, v_useLocalFile_3252_, v_a_3297_);
lean_dec_ref(v___x_3285_);
v___y_3262_ = v___x_3298_;
goto v___jp_3261_;
}
else
{
lean_object* v_a_3299_; 
lean_dec_ref(v___x_3287_);
lean_dec_ref(v___x_3285_);
lean_dec_ref(v___x_3279_);
lean_dec_ref(v_file_3248_);
v_a_3299_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3299_);
lean_dec_ref(v___x_3296_);
v_a_3255_ = v_a_3299_;
goto v___jp_3254_;
}
}
}
}
else
{
lean_object* v_a_3300_; 
lean_dec_ref(v___x_3287_);
lean_dec_ref(v___x_3285_);
lean_dec_ref(v___x_3279_);
lean_dec(v_a_3275_);
lean_dec_ref(v_file_3248_);
v_a_3300_ = lean_ctor_get(v___x_3289_, 0);
lean_inc(v_a_3300_);
lean_dec_ref(v___x_3289_);
v_a_3255_ = v_a_3300_;
goto v___jp_3254_;
}
}
else
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
lean_dec(v_a_3275_);
v___x_3301_ = lean_box(0);
v___x_3302_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3287_, v___x_3285_, v_file_3248_, v___x_3278_, v___x_3279_, v_useLocalFile_3252_, v___x_3301_);
lean_dec_ref(v___x_3285_);
v___y_3262_ = v___x_3302_;
goto v___jp_3261_;
}
}
else
{
lean_object* v_a_3303_; 
lean_dec_ref(v___x_3285_);
lean_dec_ref(v___y_3283_);
lean_dec_ref(v___x_3281_);
lean_dec_ref(v___x_3279_);
lean_dec(v_a_3275_);
lean_dec_ref(v_file_3248_);
v_a_3303_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_a_3303_);
lean_dec_ref(v___x_3286_);
v_a_3255_ = v_a_3303_;
goto v___jp_3254_;
}
}
}
else
{
lean_object* v_a_3312_; 
lean_dec_ref(v_ext_3249_);
lean_dec_ref(v_file_3248_);
lean_dec_ref(v_cache_3247_);
v_a_3312_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3312_);
lean_dec_ref(v___x_3274_);
v_a_3255_ = v_a_3312_;
goto v___jp_3254_;
}
}
else
{
lean_object* v___x_3313_; 
v___x_3313_ = l_IO_FS_readFile(v_file_3248_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3314_; lean_object* v___x_3315_; uint64_t v___x_3316_; uint64_t v___x_3317_; uint64_t v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___y_3323_; lean_object* v___x_3337_; lean_object* v___x_3338_; uint8_t v___x_3339_; 
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_a_3314_);
lean_dec_ref(v___x_3313_);
v___x_3315_ = l_String_crlfToLf(v_a_3314_);
lean_dec(v_a_3314_);
v___x_3316_ = l_Lake_Hash_nil;
v___x_3317_ = lean_string_hash(v___x_3315_);
v___x_3318_ = lean_uint64_mix_hash(v___x_3316_, v___x_3317_);
lean_inc_ref(v_ext_3249_);
v___x_3319_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3319_, 0, v_ext_3249_);
lean_ctor_set_uint64(v___x_3319_, sizeof(void*)*1, v___x_3318_);
v___x_3320_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
v___x_3321_ = l_System_FilePath_join(v_cache_3247_, v___x_3320_);
v___x_3337_ = lean_string_utf8_byte_size(v_ext_3249_);
v___x_3338_ = lean_unsigned_to_nat(0u);
v___x_3339_ = lean_nat_dec_eq(v___x_3337_, v___x_3338_);
if (v___x_3339_ == 0)
{
lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3340_ = l_Lake_Hash_hex(v___x_3318_);
v___x_3341_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_3342_ = lean_string_append(v___x_3340_, v___x_3341_);
v___x_3343_ = lean_string_append(v___x_3342_, v_ext_3249_);
lean_dec_ref(v_ext_3249_);
v___y_3323_ = v___x_3343_;
goto v___jp_3322_;
}
else
{
lean_object* v___x_3344_; 
lean_dec_ref(v_ext_3249_);
v___x_3344_ = l_Lake_Hash_hex(v___x_3318_);
v___y_3323_ = v___x_3344_;
goto v___jp_3322_;
}
v___jp_3322_:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3324_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__3));
v___x_3325_ = l_IO_setAccessRights(v_file_3248_, v___x_3324_);
if (lean_obj_tag(v___x_3325_) == 0)
{
lean_object* v___x_3326_; uint8_t v___x_3327_; 
lean_dec_ref(v___x_3325_);
v___x_3326_ = l_Lake_joinRelative(v___x_3321_, v___y_3323_);
v___x_3327_ = l_System_FilePath_pathExists(v___x_3326_);
if (v___x_3327_ == 0)
{
lean_object* v___x_3328_; 
lean_inc_ref(v___x_3326_);
v___x_3328_ = l_Lake_createParentDirs(v___x_3326_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v___x_3329_; 
lean_dec_ref(v___x_3328_);
v___x_3329_ = l_Lake_writeFileIfNew(v___x_3326_, v___x_3315_);
lean_dec_ref(v___x_3315_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v_a_3330_; lean_object* v___x_3331_; 
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_a_3330_);
lean_dec_ref(v___x_3329_);
v___x_3331_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3326_, v___x_3324_, v_file_3248_, v___x_3318_, v___x_3319_, v_useLocalFile_3252_, v_a_3330_);
v___y_3262_ = v___x_3331_;
goto v___jp_3261_;
}
else
{
lean_object* v_a_3332_; 
lean_dec_ref(v___x_3326_);
lean_dec_ref(v___x_3319_);
lean_dec_ref(v_file_3248_);
v_a_3332_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_a_3332_);
lean_dec_ref(v___x_3329_);
v_a_3255_ = v_a_3332_;
goto v___jp_3254_;
}
}
else
{
lean_object* v_a_3333_; 
lean_dec_ref(v___x_3326_);
lean_dec_ref(v___x_3319_);
lean_dec_ref(v___x_3315_);
lean_dec_ref(v_file_3248_);
v_a_3333_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_a_3333_);
lean_dec_ref(v___x_3328_);
v_a_3255_ = v_a_3333_;
goto v___jp_3254_;
}
}
else
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
lean_dec_ref(v___x_3315_);
v___x_3334_ = lean_box(0);
v___x_3335_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3326_, v___x_3324_, v_file_3248_, v___x_3318_, v___x_3319_, v_useLocalFile_3252_, v___x_3334_);
v___y_3262_ = v___x_3335_;
goto v___jp_3261_;
}
}
else
{
lean_object* v_a_3336_; 
lean_dec_ref(v___y_3323_);
lean_dec_ref(v___x_3321_);
lean_dec_ref(v___x_3319_);
lean_dec_ref(v___x_3315_);
lean_dec_ref(v_file_3248_);
v_a_3336_ = lean_ctor_get(v___x_3325_, 0);
lean_inc(v_a_3336_);
lean_dec_ref(v___x_3325_);
v_a_3255_ = v_a_3336_;
goto v___jp_3254_;
}
}
}
else
{
lean_object* v_a_3345_; 
lean_dec_ref(v_ext_3249_);
lean_dec_ref(v_file_3248_);
lean_dec_ref(v_cache_3247_);
v_a_3345_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_a_3345_);
lean_dec_ref(v___x_3313_);
v_a_3255_ = v_a_3345_;
goto v___jp_3254_;
}
}
v___jp_3254_:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
v___x_3256_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__0));
v___x_3257_ = lean_io_error_to_string(v_a_3255_);
v___x_3258_ = lean_string_append(v___x_3256_, v___x_3257_);
lean_dec_ref(v___x_3257_);
v___x_3259_ = lean_mk_io_user_error(v___x_3258_);
v___x_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3259_);
return v___x_3260_;
}
v___jp_3261_:
{
if (lean_obj_tag(v___y_3262_) == 0)
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3271_; 
v_a_3263_ = lean_ctor_get(v___y_3262_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___y_3262_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3265_ = v___y_3262_;
v_isShared_3266_ = v_isSharedCheck_3271_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___y_3262_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3271_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v_a_3267_; lean_object* v___x_3269_; 
v_a_3267_ = lean_ctor_get(v_a_3263_, 0);
lean_inc(v_a_3267_);
lean_dec(v_a_3263_);
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 0, v_a_3267_);
v___x_3269_ = v___x_3265_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3267_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
else
{
lean_object* v_a_3272_; 
v_a_3272_ = lean_ctor_get(v___y_3262_, 0);
lean_inc(v_a_3272_);
lean_dec_ref(v___y_3262_);
v_a_3255_ = v_a_3272_;
goto v___jp_3254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___boxed(lean_object* v_cache_3346_, lean_object* v_file_3347_, lean_object* v_ext_3348_, lean_object* v_text_3349_, lean_object* v_exe_3350_, lean_object* v_useLocalFile_3351_, lean_object* v_a_3352_){
_start:
{
uint8_t v_text_boxed_3353_; uint8_t v_exe_boxed_3354_; uint8_t v_useLocalFile_boxed_3355_; lean_object* v_res_3356_; 
v_text_boxed_3353_ = lean_unbox(v_text_3349_);
v_exe_boxed_3354_ = lean_unbox(v_exe_3350_);
v_useLocalFile_boxed_3355_ = lean_unbox(v_useLocalFile_3351_);
v_res_3356_ = l_Lake_Cache_saveArtifact(v_cache_3346_, v_file_3347_, v_ext_3348_, v_text_boxed_3353_, v_exe_boxed_3354_, v_useLocalFile_boxed_3355_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0(lean_object* v_x_3357_){
_start:
{
lean_object* v_lakeCache_3358_; 
v_lakeCache_3358_ = lean_ctor_get(v_x_3357_, 3);
lean_inc_ref(v_lakeCache_3358_);
return v_lakeCache_3358_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0___boxed(lean_object* v_x_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_Lake_cacheArtifact___redArg___lam__0(v_x_3359_);
lean_dec_ref(v_x_3359_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1(lean_object* v_file_3361_, lean_object* v_ext_3362_, uint8_t v_text_3363_, uint8_t v_exe_3364_, uint8_t v_useLocalFile_3365_, lean_object* v_inst_3366_, lean_object* v_____do__lift_3367_){
_start:
{
lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3368_ = lean_box(v_text_3363_);
v___x_3369_ = lean_box(v_exe_3364_);
v___x_3370_ = lean_box(v_useLocalFile_3365_);
v___x_3371_ = lean_alloc_closure((void*)(l_Lake_Cache_saveArtifact___boxed), 7, 6);
lean_closure_set(v___x_3371_, 0, v_____do__lift_3367_);
lean_closure_set(v___x_3371_, 1, v_file_3361_);
lean_closure_set(v___x_3371_, 2, v_ext_3362_);
lean_closure_set(v___x_3371_, 3, v___x_3368_);
lean_closure_set(v___x_3371_, 4, v___x_3369_);
lean_closure_set(v___x_3371_, 5, v___x_3370_);
v___x_3372_ = lean_apply_2(v_inst_3366_, lean_box(0), v___x_3371_);
return v___x_3372_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1___boxed(lean_object* v_file_3373_, lean_object* v_ext_3374_, lean_object* v_text_3375_, lean_object* v_exe_3376_, lean_object* v_useLocalFile_3377_, lean_object* v_inst_3378_, lean_object* v_____do__lift_3379_){
_start:
{
uint8_t v_text_boxed_3380_; uint8_t v_exe_boxed_3381_; uint8_t v_useLocalFile_boxed_3382_; lean_object* v_res_3383_; 
v_text_boxed_3380_ = lean_unbox(v_text_3375_);
v_exe_boxed_3381_ = lean_unbox(v_exe_3376_);
v_useLocalFile_boxed_3382_ = lean_unbox(v_useLocalFile_3377_);
v_res_3383_ = l_Lake_cacheArtifact___redArg___lam__1(v_file_3373_, v_ext_3374_, v_text_boxed_3380_, v_exe_boxed_3381_, v_useLocalFile_boxed_3382_, v_inst_3378_, v_____do__lift_3379_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg(lean_object* v_inst_3385_, lean_object* v_inst_3386_, lean_object* v_inst_3387_, lean_object* v_file_3388_, lean_object* v_ext_3389_, uint8_t v_text_3390_, uint8_t v_exe_3391_, uint8_t v_useLocalFile_3392_){
_start:
{
lean_object* v_toApplicative_3393_; lean_object* v_toFunctor_3394_; lean_object* v_toBind_3395_; lean_object* v_map_3396_; lean_object* v___f_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___f_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v_toApplicative_3393_ = lean_ctor_get(v_inst_3387_, 0);
v_toFunctor_3394_ = lean_ctor_get(v_toApplicative_3393_, 0);
lean_inc_ref(v_toFunctor_3394_);
v_toBind_3395_ = lean_ctor_get(v_inst_3387_, 1);
lean_inc(v_toBind_3395_);
lean_dec_ref(v_inst_3387_);
v_map_3396_ = lean_ctor_get(v_toFunctor_3394_, 0);
lean_inc(v_map_3396_);
lean_dec_ref(v_toFunctor_3394_);
v___f_3397_ = ((lean_object*)(l_Lake_cacheArtifact___redArg___closed__0));
v___x_3398_ = lean_box(v_text_3390_);
v___x_3399_ = lean_box(v_exe_3391_);
v___x_3400_ = lean_box(v_useLocalFile_3392_);
v___f_3401_ = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_3401_, 0, v_file_3388_);
lean_closure_set(v___f_3401_, 1, v_ext_3389_);
lean_closure_set(v___f_3401_, 2, v___x_3398_);
lean_closure_set(v___f_3401_, 3, v___x_3399_);
lean_closure_set(v___f_3401_, 4, v___x_3400_);
lean_closure_set(v___f_3401_, 5, v_inst_3386_);
v___x_3402_ = lean_apply_4(v_map_3396_, lean_box(0), lean_box(0), v___f_3397_, v_inst_3385_);
v___x_3403_ = lean_apply_4(v_toBind_3395_, lean_box(0), lean_box(0), v___x_3402_, v___f_3401_);
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___boxed(lean_object* v_inst_3404_, lean_object* v_inst_3405_, lean_object* v_inst_3406_, lean_object* v_file_3407_, lean_object* v_ext_3408_, lean_object* v_text_3409_, lean_object* v_exe_3410_, lean_object* v_useLocalFile_3411_){
_start:
{
uint8_t v_text_boxed_3412_; uint8_t v_exe_boxed_3413_; uint8_t v_useLocalFile_boxed_3414_; lean_object* v_res_3415_; 
v_text_boxed_3412_ = lean_unbox(v_text_3409_);
v_exe_boxed_3413_ = lean_unbox(v_exe_3410_);
v_useLocalFile_boxed_3414_ = lean_unbox(v_useLocalFile_3411_);
v_res_3415_ = l_Lake_cacheArtifact___redArg(v_inst_3404_, v_inst_3405_, v_inst_3406_, v_file_3407_, v_ext_3408_, v_text_boxed_3412_, v_exe_boxed_3413_, v_useLocalFile_boxed_3414_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact(lean_object* v_m_3416_, lean_object* v_inst_3417_, lean_object* v_inst_3418_, lean_object* v_inst_3419_, lean_object* v_file_3420_, lean_object* v_ext_3421_, uint8_t v_text_3422_, uint8_t v_exe_3423_, uint8_t v_useLocalFile_3424_){
_start:
{
lean_object* v_toApplicative_3425_; lean_object* v_toFunctor_3426_; lean_object* v_toBind_3427_; lean_object* v_map_3428_; lean_object* v___f_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___f_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v_toApplicative_3425_ = lean_ctor_get(v_inst_3419_, 0);
v_toFunctor_3426_ = lean_ctor_get(v_toApplicative_3425_, 0);
lean_inc_ref(v_toFunctor_3426_);
v_toBind_3427_ = lean_ctor_get(v_inst_3419_, 1);
lean_inc(v_toBind_3427_);
lean_dec_ref(v_inst_3419_);
v_map_3428_ = lean_ctor_get(v_toFunctor_3426_, 0);
lean_inc(v_map_3428_);
lean_dec_ref(v_toFunctor_3426_);
v___f_3429_ = ((lean_object*)(l_Lake_cacheArtifact___redArg___closed__0));
v___x_3430_ = lean_box(v_text_3422_);
v___x_3431_ = lean_box(v_exe_3423_);
v___x_3432_ = lean_box(v_useLocalFile_3424_);
v___f_3433_ = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_3433_, 0, v_file_3420_);
lean_closure_set(v___f_3433_, 1, v_ext_3421_);
lean_closure_set(v___f_3433_, 2, v___x_3430_);
lean_closure_set(v___f_3433_, 3, v___x_3431_);
lean_closure_set(v___f_3433_, 4, v___x_3432_);
lean_closure_set(v___f_3433_, 5, v_inst_3418_);
v___x_3434_ = lean_apply_4(v_map_3428_, lean_box(0), lean_box(0), v___f_3429_, v_inst_3417_);
v___x_3435_ = lean_apply_4(v_toBind_3427_, lean_box(0), lean_box(0), v___x_3434_, v___f_3433_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___boxed(lean_object* v_m_3436_, lean_object* v_inst_3437_, lean_object* v_inst_3438_, lean_object* v_inst_3439_, lean_object* v_file_3440_, lean_object* v_ext_3441_, lean_object* v_text_3442_, lean_object* v_exe_3443_, lean_object* v_useLocalFile_3444_){
_start:
{
uint8_t v_text_boxed_3445_; uint8_t v_exe_boxed_3446_; uint8_t v_useLocalFile_boxed_3447_; lean_object* v_res_3448_; 
v_text_boxed_3445_ = lean_unbox(v_text_3442_);
v_exe_boxed_3446_ = lean_unbox(v_exe_3443_);
v_useLocalFile_boxed_3447_ = lean_unbox(v_useLocalFile_3444_);
v_res_3448_ = l_Lake_cacheArtifact(v_m_3436_, v_inst_3437_, v_inst_3438_, v_inst_3439_, v_file_3440_, v_ext_3441_, v_text_boxed_3445_, v_exe_boxed_3446_, v_useLocalFile_boxed_3447_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0(lean_object* v_x1_3450_, lean_object* v_x2_3451_){
_start:
{
lean_object* v_message_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; 
v_message_3452_ = lean_ctor_get(v_x2_3451_, 0);
v___x_3453_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0));
v___x_3454_ = lean_string_append(v_x1_3450_, v___x_3453_);
v___x_3455_ = lean_string_append(v___x_3454_, v_message_3452_);
return v___x_3455_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___boxed(lean_object* v_x1_3456_, lean_object* v_x2_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0(v_x1_3456_, v_x2_3457_);
lean_dec_ref(v_x2_3457_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(lean_object* v_inst_3462_, uint64_t v_inputHash_3463_, lean_object* v_pkg_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_){
_start:
{
lean_object* v_toContext_3472_; lean_object* v_log_3473_; uint8_t v_action_3474_; uint8_t v_wantsRebuild_3475_; lean_object* v_trace_3476_; lean_object* v_buildTime_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3572_; 
v_toContext_3472_ = lean_ctor_get(v_a_3469_, 1);
v_log_3473_ = lean_ctor_get(v_a_3470_, 0);
v_action_3474_ = lean_ctor_get_uint8(v_a_3470_, sizeof(void*)*3);
v_wantsRebuild_3475_ = lean_ctor_get_uint8(v_a_3470_, sizeof(void*)*3 + 1);
v_trace_3476_ = lean_ctor_get(v_a_3470_, 1);
v_buildTime_3477_ = lean_ctor_get(v_a_3470_, 2);
v_isSharedCheck_3572_ = !lean_is_exclusive(v_a_3470_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3479_ = v_a_3470_;
v_isShared_3480_ = v_isSharedCheck_3572_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_buildTime_3477_);
lean_inc(v_trace_3476_);
lean_inc(v_log_3473_);
lean_dec(v_a_3470_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3572_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v_lakeCache_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v_lakeCache_3481_ = lean_ctor_get(v_toContext_3472_, 3);
v___x_3482_ = l_Lake_Package_cacheScope(v_pkg_3464_);
lean_inc_ref(v_lakeCache_3481_);
v___x_3483_ = l_Lake_Cache_readOutputs_x3f(v_lakeCache_3481_, v___x_3482_, v_inputHash_3463_, v_log_3473_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v_a_3484_; lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3559_; 
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
v_a_3485_ = lean_ctor_get(v___x_3483_, 1);
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3487_ = v___x_3483_;
v_isShared_3488_ = v_isSharedCheck_3559_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_inc(v_a_3484_);
lean_dec(v___x_3483_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3559_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 0, v_a_3485_);
v___x_3490_ = v___x_3479_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_a_3485_);
lean_ctor_set(v_reuseFailAlloc_3558_, 1, v_trace_3476_);
lean_ctor_set(v_reuseFailAlloc_3558_, 2, v_buildTime_3477_);
lean_ctor_set_uint8(v_reuseFailAlloc_3558_, sizeof(void*)*3, v_action_3474_);
lean_ctor_set_uint8(v_reuseFailAlloc_3558_, sizeof(void*)*3 + 1, v_wantsRebuild_3475_);
v___x_3490_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
if (lean_obj_tag(v_a_3484_) == 1)
{
lean_object* v_val_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3553_; 
v_val_3491_ = lean_ctor_get(v_a_3484_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v_a_3484_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3493_ = v_a_3484_;
v_isShared_3494_ = v_isSharedCheck_3553_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_val_3491_);
lean_dec(v_a_3484_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3553_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3495_; lean_object* v_r_3497_; lean_object* v___y_3498_; 
lean_inc_ref(v_a_3469_);
lean_inc(v_a_3468_);
lean_inc(v_a_3467_);
lean_inc(v_a_3466_);
v___x_3495_ = lean_apply_8(v_inst_3462_, v_val_3491_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v___x_3490_, lean_box(0));
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3502_; lean_object* v_a_3503_; lean_object* v___x_3505_; 
v_a_3502_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3502_);
v_a_3503_ = lean_ctor_get(v___x_3495_, 1);
lean_inc(v_a_3503_);
lean_dec_ref(v___x_3495_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 0, v_a_3502_);
v___x_3505_ = v___x_3493_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3502_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
v_r_3497_ = v___x_3505_;
v___y_3498_ = v_a_3503_;
goto v___jp_3496_;
}
}
else
{
lean_object* v_a_3507_; lean_object* v_a_3508_; lean_object* v_log_3509_; uint8_t v_action_3510_; uint8_t v_wantsRebuild_3511_; lean_object* v_trace_3512_; lean_object* v_buildTime_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3552_; 
lean_del_object(v___x_3493_);
v_a_3507_ = lean_ctor_get(v___x_3495_, 1);
lean_inc(v_a_3507_);
v_a_3508_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3508_);
lean_dec_ref(v___x_3495_);
v_log_3509_ = lean_ctor_get(v_a_3507_, 0);
v_action_3510_ = lean_ctor_get_uint8(v_a_3507_, sizeof(void*)*3);
v_wantsRebuild_3511_ = lean_ctor_get_uint8(v_a_3507_, sizeof(void*)*3 + 1);
v_trace_3512_ = lean_ctor_get(v_a_3507_, 1);
v_buildTime_3513_ = lean_ctor_get(v_a_3507_, 2);
v_isSharedCheck_3552_ = !lean_is_exclusive(v_a_3507_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3515_ = v_a_3507_;
v_isShared_3516_ = v_isSharedCheck_3552_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_buildTime_3513_);
lean_inc(v_trace_3512_);
lean_inc(v_log_3509_);
lean_dec(v_a_3507_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3552_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___y_3521_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; uint8_t v___x_3543_; 
v___x_3517_ = lean_array_get_size(v_log_3509_);
lean_inc(v_a_3508_);
v___x_3518_ = l_Array_extract___redArg(v_log_3509_, v_a_3508_, v___x_3517_);
v___x_3519_ = l_Array_shrink___redArg(v_log_3509_, v_a_3508_);
lean_dec(v_a_3508_);
v___x_3529_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0));
v___x_3530_ = l_Lake_Hash_hex(v_inputHash_3463_);
v___x_3531_ = lean_unsigned_to_nat(7u);
v___x_3532_ = lean_unsigned_to_nat(0u);
v___x_3533_ = lean_string_utf8_byte_size(v___x_3530_);
lean_inc_ref(v___x_3530_);
v___x_3534_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3530_);
lean_ctor_set(v___x_3534_, 1, v___x_3532_);
lean_ctor_set(v___x_3534_, 2, v___x_3533_);
v___x_3535_ = l_String_Slice_Pos_nextn(v___x_3534_, v___x_3532_, v___x_3531_);
lean_dec_ref(v___x_3534_);
v___x_3536_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3530_);
lean_ctor_set(v___x_3536_, 1, v___x_3532_);
lean_ctor_set(v___x_3536_, 2, v___x_3535_);
v___x_3537_ = l_String_Slice_toString(v___x_3536_);
lean_dec_ref(v___x_3536_);
v___x_3538_ = lean_string_append(v___x_3529_, v___x_3537_);
lean_dec_ref(v___x_3537_);
v___x_3539_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1));
v___x_3540_ = lean_string_append(v___x_3538_, v___x_3539_);
v___x_3541_ = lean_array_get_size(v___x_3518_);
v___x_3542_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__9));
v___x_3543_ = lean_nat_dec_lt(v___x_3532_, v___x_3541_);
if (v___x_3543_ == 0)
{
lean_dec_ref(v___x_3518_);
v___y_3521_ = v___x_3540_;
goto v___jp_3520_;
}
else
{
lean_object* v___f_3544_; uint8_t v___x_3545_; 
v___f_3544_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__2));
v___x_3545_ = lean_nat_dec_le(v___x_3541_, v___x_3541_);
if (v___x_3545_ == 0)
{
if (v___x_3543_ == 0)
{
lean_dec_ref(v___x_3518_);
v___y_3521_ = v___x_3540_;
goto v___jp_3520_;
}
else
{
size_t v___x_3546_; size_t v___x_3547_; lean_object* v___x_3548_; 
v___x_3546_ = ((size_t)0ULL);
v___x_3547_ = lean_usize_of_nat(v___x_3541_);
v___x_3548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3542_, v___f_3544_, v___x_3518_, v___x_3546_, v___x_3547_, v___x_3540_);
v___y_3521_ = v___x_3548_;
goto v___jp_3520_;
}
}
else
{
size_t v___x_3549_; size_t v___x_3550_; lean_object* v___x_3551_; 
v___x_3549_ = ((size_t)0ULL);
v___x_3550_ = lean_usize_of_nat(v___x_3541_);
v___x_3551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3542_, v___f_3544_, v___x_3518_, v___x_3549_, v___x_3550_, v___x_3540_);
v___y_3521_ = v___x_3551_;
goto v___jp_3520_;
}
}
v___jp_3520_:
{
uint8_t v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3526_; 
v___x_3522_ = 2;
v___x_3523_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3523_, 0, v___y_3521_);
lean_ctor_set_uint8(v___x_3523_, sizeof(void*)*1, v___x_3522_);
v___x_3524_ = lean_array_push(v___x_3519_, v___x_3523_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 0, v___x_3524_);
v___x_3526_ = v___x_3515_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3524_);
lean_ctor_set(v_reuseFailAlloc_3528_, 1, v_trace_3512_);
lean_ctor_set(v_reuseFailAlloc_3528_, 2, v_buildTime_3513_);
lean_ctor_set_uint8(v_reuseFailAlloc_3528_, sizeof(void*)*3, v_action_3510_);
lean_ctor_set_uint8(v_reuseFailAlloc_3528_, sizeof(void*)*3 + 1, v_wantsRebuild_3511_);
v___x_3526_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
lean_object* v___x_3527_; 
v___x_3527_ = lean_box(0);
v_r_3497_ = v___x_3527_;
v___y_3498_ = v___x_3526_;
goto v___jp_3496_;
}
}
}
}
v___jp_3496_:
{
lean_object* v___x_3500_; 
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 1, v___y_3498_);
lean_ctor_set(v___x_3487_, 0, v_r_3497_);
v___x_3500_ = v___x_3487_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_r_3497_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v___y_3498_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
else
{
lean_object* v___x_3554_; lean_object* v___x_3556_; 
lean_dec(v_a_3484_);
lean_dec_ref(v_a_3465_);
lean_dec_ref(v_inst_3462_);
v___x_3554_ = lean_box(0);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 1, v___x_3490_);
lean_ctor_set(v___x_3487_, 0, v___x_3554_);
v___x_3556_ = v___x_3487_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3554_);
lean_ctor_set(v_reuseFailAlloc_3557_, 1, v___x_3490_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
}
else
{
lean_object* v_a_3560_; lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3571_; 
lean_dec_ref(v_a_3465_);
lean_dec_ref(v_inst_3462_);
v_a_3560_ = lean_ctor_get(v___x_3483_, 0);
v_a_3561_ = lean_ctor_get(v___x_3483_, 1);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3563_ = v___x_3483_;
v_isShared_3564_ = v_isSharedCheck_3571_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_inc(v_a_3560_);
lean_dec(v___x_3483_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3571_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 0, v_a_3561_);
v___x_3566_ = v___x_3479_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_a_3561_);
lean_ctor_set(v_reuseFailAlloc_3570_, 1, v_trace_3476_);
lean_ctor_set(v_reuseFailAlloc_3570_, 2, v_buildTime_3477_);
lean_ctor_set_uint8(v_reuseFailAlloc_3570_, sizeof(void*)*3, v_action_3474_);
lean_ctor_set_uint8(v_reuseFailAlloc_3570_, sizeof(void*)*3 + 1, v_wantsRebuild_3475_);
v___x_3566_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
lean_object* v___x_3568_; 
if (v_isShared_3564_ == 0)
{
lean_ctor_set(v___x_3563_, 1, v___x_3566_);
v___x_3568_ = v___x_3563_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3560_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v___x_3566_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___boxed(lean_object* v_inst_3573_, lean_object* v_inputHash_3574_, lean_object* v_pkg_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_){
_start:
{
uint64_t v_inputHash_boxed_3583_; lean_object* v_res_3584_; 
v_inputHash_boxed_3583_ = lean_unbox_uint64(v_inputHash_3574_);
lean_dec_ref(v_inputHash_3574_);
v_res_3584_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3573_, v_inputHash_boxed_3583_, v_pkg_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_);
lean_dec_ref(v_a_3580_);
lean_dec(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec(v_a_3577_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f(lean_object* v_00_u03b1_3585_, lean_object* v_inst_3586_, uint64_t v_inputHash_3587_, lean_object* v_pkg_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_){
_start:
{
lean_object* v___x_3596_; 
v___x_3596_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3586_, v_inputHash_3587_, v_pkg_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___boxed(lean_object* v_00_u03b1_3597_, lean_object* v_inst_3598_, lean_object* v_inputHash_3599_, lean_object* v_pkg_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_){
_start:
{
uint64_t v_inputHash_boxed_3608_; lean_object* v_res_3609_; 
v_inputHash_boxed_3608_ = lean_unbox_uint64(v_inputHash_3599_);
lean_dec_ref(v_inputHash_3599_);
v_res_3609_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f(v_00_u03b1_3597_, v_inst_3598_, v_inputHash_boxed_3608_, v_pkg_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_);
lean_dec_ref(v_a_3605_);
lean_dec(v_a_3604_);
lean_dec(v_a_3603_);
lean_dec(v_a_3602_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(lean_object* v_a_3610_, lean_object* v_____r_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3619_, 0, v_a_3610_);
v___x_3620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3619_);
v___x_3621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3620_);
lean_ctor_set(v___x_3621_, 1, v___y_3617_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0___boxed(lean_object* v_a_3622_, lean_object* v_____r_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v_res_3631_; 
v_res_3631_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3622_, v_____r_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
lean_dec_ref(v___y_3628_);
lean_dec(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec(v___y_3625_);
lean_dec_ref(v___y_3624_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg(lean_object* v_inst_3633_, uint64_t v_inputHash_3634_, lean_object* v_savedTrace_3635_, lean_object* v_pkg_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_){
_start:
{
lean_object* v___y_3645_; lean_object* v_a_3649_; lean_object* v_a_3650_; lean_object* v___y_3665_; 
if (lean_obj_tag(v_savedTrace_3635_) == 2)
{
lean_object* v_data_3680_; uint64_t v_depHash_3681_; lean_object* v_outputs_x3f_3682_; uint8_t v___x_3683_; 
v_data_3680_ = lean_ctor_get(v_savedTrace_3635_, 0);
lean_inc_ref(v_data_3680_);
lean_dec_ref(v_savedTrace_3635_);
v_depHash_3681_ = lean_ctor_get_uint64(v_data_3680_, sizeof(void*)*3);
v_outputs_x3f_3682_ = lean_ctor_get(v_data_3680_, 1);
lean_inc(v_outputs_x3f_3682_);
lean_dec_ref(v_data_3680_);
v___x_3683_ = lean_uint64_dec_eq(v_depHash_3681_, v_inputHash_3634_);
if (v___x_3683_ == 0)
{
lean_dec(v_outputs_x3f_3682_);
lean_dec_ref(v_a_3637_);
lean_dec_ref(v_pkg_3636_);
lean_dec_ref(v_inst_3633_);
v___y_3645_ = v_a_3642_;
goto v___jp_3644_;
}
else
{
if (lean_obj_tag(v_outputs_x3f_3682_) == 1)
{
lean_object* v_val_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v_val_3684_ = lean_ctor_get(v_outputs_x3f_3682_, 0);
lean_inc_n(v_val_3684_, 2);
lean_dec_ref(v_outputs_x3f_3682_);
v___x_3685_ = lean_box(0);
v___x_3686_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3686_, 0, v_val_3684_);
lean_ctor_set(v___x_3686_, 1, v___x_3685_);
lean_ctor_set(v___x_3686_, 2, v___x_3685_);
lean_inc_ref(v_a_3641_);
lean_inc(v_a_3640_);
lean_inc(v_a_3639_);
lean_inc(v_a_3638_);
lean_inc_ref(v_a_3637_);
v___x_3687_ = lean_apply_8(v_inst_3633_, v___x_3686_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_, lean_box(0));
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_object* v_config_3688_; lean_object* v_a_3689_; lean_object* v_a_3690_; lean_object* v_enableArtifactCache_x3f_3691_; lean_object* v_a_3693_; uint8_t v_a_3697_; lean_object* v_a_3698_; 
v_config_3688_ = lean_ctor_get(v_pkg_3636_, 6);
v_a_3689_ = lean_ctor_get(v___x_3687_, 0);
lean_inc(v_a_3689_);
v_a_3690_ = lean_ctor_get(v___x_3687_, 1);
lean_inc(v_a_3690_);
lean_dec_ref(v___x_3687_);
v_enableArtifactCache_x3f_3691_ = lean_ctor_get(v_config_3688_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_3691_) == 0)
{
lean_object* v_toContext_3729_; lean_object* v_lakeEnv_3730_; lean_object* v_enableArtifactCache_x3f_3731_; 
v_toContext_3729_ = lean_ctor_get(v_a_3641_, 1);
v_lakeEnv_3730_ = lean_ctor_get(v_toContext_3729_, 1);
v_enableArtifactCache_x3f_3731_ = lean_ctor_get(v_lakeEnv_3730_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_3731_) == 0)
{
lean_object* v_root_3732_; lean_object* v_config_3733_; lean_object* v_enableArtifactCache_x3f_3734_; 
v_root_3732_ = lean_ctor_get(v_toContext_3729_, 0);
v_config_3733_ = lean_ctor_get(v_root_3732_, 6);
v_enableArtifactCache_x3f_3734_ = lean_ctor_get(v_config_3733_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_3734_) == 0)
{
lean_dec(v_val_3684_);
lean_dec_ref(v_pkg_3636_);
v_a_3693_ = v_a_3690_;
goto v___jp_3692_;
}
else
{
lean_object* v_val_3735_; uint8_t v___x_3736_; 
v_val_3735_ = lean_ctor_get(v_enableArtifactCache_x3f_3734_, 0);
v___x_3736_ = lean_unbox(v_val_3735_);
v_a_3697_ = v___x_3736_;
v_a_3698_ = v_a_3690_;
goto v___jp_3696_;
}
}
else
{
lean_object* v_val_3737_; uint8_t v___x_3738_; 
v_val_3737_ = lean_ctor_get(v_enableArtifactCache_x3f_3731_, 0);
v___x_3738_ = lean_unbox(v_val_3737_);
v_a_3697_ = v___x_3738_;
v_a_3698_ = v_a_3690_;
goto v___jp_3696_;
}
}
else
{
lean_object* v_val_3739_; uint8_t v___x_3740_; 
v_val_3739_ = lean_ctor_get(v_enableArtifactCache_x3f_3691_, 0);
v___x_3740_ = lean_unbox(v_val_3739_);
v_a_3697_ = v___x_3740_;
v_a_3698_ = v_a_3690_;
goto v___jp_3696_;
}
v___jp_3692_:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3694_ = lean_box(0);
v___x_3695_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3689_, v___x_3694_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3693_);
lean_dec_ref(v_a_3637_);
v___y_3665_ = v___x_3695_;
goto v___jp_3664_;
}
v___jp_3696_:
{
if (v_a_3697_ == 0)
{
lean_dec(v_val_3684_);
lean_dec_ref(v_pkg_3636_);
v_a_3693_ = v_a_3698_;
goto v___jp_3692_;
}
else
{
lean_object* v_toContext_3699_; lean_object* v_log_3700_; uint8_t v_action_3701_; uint8_t v_wantsRebuild_3702_; lean_object* v_trace_3703_; lean_object* v_buildTime_3704_; lean_object* v_lakeCache_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v_toContext_3699_ = lean_ctor_get(v_a_3641_, 1);
v_log_3700_ = lean_ctor_get(v_a_3698_, 0);
v_action_3701_ = lean_ctor_get_uint8(v_a_3698_, sizeof(void*)*3);
v_wantsRebuild_3702_ = lean_ctor_get_uint8(v_a_3698_, sizeof(void*)*3 + 1);
v_trace_3703_ = lean_ctor_get(v_a_3698_, 1);
v_buildTime_3704_ = lean_ctor_get(v_a_3698_, 2);
v_lakeCache_3705_ = lean_ctor_get(v_toContext_3699_, 3);
v___x_3706_ = l_Lake_Package_cacheScope(v_pkg_3636_);
lean_inc_ref(v_lakeCache_3705_);
v___x_3707_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_3705_, v___x_3706_, v_inputHash_3634_, v_val_3684_, v___x_3685_, v___x_3685_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v___x_3708_; lean_object* v___x_3709_; 
lean_dec_ref(v___x_3707_);
v___x_3708_ = lean_box(0);
v___x_3709_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3689_, v___x_3708_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3698_);
lean_dec_ref(v_a_3637_);
v___y_3665_ = v___x_3709_;
goto v___jp_3664_;
}
else
{
lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3725_; 
lean_inc(v_buildTime_3704_);
lean_inc_ref(v_trace_3703_);
lean_inc_ref(v_log_3700_);
v_isSharedCheck_3725_ = !lean_is_exclusive(v_a_3698_);
if (v_isSharedCheck_3725_ == 0)
{
lean_object* v_unused_3726_; lean_object* v_unused_3727_; lean_object* v_unused_3728_; 
v_unused_3726_ = lean_ctor_get(v_a_3698_, 2);
lean_dec(v_unused_3726_);
v_unused_3727_ = lean_ctor_get(v_a_3698_, 1);
lean_dec(v_unused_3727_);
v_unused_3728_ = lean_ctor_get(v_a_3698_, 0);
lean_dec(v_unused_3728_);
v___x_3711_ = v_a_3698_;
v_isShared_3712_ = v_isSharedCheck_3725_;
goto v_resetjp_3710_;
}
else
{
lean_dec(v_a_3698_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3725_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v_a_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; uint8_t v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3722_; 
v_a_3713_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_a_3713_);
lean_dec_ref(v___x_3707_);
v___x_3714_ = ((lean_object*)(l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0));
v___x_3715_ = lean_io_error_to_string(v_a_3713_);
v___x_3716_ = lean_string_append(v___x_3714_, v___x_3715_);
lean_dec_ref(v___x_3715_);
v___x_3717_ = 2;
v___x_3718_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3718_, 0, v___x_3716_);
lean_ctor_set_uint8(v___x_3718_, sizeof(void*)*1, v___x_3717_);
v___x_3719_ = lean_box(0);
v___x_3720_ = lean_array_push(v_log_3700_, v___x_3718_);
if (v_isShared_3712_ == 0)
{
lean_ctor_set(v___x_3711_, 0, v___x_3720_);
v___x_3722_ = v___x_3711_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___x_3720_);
lean_ctor_set(v_reuseFailAlloc_3724_, 1, v_trace_3703_);
lean_ctor_set(v_reuseFailAlloc_3724_, 2, v_buildTime_3704_);
lean_ctor_set_uint8(v_reuseFailAlloc_3724_, sizeof(void*)*3, v_action_3701_);
lean_ctor_set_uint8(v_reuseFailAlloc_3724_, sizeof(void*)*3 + 1, v_wantsRebuild_3702_);
v___x_3722_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
lean_object* v___x_3723_; 
v___x_3723_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3689_, v___x_3719_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_, v___x_3722_);
lean_dec_ref(v_a_3637_);
v___y_3665_ = v___x_3723_;
goto v___jp_3664_;
}
}
}
}
}
}
else
{
lean_object* v_a_3741_; lean_object* v_a_3742_; 
lean_dec(v_val_3684_);
lean_dec_ref(v_a_3637_);
lean_dec_ref(v_pkg_3636_);
v_a_3741_ = lean_ctor_get(v___x_3687_, 0);
lean_inc(v_a_3741_);
v_a_3742_ = lean_ctor_get(v___x_3687_, 1);
lean_inc(v_a_3742_);
lean_dec_ref(v___x_3687_);
v_a_3649_ = v_a_3741_;
v_a_3650_ = v_a_3742_;
goto v___jp_3648_;
}
}
else
{
lean_dec(v_outputs_x3f_3682_);
lean_dec_ref(v_a_3637_);
lean_dec_ref(v_pkg_3636_);
lean_dec_ref(v_inst_3633_);
v___y_3645_ = v_a_3642_;
goto v___jp_3644_;
}
}
}
else
{
lean_dec_ref(v_a_3637_);
lean_dec_ref(v_pkg_3636_);
lean_dec(v_savedTrace_3635_);
lean_dec_ref(v_inst_3633_);
v___y_3645_ = v_a_3642_;
goto v___jp_3644_;
}
v___jp_3644_:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3646_ = lean_box(0);
v___x_3647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3646_);
lean_ctor_set(v___x_3647_, 1, v___y_3645_);
return v___x_3647_;
}
v___jp_3648_:
{
lean_object* v_log_3651_; uint8_t v_action_3652_; uint8_t v_wantsRebuild_3653_; lean_object* v_trace_3654_; lean_object* v_buildTime_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3663_; 
v_log_3651_ = lean_ctor_get(v_a_3650_, 0);
v_action_3652_ = lean_ctor_get_uint8(v_a_3650_, sizeof(void*)*3);
v_wantsRebuild_3653_ = lean_ctor_get_uint8(v_a_3650_, sizeof(void*)*3 + 1);
v_trace_3654_ = lean_ctor_get(v_a_3650_, 1);
v_buildTime_3655_ = lean_ctor_get(v_a_3650_, 2);
v_isSharedCheck_3663_ = !lean_is_exclusive(v_a_3650_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3657_ = v_a_3650_;
v_isShared_3658_ = v_isSharedCheck_3663_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_buildTime_3655_);
lean_inc(v_trace_3654_);
lean_inc(v_log_3651_);
lean_dec(v_a_3650_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3663_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3659_; lean_object* v___x_3661_; 
v___x_3659_ = l_Array_shrink___redArg(v_log_3651_, v_a_3649_);
lean_dec(v_a_3649_);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 0, v___x_3659_);
v___x_3661_ = v___x_3657_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3659_);
lean_ctor_set(v_reuseFailAlloc_3662_, 1, v_trace_3654_);
lean_ctor_set(v_reuseFailAlloc_3662_, 2, v_buildTime_3655_);
lean_ctor_set_uint8(v_reuseFailAlloc_3662_, sizeof(void*)*3, v_action_3652_);
lean_ctor_set_uint8(v_reuseFailAlloc_3662_, sizeof(void*)*3 + 1, v_wantsRebuild_3653_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
v___y_3645_ = v___x_3661_;
goto v___jp_3644_;
}
}
}
v___jp_3664_:
{
if (lean_obj_tag(v___y_3665_) == 0)
{
lean_object* v_a_3666_; 
v_a_3666_ = lean_ctor_get(v___y_3665_, 0);
if (lean_obj_tag(v_a_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3675_; 
lean_inc_ref(v_a_3666_);
v_a_3667_ = lean_ctor_get(v___y_3665_, 1);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___y_3665_);
if (v_isSharedCheck_3675_ == 0)
{
lean_object* v_unused_3676_; 
v_unused_3676_ = lean_ctor_get(v___y_3665_, 0);
lean_dec(v_unused_3676_);
v___x_3669_ = v___y_3665_;
v_isShared_3670_ = v_isSharedCheck_3675_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___y_3665_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3675_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v_a_3671_; lean_object* v___x_3673_; 
v_a_3671_ = lean_ctor_get(v_a_3666_, 0);
lean_inc(v_a_3671_);
lean_dec_ref(v_a_3666_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v_a_3671_);
v___x_3673_ = v___x_3669_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_a_3671_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v_a_3667_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
else
{
lean_object* v_a_3677_; 
v_a_3677_ = lean_ctor_get(v___y_3665_, 1);
lean_inc(v_a_3677_);
lean_dec_ref(v___y_3665_);
v___y_3645_ = v_a_3677_;
goto v___jp_3644_;
}
}
else
{
lean_object* v_a_3678_; lean_object* v_a_3679_; 
v_a_3678_ = lean_ctor_get(v___y_3665_, 0);
lean_inc(v_a_3678_);
v_a_3679_ = lean_ctor_get(v___y_3665_, 1);
lean_inc(v_a_3679_);
lean_dec_ref(v___y_3665_);
v_a_3649_ = v_a_3678_;
v_a_3650_ = v_a_3679_;
goto v___jp_3648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___boxed(lean_object* v_inst_3743_, lean_object* v_inputHash_3744_, lean_object* v_savedTrace_3745_, lean_object* v_pkg_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_){
_start:
{
uint64_t v_inputHash_boxed_3754_; lean_object* v_res_3755_; 
v_inputHash_boxed_3754_ = lean_unbox_uint64(v_inputHash_3744_);
lean_dec_ref(v_inputHash_3744_);
v_res_3755_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3743_, v_inputHash_boxed_3754_, v_savedTrace_3745_, v_pkg_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
lean_dec_ref(v_a_3751_);
lean_dec(v_a_3750_);
lean_dec(v_a_3749_);
lean_dec(v_a_3748_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f(lean_object* v_00_u03b1_3756_, lean_object* v_inst_3757_, uint64_t v_inputHash_3758_, lean_object* v_savedTrace_3759_, lean_object* v_pkg_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_){
_start:
{
lean_object* v___x_3768_; 
v___x_3768_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3757_, v_inputHash_3758_, v_savedTrace_3759_, v_pkg_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_);
return v___x_3768_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___boxed(lean_object* v_00_u03b1_3769_, lean_object* v_inst_3770_, lean_object* v_inputHash_3771_, lean_object* v_savedTrace_3772_, lean_object* v_pkg_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_){
_start:
{
uint64_t v_inputHash_boxed_3781_; lean_object* v_res_3782_; 
v_inputHash_boxed_3781_ = lean_unbox_uint64(v_inputHash_3771_);
lean_dec_ref(v_inputHash_3771_);
v_res_3782_ = l_Lake_getArtifactsUsingTrace_x3f(v_00_u03b1_3769_, v_inst_3770_, v_inputHash_boxed_3781_, v_savedTrace_3772_, v_pkg_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_);
lean_dec_ref(v_a_3778_);
lean_dec(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec(v_a_3775_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg(lean_object* v_inst_3783_, uint64_t v_inputHash_3784_, lean_object* v_savedTrace_3785_, lean_object* v_pkg_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_){
_start:
{
lean_object* v___x_3794_; 
lean_inc_ref(v_a_3787_);
lean_inc_ref(v_pkg_3786_);
lean_inc_ref(v_inst_3783_);
v___x_3794_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3783_, v_inputHash_3784_, v_pkg_3786_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_object* v_a_3795_; 
v_a_3795_ = lean_ctor_get(v___x_3794_, 0);
lean_inc(v_a_3795_);
if (lean_obj_tag(v_a_3795_) == 1)
{
lean_dec_ref(v_a_3795_);
lean_dec_ref(v_a_3787_);
lean_dec_ref(v_pkg_3786_);
lean_dec(v_savedTrace_3785_);
lean_dec_ref(v_inst_3783_);
return v___x_3794_;
}
else
{
lean_object* v_a_3796_; lean_object* v___x_3797_; lean_object* v_a_3798_; 
lean_dec(v_a_3795_);
v_a_3796_ = lean_ctor_get(v___x_3794_, 1);
lean_inc(v_a_3796_);
lean_dec_ref(v___x_3794_);
v___x_3797_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3783_, v_inputHash_3784_, v_savedTrace_3785_, v_pkg_3786_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3796_);
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
if (lean_obj_tag(v_a_3798_) == 1)
{
lean_dec_ref(v_a_3798_);
return v___x_3797_;
}
else
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3807_; 
lean_dec(v_a_3798_);
v_a_3799_ = lean_ctor_get(v___x_3797_, 1);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3807_ == 0)
{
lean_object* v_unused_3808_; 
v_unused_3808_ = lean_ctor_get(v___x_3797_, 0);
lean_dec(v_unused_3808_);
v___x_3801_ = v___x_3797_;
v_isShared_3802_ = v_isSharedCheck_3807_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3797_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3807_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3803_; lean_object* v___x_3805_; 
v___x_3803_ = lean_box(0);
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 0, v___x_3803_);
v___x_3805_ = v___x_3801_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3803_);
lean_ctor_set(v_reuseFailAlloc_3806_, 1, v_a_3799_);
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
lean_dec_ref(v_a_3787_);
lean_dec_ref(v_pkg_3786_);
lean_dec(v_savedTrace_3785_);
lean_dec_ref(v_inst_3783_);
return v___x_3794_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___boxed(lean_object* v_inst_3809_, lean_object* v_inputHash_3810_, lean_object* v_savedTrace_3811_, lean_object* v_pkg_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_){
_start:
{
uint64_t v_inputHash_boxed_3820_; lean_object* v_res_3821_; 
v_inputHash_boxed_3820_ = lean_unbox_uint64(v_inputHash_3810_);
lean_dec_ref(v_inputHash_3810_);
v_res_3821_ = l_Lake_getArtifacts_x3f___redArg(v_inst_3809_, v_inputHash_boxed_3820_, v_savedTrace_3811_, v_pkg_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_);
lean_dec_ref(v_a_3817_);
lean_dec(v_a_3816_);
lean_dec(v_a_3815_);
lean_dec(v_a_3814_);
return v_res_3821_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f(lean_object* v_00_u03b1_3822_, lean_object* v_inst_3823_, uint64_t v_inputHash_3824_, lean_object* v_savedTrace_3825_, lean_object* v_pkg_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_){
_start:
{
lean_object* v___x_3834_; 
lean_inc_ref(v_a_3827_);
lean_inc_ref(v_pkg_3826_);
lean_inc_ref(v_inst_3823_);
v___x_3834_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3823_, v_inputHash_3824_, v_pkg_3826_, v_a_3827_, v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v_a_3835_; 
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
lean_inc(v_a_3835_);
if (lean_obj_tag(v_a_3835_) == 1)
{
lean_dec_ref(v_a_3835_);
lean_dec_ref(v_a_3827_);
lean_dec_ref(v_pkg_3826_);
lean_dec(v_savedTrace_3825_);
lean_dec_ref(v_inst_3823_);
return v___x_3834_;
}
else
{
lean_object* v_a_3836_; lean_object* v___x_3837_; lean_object* v_a_3838_; 
lean_dec(v_a_3835_);
v_a_3836_ = lean_ctor_get(v___x_3834_, 1);
lean_inc(v_a_3836_);
lean_dec_ref(v___x_3834_);
v___x_3837_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3823_, v_inputHash_3824_, v_savedTrace_3825_, v_pkg_3826_, v_a_3827_, v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3836_);
v_a_3838_ = lean_ctor_get(v___x_3837_, 0);
lean_inc(v_a_3838_);
if (lean_obj_tag(v_a_3838_) == 1)
{
lean_dec_ref(v_a_3838_);
return v___x_3837_;
}
else
{
lean_object* v_a_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3847_; 
lean_dec(v_a_3838_);
v_a_3839_ = lean_ctor_get(v___x_3837_, 1);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3847_ == 0)
{
lean_object* v_unused_3848_; 
v_unused_3848_ = lean_ctor_get(v___x_3837_, 0);
lean_dec(v_unused_3848_);
v___x_3841_ = v___x_3837_;
v_isShared_3842_ = v_isSharedCheck_3847_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_a_3839_);
lean_dec(v___x_3837_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3847_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3843_; lean_object* v___x_3845_; 
v___x_3843_ = lean_box(0);
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 0, v___x_3843_);
v___x_3845_ = v___x_3841_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3843_);
lean_ctor_set(v_reuseFailAlloc_3846_, 1, v_a_3839_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_3827_);
lean_dec_ref(v_pkg_3826_);
lean_dec(v_savedTrace_3825_);
lean_dec_ref(v_inst_3823_);
return v___x_3834_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___boxed(lean_object* v_00_u03b1_3849_, lean_object* v_inst_3850_, lean_object* v_inputHash_3851_, lean_object* v_savedTrace_3852_, lean_object* v_pkg_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_){
_start:
{
uint64_t v_inputHash_boxed_3861_; lean_object* v_res_3862_; 
v_inputHash_boxed_3861_ = lean_unbox_uint64(v_inputHash_3851_);
lean_dec_ref(v_inputHash_3851_);
v_res_3862_ = l_Lake_getArtifacts_x3f(v_00_u03b1_3849_, v_inst_3850_, v_inputHash_boxed_3861_, v_savedTrace_3852_, v_pkg_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_);
lean_dec_ref(v_a_3858_);
lean_dec(v_a_3857_);
lean_dec(v_a_3856_);
lean_dec(v_a_3855_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__0(lean_object* v_descr_3863_, lean_object* v___x_3864_, lean_object* v_mtime_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; 
lean_inc_ref(v___x_3864_);
v___x_3873_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3873_, 0, v_descr_3863_);
lean_ctor_set(v___x_3873_, 1, v___x_3864_);
lean_ctor_set(v___x_3873_, 2, v___x_3864_);
lean_ctor_set(v___x_3873_, 3, v_mtime_3865_);
v___x_3874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3873_);
lean_ctor_set(v___x_3874_, 1, v___y_3871_);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__0___boxed(lean_object* v_descr_3875_, lean_object* v___x_3876_, lean_object* v_mtime_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l_Lake_resolveArtifact___lam__0(v_descr_3875_, v___x_3876_, v_mtime_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec(v___y_3880_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__1(lean_object* v___x_3887_, lean_object* v___f_3888_, lean_object* v_____r_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_){
_start:
{
lean_object* v_log_3897_; uint8_t v_action_3898_; uint8_t v_wantsRebuild_3899_; lean_object* v_trace_3900_; lean_object* v_buildTime_3901_; lean_object* v___x_3902_; 
v_log_3897_ = lean_ctor_get(v___y_3895_, 0);
v_action_3898_ = lean_ctor_get_uint8(v___y_3895_, sizeof(void*)*3);
v_wantsRebuild_3899_ = lean_ctor_get_uint8(v___y_3895_, sizeof(void*)*3 + 1);
v_trace_3900_ = lean_ctor_get(v___y_3895_, 1);
v_buildTime_3901_ = lean_ctor_get(v___y_3895_, 2);
v___x_3902_ = lean_io_metadata(v___x_3887_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v_a_3903_; lean_object* v_modified_3904_; lean_object* v___x_3905_; 
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_a_3903_);
lean_dec_ref(v___x_3902_);
v_modified_3904_ = lean_ctor_get(v_a_3903_, 1);
lean_inc_ref(v_modified_3904_);
lean_dec(v_a_3903_);
lean_inc_ref(v___y_3894_);
lean_inc(v___y_3893_);
lean_inc(v___y_3892_);
lean_inc(v___y_3891_);
v___x_3905_ = lean_apply_8(v___f_3888_, v_modified_3904_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, lean_box(0));
return v___x_3905_;
}
else
{
lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3921_; 
lean_inc(v_buildTime_3901_);
lean_inc_ref(v_trace_3900_);
lean_inc_ref(v_log_3897_);
lean_dec_ref(v___y_3890_);
lean_dec_ref(v___f_3888_);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___y_3895_);
if (v_isSharedCheck_3921_ == 0)
{
lean_object* v_unused_3922_; lean_object* v_unused_3923_; lean_object* v_unused_3924_; 
v_unused_3922_ = lean_ctor_get(v___y_3895_, 2);
lean_dec(v_unused_3922_);
v_unused_3923_ = lean_ctor_get(v___y_3895_, 1);
lean_dec(v_unused_3923_);
v_unused_3924_ = lean_ctor_get(v___y_3895_, 0);
lean_dec(v_unused_3924_);
v___x_3907_ = v___y_3895_;
v_isShared_3908_ = v_isSharedCheck_3921_;
goto v_resetjp_3906_;
}
else
{
lean_dec(v___y_3895_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3921_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v_a_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; uint8_t v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3918_; 
v_a_3909_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_a_3909_);
lean_dec_ref(v___x_3902_);
v___x_3910_ = ((lean_object*)(l_Lake_resolveArtifact___lam__1___closed__0));
v___x_3911_ = lean_io_error_to_string(v_a_3909_);
v___x_3912_ = lean_string_append(v___x_3910_, v___x_3911_);
lean_dec_ref(v___x_3911_);
v___x_3913_ = 3;
v___x_3914_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3914_, 0, v___x_3912_);
lean_ctor_set_uint8(v___x_3914_, sizeof(void*)*1, v___x_3913_);
v___x_3915_ = lean_array_get_size(v_log_3897_);
v___x_3916_ = lean_array_push(v_log_3897_, v___x_3914_);
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 0, v___x_3916_);
v___x_3918_ = v___x_3907_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3916_);
lean_ctor_set(v_reuseFailAlloc_3920_, 1, v_trace_3900_);
lean_ctor_set(v_reuseFailAlloc_3920_, 2, v_buildTime_3901_);
lean_ctor_set_uint8(v_reuseFailAlloc_3920_, sizeof(void*)*3, v_action_3898_);
lean_ctor_set_uint8(v_reuseFailAlloc_3920_, sizeof(void*)*3 + 1, v_wantsRebuild_3899_);
v___x_3918_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
lean_object* v___x_3919_; 
v___x_3919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3915_);
lean_ctor_set(v___x_3919_, 1, v___x_3918_);
return v___x_3919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__1___boxed(lean_object* v___x_3925_, lean_object* v___f_3926_, lean_object* v_____r_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_){
_start:
{
lean_object* v_res_3935_; 
v_res_3935_ = l_Lake_resolveArtifact___lam__1(v___x_3925_, v___f_3926_, v_____r_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_);
lean_dec_ref(v___y_3932_);
lean_dec(v___y_3931_);
lean_dec(v___y_3930_);
lean_dec(v___y_3929_);
lean_dec_ref(v___x_3925_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact(lean_object* v_descr_3947_, lean_object* v_service_x3f_3948_, lean_object* v_scope_x3f_3949_, uint8_t v_exe_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_){
_start:
{
lean_object* v___y_3959_; lean_object* v_a_3960_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v_toContext_3966_; lean_object* v_log_3967_; uint8_t v_action_3968_; uint8_t v_wantsRebuild_3969_; lean_object* v_trace_3970_; lean_object* v_buildTime_3971_; lean_object* v_lakeConfig_3972_; lean_object* v_lakeCache_3973_; uint64_t v_hash_3974_; lean_object* v_ext_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___y_3979_; lean_object* v___x_4077_; lean_object* v___x_4078_; uint8_t v___x_4079_; 
v_toContext_3966_ = lean_ctor_get(v_a_3955_, 1);
v_log_3967_ = lean_ctor_get(v_a_3956_, 0);
v_action_3968_ = lean_ctor_get_uint8(v_a_3956_, sizeof(void*)*3);
v_wantsRebuild_3969_ = lean_ctor_get_uint8(v_a_3956_, sizeof(void*)*3 + 1);
v_trace_3970_ = lean_ctor_get(v_a_3956_, 1);
v_buildTime_3971_ = lean_ctor_get(v_a_3956_, 2);
v_lakeConfig_3972_ = lean_ctor_get(v_toContext_3966_, 2);
v_lakeCache_3973_ = lean_ctor_get(v_toContext_3966_, 3);
v_hash_3974_ = lean_ctor_get_uint64(v_descr_3947_, sizeof(void*)*1);
v_ext_3975_ = lean_ctor_get(v_descr_3947_, 0);
v___x_3976_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
lean_inc_ref(v_lakeCache_3973_);
v___x_3977_ = l_System_FilePath_join(v_lakeCache_3973_, v___x_3976_);
v___x_4077_ = lean_string_utf8_byte_size(v_ext_3975_);
v___x_4078_ = lean_unsigned_to_nat(0u);
v___x_4079_ = lean_nat_dec_eq(v___x_4077_, v___x_4078_);
if (v___x_4079_ == 0)
{
lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4080_ = l_Lake_Hash_hex(v_hash_3974_);
v___x_4081_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_4082_ = lean_string_append(v___x_4080_, v___x_4081_);
v___x_4083_ = lean_string_append(v___x_4082_, v_ext_3975_);
v___y_3979_ = v___x_4083_;
goto v___jp_3978_;
}
else
{
lean_object* v___x_4084_; 
v___x_4084_ = l_Lake_Hash_hex(v_hash_3974_);
v___y_3979_ = v___x_4084_;
goto v___jp_3978_;
}
v___jp_3958_:
{
lean_object* v___x_3961_; 
v___x_3961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3961_, 0, v___y_3959_);
lean_ctor_set(v___x_3961_, 1, v_a_3960_);
return v___x_3961_;
}
v___jp_3962_:
{
if (lean_obj_tag(v___y_3964_) == 0)
{
lean_dec(v___y_3963_);
return v___y_3964_;
}
else
{
lean_object* v_a_3965_; 
v_a_3965_ = lean_ctor_get(v___y_3964_, 1);
lean_inc(v_a_3965_);
lean_dec_ref(v___y_3964_);
v___y_3959_ = v___y_3963_;
v_a_3960_ = v_a_3965_;
goto v___jp_3958_;
}
}
v___jp_3978_:
{
lean_object* v___x_3980_; lean_object* v___f_3981_; lean_object* v___x_3982_; 
v___x_3980_ = l_Lake_joinRelative(v___x_3977_, v___y_3979_);
lean_inc_ref(v___x_3980_);
lean_inc_ref(v_descr_3947_);
v___f_3981_ = lean_alloc_closure((void*)(l_Lake_resolveArtifact___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3981_, 0, v_descr_3947_);
lean_closure_set(v___f_3981_, 1, v___x_3980_);
v___x_3982_ = lean_io_metadata(v___x_3980_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v_a_3983_; lean_object* v_modified_3984_; lean_object* v___x_3985_; 
lean_dec_ref(v___f_3981_);
lean_dec(v_scope_x3f_3949_);
lean_dec(v_service_x3f_3948_);
v_a_3983_ = lean_ctor_get(v___x_3982_, 0);
lean_inc(v_a_3983_);
lean_dec_ref(v___x_3982_);
v_modified_3984_ = lean_ctor_get(v_a_3983_, 1);
lean_inc_ref(v_modified_3984_);
lean_dec(v_a_3983_);
v___x_3985_ = l_Lake_resolveArtifact___lam__0(v_descr_3947_, v___x_3980_, v_modified_3984_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_);
lean_dec_ref(v_a_3951_);
return v___x_3985_;
}
else
{
lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_4073_; 
lean_inc(v_buildTime_3971_);
lean_inc_ref(v_trace_3970_);
lean_inc_ref(v_log_3967_);
lean_dec_ref(v_descr_3947_);
v_isSharedCheck_4073_ = !lean_is_exclusive(v_a_3956_);
if (v_isSharedCheck_4073_ == 0)
{
lean_object* v_unused_4074_; lean_object* v_unused_4075_; lean_object* v_unused_4076_; 
v_unused_4074_ = lean_ctor_get(v_a_3956_, 2);
lean_dec(v_unused_4074_);
v_unused_4075_ = lean_ctor_get(v_a_3956_, 1);
lean_dec(v_unused_4075_);
v_unused_4076_ = lean_ctor_get(v_a_3956_, 0);
lean_dec(v_unused_4076_);
v___x_3987_ = v_a_3956_;
v_isShared_3988_ = v_isSharedCheck_4073_;
goto v_resetjp_3986_;
}
else
{
lean_dec(v_a_3956_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_4073_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v_a_3989_; 
v_a_3989_ = lean_ctor_get(v___x_3982_, 0);
lean_inc(v_a_3989_);
lean_dec_ref(v___x_3982_);
if (lean_obj_tag(v_a_3989_) == 11)
{
lean_object* v___x_3990_; 
lean_dec_ref(v_a_3989_);
v___x_3990_ = lean_array_get_size(v_log_3967_);
if (lean_obj_tag(v_service_x3f_3948_) == 1)
{
lean_object* v_val_3991_; lean_object* v_cacheServices_3992_; uint8_t v___x_3993_; uint8_t v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; 
v_val_3991_ = lean_ctor_get(v_service_x3f_3948_, 0);
lean_inc_n(v_val_3991_, 2);
lean_dec_ref(v_service_x3f_3948_);
v_cacheServices_3992_ = lean_ctor_get(v_lakeConfig_3972_, 3);
v___x_3993_ = 2;
v___x_3994_ = l_Lake_JobAction_merge(v_action_3968_, v___x_3993_);
v___x_3995_ = lean_box(0);
v___x_3996_ = l_Lean_Name_str___override(v___x_3995_, v_val_3991_);
v___x_3997_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_cacheServices_3992_, v___x_3996_);
lean_dec(v___x_3996_);
if (lean_obj_tag(v___x_3997_) == 1)
{
lean_dec(v_val_3991_);
if (lean_obj_tag(v_scope_x3f_3949_) == 1)
{
lean_object* v_val_3998_; lean_object* v_val_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; uint8_t v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
v_val_3998_ = lean_ctor_get(v___x_3997_, 0);
lean_inc(v_val_3998_);
lean_dec_ref(v___x_3997_);
v_val_3999_ = lean_ctor_get(v_scope_x3f_3949_, 0);
lean_inc(v_val_3999_);
lean_dec_ref(v_scope_x3f_3949_);
v___x_4000_ = l_Lake_CacheService_artifactUrl(v_hash_3974_, v_val_3998_, v_val_3999_);
v___x_4001_ = ((lean_object*)(l_Lake_resolveArtifact___closed__0));
v___x_4002_ = l_Lake_Hash_hex(v_hash_3974_);
v___x_4003_ = lean_string_append(v___x_4001_, v___x_4002_);
lean_dec_ref(v___x_4002_);
v___x_4004_ = ((lean_object*)(l_Lake_resolveArtifact___closed__1));
v___x_4005_ = lean_string_append(v___x_4003_, v___x_4004_);
v___x_4006_ = lean_string_append(v___x_4005_, v___x_3980_);
v___x_4007_ = ((lean_object*)(l_Lake_resolveArtifact___closed__2));
v___x_4008_ = lean_string_append(v___x_4006_, v___x_4007_);
v___x_4009_ = lean_string_append(v___x_4008_, v___x_4000_);
v___x_4010_ = 0;
v___x_4011_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4011_, 0, v___x_4009_);
lean_ctor_set_uint8(v___x_4011_, sizeof(void*)*1, v___x_4010_);
v___x_4012_ = lean_array_push(v_log_3967_, v___x_4011_);
lean_inc_ref(v___x_3980_);
v___x_4013_ = l_Lake_downloadArtifactCore(v_hash_3974_, v___x_4000_, v___x_3980_, v___x_4012_);
if (lean_obj_tag(v___x_4013_) == 0)
{
lean_object* v_a_4014_; uint8_t v___x_4015_; uint8_t v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; 
v_a_4014_ = lean_ctor_get(v___x_4013_, 1);
lean_inc(v_a_4014_);
lean_dec_ref(v___x_4013_);
v___x_4015_ = 1;
v___x_4016_ = 0;
v___x_4017_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4017_, 0, v___x_4015_);
lean_ctor_set_uint8(v___x_4017_, 1, v___x_4016_);
lean_ctor_set_uint8(v___x_4017_, 2, v_exe_3950_);
lean_inc_ref_n(v___x_4017_, 2);
v___x_4018_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4017_);
lean_ctor_set(v___x_4018_, 1, v___x_4017_);
lean_ctor_set(v___x_4018_, 2, v___x_4017_);
v___x_4019_ = l_IO_setAccessRights(v___x_3980_, v___x_4018_);
lean_dec_ref(v___x_4018_);
if (lean_obj_tag(v___x_4019_) == 0)
{
lean_object* v___x_4021_; 
lean_dec_ref(v___x_4019_);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 0, v_a_4014_);
v___x_4021_ = v___x_3987_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_a_4014_);
lean_ctor_set(v_reuseFailAlloc_4024_, 1, v_trace_3970_);
lean_ctor_set(v_reuseFailAlloc_4024_, 2, v_buildTime_3971_);
lean_ctor_set_uint8(v_reuseFailAlloc_4024_, sizeof(void*)*3 + 1, v_wantsRebuild_3969_);
v___x_4021_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
lean_object* v___x_4022_; lean_object* v___x_4023_; 
lean_ctor_set_uint8(v___x_4021_, sizeof(void*)*3, v___x_3994_);
v___x_4022_ = lean_box(0);
v___x_4023_ = l_Lake_resolveArtifact___lam__1(v___x_3980_, v___f_3981_, v___x_4022_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v___x_4021_);
lean_dec_ref(v___x_3980_);
v___y_3963_ = v___x_3990_;
v___y_3964_ = v___x_4023_;
goto v___jp_3962_;
}
}
else
{
lean_object* v_a_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; uint8_t v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4034_; 
v_a_4025_ = lean_ctor_get(v___x_4019_, 0);
lean_inc(v_a_4025_);
lean_dec_ref(v___x_4019_);
v___x_4026_ = ((lean_object*)(l_Lake_resolveArtifact___closed__3));
v___x_4027_ = lean_io_error_to_string(v_a_4025_);
v___x_4028_ = lean_string_append(v___x_4026_, v___x_4027_);
lean_dec_ref(v___x_4027_);
v___x_4029_ = 2;
v___x_4030_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4030_, 0, v___x_4028_);
lean_ctor_set_uint8(v___x_4030_, sizeof(void*)*1, v___x_4029_);
v___x_4031_ = lean_box(0);
v___x_4032_ = lean_array_push(v_a_4014_, v___x_4030_);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 0, v___x_4032_);
v___x_4034_ = v___x_3987_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v___x_4032_);
lean_ctor_set(v_reuseFailAlloc_4036_, 1, v_trace_3970_);
lean_ctor_set(v_reuseFailAlloc_4036_, 2, v_buildTime_3971_);
lean_ctor_set_uint8(v_reuseFailAlloc_4036_, sizeof(void*)*3 + 1, v_wantsRebuild_3969_);
v___x_4034_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
lean_object* v___x_4035_; 
lean_ctor_set_uint8(v___x_4034_, sizeof(void*)*3, v___x_3994_);
v___x_4035_ = l_Lake_resolveArtifact___lam__1(v___x_3980_, v___f_3981_, v___x_4031_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v___x_4034_);
lean_dec_ref(v___x_3980_);
v___y_3963_ = v___x_3990_;
v___y_3964_ = v___x_4035_;
goto v___jp_3962_;
}
}
}
else
{
lean_object* v_a_4037_; lean_object* v___x_4039_; 
lean_dec_ref(v___f_3981_);
lean_dec_ref(v___x_3980_);
lean_dec_ref(v_a_3951_);
v_a_4037_ = lean_ctor_get(v___x_4013_, 1);
lean_inc(v_a_4037_);
lean_dec_ref(v___x_4013_);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 0, v_a_4037_);
v___x_4039_ = v___x_3987_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_a_4037_);
lean_ctor_set(v_reuseFailAlloc_4040_, 1, v_trace_3970_);
lean_ctor_set(v_reuseFailAlloc_4040_, 2, v_buildTime_3971_);
lean_ctor_set_uint8(v_reuseFailAlloc_4040_, sizeof(void*)*3 + 1, v_wantsRebuild_3969_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
lean_ctor_set_uint8(v___x_4039_, sizeof(void*)*3, v___x_3994_);
v___y_3959_ = v___x_3990_;
v_a_3960_ = v___x_4039_;
goto v___jp_3958_;
}
}
}
else
{
lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4044_; 
lean_dec_ref(v___x_3997_);
lean_dec_ref(v___f_3981_);
lean_dec_ref(v___x_3980_);
lean_dec_ref(v_a_3951_);
lean_dec(v_scope_x3f_3949_);
v___x_4041_ = ((lean_object*)(l_Lake_resolveArtifact___closed__5));
v___x_4042_ = lean_array_push(v_log_3967_, v___x_4041_);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 0, v___x_4042_);
v___x_4044_ = v___x_3987_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_4042_);
lean_ctor_set(v_reuseFailAlloc_4045_, 1, v_trace_3970_);
lean_ctor_set(v_reuseFailAlloc_4045_, 2, v_buildTime_3971_);
lean_ctor_set_uint8(v_reuseFailAlloc_4045_, sizeof(void*)*3 + 1, v_wantsRebuild_3969_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
lean_ctor_set_uint8(v___x_4044_, sizeof(void*)*3, v___x_3994_);
v___y_3959_ = v___x_3990_;
v_a_3960_ = v___x_4044_;
goto v___jp_3958_;
}
}
}
else
{
lean_object* v___x_4046_; lean_object* v___x_4047_; uint8_t v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4052_; 
lean_dec(v___x_3997_);
lean_dec_ref(v___f_3981_);
lean_dec_ref(v___x_3980_);
lean_dec_ref(v_a_3951_);
lean_dec(v_scope_x3f_3949_);
v___x_4046_ = ((lean_object*)(l_Lake_resolveArtifact___closed__6));
v___x_4047_ = lean_string_append(v___x_4046_, v_val_3991_);
lean_dec(v_val_3991_);
v___x_4048_ = 3;
v___x_4049_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4049_, 0, v___x_4047_);
lean_ctor_set_uint8(v___x_4049_, sizeof(void*)*1, v___x_4048_);
v___x_4050_ = lean_array_push(v_log_3967_, v___x_4049_);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 0, v___x_4050_);
v___x_4052_ = v___x_3987_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v___x_4050_);
lean_ctor_set(v_reuseFailAlloc_4053_, 1, v_trace_3970_);
lean_ctor_set(v_reuseFailAlloc_4053_, 2, v_buildTime_3971_);
lean_ctor_set_uint8(v_reuseFailAlloc_4053_, sizeof(void*)*3 + 1, v_wantsRebuild_3969_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
lean_ctor_set_uint8(v___x_4052_, sizeof(void*)*3, v___x_3994_);
v___y_3959_ = v___x_3990_;
v_a_3960_ = v___x_4052_;
goto v___jp_3958_;
}
}
}
else
{
lean_object* v___x_4054_; lean_object* v___x_4055_; uint8_t v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4060_; 
lean_dec_ref(v___f_3981_);
lean_dec_ref(v_a_3951_);
lean_dec(v_scope_x3f_3949_);
lean_dec(v_service_x3f_3948_);
v___x_4054_ = ((lean_object*)(l_Lake_resolveArtifact___closed__7));
v___x_4055_ = lean_string_append(v___x_4054_, v___x_3980_);
lean_dec_ref(v___x_3980_);
v___x_4056_ = 3;
v___x_4057_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4057_, 0, v___x_4055_);
lean_ctor_set_uint8(v___x_4057_, sizeof(void*)*1, v___x_4056_);
v___x_4058_ = lean_array_push(v_log_3967_, v___x_4057_);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 0, v___x_4058_);
v___x_4060_ = v___x_3987_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v___x_4058_);
lean_ctor_set(v_reuseFailAlloc_4061_, 1, v_trace_3970_);
lean_ctor_set(v_reuseFailAlloc_4061_, 2, v_buildTime_3971_);
lean_ctor_set_uint8(v_reuseFailAlloc_4061_, sizeof(void*)*3, v_action_3968_);
lean_ctor_set_uint8(v_reuseFailAlloc_4061_, sizeof(void*)*3 + 1, v_wantsRebuild_3969_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
v___y_3959_ = v___x_3990_;
v_a_3960_ = v___x_4060_;
goto v___jp_3958_;
}
}
}
else
{
lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; uint8_t v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4070_; 
lean_dec_ref(v___f_3981_);
lean_dec_ref(v___x_3980_);
lean_dec_ref(v_a_3951_);
lean_dec(v_scope_x3f_3949_);
lean_dec(v_service_x3f_3948_);
v___x_4062_ = ((lean_object*)(l_Lake_resolveArtifact___closed__8));
v___x_4063_ = lean_io_error_to_string(v_a_3989_);
v___x_4064_ = lean_string_append(v___x_4062_, v___x_4063_);
lean_dec_ref(v___x_4063_);
v___x_4065_ = 3;
v___x_4066_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4066_, 0, v___x_4064_);
lean_ctor_set_uint8(v___x_4066_, sizeof(void*)*1, v___x_4065_);
v___x_4067_ = lean_array_get_size(v_log_3967_);
v___x_4068_ = lean_array_push(v_log_3967_, v___x_4066_);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 0, v___x_4068_);
v___x_4070_ = v___x_3987_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v___x_4068_);
lean_ctor_set(v_reuseFailAlloc_4072_, 1, v_trace_3970_);
lean_ctor_set(v_reuseFailAlloc_4072_, 2, v_buildTime_3971_);
lean_ctor_set_uint8(v_reuseFailAlloc_4072_, sizeof(void*)*3, v_action_3968_);
lean_ctor_set_uint8(v_reuseFailAlloc_4072_, sizeof(void*)*3 + 1, v_wantsRebuild_3969_);
v___x_4070_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
lean_object* v___x_4071_; 
v___x_4071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4071_, 0, v___x_4067_);
lean_ctor_set(v___x_4071_, 1, v___x_4070_);
return v___x_4071_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___boxed(lean_object* v_descr_4085_, lean_object* v_service_x3f_4086_, lean_object* v_scope_x3f_4087_, lean_object* v_exe_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_){
_start:
{
uint8_t v_exe_boxed_4096_; lean_object* v_res_4097_; 
v_exe_boxed_4096_ = lean_unbox(v_exe_4088_);
v_res_4097_ = l_Lake_resolveArtifact(v_descr_4085_, v_service_x3f_4086_, v_scope_x3f_4087_, v_exe_boxed_4096_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_, v_a_4093_, v_a_4094_);
lean_dec_ref(v_a_4093_);
lean_dec(v_a_4092_);
lean_dec(v_a_4091_);
lean_dec(v_a_4090_);
return v_res_4097_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput(lean_object* v_out_4100_, uint8_t v_exe_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_){
_start:
{
lean_object* v_data_4109_; lean_object* v_service_x3f_4110_; lean_object* v_scope_x3f_4111_; lean_object* v___x_4112_; 
v_data_4109_ = lean_ctor_get(v_out_4100_, 0);
lean_inc_n(v_data_4109_, 2);
v_service_x3f_4110_ = lean_ctor_get(v_out_4100_, 1);
lean_inc(v_service_x3f_4110_);
v_scope_x3f_4111_ = lean_ctor_get(v_out_4100_, 2);
lean_inc(v_scope_x3f_4111_);
lean_dec_ref(v_out_4100_);
v___x_4112_ = l_Lake_ArtifactDescr_fromJson_x3f(v_data_4109_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v_a_4113_; lean_object* v_log_4114_; uint8_t v_action_4115_; uint8_t v_wantsRebuild_4116_; lean_object* v_trace_4117_; lean_object* v_buildTime_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4140_; 
lean_dec(v_scope_x3f_4111_);
lean_dec(v_service_x3f_4110_);
lean_dec_ref(v_a_4102_);
v_a_4113_ = lean_ctor_get(v___x_4112_, 0);
lean_inc(v_a_4113_);
lean_dec_ref(v___x_4112_);
v_log_4114_ = lean_ctor_get(v_a_4107_, 0);
v_action_4115_ = lean_ctor_get_uint8(v_a_4107_, sizeof(void*)*3);
v_wantsRebuild_4116_ = lean_ctor_get_uint8(v_a_4107_, sizeof(void*)*3 + 1);
v_trace_4117_ = lean_ctor_get(v_a_4107_, 1);
v_buildTime_4118_ = lean_ctor_get(v_a_4107_, 2);
v_isSharedCheck_4140_ = !lean_is_exclusive(v_a_4107_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4120_ = v_a_4107_;
v_isShared_4121_ = v_isSharedCheck_4140_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_buildTime_4118_);
lean_inc(v_trace_4117_);
lean_inc(v_log_4114_);
lean_dec(v_a_4107_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4140_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; uint8_t v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4137_; 
v___x_4122_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__0));
v___x_4123_ = l_Lean_Json_render(v_data_4109_);
v___x_4124_ = lean_unsigned_to_nat(80u);
v___x_4125_ = lean_unsigned_to_nat(2u);
v___x_4126_ = lean_unsigned_to_nat(0u);
v___x_4127_ = l_Std_Format_pretty(v___x_4123_, v___x_4124_, v___x_4125_, v___x_4126_);
v___x_4128_ = lean_string_append(v___x_4122_, v___x_4127_);
lean_dec_ref(v___x_4127_);
v___x_4129_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__1));
v___x_4130_ = lean_string_append(v___x_4128_, v___x_4129_);
v___x_4131_ = lean_string_append(v___x_4130_, v_a_4113_);
lean_dec(v_a_4113_);
v___x_4132_ = 3;
v___x_4133_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4133_, 0, v___x_4131_);
lean_ctor_set_uint8(v___x_4133_, sizeof(void*)*1, v___x_4132_);
v___x_4134_ = lean_array_get_size(v_log_4114_);
v___x_4135_ = lean_array_push(v_log_4114_, v___x_4133_);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 0, v___x_4135_);
v___x_4137_ = v___x_4120_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4135_);
lean_ctor_set(v_reuseFailAlloc_4139_, 1, v_trace_4117_);
lean_ctor_set(v_reuseFailAlloc_4139_, 2, v_buildTime_4118_);
lean_ctor_set_uint8(v_reuseFailAlloc_4139_, sizeof(void*)*3, v_action_4115_);
lean_ctor_set_uint8(v_reuseFailAlloc_4139_, sizeof(void*)*3 + 1, v_wantsRebuild_4116_);
v___x_4137_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
lean_object* v___x_4138_; 
v___x_4138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4134_);
lean_ctor_set(v___x_4138_, 1, v___x_4137_);
return v___x_4138_;
}
}
}
else
{
lean_object* v_a_4141_; lean_object* v___x_4142_; 
lean_dec(v_data_4109_);
v_a_4141_ = lean_ctor_get(v___x_4112_, 0);
lean_inc(v_a_4141_);
lean_dec_ref(v___x_4112_);
v___x_4142_ = l_Lake_resolveArtifact(v_a_4141_, v_service_x3f_4110_, v_scope_x3f_4111_, v_exe_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_);
return v___x_4142_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput___boxed(lean_object* v_out_4143_, lean_object* v_exe_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_){
_start:
{
uint8_t v_exe_boxed_4152_; lean_object* v_res_4153_; 
v_exe_boxed_4152_ = lean_unbox(v_exe_4144_);
v_res_4153_ = l_Lake_resolveArtifactOutput(v_out_4143_, v_exe_boxed_4152_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_, v_a_4150_);
lean_dec_ref(v_a_4149_);
lean_dec(v_a_4148_);
lean_dec(v_a_4147_);
lean_dec(v_a_4146_);
return v_res_4153_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(uint8_t v_exe_4154_, lean_object* v_out_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_){
_start:
{
lean_object* v___x_4163_; 
v___x_4163_ = l_Lake_resolveArtifactOutput(v_out_4155_, v_exe_4154_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_);
return v___x_4163_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed(lean_object* v_exe_4164_, lean_object* v_out_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_){
_start:
{
uint8_t v_exe_boxed_4173_; lean_object* v_res_4174_; 
v_exe_boxed_4173_ = lean_unbox(v_exe_4164_);
v_res_4174_ = l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(v_exe_boxed_4173_, v_out_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
lean_dec_ref(v___y_4170_);
lean_dec(v___y_4169_);
lean_dec(v___y_4168_);
lean_dec(v___y_4167_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(uint8_t v_exe_4175_){
_start:
{
lean_object* v___x_4176_; lean_object* v___f_4177_; 
v___x_4176_ = lean_box(v_exe_4175_);
v___f_4177_ = lean_alloc_closure((void*)(l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4177_, 0, v___x_4176_);
return v___f_4177_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___boxed(lean_object* v_exe_4178_){
_start:
{
uint8_t v_exe_boxed_4179_; lean_object* v_res_4180_; 
v_exe_boxed_4179_ = lean_unbox(v_exe_4178_);
v_res_4180_ = l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(v_exe_boxed_4179_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg(lean_object* v_path_4181_, lean_object* v_ext_4182_, uint8_t v_text_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_){
_start:
{
lean_object* v___x_4187_; 
lean_inc_ref(v_path_4181_);
v___x_4187_ = l_Lake_fetchFileHash___redArg(v_path_4181_, v_text_4183_, v_a_4184_, v_a_4185_);
if (lean_obj_tag(v___x_4187_) == 0)
{
lean_object* v_a_4188_; lean_object* v_a_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4206_; 
v_a_4188_ = lean_ctor_get(v___x_4187_, 0);
v_a_4189_ = lean_ctor_get(v___x_4187_, 1);
v_isSharedCheck_4206_ = !lean_is_exclusive(v___x_4187_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4191_ = v___x_4187_;
v_isShared_4192_ = v_isSharedCheck_4206_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_a_4189_);
lean_inc(v_a_4188_);
lean_dec(v___x_4187_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4206_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___x_4202_; 
v___x_4202_ = lean_io_metadata(v_path_4181_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v_a_4203_; lean_object* v_modified_4204_; 
v_a_4203_ = lean_ctor_get(v___x_4202_, 0);
lean_inc(v_a_4203_);
lean_dec_ref(v___x_4202_);
v_modified_4204_ = lean_ctor_get(v_a_4203_, 1);
lean_inc_ref(v_modified_4204_);
lean_dec(v_a_4203_);
v___y_4194_ = v_a_4189_;
v___y_4195_ = v_modified_4204_;
goto v___jp_4193_;
}
else
{
lean_object* v___x_4205_; 
lean_dec_ref(v___x_4202_);
v___x_4205_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___y_4194_ = v_a_4189_;
v___y_4195_ = v___x_4205_;
goto v___jp_4193_;
}
v___jp_4193_:
{
lean_object* v___x_4196_; uint64_t v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4200_; 
v___x_4196_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4196_, 0, v_ext_4182_);
v___x_4197_ = lean_unbox_uint64(v_a_4188_);
lean_dec(v_a_4188_);
lean_ctor_set_uint64(v___x_4196_, sizeof(void*)*1, v___x_4197_);
lean_inc_ref(v_path_4181_);
v___x_4198_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4198_, 0, v___x_4196_);
lean_ctor_set(v___x_4198_, 1, v_path_4181_);
lean_ctor_set(v___x_4198_, 2, v_path_4181_);
lean_ctor_set(v___x_4198_, 3, v___y_4195_);
if (v_isShared_4192_ == 0)
{
lean_ctor_set(v___x_4191_, 1, v___y_4194_);
lean_ctor_set(v___x_4191_, 0, v___x_4198_);
v___x_4200_ = v___x_4191_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v___x_4198_);
lean_ctor_set(v_reuseFailAlloc_4201_, 1, v___y_4194_);
v___x_4200_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
return v___x_4200_;
}
}
}
}
else
{
lean_object* v_a_4207_; lean_object* v_a_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4215_; 
lean_dec_ref(v_ext_4182_);
lean_dec_ref(v_path_4181_);
v_a_4207_ = lean_ctor_get(v___x_4187_, 0);
v_a_4208_ = lean_ctor_get(v___x_4187_, 1);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4187_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4210_ = v___x_4187_;
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_a_4208_);
lean_inc(v_a_4207_);
lean_dec(v___x_4187_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4213_; 
if (v_isShared_4211_ == 0)
{
v___x_4213_ = v___x_4210_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_a_4207_);
lean_ctor_set(v_reuseFailAlloc_4214_, 1, v_a_4208_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg___boxed(lean_object* v_path_4216_, lean_object* v_ext_4217_, lean_object* v_text_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_){
_start:
{
uint8_t v_text_boxed_4222_; lean_object* v_res_4223_; 
v_text_boxed_4222_ = lean_unbox(v_text_4218_);
v_res_4223_ = l_Lake_computeArtifact___redArg(v_path_4216_, v_ext_4217_, v_text_boxed_4222_, v_a_4219_, v_a_4220_);
lean_dec_ref(v_a_4219_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact(lean_object* v_path_4224_, lean_object* v_ext_4225_, uint8_t v_text_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_){
_start:
{
lean_object* v___x_4234_; 
v___x_4234_ = l_Lake_computeArtifact___redArg(v_path_4224_, v_ext_4225_, v_text_4226_, v_a_4231_, v_a_4232_);
return v___x_4234_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___boxed(lean_object* v_path_4235_, lean_object* v_ext_4236_, lean_object* v_text_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_){
_start:
{
uint8_t v_text_boxed_4245_; lean_object* v_res_4246_; 
v_text_boxed_4245_ = lean_unbox(v_text_4237_);
v_res_4246_ = l_Lake_computeArtifact(v_path_4235_, v_ext_4236_, v_text_boxed_4245_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_);
lean_dec_ref(v_a_4242_);
lean_dec(v_a_4241_);
lean_dec(v_a_4240_);
lean_dec(v_a_4239_);
lean_dec_ref(v_a_4238_);
return v_res_4246_;
}
}
LEAN_EXPORT lean_object* l_Lake_restoreArtifact(lean_object* v_file_4250_, lean_object* v_art_4251_, uint8_t v_exe_4252_, lean_object* v_a_4253_){
_start:
{
lean_object* v___y_4256_; uint8_t v___x_4269_; 
v___x_4269_ = l_System_FilePath_pathExists(v_file_4250_);
if (v___x_4269_ == 0)
{
lean_object* v_descr_4270_; lean_object* v_path_4271_; lean_object* v___y_4273_; lean_object* v___x_4288_; lean_object* v___x_4289_; uint8_t v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; 
v_descr_4270_ = lean_ctor_get(v_art_4251_, 0);
v_path_4271_ = lean_ctor_get(v_art_4251_, 1);
v___x_4288_ = ((lean_object*)(l_Lake_restoreArtifact___closed__1));
v___x_4289_ = lean_string_append(v___x_4288_, v_path_4271_);
v___x_4290_ = 0;
v___x_4291_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4291_, 0, v___x_4289_);
lean_ctor_set_uint8(v___x_4291_, sizeof(void*)*1, v___x_4290_);
v___x_4292_ = lean_array_push(v_a_4253_, v___x_4291_);
lean_inc_ref(v_file_4250_);
v___x_4293_ = l_Lake_createParentDirs(v_file_4250_);
if (lean_obj_tag(v___x_4293_) == 0)
{
lean_object* v___x_4294_; 
lean_dec_ref(v___x_4293_);
v___x_4294_ = lean_io_hard_link(v_path_4271_, v_file_4250_);
if (lean_obj_tag(v___x_4294_) == 0)
{
lean_dec_ref(v___x_4294_);
v___y_4273_ = v___x_4292_;
goto v___jp_4272_;
}
else
{
lean_object* v_a_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v_a_4295_ = lean_ctor_get(v___x_4294_, 0);
lean_inc(v_a_4295_);
lean_dec_ref(v___x_4294_);
v___x_4296_ = ((lean_object*)(l_Lake_restoreArtifact___closed__2));
v___x_4297_ = lean_io_error_to_string(v_a_4295_);
v___x_4298_ = lean_string_append(v___x_4296_, v___x_4297_);
lean_dec_ref(v___x_4297_);
v___x_4299_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4299_, 0, v___x_4298_);
lean_ctor_set_uint8(v___x_4299_, sizeof(void*)*1, v___x_4290_);
v___x_4300_ = lean_array_push(v___x_4292_, v___x_4299_);
v___x_4301_ = l_Lake_copyFile(v_path_4271_, v_file_4250_);
if (lean_obj_tag(v___x_4301_) == 0)
{
uint8_t v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; 
lean_dec_ref(v___x_4301_);
v___x_4302_ = 1;
v___x_4303_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4303_, 0, v___x_4302_);
lean_ctor_set_uint8(v___x_4303_, 1, v___x_4269_);
lean_ctor_set_uint8(v___x_4303_, 2, v_exe_4252_);
lean_inc_ref_n(v___x_4303_, 2);
v___x_4304_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4304_, 0, v___x_4303_);
lean_ctor_set(v___x_4304_, 1, v___x_4303_);
lean_ctor_set(v___x_4304_, 2, v___x_4303_);
v___x_4305_ = l_IO_setAccessRights(v_file_4250_, v___x_4304_);
lean_dec_ref(v___x_4304_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_dec_ref(v___x_4305_);
v___y_4273_ = v___x_4300_;
goto v___jp_4272_;
}
else
{
lean_object* v_a_4306_; lean_object* v___x_4307_; uint8_t v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; 
lean_dec_ref(v_art_4251_);
lean_dec_ref(v_file_4250_);
v_a_4306_ = lean_ctor_get(v___x_4305_, 0);
lean_inc(v_a_4306_);
lean_dec_ref(v___x_4305_);
v___x_4307_ = lean_io_error_to_string(v_a_4306_);
v___x_4308_ = 3;
v___x_4309_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4309_, 0, v___x_4307_);
lean_ctor_set_uint8(v___x_4309_, sizeof(void*)*1, v___x_4308_);
v___x_4310_ = lean_array_get_size(v___x_4300_);
v___x_4311_ = lean_array_push(v___x_4300_, v___x_4309_);
v___x_4312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4312_, 0, v___x_4310_);
lean_ctor_set(v___x_4312_, 1, v___x_4311_);
return v___x_4312_;
}
}
else
{
lean_object* v_a_4313_; lean_object* v___x_4314_; uint8_t v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
lean_dec_ref(v_art_4251_);
lean_dec_ref(v_file_4250_);
v_a_4313_ = lean_ctor_get(v___x_4301_, 0);
lean_inc(v_a_4313_);
lean_dec_ref(v___x_4301_);
v___x_4314_ = lean_io_error_to_string(v_a_4313_);
v___x_4315_ = 3;
v___x_4316_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4316_, 0, v___x_4314_);
lean_ctor_set_uint8(v___x_4316_, sizeof(void*)*1, v___x_4315_);
v___x_4317_ = lean_array_get_size(v___x_4300_);
v___x_4318_ = lean_array_push(v___x_4300_, v___x_4316_);
v___x_4319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4319_, 0, v___x_4317_);
lean_ctor_set(v___x_4319_, 1, v___x_4318_);
return v___x_4319_;
}
}
}
else
{
lean_object* v_a_4320_; lean_object* v___x_4321_; uint8_t v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; 
lean_dec_ref(v_art_4251_);
lean_dec_ref(v_file_4250_);
v_a_4320_ = lean_ctor_get(v___x_4293_, 0);
lean_inc(v_a_4320_);
lean_dec_ref(v___x_4293_);
v___x_4321_ = lean_io_error_to_string(v_a_4320_);
v___x_4322_ = 3;
v___x_4323_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4323_, 0, v___x_4321_);
lean_ctor_set_uint8(v___x_4323_, sizeof(void*)*1, v___x_4322_);
v___x_4324_ = lean_array_get_size(v___x_4292_);
v___x_4325_ = lean_array_push(v___x_4292_, v___x_4323_);
v___x_4326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4326_, 0, v___x_4324_);
lean_ctor_set(v___x_4326_, 1, v___x_4325_);
return v___x_4326_;
}
v___jp_4272_:
{
uint64_t v_hash_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; uint8_t v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; 
v_hash_4274_ = lean_ctor_get_uint64(v_descr_4270_, sizeof(void*)*1);
v___x_4275_ = ((lean_object*)(l_Lake_restoreArtifact___closed__0));
v___x_4276_ = lean_string_append(v___x_4275_, v_file_4250_);
v___x_4277_ = 0;
v___x_4278_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4278_, 0, v___x_4276_);
lean_ctor_set_uint8(v___x_4278_, sizeof(void*)*1, v___x_4277_);
v___x_4279_ = lean_array_push(v___y_4273_, v___x_4278_);
lean_inc_ref(v_file_4250_);
v___x_4280_ = l_Lake_writeFileHash(v_file_4250_, v_hash_4274_);
if (lean_obj_tag(v___x_4280_) == 0)
{
lean_dec_ref(v___x_4280_);
v___y_4256_ = v___x_4279_;
goto v___jp_4255_;
}
else
{
lean_object* v_a_4281_; lean_object* v___x_4282_; uint8_t v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
lean_dec_ref(v_art_4251_);
lean_dec_ref(v_file_4250_);
v_a_4281_ = lean_ctor_get(v___x_4280_, 0);
lean_inc(v_a_4281_);
lean_dec_ref(v___x_4280_);
v___x_4282_ = lean_io_error_to_string(v_a_4281_);
v___x_4283_ = 3;
v___x_4284_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4284_, 0, v___x_4282_);
lean_ctor_set_uint8(v___x_4284_, sizeof(void*)*1, v___x_4283_);
v___x_4285_ = lean_array_get_size(v___x_4279_);
v___x_4286_ = lean_array_push(v___x_4279_, v___x_4284_);
v___x_4287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4285_);
lean_ctor_set(v___x_4287_, 1, v___x_4286_);
return v___x_4287_;
}
}
}
else
{
v___y_4256_ = v_a_4253_;
goto v___jp_4255_;
}
v___jp_4255_:
{
lean_object* v_descr_4257_; lean_object* v_mtime_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4266_; 
v_descr_4257_ = lean_ctor_get(v_art_4251_, 0);
v_mtime_4258_ = lean_ctor_get(v_art_4251_, 3);
v_isSharedCheck_4266_ = !lean_is_exclusive(v_art_4251_);
if (v_isSharedCheck_4266_ == 0)
{
lean_object* v_unused_4267_; lean_object* v_unused_4268_; 
v_unused_4267_ = lean_ctor_get(v_art_4251_, 2);
lean_dec(v_unused_4267_);
v_unused_4268_ = lean_ctor_get(v_art_4251_, 1);
lean_dec(v_unused_4268_);
v___x_4260_ = v_art_4251_;
v_isShared_4261_ = v_isSharedCheck_4266_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_mtime_4258_);
lean_inc(v_descr_4257_);
lean_dec(v_art_4251_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4266_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4263_; 
lean_inc_ref(v_file_4250_);
if (v_isShared_4261_ == 0)
{
lean_ctor_set(v___x_4260_, 2, v_file_4250_);
lean_ctor_set(v___x_4260_, 1, v_file_4250_);
v___x_4263_ = v___x_4260_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_descr_4257_);
lean_ctor_set(v_reuseFailAlloc_4265_, 1, v_file_4250_);
lean_ctor_set(v_reuseFailAlloc_4265_, 2, v_file_4250_);
lean_ctor_set(v_reuseFailAlloc_4265_, 3, v_mtime_4258_);
v___x_4263_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
lean_object* v___x_4264_; 
v___x_4264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4264_, 0, v___x_4263_);
lean_ctor_set(v___x_4264_, 1, v___y_4256_);
return v___x_4264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_restoreArtifact___boxed(lean_object* v_file_4327_, lean_object* v_art_4328_, lean_object* v_exe_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_){
_start:
{
uint8_t v_exe_boxed_4332_; lean_object* v_res_4333_; 
v_exe_boxed_4332_ = lean_unbox(v_exe_4329_);
v_res_4333_ = l_Lake_restoreArtifact(v_file_4327_, v_art_4328_, v_exe_boxed_4332_, v_a_4330_);
return v_res_4333_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(lean_object* v_val_4334_, lean_object* v_a_x3f_4335_, lean_object* v___y_4336_){
_start:
{
lean_object* v___x_4338_; lean_object* v_log_4339_; uint8_t v_action_4340_; uint8_t v_wantsRebuild_4341_; lean_object* v_trace_4342_; lean_object* v_buildTime_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4354_; 
v___x_4338_ = lean_io_mono_ms_now();
v_log_4339_ = lean_ctor_get(v___y_4336_, 0);
v_action_4340_ = lean_ctor_get_uint8(v___y_4336_, sizeof(void*)*3);
v_wantsRebuild_4341_ = lean_ctor_get_uint8(v___y_4336_, sizeof(void*)*3 + 1);
v_trace_4342_ = lean_ctor_get(v___y_4336_, 1);
v_buildTime_4343_ = lean_ctor_get(v___y_4336_, 2);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___y_4336_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4345_ = v___y_4336_;
v_isShared_4346_ = v_isSharedCheck_4354_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_buildTime_4343_);
lean_inc(v_trace_4342_);
lean_inc(v_log_4339_);
lean_dec(v___y_4336_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4354_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4351_; 
v___x_4347_ = lean_nat_sub(v___x_4338_, v_val_4334_);
lean_dec(v___x_4338_);
v___x_4348_ = lean_box(0);
v___x_4349_ = lean_nat_add(v_buildTime_4343_, v___x_4347_);
lean_dec(v___x_4347_);
lean_dec(v_buildTime_4343_);
if (v_isShared_4346_ == 0)
{
lean_ctor_set(v___x_4345_, 2, v___x_4349_);
v___x_4351_ = v___x_4345_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_log_4339_);
lean_ctor_set(v_reuseFailAlloc_4353_, 1, v_trace_4342_);
lean_ctor_set(v_reuseFailAlloc_4353_, 2, v___x_4349_);
lean_ctor_set_uint8(v_reuseFailAlloc_4353_, sizeof(void*)*3, v_action_4340_);
lean_ctor_set_uint8(v_reuseFailAlloc_4353_, sizeof(void*)*3 + 1, v_wantsRebuild_4341_);
v___x_4351_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
lean_object* v___x_4352_; 
v___x_4352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4352_, 0, v___x_4348_);
lean_ctor_set(v___x_4352_, 1, v___x_4351_);
return v___x_4352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0___boxed(lean_object* v_val_4355_, lean_object* v_a_x3f_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_){
_start:
{
lean_object* v_res_4359_; 
v_res_4359_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v_val_4355_, v_a_x3f_4356_, v___y_4357_);
lean_dec(v_a_x3f_4356_);
lean_dec(v_val_4355_);
return v_res_4359_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(lean_object* v_file_4360_, lean_object* v_build_4361_, lean_object* v_traceFile_4362_, lean_object* v_ext_4363_, uint8_t v_text_4364_, lean_object* v_a_4365_, lean_object* v_depTrace_4366_, lean_object* v_traceFile_4367_, uint8_t v_action_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_){
_start:
{
lean_object* v_a_4376_; lean_object* v_a_4377_; lean_object* v_log_4380_; uint8_t v_action_4381_; uint8_t v_wantsRebuild_4382_; lean_object* v_trace_4383_; lean_object* v_buildTime_4384_; lean_object* v_toBuildConfig_4390_; lean_object* v_log_4391_; uint8_t v_action_4392_; uint8_t v_wantsRebuild_4393_; lean_object* v_trace_4394_; lean_object* v_buildTime_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4574_; 
v_toBuildConfig_4390_ = lean_ctor_get(v_a_4372_, 0);
v_log_4391_ = lean_ctor_get(v_a_4373_, 0);
v_action_4392_ = lean_ctor_get_uint8(v_a_4373_, sizeof(void*)*3);
v_wantsRebuild_4393_ = lean_ctor_get_uint8(v_a_4373_, sizeof(void*)*3 + 1);
v_trace_4394_ = lean_ctor_get(v_a_4373_, 1);
v_buildTime_4395_ = lean_ctor_get(v_a_4373_, 2);
v_isSharedCheck_4574_ = !lean_is_exclusive(v_a_4373_);
if (v_isSharedCheck_4574_ == 0)
{
v___x_4397_ = v_a_4373_;
v_isShared_4398_ = v_isSharedCheck_4574_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_buildTime_4395_);
lean_inc(v_trace_4394_);
lean_inc(v_log_4391_);
lean_dec(v_a_4373_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4574_;
goto v_resetjp_4396_;
}
v___jp_4375_:
{
lean_object* v___x_4378_; 
v___x_4378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4378_, 0, v_a_4376_);
lean_ctor_set(v___x_4378_, 1, v_a_4377_);
return v___x_4378_;
}
v___jp_4379_:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; 
v___x_4385_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_4386_ = lean_array_get_size(v_log_4380_);
v___x_4387_ = lean_array_push(v_log_4380_, v___x_4385_);
v___x_4388_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4388_, 0, v___x_4387_);
lean_ctor_set(v___x_4388_, 1, v_trace_4383_);
lean_ctor_set(v___x_4388_, 2, v_buildTime_4384_);
lean_ctor_set_uint8(v___x_4388_, sizeof(void*)*3, v_action_4381_);
lean_ctor_set_uint8(v___x_4388_, sizeof(void*)*3 + 1, v_wantsRebuild_4382_);
v___x_4389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4386_);
lean_ctor_set(v___x_4389_, 1, v___x_4388_);
return v___x_4389_;
}
v_resetjp_4396_:
{
uint8_t v_noBuild_4399_; uint8_t v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; 
v_noBuild_4399_ = lean_ctor_get_uint8(v_toBuildConfig_4390_, sizeof(void*)*2 + 2);
v___x_4400_ = l_Lake_JobAction_merge(v_action_4392_, v_action_4368_);
v___x_4401_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_4367_);
v___x_4402_ = l_System_FilePath_addExtension(v_traceFile_4367_, v___x_4401_);
if (v_noBuild_4399_ == 0)
{
lean_object* v___x_4403_; lean_object* v_a_4405_; lean_object* v_a_4406_; lean_object* v___x_4410_; 
v___x_4403_ = lean_io_mono_ms_now();
v___x_4410_ = l_Lake_removeFileIfExists(v_file_4360_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v___x_4412_; 
lean_dec_ref(v___x_4410_);
lean_inc_ref(v_log_4391_);
if (v_isShared_4398_ == 0)
{
v___x_4412_ = v___x_4397_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_log_4391_);
lean_ctor_set(v_reuseFailAlloc_4549_, 1, v_trace_4394_);
lean_ctor_set(v_reuseFailAlloc_4549_, 2, v_buildTime_4395_);
lean_ctor_set_uint8(v_reuseFailAlloc_4549_, sizeof(void*)*3 + 1, v_wantsRebuild_4393_);
v___x_4412_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
lean_object* v___x_4413_; 
lean_ctor_set_uint8(v___x_4412_, sizeof(void*)*3, v___x_4400_);
lean_inc_ref(v_a_4372_);
lean_inc(v_a_4371_);
lean_inc(v_a_4370_);
lean_inc(v_a_4369_);
v___x_4413_ = lean_apply_7(v_build_4361_, v_a_4365_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v___x_4412_, lean_box(0));
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_object* v_a_4414_; lean_object* v_log_4415_; uint8_t v_action_4416_; uint8_t v_wantsRebuild_4417_; lean_object* v_trace_4418_; lean_object* v_buildTime_4419_; lean_object* v___x_4420_; 
v_a_4414_ = lean_ctor_get(v___x_4413_, 1);
lean_inc(v_a_4414_);
lean_dec_ref(v___x_4413_);
v_log_4415_ = lean_ctor_get(v_a_4414_, 0);
v_action_4416_ = lean_ctor_get_uint8(v_a_4414_, sizeof(void*)*3);
v_wantsRebuild_4417_ = lean_ctor_get_uint8(v_a_4414_, sizeof(void*)*3 + 1);
v_trace_4418_ = lean_ctor_get(v_a_4414_, 1);
v_buildTime_4419_ = lean_ctor_get(v_a_4414_, 2);
lean_inc_ref(v_file_4360_);
v___x_4420_ = l_Lake_clearFileHash(v_file_4360_);
if (lean_obj_tag(v___x_4420_) == 0)
{
lean_object* v___x_4421_; 
lean_dec_ref(v___x_4420_);
v___x_4421_ = l_Lake_removeFileIfExists(v_traceFile_4362_);
if (lean_obj_tag(v___x_4421_) == 0)
{
lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4513_; 
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4513_ == 0)
{
lean_object* v_unused_4514_; 
v_unused_4514_ = lean_ctor_get(v___x_4421_, 0);
lean_dec(v_unused_4514_);
v___x_4423_ = v___x_4421_;
v_isShared_4424_ = v_isSharedCheck_4513_;
goto v_resetjp_4422_;
}
else
{
lean_dec(v___x_4421_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4513_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v___x_4425_; 
v___x_4425_ = l_Lake_computeArtifact___redArg(v_file_4360_, v_ext_4363_, v_text_4364_, v_a_4372_, v_a_4414_);
if (lean_obj_tag(v___x_4425_) == 0)
{
lean_object* v_a_4426_; lean_object* v_a_4427_; lean_object* v_descr_4428_; lean_object* v_log_4429_; uint8_t v_action_4430_; uint8_t v_wantsRebuild_4431_; lean_object* v_trace_4432_; lean_object* v_buildTime_4433_; uint64_t v_hash_4434_; lean_object* v_ext_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___y_4440_; lean_object* v___x_4503_; lean_object* v___x_4504_; uint8_t v___x_4505_; 
v_a_4426_ = lean_ctor_get(v___x_4425_, 1);
lean_inc(v_a_4426_);
v_a_4427_ = lean_ctor_get(v___x_4425_, 0);
lean_inc(v_a_4427_);
lean_dec_ref(v___x_4425_);
v_descr_4428_ = lean_ctor_get(v_a_4427_, 0);
v_log_4429_ = lean_ctor_get(v_a_4426_, 0);
v_action_4430_ = lean_ctor_get_uint8(v_a_4426_, sizeof(void*)*3);
v_wantsRebuild_4431_ = lean_ctor_get_uint8(v_a_4426_, sizeof(void*)*3 + 1);
v_trace_4432_ = lean_ctor_get(v_a_4426_, 1);
v_buildTime_4433_ = lean_ctor_get(v_a_4426_, 2);
v_hash_4434_ = lean_ctor_get_uint64(v_descr_4428_, sizeof(void*)*1);
v_ext_4435_ = lean_ctor_get(v_descr_4428_, 0);
v___x_4436_ = lean_array_get_size(v_log_4391_);
lean_dec_ref(v_log_4391_);
v___x_4437_ = lean_array_get_size(v_log_4429_);
v___x_4438_ = l_Array_extract___redArg(v_log_4429_, v___x_4436_, v___x_4437_);
v___x_4503_ = lean_string_utf8_byte_size(v_ext_4435_);
v___x_4504_ = lean_unsigned_to_nat(0u);
v___x_4505_ = lean_nat_dec_eq(v___x_4503_, v___x_4504_);
if (v___x_4505_ == 0)
{
lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; 
v___x_4506_ = l_Lake_Hash_hex(v_hash_4434_);
v___x_4507_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_4508_ = lean_string_append(v___x_4506_, v___x_4507_);
v___x_4509_ = lean_string_append(v___x_4508_, v_ext_4435_);
v___y_4440_ = v___x_4509_;
goto v___jp_4439_;
}
else
{
lean_object* v___x_4510_; 
v___x_4510_ = l_Lake_Hash_hex(v_hash_4434_);
v___y_4440_ = v___x_4510_;
goto v___jp_4439_;
}
v___jp_4439_:
{
lean_object* v___x_4442_; 
if (v_isShared_4424_ == 0)
{
lean_ctor_set_tag(v___x_4423_, 3);
lean_ctor_set(v___x_4423_, 0, v___y_4440_);
v___x_4442_ = v___x_4423_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v___y_4440_);
v___x_4442_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
lean_object* v___x_4443_; lean_object* v___x_4444_; 
v___x_4443_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_4366_, v___x_4442_, v___x_4438_);
v___x_4444_ = l_Lake_BuildMetadata_writeFile(v_traceFile_4367_, v___x_4443_);
if (lean_obj_tag(v___x_4444_) == 0)
{
lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4485_; 
v_isSharedCheck_4485_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4485_ == 0)
{
lean_object* v_unused_4486_; 
v_unused_4486_ = lean_ctor_get(v___x_4444_, 0);
lean_dec(v_unused_4486_);
v___x_4446_ = v___x_4444_;
v_isShared_4447_ = v_isSharedCheck_4485_;
goto v_resetjp_4445_;
}
else
{
lean_dec(v___x_4444_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4485_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v___x_4448_; 
v___x_4448_ = l_Lake_removeFileIfExists(v___x_4402_);
lean_dec_ref(v___x_4402_);
if (lean_obj_tag(v___x_4448_) == 0)
{
lean_object* v___x_4450_; uint8_t v_isShared_4451_; uint8_t v_isSharedCheck_4468_; 
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4448_);
if (v_isSharedCheck_4468_ == 0)
{
lean_object* v_unused_4469_; 
v_unused_4469_ = lean_ctor_get(v___x_4448_, 0);
lean_dec(v_unused_4469_);
v___x_4450_ = v___x_4448_;
v_isShared_4451_ = v_isSharedCheck_4468_;
goto v_resetjp_4449_;
}
else
{
lean_dec(v___x_4448_);
v___x_4450_ = lean_box(0);
v_isShared_4451_ = v_isSharedCheck_4468_;
goto v_resetjp_4449_;
}
v_resetjp_4449_:
{
lean_object* v___x_4453_; 
lean_inc(v_a_4427_);
if (v_isShared_4451_ == 0)
{
lean_ctor_set(v___x_4450_, 0, v_a_4427_);
v___x_4453_ = v___x_4450_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_a_4427_);
v___x_4453_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
lean_object* v___x_4455_; 
if (v_isShared_4447_ == 0)
{
lean_ctor_set_tag(v___x_4446_, 1);
lean_ctor_set(v___x_4446_, 0, v___x_4453_);
v___x_4455_ = v___x_4446_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v___x_4453_);
v___x_4455_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
lean_object* v___x_4456_; lean_object* v_a_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4464_; 
v___x_4456_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v___x_4403_, v___x_4455_, v_a_4426_);
lean_dec_ref(v___x_4455_);
lean_dec(v___x_4403_);
v_a_4457_ = lean_ctor_get(v___x_4456_, 1);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4456_);
if (v_isSharedCheck_4464_ == 0)
{
lean_object* v_unused_4465_; 
v_unused_4465_ = lean_ctor_get(v___x_4456_, 0);
lean_dec(v_unused_4465_);
v___x_4459_ = v___x_4456_;
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_a_4457_);
lean_dec(v___x_4456_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4462_; 
if (v_isShared_4460_ == 0)
{
lean_ctor_set(v___x_4459_, 0, v_a_4427_);
v___x_4462_ = v___x_4459_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_a_4427_);
lean_ctor_set(v_reuseFailAlloc_4463_, 1, v_a_4457_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
}
}
}
}
else
{
lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4481_; 
lean_inc(v_buildTime_4433_);
lean_inc_ref(v_trace_4432_);
lean_inc_ref(v_log_4429_);
lean_del_object(v___x_4446_);
lean_dec(v_a_4427_);
v_isSharedCheck_4481_ = !lean_is_exclusive(v_a_4426_);
if (v_isSharedCheck_4481_ == 0)
{
lean_object* v_unused_4482_; lean_object* v_unused_4483_; lean_object* v_unused_4484_; 
v_unused_4482_ = lean_ctor_get(v_a_4426_, 2);
lean_dec(v_unused_4482_);
v_unused_4483_ = lean_ctor_get(v_a_4426_, 1);
lean_dec(v_unused_4483_);
v_unused_4484_ = lean_ctor_get(v_a_4426_, 0);
lean_dec(v_unused_4484_);
v___x_4471_ = v_a_4426_;
v_isShared_4472_ = v_isSharedCheck_4481_;
goto v_resetjp_4470_;
}
else
{
lean_dec(v_a_4426_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4481_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v_a_4473_; lean_object* v___x_4474_; uint8_t v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4479_; 
v_a_4473_ = lean_ctor_get(v___x_4448_, 0);
lean_inc(v_a_4473_);
lean_dec_ref(v___x_4448_);
v___x_4474_ = lean_io_error_to_string(v_a_4473_);
v___x_4475_ = 3;
v___x_4476_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4476_, 0, v___x_4474_);
lean_ctor_set_uint8(v___x_4476_, sizeof(void*)*1, v___x_4475_);
v___x_4477_ = lean_array_push(v_log_4429_, v___x_4476_);
if (v_isShared_4472_ == 0)
{
lean_ctor_set(v___x_4471_, 0, v___x_4477_);
v___x_4479_ = v___x_4471_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4477_);
lean_ctor_set(v_reuseFailAlloc_4480_, 1, v_trace_4432_);
lean_ctor_set(v_reuseFailAlloc_4480_, 2, v_buildTime_4433_);
lean_ctor_set_uint8(v_reuseFailAlloc_4480_, sizeof(void*)*3, v_action_4430_);
lean_ctor_set_uint8(v_reuseFailAlloc_4480_, sizeof(void*)*3 + 1, v_wantsRebuild_4431_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
v_a_4405_ = v___x_4437_;
v_a_4406_ = v___x_4479_;
goto v___jp_4404_;
}
}
}
}
}
else
{
lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4498_; 
lean_inc(v_buildTime_4433_);
lean_inc_ref(v_trace_4432_);
lean_inc_ref(v_log_4429_);
lean_dec(v_a_4427_);
lean_dec_ref(v___x_4402_);
v_isSharedCheck_4498_ = !lean_is_exclusive(v_a_4426_);
if (v_isSharedCheck_4498_ == 0)
{
lean_object* v_unused_4499_; lean_object* v_unused_4500_; lean_object* v_unused_4501_; 
v_unused_4499_ = lean_ctor_get(v_a_4426_, 2);
lean_dec(v_unused_4499_);
v_unused_4500_ = lean_ctor_get(v_a_4426_, 1);
lean_dec(v_unused_4500_);
v_unused_4501_ = lean_ctor_get(v_a_4426_, 0);
lean_dec(v_unused_4501_);
v___x_4488_ = v_a_4426_;
v_isShared_4489_ = v_isSharedCheck_4498_;
goto v_resetjp_4487_;
}
else
{
lean_dec(v_a_4426_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4498_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v_a_4490_; lean_object* v___x_4491_; uint8_t v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4496_; 
v_a_4490_ = lean_ctor_get(v___x_4444_, 0);
lean_inc(v_a_4490_);
lean_dec_ref(v___x_4444_);
v___x_4491_ = lean_io_error_to_string(v_a_4490_);
v___x_4492_ = 3;
v___x_4493_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4493_, 0, v___x_4491_);
lean_ctor_set_uint8(v___x_4493_, sizeof(void*)*1, v___x_4492_);
v___x_4494_ = lean_array_push(v_log_4429_, v___x_4493_);
if (v_isShared_4489_ == 0)
{
lean_ctor_set(v___x_4488_, 0, v___x_4494_);
v___x_4496_ = v___x_4488_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v___x_4494_);
lean_ctor_set(v_reuseFailAlloc_4497_, 1, v_trace_4432_);
lean_ctor_set(v_reuseFailAlloc_4497_, 2, v_buildTime_4433_);
lean_ctor_set_uint8(v_reuseFailAlloc_4497_, sizeof(void*)*3, v_action_4430_);
lean_ctor_set_uint8(v_reuseFailAlloc_4497_, sizeof(void*)*3 + 1, v_wantsRebuild_4431_);
v___x_4496_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
v_a_4405_ = v___x_4437_;
v_a_4406_ = v___x_4496_;
goto v___jp_4404_;
}
}
}
}
}
}
else
{
lean_object* v_a_4511_; lean_object* v_a_4512_; 
lean_del_object(v___x_4423_);
lean_dec_ref(v___x_4402_);
lean_dec_ref(v_log_4391_);
lean_dec_ref(v_traceFile_4367_);
v_a_4511_ = lean_ctor_get(v___x_4425_, 0);
lean_inc(v_a_4511_);
v_a_4512_ = lean_ctor_get(v___x_4425_, 1);
lean_inc(v_a_4512_);
lean_dec_ref(v___x_4425_);
v_a_4405_ = v_a_4511_;
v_a_4406_ = v_a_4512_;
goto v___jp_4404_;
}
}
}
else
{
lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4527_; 
lean_inc(v_buildTime_4419_);
lean_inc_ref(v_trace_4418_);
lean_inc_ref(v_log_4415_);
lean_dec_ref(v___x_4402_);
lean_dec_ref(v_log_4391_);
lean_dec_ref(v_traceFile_4367_);
lean_dec_ref(v_ext_4363_);
lean_dec_ref(v_file_4360_);
v_isSharedCheck_4527_ = !lean_is_exclusive(v_a_4414_);
if (v_isSharedCheck_4527_ == 0)
{
lean_object* v_unused_4528_; lean_object* v_unused_4529_; lean_object* v_unused_4530_; 
v_unused_4528_ = lean_ctor_get(v_a_4414_, 2);
lean_dec(v_unused_4528_);
v_unused_4529_ = lean_ctor_get(v_a_4414_, 1);
lean_dec(v_unused_4529_);
v_unused_4530_ = lean_ctor_get(v_a_4414_, 0);
lean_dec(v_unused_4530_);
v___x_4516_ = v_a_4414_;
v_isShared_4517_ = v_isSharedCheck_4527_;
goto v_resetjp_4515_;
}
else
{
lean_dec(v_a_4414_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4527_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v_a_4518_; lean_object* v___x_4519_; uint8_t v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4525_; 
v_a_4518_ = lean_ctor_get(v___x_4421_, 0);
lean_inc(v_a_4518_);
lean_dec_ref(v___x_4421_);
v___x_4519_ = lean_io_error_to_string(v_a_4518_);
v___x_4520_ = 3;
v___x_4521_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4521_, 0, v___x_4519_);
lean_ctor_set_uint8(v___x_4521_, sizeof(void*)*1, v___x_4520_);
v___x_4522_ = lean_array_get_size(v_log_4415_);
v___x_4523_ = lean_array_push(v_log_4415_, v___x_4521_);
if (v_isShared_4517_ == 0)
{
lean_ctor_set(v___x_4516_, 0, v___x_4523_);
v___x_4525_ = v___x_4516_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v___x_4523_);
lean_ctor_set(v_reuseFailAlloc_4526_, 1, v_trace_4418_);
lean_ctor_set(v_reuseFailAlloc_4526_, 2, v_buildTime_4419_);
lean_ctor_set_uint8(v_reuseFailAlloc_4526_, sizeof(void*)*3, v_action_4416_);
lean_ctor_set_uint8(v_reuseFailAlloc_4526_, sizeof(void*)*3 + 1, v_wantsRebuild_4417_);
v___x_4525_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
v_a_4405_ = v___x_4522_;
v_a_4406_ = v___x_4525_;
goto v___jp_4404_;
}
}
}
}
else
{
lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4543_; 
lean_inc(v_buildTime_4419_);
lean_inc_ref(v_trace_4418_);
lean_inc_ref(v_log_4415_);
lean_dec_ref(v___x_4402_);
lean_dec_ref(v_log_4391_);
lean_dec_ref(v_traceFile_4367_);
lean_dec_ref(v_ext_4363_);
lean_dec_ref(v_file_4360_);
v_isSharedCheck_4543_ = !lean_is_exclusive(v_a_4414_);
if (v_isSharedCheck_4543_ == 0)
{
lean_object* v_unused_4544_; lean_object* v_unused_4545_; lean_object* v_unused_4546_; 
v_unused_4544_ = lean_ctor_get(v_a_4414_, 2);
lean_dec(v_unused_4544_);
v_unused_4545_ = lean_ctor_get(v_a_4414_, 1);
lean_dec(v_unused_4545_);
v_unused_4546_ = lean_ctor_get(v_a_4414_, 0);
lean_dec(v_unused_4546_);
v___x_4532_ = v_a_4414_;
v_isShared_4533_ = v_isSharedCheck_4543_;
goto v_resetjp_4531_;
}
else
{
lean_dec(v_a_4414_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4543_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v_a_4534_; lean_object* v___x_4535_; uint8_t v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4541_; 
v_a_4534_ = lean_ctor_get(v___x_4420_, 0);
lean_inc(v_a_4534_);
lean_dec_ref(v___x_4420_);
v___x_4535_ = lean_io_error_to_string(v_a_4534_);
v___x_4536_ = 3;
v___x_4537_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4537_, 0, v___x_4535_);
lean_ctor_set_uint8(v___x_4537_, sizeof(void*)*1, v___x_4536_);
v___x_4538_ = lean_array_get_size(v_log_4415_);
v___x_4539_ = lean_array_push(v_log_4415_, v___x_4537_);
if (v_isShared_4533_ == 0)
{
lean_ctor_set(v___x_4532_, 0, v___x_4539_);
v___x_4541_ = v___x_4532_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v___x_4539_);
lean_ctor_set(v_reuseFailAlloc_4542_, 1, v_trace_4418_);
lean_ctor_set(v_reuseFailAlloc_4542_, 2, v_buildTime_4419_);
lean_ctor_set_uint8(v_reuseFailAlloc_4542_, sizeof(void*)*3, v_action_4416_);
lean_ctor_set_uint8(v_reuseFailAlloc_4542_, sizeof(void*)*3 + 1, v_wantsRebuild_4417_);
v___x_4541_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
v_a_4405_ = v___x_4538_;
v_a_4406_ = v___x_4541_;
goto v___jp_4404_;
}
}
}
}
else
{
lean_object* v_a_4547_; lean_object* v_a_4548_; 
lean_dec_ref(v___x_4402_);
lean_dec_ref(v_log_4391_);
lean_dec_ref(v_traceFile_4367_);
lean_dec_ref(v_ext_4363_);
lean_dec_ref(v_file_4360_);
v_a_4547_ = lean_ctor_get(v___x_4413_, 0);
lean_inc(v_a_4547_);
v_a_4548_ = lean_ctor_get(v___x_4413_, 1);
lean_inc(v_a_4548_);
lean_dec_ref(v___x_4413_);
v_a_4405_ = v_a_4547_;
v_a_4406_ = v_a_4548_;
goto v___jp_4404_;
}
}
}
else
{
lean_object* v_a_4550_; lean_object* v___x_4551_; uint8_t v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4557_; 
lean_dec_ref(v___x_4402_);
lean_dec_ref(v_traceFile_4367_);
lean_dec_ref(v_a_4365_);
lean_dec_ref(v_ext_4363_);
lean_dec_ref(v_build_4361_);
lean_dec_ref(v_file_4360_);
v_a_4550_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_a_4550_);
lean_dec_ref(v___x_4410_);
v___x_4551_ = lean_io_error_to_string(v_a_4550_);
v___x_4552_ = 3;
v___x_4553_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4553_, 0, v___x_4551_);
lean_ctor_set_uint8(v___x_4553_, sizeof(void*)*1, v___x_4552_);
v___x_4554_ = lean_array_get_size(v_log_4391_);
v___x_4555_ = lean_array_push(v_log_4391_, v___x_4553_);
if (v_isShared_4398_ == 0)
{
lean_ctor_set(v___x_4397_, 0, v___x_4555_);
v___x_4557_ = v___x_4397_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v___x_4555_);
lean_ctor_set(v_reuseFailAlloc_4558_, 1, v_trace_4394_);
lean_ctor_set(v_reuseFailAlloc_4558_, 2, v_buildTime_4395_);
lean_ctor_set_uint8(v_reuseFailAlloc_4558_, sizeof(void*)*3 + 1, v_wantsRebuild_4393_);
v___x_4557_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
lean_ctor_set_uint8(v___x_4557_, sizeof(void*)*3, v___x_4400_);
v_a_4405_ = v___x_4554_;
v_a_4406_ = v___x_4557_;
goto v___jp_4404_;
}
}
v___jp_4404_:
{
lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v_a_4409_; 
v___x_4407_ = lean_box(0);
v___x_4408_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v___x_4403_, v___x_4407_, v_a_4406_);
lean_dec(v___x_4403_);
v_a_4409_ = lean_ctor_get(v___x_4408_, 1);
lean_inc(v_a_4409_);
lean_dec_ref(v___x_4408_);
v_a_4376_ = v_a_4405_;
v_a_4377_ = v_a_4409_;
goto v___jp_4375_;
}
}
else
{
uint8_t v___x_4559_; 
lean_dec_ref(v_a_4365_);
lean_dec_ref(v_ext_4363_);
lean_dec_ref(v_build_4361_);
lean_dec_ref(v_file_4360_);
v___x_4559_ = l_System_FilePath_pathExists(v_traceFile_4367_);
lean_dec_ref(v_traceFile_4367_);
if (v___x_4559_ == 0)
{
lean_dec_ref(v___x_4402_);
lean_del_object(v___x_4397_);
v_log_4380_ = v_log_4391_;
v_action_4381_ = v___x_4400_;
v_wantsRebuild_4382_ = v_noBuild_4399_;
v_trace_4383_ = v_trace_4394_;
v_buildTime_4384_ = v_buildTime_4395_;
goto v___jp_4379_;
}
else
{
lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4560_ = lean_box(0);
v___x_4561_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_4562_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_4366_, v___x_4560_, v___x_4561_);
v___x_4563_ = l_Lake_BuildMetadata_writeFile(v___x_4402_, v___x_4562_);
if (lean_obj_tag(v___x_4563_) == 0)
{
lean_dec_ref(v___x_4563_);
lean_del_object(v___x_4397_);
v_log_4380_ = v_log_4391_;
v_action_4381_ = v___x_4400_;
v_wantsRebuild_4382_ = v_noBuild_4399_;
v_trace_4383_ = v_trace_4394_;
v_buildTime_4384_ = v_buildTime_4395_;
goto v___jp_4379_;
}
else
{
lean_object* v_a_4564_; lean_object* v___x_4565_; uint8_t v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4571_; 
v_a_4564_ = lean_ctor_get(v___x_4563_, 0);
lean_inc(v_a_4564_);
lean_dec_ref(v___x_4563_);
v___x_4565_ = lean_io_error_to_string(v_a_4564_);
v___x_4566_ = 3;
v___x_4567_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4567_, 0, v___x_4565_);
lean_ctor_set_uint8(v___x_4567_, sizeof(void*)*1, v___x_4566_);
v___x_4568_ = lean_array_get_size(v_log_4391_);
v___x_4569_ = lean_array_push(v_log_4391_, v___x_4567_);
if (v_isShared_4398_ == 0)
{
lean_ctor_set(v___x_4397_, 0, v___x_4569_);
v___x_4571_ = v___x_4397_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4573_; 
v_reuseFailAlloc_4573_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4573_, 0, v___x_4569_);
lean_ctor_set(v_reuseFailAlloc_4573_, 1, v_trace_4394_);
lean_ctor_set(v_reuseFailAlloc_4573_, 2, v_buildTime_4395_);
v___x_4571_ = v_reuseFailAlloc_4573_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
lean_object* v___x_4572_; 
lean_ctor_set_uint8(v___x_4571_, sizeof(void*)*3, v___x_4400_);
lean_ctor_set_uint8(v___x_4571_, sizeof(void*)*3 + 1, v_noBuild_4399_);
v___x_4572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4572_, 0, v___x_4568_);
lean_ctor_set(v___x_4572_, 1, v___x_4571_);
return v___x_4572_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___boxed(lean_object* v_file_4575_, lean_object* v_build_4576_, lean_object* v_traceFile_4577_, lean_object* v_ext_4578_, lean_object* v_text_4579_, lean_object* v_a_4580_, lean_object* v_depTrace_4581_, lean_object* v_traceFile_4582_, lean_object* v_action_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_){
_start:
{
uint8_t v_text_boxed_4590_; uint8_t v_action_boxed_4591_; lean_object* v_res_4592_; 
v_text_boxed_4590_ = lean_unbox(v_text_4579_);
v_action_boxed_4591_ = lean_unbox(v_action_4583_);
v_res_4592_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(v_file_4575_, v_build_4576_, v_traceFile_4577_, v_ext_4578_, v_text_boxed_4590_, v_a_4580_, v_depTrace_4581_, v_traceFile_4582_, v_action_boxed_4591_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_);
lean_dec_ref(v_a_4587_);
lean_dec(v_a_4586_);
lean_dec(v_a_4585_);
lean_dec(v_a_4584_);
lean_dec_ref(v_depTrace_4581_);
lean_dec_ref(v_traceFile_4577_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(lean_object* v_file_4593_, lean_object* v_build_4594_, uint8_t v_text_4595_, lean_object* v_ext_4596_, lean_object* v_depTrace_4597_, lean_object* v_traceFile_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_){
_start:
{
uint8_t v___x_4606_; lean_object* v___x_4607_; 
v___x_4606_ = 3;
lean_inc_ref(v_traceFile_4598_);
v___x_4607_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(v_file_4593_, v_build_4594_, v_traceFile_4598_, v_ext_4596_, v_text_4595_, v_a_4599_, v_depTrace_4597_, v_traceFile_4598_, v___x_4606_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_, v_a_4604_);
lean_dec_ref(v_traceFile_4598_);
return v___x_4607_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild___boxed(lean_object* v_file_4608_, lean_object* v_build_4609_, lean_object* v_text_4610_, lean_object* v_ext_4611_, lean_object* v_depTrace_4612_, lean_object* v_traceFile_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_){
_start:
{
uint8_t v_text_boxed_4621_; lean_object* v_res_4622_; 
v_text_boxed_4621_ = lean_unbox(v_text_4610_);
v_res_4622_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_4608_, v_build_4609_, v_text_boxed_4621_, v_ext_4611_, v_depTrace_4612_, v_traceFile_4613_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_, v_a_4619_);
lean_dec_ref(v_a_4618_);
lean_dec(v_a_4617_);
lean_dec(v_a_4616_);
lean_dec(v_a_4615_);
lean_dec_ref(v_depTrace_4612_);
return v_res_4622_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(lean_object* v_art_4624_, lean_object* v_traceFile_4625_, lean_object* v_a_4626_){
_start:
{
lean_object* v_log_4628_; uint8_t v_action_4629_; uint8_t v_wantsRebuild_4630_; lean_object* v_trace_4631_; lean_object* v_buildTime_4632_; lean_object* v___x_4633_; 
v_log_4628_ = lean_ctor_get(v_a_4626_, 0);
v_action_4629_ = lean_ctor_get_uint8(v_a_4626_, sizeof(void*)*3);
v_wantsRebuild_4630_ = lean_ctor_get_uint8(v_a_4626_, sizeof(void*)*3 + 1);
v_trace_4631_ = lean_ctor_get(v_a_4626_, 1);
v_buildTime_4632_ = lean_ctor_get(v_a_4626_, 2);
v___x_4633_ = lean_io_metadata(v_traceFile_4625_);
if (lean_obj_tag(v___x_4633_) == 0)
{
lean_object* v_a_4634_; lean_object* v_modified_4635_; lean_object* v_descr_4636_; lean_object* v_path_4637_; lean_object* v_name_4638_; lean_object* v___x_4640_; uint8_t v_isShared_4641_; uint8_t v_isSharedCheck_4646_; 
v_a_4634_ = lean_ctor_get(v___x_4633_, 0);
lean_inc(v_a_4634_);
lean_dec_ref(v___x_4633_);
v_modified_4635_ = lean_ctor_get(v_a_4634_, 1);
lean_inc_ref(v_modified_4635_);
lean_dec(v_a_4634_);
v_descr_4636_ = lean_ctor_get(v_art_4624_, 0);
v_path_4637_ = lean_ctor_get(v_art_4624_, 1);
v_name_4638_ = lean_ctor_get(v_art_4624_, 2);
v_isSharedCheck_4646_ = !lean_is_exclusive(v_art_4624_);
if (v_isSharedCheck_4646_ == 0)
{
lean_object* v_unused_4647_; 
v_unused_4647_ = lean_ctor_get(v_art_4624_, 3);
lean_dec(v_unused_4647_);
v___x_4640_ = v_art_4624_;
v_isShared_4641_ = v_isSharedCheck_4646_;
goto v_resetjp_4639_;
}
else
{
lean_inc(v_name_4638_);
lean_inc(v_path_4637_);
lean_inc(v_descr_4636_);
lean_dec(v_art_4624_);
v___x_4640_ = lean_box(0);
v_isShared_4641_ = v_isSharedCheck_4646_;
goto v_resetjp_4639_;
}
v_resetjp_4639_:
{
lean_object* v___x_4643_; 
if (v_isShared_4641_ == 0)
{
lean_ctor_set(v___x_4640_, 3, v_modified_4635_);
v___x_4643_ = v___x_4640_;
goto v_reusejp_4642_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_descr_4636_);
lean_ctor_set(v_reuseFailAlloc_4645_, 1, v_path_4637_);
lean_ctor_set(v_reuseFailAlloc_4645_, 2, v_name_4638_);
lean_ctor_set(v_reuseFailAlloc_4645_, 3, v_modified_4635_);
v___x_4643_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4642_;
}
v_reusejp_4642_:
{
lean_object* v___x_4644_; 
v___x_4644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4644_, 0, v___x_4643_);
lean_ctor_set(v___x_4644_, 1, v_a_4626_);
return v___x_4644_;
}
}
}
else
{
lean_object* v_a_4648_; 
v_a_4648_ = lean_ctor_get(v___x_4633_, 0);
lean_inc(v_a_4648_);
lean_dec_ref(v___x_4633_);
if (lean_obj_tag(v_a_4648_) == 11)
{
lean_object* v___x_4649_; 
lean_dec_ref(v_a_4648_);
v___x_4649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4649_, 0, v_art_4624_);
lean_ctor_set(v___x_4649_, 1, v_a_4626_);
return v___x_4649_;
}
else
{
lean_object* v___x_4651_; uint8_t v_isShared_4652_; uint8_t v_isSharedCheck_4664_; 
lean_inc(v_buildTime_4632_);
lean_inc_ref(v_trace_4631_);
lean_inc_ref(v_log_4628_);
lean_dec_ref(v_art_4624_);
v_isSharedCheck_4664_ = !lean_is_exclusive(v_a_4626_);
if (v_isSharedCheck_4664_ == 0)
{
lean_object* v_unused_4665_; lean_object* v_unused_4666_; lean_object* v_unused_4667_; 
v_unused_4665_ = lean_ctor_get(v_a_4626_, 2);
lean_dec(v_unused_4665_);
v_unused_4666_ = lean_ctor_get(v_a_4626_, 1);
lean_dec(v_unused_4666_);
v_unused_4667_ = lean_ctor_get(v_a_4626_, 0);
lean_dec(v_unused_4667_);
v___x_4651_ = v_a_4626_;
v_isShared_4652_ = v_isSharedCheck_4664_;
goto v_resetjp_4650_;
}
else
{
lean_dec(v_a_4626_);
v___x_4651_ = lean_box(0);
v_isShared_4652_ = v_isSharedCheck_4664_;
goto v_resetjp_4650_;
}
v_resetjp_4650_:
{
lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; uint8_t v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4661_; 
v___x_4653_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___closed__0));
v___x_4654_ = lean_io_error_to_string(v_a_4648_);
v___x_4655_ = lean_string_append(v___x_4653_, v___x_4654_);
lean_dec_ref(v___x_4654_);
v___x_4656_ = 3;
v___x_4657_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4657_, 0, v___x_4655_);
lean_ctor_set_uint8(v___x_4657_, sizeof(void*)*1, v___x_4656_);
v___x_4658_ = lean_array_get_size(v_log_4628_);
v___x_4659_ = lean_array_push(v_log_4628_, v___x_4657_);
if (v_isShared_4652_ == 0)
{
lean_ctor_set(v___x_4651_, 0, v___x_4659_);
v___x_4661_ = v___x_4651_;
goto v_reusejp_4660_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v___x_4659_);
lean_ctor_set(v_reuseFailAlloc_4663_, 1, v_trace_4631_);
lean_ctor_set(v_reuseFailAlloc_4663_, 2, v_buildTime_4632_);
lean_ctor_set_uint8(v_reuseFailAlloc_4663_, sizeof(void*)*3, v_action_4629_);
lean_ctor_set_uint8(v_reuseFailAlloc_4663_, sizeof(void*)*3 + 1, v_wantsRebuild_4630_);
v___x_4661_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4660_;
}
v_reusejp_4660_:
{
lean_object* v___x_4662_; 
v___x_4662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4662_, 0, v___x_4658_);
lean_ctor_set(v___x_4662_, 1, v___x_4661_);
return v___x_4662_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___boxed(lean_object* v_art_4668_, lean_object* v_traceFile_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_){
_start:
{
lean_object* v_res_4672_; 
v_res_4672_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_4668_, v_traceFile_4669_, v_a_4670_);
lean_dec_ref(v_traceFile_4669_);
return v_res_4672_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(lean_object* v_art_4673_, lean_object* v_traceFile_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_){
_start:
{
lean_object* v___x_4682_; 
v___x_4682_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_4673_, v_traceFile_4674_, v_a_4680_);
return v___x_4682_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___boxed(lean_object* v_art_4683_, lean_object* v_traceFile_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_){
_start:
{
lean_object* v_res_4692_; 
v_res_4692_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(v_art_4683_, v_traceFile_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_, v_a_4690_);
lean_dec_ref(v_a_4689_);
lean_dec(v_a_4688_);
lean_dec(v_a_4687_);
lean_dec(v_a_4686_);
lean_dec_ref(v_a_4685_);
lean_dec_ref(v_traceFile_4684_);
return v_res_4692_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0(lean_object* v_a_4693_, lean_object* v_____r_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_){
_start:
{
lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___x_4702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4702_, 0, v_a_4693_);
v___x_4703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4703_, 0, v___x_4702_);
v___x_4704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4704_, 0, v___x_4703_);
lean_ctor_set(v___x_4704_, 1, v___y_4700_);
return v___x_4704_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0___boxed(lean_object* v_a_4705_, lean_object* v_____r_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_){
_start:
{
lean_object* v_res_4714_; 
v_res_4714_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0(v_a_4705_, v_____r_4706_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_);
lean_dec_ref(v___y_4711_);
lean_dec(v___y_4710_);
lean_dec(v___y_4709_);
lean_dec(v___y_4708_);
lean_dec_ref(v___y_4707_);
return v_res_4714_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(uint8_t v_exe_4715_, lean_object* v___y_4716_, uint64_t v_inputHash_4717_, lean_object* v_savedTrace_4718_, lean_object* v_pkg_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_){
_start:
{
lean_object* v___y_4727_; lean_object* v_a_4731_; lean_object* v_a_4732_; lean_object* v___y_4747_; 
if (lean_obj_tag(v_savedTrace_4718_) == 2)
{
lean_object* v_data_4762_; uint64_t v_depHash_4763_; lean_object* v_outputs_x3f_4764_; uint8_t v___x_4765_; 
v_data_4762_ = lean_ctor_get(v_savedTrace_4718_, 0);
lean_inc_ref(v_data_4762_);
lean_dec_ref(v_savedTrace_4718_);
v_depHash_4763_ = lean_ctor_get_uint64(v_data_4762_, sizeof(void*)*3);
v_outputs_x3f_4764_ = lean_ctor_get(v_data_4762_, 1);
lean_inc(v_outputs_x3f_4764_);
lean_dec_ref(v_data_4762_);
v___x_4765_ = lean_uint64_dec_eq(v_depHash_4763_, v_inputHash_4717_);
if (v___x_4765_ == 0)
{
lean_dec(v_outputs_x3f_4764_);
lean_dec_ref(v_pkg_4719_);
lean_dec_ref(v___y_4716_);
v___y_4727_ = v_a_4724_;
goto v___jp_4726_;
}
else
{
if (lean_obj_tag(v_outputs_x3f_4764_) == 1)
{
lean_object* v_val_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; 
v_val_4766_ = lean_ctor_get(v_outputs_x3f_4764_, 0);
lean_inc_n(v_val_4766_, 2);
lean_dec_ref(v_outputs_x3f_4764_);
v___x_4767_ = lean_box(0);
v___x_4768_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4768_, 0, v_val_4766_);
lean_ctor_set(v___x_4768_, 1, v___x_4767_);
lean_ctor_set(v___x_4768_, 2, v___x_4767_);
lean_inc_ref(v___y_4716_);
v___x_4769_ = l_Lake_resolveArtifactOutput(v___x_4768_, v_exe_4715_, v___y_4716_, v_a_4720_, v_a_4721_, v_a_4722_, v_a_4723_, v_a_4724_);
if (lean_obj_tag(v___x_4769_) == 0)
{
lean_object* v_config_4770_; lean_object* v_a_4771_; lean_object* v_a_4772_; lean_object* v_enableArtifactCache_x3f_4773_; lean_object* v_a_4775_; uint8_t v_a_4779_; lean_object* v_a_4780_; 
v_config_4770_ = lean_ctor_get(v_pkg_4719_, 6);
v_a_4771_ = lean_ctor_get(v___x_4769_, 0);
lean_inc(v_a_4771_);
v_a_4772_ = lean_ctor_get(v___x_4769_, 1);
lean_inc(v_a_4772_);
lean_dec_ref(v___x_4769_);
v_enableArtifactCache_x3f_4773_ = lean_ctor_get(v_config_4770_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_4773_) == 0)
{
lean_object* v_toContext_4811_; lean_object* v_lakeEnv_4812_; lean_object* v_enableArtifactCache_x3f_4813_; 
v_toContext_4811_ = lean_ctor_get(v_a_4723_, 1);
v_lakeEnv_4812_ = lean_ctor_get(v_toContext_4811_, 1);
v_enableArtifactCache_x3f_4813_ = lean_ctor_get(v_lakeEnv_4812_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_4813_) == 0)
{
lean_object* v_root_4814_; lean_object* v_config_4815_; lean_object* v_enableArtifactCache_x3f_4816_; 
v_root_4814_ = lean_ctor_get(v_toContext_4811_, 0);
v_config_4815_ = lean_ctor_get(v_root_4814_, 6);
v_enableArtifactCache_x3f_4816_ = lean_ctor_get(v_config_4815_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_4816_) == 0)
{
lean_dec(v_val_4766_);
lean_dec_ref(v_pkg_4719_);
v_a_4775_ = v_a_4772_;
goto v___jp_4774_;
}
else
{
lean_object* v_val_4817_; uint8_t v___x_4818_; 
v_val_4817_ = lean_ctor_get(v_enableArtifactCache_x3f_4816_, 0);
v___x_4818_ = lean_unbox(v_val_4817_);
v_a_4779_ = v___x_4818_;
v_a_4780_ = v_a_4772_;
goto v___jp_4778_;
}
}
else
{
lean_object* v_val_4819_; uint8_t v___x_4820_; 
v_val_4819_ = lean_ctor_get(v_enableArtifactCache_x3f_4813_, 0);
v___x_4820_ = lean_unbox(v_val_4819_);
v_a_4779_ = v___x_4820_;
v_a_4780_ = v_a_4772_;
goto v___jp_4778_;
}
}
else
{
lean_object* v_val_4821_; uint8_t v___x_4822_; 
v_val_4821_ = lean_ctor_get(v_enableArtifactCache_x3f_4773_, 0);
v___x_4822_ = lean_unbox(v_val_4821_);
v_a_4779_ = v___x_4822_;
v_a_4780_ = v_a_4772_;
goto v___jp_4778_;
}
v___jp_4774_:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4776_ = lean_box(0);
v___x_4777_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0(v_a_4771_, v___x_4776_, v___y_4716_, v_a_4720_, v_a_4721_, v_a_4722_, v_a_4723_, v_a_4775_);
lean_dec_ref(v___y_4716_);
v___y_4747_ = v___x_4777_;
goto v___jp_4746_;
}
v___jp_4778_:
{
if (v_a_4779_ == 0)
{
lean_dec(v_val_4766_);
lean_dec_ref(v_pkg_4719_);
v_a_4775_ = v_a_4780_;
goto v___jp_4774_;
}
else
{
lean_object* v_toContext_4781_; lean_object* v_log_4782_; uint8_t v_action_4783_; uint8_t v_wantsRebuild_4784_; lean_object* v_trace_4785_; lean_object* v_buildTime_4786_; lean_object* v_lakeCache_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; 
v_toContext_4781_ = lean_ctor_get(v_a_4723_, 1);
v_log_4782_ = lean_ctor_get(v_a_4780_, 0);
v_action_4783_ = lean_ctor_get_uint8(v_a_4780_, sizeof(void*)*3);
v_wantsRebuild_4784_ = lean_ctor_get_uint8(v_a_4780_, sizeof(void*)*3 + 1);
v_trace_4785_ = lean_ctor_get(v_a_4780_, 1);
v_buildTime_4786_ = lean_ctor_get(v_a_4780_, 2);
v_lakeCache_4787_ = lean_ctor_get(v_toContext_4781_, 3);
v___x_4788_ = l_Lake_Package_cacheScope(v_pkg_4719_);
lean_inc_ref(v_lakeCache_4787_);
v___x_4789_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_4787_, v___x_4788_, v_inputHash_4717_, v_val_4766_, v___x_4767_, v___x_4767_);
if (lean_obj_tag(v___x_4789_) == 0)
{
lean_object* v___x_4790_; lean_object* v___x_4791_; 
lean_dec_ref(v___x_4789_);
v___x_4790_ = lean_box(0);
v___x_4791_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0(v_a_4771_, v___x_4790_, v___y_4716_, v_a_4720_, v_a_4721_, v_a_4722_, v_a_4723_, v_a_4780_);
lean_dec_ref(v___y_4716_);
v___y_4747_ = v___x_4791_;
goto v___jp_4746_;
}
else
{
lean_object* v___x_4793_; uint8_t v_isShared_4794_; uint8_t v_isSharedCheck_4807_; 
lean_inc(v_buildTime_4786_);
lean_inc_ref(v_trace_4785_);
lean_inc_ref(v_log_4782_);
v_isSharedCheck_4807_ = !lean_is_exclusive(v_a_4780_);
if (v_isSharedCheck_4807_ == 0)
{
lean_object* v_unused_4808_; lean_object* v_unused_4809_; lean_object* v_unused_4810_; 
v_unused_4808_ = lean_ctor_get(v_a_4780_, 2);
lean_dec(v_unused_4808_);
v_unused_4809_ = lean_ctor_get(v_a_4780_, 1);
lean_dec(v_unused_4809_);
v_unused_4810_ = lean_ctor_get(v_a_4780_, 0);
lean_dec(v_unused_4810_);
v___x_4793_ = v_a_4780_;
v_isShared_4794_ = v_isSharedCheck_4807_;
goto v_resetjp_4792_;
}
else
{
lean_dec(v_a_4780_);
v___x_4793_ = lean_box(0);
v_isShared_4794_ = v_isSharedCheck_4807_;
goto v_resetjp_4792_;
}
v_resetjp_4792_:
{
lean_object* v_a_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; uint8_t v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4804_; 
v_a_4795_ = lean_ctor_get(v___x_4789_, 0);
lean_inc(v_a_4795_);
lean_dec_ref(v___x_4789_);
v___x_4796_ = ((lean_object*)(l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0));
v___x_4797_ = lean_io_error_to_string(v_a_4795_);
v___x_4798_ = lean_string_append(v___x_4796_, v___x_4797_);
lean_dec_ref(v___x_4797_);
v___x_4799_ = 2;
v___x_4800_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4800_, 0, v___x_4798_);
lean_ctor_set_uint8(v___x_4800_, sizeof(void*)*1, v___x_4799_);
v___x_4801_ = lean_box(0);
v___x_4802_ = lean_array_push(v_log_4782_, v___x_4800_);
if (v_isShared_4794_ == 0)
{
lean_ctor_set(v___x_4793_, 0, v___x_4802_);
v___x_4804_ = v___x_4793_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v___x_4802_);
lean_ctor_set(v_reuseFailAlloc_4806_, 1, v_trace_4785_);
lean_ctor_set(v_reuseFailAlloc_4806_, 2, v_buildTime_4786_);
lean_ctor_set_uint8(v_reuseFailAlloc_4806_, sizeof(void*)*3, v_action_4783_);
lean_ctor_set_uint8(v_reuseFailAlloc_4806_, sizeof(void*)*3 + 1, v_wantsRebuild_4784_);
v___x_4804_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
lean_object* v___x_4805_; 
v___x_4805_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0(v_a_4771_, v___x_4801_, v___y_4716_, v_a_4720_, v_a_4721_, v_a_4722_, v_a_4723_, v___x_4804_);
lean_dec_ref(v___y_4716_);
v___y_4747_ = v___x_4805_;
goto v___jp_4746_;
}
}
}
}
}
}
else
{
lean_object* v_a_4823_; lean_object* v_a_4824_; 
lean_dec(v_val_4766_);
lean_dec_ref(v_pkg_4719_);
lean_dec_ref(v___y_4716_);
v_a_4823_ = lean_ctor_get(v___x_4769_, 0);
lean_inc(v_a_4823_);
v_a_4824_ = lean_ctor_get(v___x_4769_, 1);
lean_inc(v_a_4824_);
lean_dec_ref(v___x_4769_);
v_a_4731_ = v_a_4823_;
v_a_4732_ = v_a_4824_;
goto v___jp_4730_;
}
}
else
{
lean_dec(v_outputs_x3f_4764_);
lean_dec_ref(v_pkg_4719_);
lean_dec_ref(v___y_4716_);
v___y_4727_ = v_a_4724_;
goto v___jp_4726_;
}
}
}
else
{
lean_dec_ref(v_pkg_4719_);
lean_dec(v_savedTrace_4718_);
lean_dec_ref(v___y_4716_);
v___y_4727_ = v_a_4724_;
goto v___jp_4726_;
}
v___jp_4726_:
{
lean_object* v___x_4728_; lean_object* v___x_4729_; 
v___x_4728_ = lean_box(0);
v___x_4729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4729_, 0, v___x_4728_);
lean_ctor_set(v___x_4729_, 1, v___y_4727_);
return v___x_4729_;
}
v___jp_4730_:
{
lean_object* v_log_4733_; uint8_t v_action_4734_; uint8_t v_wantsRebuild_4735_; lean_object* v_trace_4736_; lean_object* v_buildTime_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4745_; 
v_log_4733_ = lean_ctor_get(v_a_4732_, 0);
v_action_4734_ = lean_ctor_get_uint8(v_a_4732_, sizeof(void*)*3);
v_wantsRebuild_4735_ = lean_ctor_get_uint8(v_a_4732_, sizeof(void*)*3 + 1);
v_trace_4736_ = lean_ctor_get(v_a_4732_, 1);
v_buildTime_4737_ = lean_ctor_get(v_a_4732_, 2);
v_isSharedCheck_4745_ = !lean_is_exclusive(v_a_4732_);
if (v_isSharedCheck_4745_ == 0)
{
v___x_4739_ = v_a_4732_;
v_isShared_4740_ = v_isSharedCheck_4745_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_buildTime_4737_);
lean_inc(v_trace_4736_);
lean_inc(v_log_4733_);
lean_dec(v_a_4732_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4745_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v___x_4741_; lean_object* v___x_4743_; 
v___x_4741_ = l_Array_shrink___redArg(v_log_4733_, v_a_4731_);
lean_dec(v_a_4731_);
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 0, v___x_4741_);
v___x_4743_ = v___x_4739_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v___x_4741_);
lean_ctor_set(v_reuseFailAlloc_4744_, 1, v_trace_4736_);
lean_ctor_set(v_reuseFailAlloc_4744_, 2, v_buildTime_4737_);
lean_ctor_set_uint8(v_reuseFailAlloc_4744_, sizeof(void*)*3, v_action_4734_);
lean_ctor_set_uint8(v_reuseFailAlloc_4744_, sizeof(void*)*3 + 1, v_wantsRebuild_4735_);
v___x_4743_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
v___y_4727_ = v___x_4743_;
goto v___jp_4726_;
}
}
}
v___jp_4746_:
{
if (lean_obj_tag(v___y_4747_) == 0)
{
lean_object* v_a_4748_; 
v_a_4748_ = lean_ctor_get(v___y_4747_, 0);
if (lean_obj_tag(v_a_4748_) == 0)
{
lean_object* v_a_4749_; lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4757_; 
lean_inc_ref(v_a_4748_);
v_a_4749_ = lean_ctor_get(v___y_4747_, 1);
v_isSharedCheck_4757_ = !lean_is_exclusive(v___y_4747_);
if (v_isSharedCheck_4757_ == 0)
{
lean_object* v_unused_4758_; 
v_unused_4758_ = lean_ctor_get(v___y_4747_, 0);
lean_dec(v_unused_4758_);
v___x_4751_ = v___y_4747_;
v_isShared_4752_ = v_isSharedCheck_4757_;
goto v_resetjp_4750_;
}
else
{
lean_inc(v_a_4749_);
lean_dec(v___y_4747_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4757_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
lean_object* v_a_4753_; lean_object* v___x_4755_; 
v_a_4753_ = lean_ctor_get(v_a_4748_, 0);
lean_inc(v_a_4753_);
lean_dec_ref(v_a_4748_);
if (v_isShared_4752_ == 0)
{
lean_ctor_set(v___x_4751_, 0, v_a_4753_);
v___x_4755_ = v___x_4751_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v_a_4753_);
lean_ctor_set(v_reuseFailAlloc_4756_, 1, v_a_4749_);
v___x_4755_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
return v___x_4755_;
}
}
}
else
{
lean_object* v_a_4759_; 
v_a_4759_ = lean_ctor_get(v___y_4747_, 1);
lean_inc(v_a_4759_);
lean_dec_ref(v___y_4747_);
v___y_4727_ = v_a_4759_;
goto v___jp_4726_;
}
}
else
{
lean_object* v_a_4760_; lean_object* v_a_4761_; 
v_a_4760_ = lean_ctor_get(v___y_4747_, 0);
lean_inc(v_a_4760_);
v_a_4761_ = lean_ctor_get(v___y_4747_, 1);
lean_inc(v_a_4761_);
lean_dec_ref(v___y_4747_);
v_a_4731_ = v_a_4760_;
v_a_4732_ = v_a_4761_;
goto v___jp_4730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___boxed(lean_object* v_exe_4825_, lean_object* v___y_4826_, lean_object* v_inputHash_4827_, lean_object* v_savedTrace_4828_, lean_object* v_pkg_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_){
_start:
{
uint8_t v_exe_boxed_4836_; uint64_t v_inputHash_boxed_4837_; lean_object* v_res_4838_; 
v_exe_boxed_4836_ = lean_unbox(v_exe_4825_);
v_inputHash_boxed_4837_ = lean_unbox_uint64(v_inputHash_4827_);
lean_dec_ref(v_inputHash_4827_);
v_res_4838_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(v_exe_boxed_4836_, v___y_4826_, v_inputHash_boxed_4837_, v_savedTrace_4828_, v_pkg_4829_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_);
lean_dec_ref(v_a_4833_);
lean_dec(v_a_4832_);
lean_dec(v_a_4831_);
lean_dec(v_a_4830_);
return v_res_4838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(lean_object* v_as_4839_, size_t v_i_4840_, size_t v_stop_4841_, lean_object* v_b_4842_){
_start:
{
uint8_t v___x_4843_; 
v___x_4843_ = lean_usize_dec_eq(v_i_4840_, v_stop_4841_);
if (v___x_4843_ == 0)
{
lean_object* v___x_4844_; lean_object* v_message_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; size_t v___x_4849_; size_t v___x_4850_; 
v___x_4844_ = lean_array_uget_borrowed(v_as_4839_, v_i_4840_);
v_message_4845_ = lean_ctor_get(v___x_4844_, 0);
v___x_4846_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0));
v___x_4847_ = lean_string_append(v_b_4842_, v___x_4846_);
v___x_4848_ = lean_string_append(v___x_4847_, v_message_4845_);
v___x_4849_ = ((size_t)1ULL);
v___x_4850_ = lean_usize_add(v_i_4840_, v___x_4849_);
v_i_4840_ = v___x_4850_;
v_b_4842_ = v___x_4848_;
goto _start;
}
else
{
return v_b_4842_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0___boxed(lean_object* v_as_4852_, lean_object* v_i_4853_, lean_object* v_stop_4854_, lean_object* v_b_4855_){
_start:
{
size_t v_i_boxed_4856_; size_t v_stop_boxed_4857_; lean_object* v_res_4858_; 
v_i_boxed_4856_ = lean_unbox_usize(v_i_4853_);
lean_dec(v_i_4853_);
v_stop_boxed_4857_ = lean_unbox_usize(v_stop_4854_);
lean_dec(v_stop_4854_);
v_res_4858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(v_as_4852_, v_i_boxed_4856_, v_stop_boxed_4857_, v_b_4855_);
lean_dec_ref(v_as_4852_);
return v_res_4858_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(uint8_t v_exe_4859_, lean_object* v___y_4860_, uint64_t v_inputHash_4861_, lean_object* v_pkg_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_){
_start:
{
lean_object* v_toContext_4869_; lean_object* v_log_4870_; uint8_t v_action_4871_; uint8_t v_wantsRebuild_4872_; lean_object* v_trace_4873_; lean_object* v_buildTime_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4967_; 
v_toContext_4869_ = lean_ctor_get(v_a_4866_, 1);
v_log_4870_ = lean_ctor_get(v_a_4867_, 0);
v_action_4871_ = lean_ctor_get_uint8(v_a_4867_, sizeof(void*)*3);
v_wantsRebuild_4872_ = lean_ctor_get_uint8(v_a_4867_, sizeof(void*)*3 + 1);
v_trace_4873_ = lean_ctor_get(v_a_4867_, 1);
v_buildTime_4874_ = lean_ctor_get(v_a_4867_, 2);
v_isSharedCheck_4967_ = !lean_is_exclusive(v_a_4867_);
if (v_isSharedCheck_4967_ == 0)
{
v___x_4876_ = v_a_4867_;
v_isShared_4877_ = v_isSharedCheck_4967_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_buildTime_4874_);
lean_inc(v_trace_4873_);
lean_inc(v_log_4870_);
lean_dec(v_a_4867_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4967_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v_lakeCache_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; 
v_lakeCache_4878_ = lean_ctor_get(v_toContext_4869_, 3);
v___x_4879_ = l_Lake_Package_cacheScope(v_pkg_4862_);
lean_inc_ref(v_lakeCache_4878_);
v___x_4880_ = l_Lake_Cache_readOutputs_x3f(v_lakeCache_4878_, v___x_4879_, v_inputHash_4861_, v_log_4870_);
if (lean_obj_tag(v___x_4880_) == 0)
{
lean_object* v_a_4881_; lean_object* v_a_4882_; lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4954_; 
v_a_4881_ = lean_ctor_get(v___x_4880_, 0);
v_a_4882_ = lean_ctor_get(v___x_4880_, 1);
v_isSharedCheck_4954_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_4954_ == 0)
{
v___x_4884_ = v___x_4880_;
v_isShared_4885_ = v_isSharedCheck_4954_;
goto v_resetjp_4883_;
}
else
{
lean_inc(v_a_4882_);
lean_inc(v_a_4881_);
lean_dec(v___x_4880_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4954_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
lean_object* v___x_4887_; 
if (v_isShared_4877_ == 0)
{
lean_ctor_set(v___x_4876_, 0, v_a_4882_);
v___x_4887_ = v___x_4876_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4953_; 
v_reuseFailAlloc_4953_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4953_, 0, v_a_4882_);
lean_ctor_set(v_reuseFailAlloc_4953_, 1, v_trace_4873_);
lean_ctor_set(v_reuseFailAlloc_4953_, 2, v_buildTime_4874_);
lean_ctor_set_uint8(v_reuseFailAlloc_4953_, sizeof(void*)*3, v_action_4871_);
lean_ctor_set_uint8(v_reuseFailAlloc_4953_, sizeof(void*)*3 + 1, v_wantsRebuild_4872_);
v___x_4887_ = v_reuseFailAlloc_4953_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
if (lean_obj_tag(v_a_4881_) == 1)
{
lean_object* v_val_4888_; lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4948_; 
v_val_4888_ = lean_ctor_get(v_a_4881_, 0);
v_isSharedCheck_4948_ = !lean_is_exclusive(v_a_4881_);
if (v_isSharedCheck_4948_ == 0)
{
v___x_4890_ = v_a_4881_;
v_isShared_4891_ = v_isSharedCheck_4948_;
goto v_resetjp_4889_;
}
else
{
lean_inc(v_val_4888_);
lean_dec(v_a_4881_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4948_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
lean_object* v___x_4892_; lean_object* v_r_4894_; lean_object* v___y_4895_; 
v___x_4892_ = l_Lake_resolveArtifactOutput(v_val_4888_, v_exe_4859_, v___y_4860_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v___x_4887_);
if (lean_obj_tag(v___x_4892_) == 0)
{
lean_object* v_a_4899_; lean_object* v_a_4900_; lean_object* v___x_4902_; 
v_a_4899_ = lean_ctor_get(v___x_4892_, 0);
lean_inc(v_a_4899_);
v_a_4900_ = lean_ctor_get(v___x_4892_, 1);
lean_inc(v_a_4900_);
lean_dec_ref(v___x_4892_);
if (v_isShared_4891_ == 0)
{
lean_ctor_set(v___x_4890_, 0, v_a_4899_);
v___x_4902_ = v___x_4890_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_a_4899_);
v___x_4902_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
v_r_4894_ = v___x_4902_;
v___y_4895_ = v_a_4900_;
goto v___jp_4893_;
}
}
else
{
lean_object* v_a_4904_; lean_object* v_a_4905_; lean_object* v_log_4906_; uint8_t v_action_4907_; uint8_t v_wantsRebuild_4908_; lean_object* v_trace_4909_; lean_object* v_buildTime_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4947_; 
lean_del_object(v___x_4890_);
v_a_4904_ = lean_ctor_get(v___x_4892_, 1);
lean_inc(v_a_4904_);
v_a_4905_ = lean_ctor_get(v___x_4892_, 0);
lean_inc(v_a_4905_);
lean_dec_ref(v___x_4892_);
v_log_4906_ = lean_ctor_get(v_a_4904_, 0);
v_action_4907_ = lean_ctor_get_uint8(v_a_4904_, sizeof(void*)*3);
v_wantsRebuild_4908_ = lean_ctor_get_uint8(v_a_4904_, sizeof(void*)*3 + 1);
v_trace_4909_ = lean_ctor_get(v_a_4904_, 1);
v_buildTime_4910_ = lean_ctor_get(v_a_4904_, 2);
v_isSharedCheck_4947_ = !lean_is_exclusive(v_a_4904_);
if (v_isSharedCheck_4947_ == 0)
{
v___x_4912_ = v_a_4904_;
v_isShared_4913_ = v_isSharedCheck_4947_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_buildTime_4910_);
lean_inc(v_trace_4909_);
lean_inc(v_log_4906_);
lean_dec(v_a_4904_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4947_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___y_4918_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; uint8_t v___x_4939_; 
v___x_4914_ = lean_array_get_size(v_log_4906_);
lean_inc(v_a_4905_);
v___x_4915_ = l_Array_extract___redArg(v_log_4906_, v_a_4905_, v___x_4914_);
v___x_4916_ = l_Array_shrink___redArg(v_log_4906_, v_a_4905_);
lean_dec(v_a_4905_);
v___x_4926_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0));
v___x_4927_ = l_Lake_Hash_hex(v_inputHash_4861_);
v___x_4928_ = lean_unsigned_to_nat(7u);
v___x_4929_ = lean_unsigned_to_nat(0u);
v___x_4930_ = lean_string_utf8_byte_size(v___x_4927_);
lean_inc_ref(v___x_4927_);
v___x_4931_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4931_, 0, v___x_4927_);
lean_ctor_set(v___x_4931_, 1, v___x_4929_);
lean_ctor_set(v___x_4931_, 2, v___x_4930_);
v___x_4932_ = l_String_Slice_Pos_nextn(v___x_4931_, v___x_4929_, v___x_4928_);
lean_dec_ref(v___x_4931_);
v___x_4933_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4933_, 0, v___x_4927_);
lean_ctor_set(v___x_4933_, 1, v___x_4929_);
lean_ctor_set(v___x_4933_, 2, v___x_4932_);
v___x_4934_ = l_String_Slice_toString(v___x_4933_);
lean_dec_ref(v___x_4933_);
v___x_4935_ = lean_string_append(v___x_4926_, v___x_4934_);
lean_dec_ref(v___x_4934_);
v___x_4936_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1));
v___x_4937_ = lean_string_append(v___x_4935_, v___x_4936_);
v___x_4938_ = lean_array_get_size(v___x_4915_);
v___x_4939_ = lean_nat_dec_lt(v___x_4929_, v___x_4938_);
if (v___x_4939_ == 0)
{
lean_dec_ref(v___x_4915_);
v___y_4918_ = v___x_4937_;
goto v___jp_4917_;
}
else
{
uint8_t v___x_4940_; 
v___x_4940_ = lean_nat_dec_le(v___x_4938_, v___x_4938_);
if (v___x_4940_ == 0)
{
if (v___x_4939_ == 0)
{
lean_dec_ref(v___x_4915_);
v___y_4918_ = v___x_4937_;
goto v___jp_4917_;
}
else
{
size_t v___x_4941_; size_t v___x_4942_; lean_object* v___x_4943_; 
v___x_4941_ = ((size_t)0ULL);
v___x_4942_ = lean_usize_of_nat(v___x_4938_);
v___x_4943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(v___x_4915_, v___x_4941_, v___x_4942_, v___x_4937_);
lean_dec_ref(v___x_4915_);
v___y_4918_ = v___x_4943_;
goto v___jp_4917_;
}
}
else
{
size_t v___x_4944_; size_t v___x_4945_; lean_object* v___x_4946_; 
v___x_4944_ = ((size_t)0ULL);
v___x_4945_ = lean_usize_of_nat(v___x_4938_);
v___x_4946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(v___x_4915_, v___x_4944_, v___x_4945_, v___x_4937_);
lean_dec_ref(v___x_4915_);
v___y_4918_ = v___x_4946_;
goto v___jp_4917_;
}
}
v___jp_4917_:
{
uint8_t v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4923_; 
v___x_4919_ = 2;
v___x_4920_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4920_, 0, v___y_4918_);
lean_ctor_set_uint8(v___x_4920_, sizeof(void*)*1, v___x_4919_);
v___x_4921_ = lean_array_push(v___x_4916_, v___x_4920_);
if (v_isShared_4913_ == 0)
{
lean_ctor_set(v___x_4912_, 0, v___x_4921_);
v___x_4923_ = v___x_4912_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4925_; 
v_reuseFailAlloc_4925_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4925_, 0, v___x_4921_);
lean_ctor_set(v_reuseFailAlloc_4925_, 1, v_trace_4909_);
lean_ctor_set(v_reuseFailAlloc_4925_, 2, v_buildTime_4910_);
lean_ctor_set_uint8(v_reuseFailAlloc_4925_, sizeof(void*)*3, v_action_4907_);
lean_ctor_set_uint8(v_reuseFailAlloc_4925_, sizeof(void*)*3 + 1, v_wantsRebuild_4908_);
v___x_4923_ = v_reuseFailAlloc_4925_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
lean_object* v___x_4924_; 
v___x_4924_ = lean_box(0);
v_r_4894_ = v___x_4924_;
v___y_4895_ = v___x_4923_;
goto v___jp_4893_;
}
}
}
}
v___jp_4893_:
{
lean_object* v___x_4897_; 
if (v_isShared_4885_ == 0)
{
lean_ctor_set(v___x_4884_, 1, v___y_4895_);
lean_ctor_set(v___x_4884_, 0, v_r_4894_);
v___x_4897_ = v___x_4884_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_r_4894_);
lean_ctor_set(v_reuseFailAlloc_4898_, 1, v___y_4895_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
return v___x_4897_;
}
}
}
}
else
{
lean_object* v___x_4949_; lean_object* v___x_4951_; 
lean_dec(v_a_4881_);
lean_dec_ref(v___y_4860_);
v___x_4949_ = lean_box(0);
if (v_isShared_4885_ == 0)
{
lean_ctor_set(v___x_4884_, 1, v___x_4887_);
lean_ctor_set(v___x_4884_, 0, v___x_4949_);
v___x_4951_ = v___x_4884_;
goto v_reusejp_4950_;
}
else
{
lean_object* v_reuseFailAlloc_4952_; 
v_reuseFailAlloc_4952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4952_, 0, v___x_4949_);
lean_ctor_set(v_reuseFailAlloc_4952_, 1, v___x_4887_);
v___x_4951_ = v_reuseFailAlloc_4952_;
goto v_reusejp_4950_;
}
v_reusejp_4950_:
{
return v___x_4951_;
}
}
}
}
}
else
{
lean_object* v_a_4955_; lean_object* v_a_4956_; lean_object* v___x_4958_; uint8_t v_isShared_4959_; uint8_t v_isSharedCheck_4966_; 
lean_dec_ref(v___y_4860_);
v_a_4955_ = lean_ctor_get(v___x_4880_, 0);
v_a_4956_ = lean_ctor_get(v___x_4880_, 1);
v_isSharedCheck_4966_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_4966_ == 0)
{
v___x_4958_ = v___x_4880_;
v_isShared_4959_ = v_isSharedCheck_4966_;
goto v_resetjp_4957_;
}
else
{
lean_inc(v_a_4956_);
lean_inc(v_a_4955_);
lean_dec(v___x_4880_);
v___x_4958_ = lean_box(0);
v_isShared_4959_ = v_isSharedCheck_4966_;
goto v_resetjp_4957_;
}
v_resetjp_4957_:
{
lean_object* v___x_4961_; 
if (v_isShared_4877_ == 0)
{
lean_ctor_set(v___x_4876_, 0, v_a_4956_);
v___x_4961_ = v___x_4876_;
goto v_reusejp_4960_;
}
else
{
lean_object* v_reuseFailAlloc_4965_; 
v_reuseFailAlloc_4965_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4965_, 0, v_a_4956_);
lean_ctor_set(v_reuseFailAlloc_4965_, 1, v_trace_4873_);
lean_ctor_set(v_reuseFailAlloc_4965_, 2, v_buildTime_4874_);
lean_ctor_set_uint8(v_reuseFailAlloc_4965_, sizeof(void*)*3, v_action_4871_);
lean_ctor_set_uint8(v_reuseFailAlloc_4965_, sizeof(void*)*3 + 1, v_wantsRebuild_4872_);
v___x_4961_ = v_reuseFailAlloc_4965_;
goto v_reusejp_4960_;
}
v_reusejp_4960_:
{
lean_object* v___x_4963_; 
if (v_isShared_4959_ == 0)
{
lean_ctor_set(v___x_4958_, 1, v___x_4961_);
v___x_4963_ = v___x_4958_;
goto v_reusejp_4962_;
}
else
{
lean_object* v_reuseFailAlloc_4964_; 
v_reuseFailAlloc_4964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4964_, 0, v_a_4955_);
lean_ctor_set(v_reuseFailAlloc_4964_, 1, v___x_4961_);
v___x_4963_ = v_reuseFailAlloc_4964_;
goto v_reusejp_4962_;
}
v_reusejp_4962_:
{
return v___x_4963_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object* v_exe_4968_, lean_object* v___y_4969_, lean_object* v_inputHash_4970_, lean_object* v_pkg_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_){
_start:
{
uint8_t v_exe_boxed_4978_; uint64_t v_inputHash_boxed_4979_; lean_object* v_res_4980_; 
v_exe_boxed_4978_ = lean_unbox(v_exe_4968_);
v_inputHash_boxed_4979_ = lean_unbox_uint64(v_inputHash_4970_);
lean_dec_ref(v_inputHash_4970_);
v_res_4980_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(v_exe_boxed_4978_, v___y_4969_, v_inputHash_boxed_4979_, v_pkg_4971_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_);
lean_dec_ref(v_a_4975_);
lean_dec(v_a_4974_);
lean_dec(v_a_4973_);
lean_dec(v_a_4972_);
return v_res_4980_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(uint8_t v_exe_4981_, uint64_t v_hash_4982_, lean_object* v_val_4983_, lean_object* v_file_4984_, lean_object* v___x_4985_, lean_object* v_a_4986_, uint8_t v_restore_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_){
_start:
{
lean_object* v_a_4996_; lean_object* v___y_5000_; lean_object* v___y_5001_; lean_object* v___y_5002_; lean_object* v___y_5040_; lean_object* v___y_5041_; lean_object* v___y_5042_; lean_object* v___y_5043_; uint8_t v___y_5044_; uint8_t v___y_5045_; lean_object* v___y_5046_; lean_object* v___y_5047_; lean_object* v___y_5061_; lean_object* v___x_5118_; 
lean_inc_ref(v_val_4983_);
lean_inc_ref(v___y_4988_);
v___x_5118_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(v_exe_4981_, v___y_4988_, v_hash_4982_, v_val_4983_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_, v___y_4993_);
if (lean_obj_tag(v___x_5118_) == 0)
{
lean_object* v_a_5119_; 
v_a_5119_ = lean_ctor_get(v___x_5118_, 0);
lean_inc(v_a_5119_);
if (lean_obj_tag(v_a_5119_) == 1)
{
lean_dec_ref(v_a_5119_);
lean_dec_ref(v___y_4988_);
lean_dec_ref(v_val_4983_);
v___y_5061_ = v___x_5118_;
goto v___jp_5060_;
}
else
{
lean_object* v_a_5120_; lean_object* v___x_5121_; lean_object* v_a_5122_; 
lean_dec(v_a_5119_);
v_a_5120_ = lean_ctor_get(v___x_5118_, 1);
lean_inc(v_a_5120_);
lean_dec_ref(v___x_5118_);
lean_inc(v_a_4986_);
v___x_5121_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(v_exe_4981_, v___y_4988_, v_hash_4982_, v_a_4986_, v_val_4983_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_, v_a_5120_);
v_a_5122_ = lean_ctor_get(v___x_5121_, 0);
lean_inc(v_a_5122_);
if (lean_obj_tag(v_a_5122_) == 1)
{
lean_dec_ref(v_a_5122_);
v___y_5061_ = v___x_5121_;
goto v___jp_5060_;
}
else
{
lean_object* v_a_5123_; 
lean_dec(v_a_5122_);
lean_dec(v_a_4986_);
lean_dec_ref(v___x_4985_);
lean_dec_ref(v_file_4984_);
v_a_5123_ = lean_ctor_get(v___x_5121_, 1);
lean_inc(v_a_5123_);
lean_dec_ref(v___x_5121_);
v_a_4996_ = v_a_5123_;
goto v___jp_4995_;
}
}
}
else
{
lean_dec_ref(v___y_4988_);
lean_dec_ref(v_val_4983_);
v___y_5061_ = v___x_5118_;
goto v___jp_5060_;
}
v___jp_4995_:
{
lean_object* v___x_4997_; lean_object* v___x_4998_; 
v___x_4997_ = lean_box(0);
v___x_4998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4998_, 0, v___x_4997_);
lean_ctor_set(v___x_4998_, 1, v_a_4996_);
return v___x_4998_;
}
v___jp_4999_:
{
if (v_restore_4987_ == 0)
{
lean_object* v___x_5003_; 
lean_dec_ref(v___y_5000_);
lean_dec_ref(v_file_4984_);
v___x_5003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5003_, 0, v___y_5001_);
lean_ctor_set(v___x_5003_, 1, v___y_5002_);
return v___x_5003_;
}
else
{
lean_object* v_log_5004_; uint8_t v_action_5005_; uint8_t v_wantsRebuild_5006_; lean_object* v_trace_5007_; lean_object* v_buildTime_5008_; lean_object* v___x_5010_; uint8_t v_isShared_5011_; uint8_t v_isSharedCheck_5038_; 
lean_dec(v___y_5001_);
v_log_5004_ = lean_ctor_get(v___y_5002_, 0);
v_action_5005_ = lean_ctor_get_uint8(v___y_5002_, sizeof(void*)*3);
v_wantsRebuild_5006_ = lean_ctor_get_uint8(v___y_5002_, sizeof(void*)*3 + 1);
v_trace_5007_ = lean_ctor_get(v___y_5002_, 1);
v_buildTime_5008_ = lean_ctor_get(v___y_5002_, 2);
v_isSharedCheck_5038_ = !lean_is_exclusive(v___y_5002_);
if (v_isSharedCheck_5038_ == 0)
{
v___x_5010_ = v___y_5002_;
v_isShared_5011_ = v_isSharedCheck_5038_;
goto v_resetjp_5009_;
}
else
{
lean_inc(v_buildTime_5008_);
lean_inc(v_trace_5007_);
lean_inc(v_log_5004_);
lean_dec(v___y_5002_);
v___x_5010_ = lean_box(0);
v_isShared_5011_ = v_isSharedCheck_5038_;
goto v_resetjp_5009_;
}
v_resetjp_5009_:
{
lean_object* v___x_5012_; 
v___x_5012_ = l_Lake_restoreArtifact(v_file_4984_, v___y_5000_, v_exe_4981_, v_log_5004_);
if (lean_obj_tag(v___x_5012_) == 0)
{
lean_object* v_a_5013_; lean_object* v_a_5014_; lean_object* v___x_5016_; uint8_t v_isShared_5017_; uint8_t v_isSharedCheck_5025_; 
v_a_5013_ = lean_ctor_get(v___x_5012_, 0);
v_a_5014_ = lean_ctor_get(v___x_5012_, 1);
v_isSharedCheck_5025_ = !lean_is_exclusive(v___x_5012_);
if (v_isSharedCheck_5025_ == 0)
{
v___x_5016_ = v___x_5012_;
v_isShared_5017_ = v_isSharedCheck_5025_;
goto v_resetjp_5015_;
}
else
{
lean_inc(v_a_5014_);
lean_inc(v_a_5013_);
lean_dec(v___x_5012_);
v___x_5016_ = lean_box(0);
v_isShared_5017_ = v_isSharedCheck_5025_;
goto v_resetjp_5015_;
}
v_resetjp_5015_:
{
lean_object* v___x_5019_; 
if (v_isShared_5011_ == 0)
{
lean_ctor_set(v___x_5010_, 0, v_a_5014_);
v___x_5019_ = v___x_5010_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_a_5014_);
lean_ctor_set(v_reuseFailAlloc_5024_, 1, v_trace_5007_);
lean_ctor_set(v_reuseFailAlloc_5024_, 2, v_buildTime_5008_);
lean_ctor_set_uint8(v_reuseFailAlloc_5024_, sizeof(void*)*3, v_action_5005_);
lean_ctor_set_uint8(v_reuseFailAlloc_5024_, sizeof(void*)*3 + 1, v_wantsRebuild_5006_);
v___x_5019_ = v_reuseFailAlloc_5024_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
lean_object* v___x_5020_; lean_object* v___x_5022_; 
v___x_5020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5020_, 0, v_a_5013_);
if (v_isShared_5017_ == 0)
{
lean_ctor_set(v___x_5016_, 1, v___x_5019_);
lean_ctor_set(v___x_5016_, 0, v___x_5020_);
v___x_5022_ = v___x_5016_;
goto v_reusejp_5021_;
}
else
{
lean_object* v_reuseFailAlloc_5023_; 
v_reuseFailAlloc_5023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5023_, 0, v___x_5020_);
lean_ctor_set(v_reuseFailAlloc_5023_, 1, v___x_5019_);
v___x_5022_ = v_reuseFailAlloc_5023_;
goto v_reusejp_5021_;
}
v_reusejp_5021_:
{
return v___x_5022_;
}
}
}
}
else
{
lean_object* v_a_5026_; lean_object* v_a_5027_; lean_object* v___x_5029_; uint8_t v_isShared_5030_; uint8_t v_isSharedCheck_5037_; 
v_a_5026_ = lean_ctor_get(v___x_5012_, 0);
v_a_5027_ = lean_ctor_get(v___x_5012_, 1);
v_isSharedCheck_5037_ = !lean_is_exclusive(v___x_5012_);
if (v_isSharedCheck_5037_ == 0)
{
v___x_5029_ = v___x_5012_;
v_isShared_5030_ = v_isSharedCheck_5037_;
goto v_resetjp_5028_;
}
else
{
lean_inc(v_a_5027_);
lean_inc(v_a_5026_);
lean_dec(v___x_5012_);
v___x_5029_ = lean_box(0);
v_isShared_5030_ = v_isSharedCheck_5037_;
goto v_resetjp_5028_;
}
v_resetjp_5028_:
{
lean_object* v___x_5032_; 
if (v_isShared_5011_ == 0)
{
lean_ctor_set(v___x_5010_, 0, v_a_5027_);
v___x_5032_ = v___x_5010_;
goto v_reusejp_5031_;
}
else
{
lean_object* v_reuseFailAlloc_5036_; 
v_reuseFailAlloc_5036_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5036_, 0, v_a_5027_);
lean_ctor_set(v_reuseFailAlloc_5036_, 1, v_trace_5007_);
lean_ctor_set(v_reuseFailAlloc_5036_, 2, v_buildTime_5008_);
lean_ctor_set_uint8(v_reuseFailAlloc_5036_, sizeof(void*)*3, v_action_5005_);
lean_ctor_set_uint8(v_reuseFailAlloc_5036_, sizeof(void*)*3 + 1, v_wantsRebuild_5006_);
v___x_5032_ = v_reuseFailAlloc_5036_;
goto v_reusejp_5031_;
}
v_reusejp_5031_:
{
lean_object* v___x_5034_; 
if (v_isShared_5030_ == 0)
{
lean_ctor_set(v___x_5029_, 1, v___x_5032_);
v___x_5034_ = v___x_5029_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5035_; 
v_reuseFailAlloc_5035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5035_, 0, v_a_5026_);
lean_ctor_set(v_reuseFailAlloc_5035_, 1, v___x_5032_);
v___x_5034_ = v_reuseFailAlloc_5035_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
return v___x_5034_;
}
}
}
}
}
}
}
v___jp_5039_:
{
lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; 
v___x_5048_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5048_, 0, v___y_5047_);
v___x_5049_ = l_Lake_BuildMetadata_ofFetch(v_hash_4982_, v___x_5048_);
v___x_5050_ = l_Lake_BuildMetadata_writeFile(v___x_4985_, v___x_5049_);
if (lean_obj_tag(v___x_5050_) == 0)
{
lean_object* v___x_5051_; 
lean_dec_ref(v___x_5050_);
v___x_5051_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5051_, 0, v___y_5046_);
lean_ctor_set(v___x_5051_, 1, v___y_5040_);
lean_ctor_set(v___x_5051_, 2, v___y_5041_);
lean_ctor_set_uint8(v___x_5051_, sizeof(void*)*3, v___y_5045_);
lean_ctor_set_uint8(v___x_5051_, sizeof(void*)*3 + 1, v___y_5044_);
v___y_5000_ = v___y_5042_;
v___y_5001_ = v___y_5043_;
v___y_5002_ = v___x_5051_;
goto v___jp_4999_;
}
else
{
lean_object* v_a_5052_; lean_object* v___x_5053_; uint8_t v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; 
lean_dec(v___y_5043_);
lean_dec_ref(v___y_5042_);
lean_dec_ref(v_file_4984_);
v_a_5052_ = lean_ctor_get(v___x_5050_, 0);
lean_inc(v_a_5052_);
lean_dec_ref(v___x_5050_);
v___x_5053_ = lean_io_error_to_string(v_a_5052_);
v___x_5054_ = 3;
v___x_5055_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5055_, 0, v___x_5053_);
lean_ctor_set_uint8(v___x_5055_, sizeof(void*)*1, v___x_5054_);
v___x_5056_ = lean_array_get_size(v___y_5046_);
v___x_5057_ = lean_array_push(v___y_5046_, v___x_5055_);
v___x_5058_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5058_, 0, v___x_5057_);
lean_ctor_set(v___x_5058_, 1, v___y_5040_);
lean_ctor_set(v___x_5058_, 2, v___y_5041_);
lean_ctor_set_uint8(v___x_5058_, sizeof(void*)*3, v___y_5045_);
lean_ctor_set_uint8(v___x_5058_, sizeof(void*)*3 + 1, v___y_5044_);
v___x_5059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5059_, 0, v___x_5056_);
lean_ctor_set(v___x_5059_, 1, v___x_5058_);
return v___x_5059_;
}
}
v___jp_5060_:
{
if (lean_obj_tag(v___y_5061_) == 0)
{
lean_object* v_a_5062_; 
v_a_5062_ = lean_ctor_get(v___y_5061_, 0);
if (lean_obj_tag(v_a_5062_) == 1)
{
lean_object* v_a_5063_; lean_object* v_val_5064_; lean_object* v___x_5065_; 
lean_inc_ref(v_a_5062_);
v_a_5063_ = lean_ctor_get(v___y_5061_, 1);
lean_inc(v_a_5063_);
lean_dec_ref(v___y_5061_);
v_val_5064_ = lean_ctor_get(v_a_5062_, 0);
lean_inc(v_val_5064_);
v___x_5065_ = l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(v_hash_4982_, v_a_4986_, v_a_5063_);
lean_dec(v_a_4986_);
if (lean_obj_tag(v___x_5065_) == 0)
{
lean_object* v_a_5066_; uint8_t v___x_5067_; 
v_a_5066_ = lean_ctor_get(v___x_5065_, 0);
lean_inc(v_a_5066_);
v___x_5067_ = lean_unbox(v_a_5066_);
lean_dec(v_a_5066_);
if (v___x_5067_ == 0)
{
lean_object* v_a_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5105_; 
v_a_5068_ = lean_ctor_get(v___x_5065_, 1);
v_isSharedCheck_5105_ = !lean_is_exclusive(v___x_5065_);
if (v_isSharedCheck_5105_ == 0)
{
lean_object* v_unused_5106_; 
v_unused_5106_ = lean_ctor_get(v___x_5065_, 0);
lean_dec(v_unused_5106_);
v___x_5070_ = v___x_5065_;
v_isShared_5071_ = v_isSharedCheck_5105_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_a_5068_);
lean_dec(v___x_5065_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5105_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v_log_5072_; uint8_t v_action_5073_; uint8_t v_wantsRebuild_5074_; lean_object* v_trace_5075_; lean_object* v_buildTime_5076_; lean_object* v___x_5078_; uint8_t v_isShared_5079_; uint8_t v_isSharedCheck_5104_; 
v_log_5072_ = lean_ctor_get(v_a_5068_, 0);
v_action_5073_ = lean_ctor_get_uint8(v_a_5068_, sizeof(void*)*3);
v_wantsRebuild_5074_ = lean_ctor_get_uint8(v_a_5068_, sizeof(void*)*3 + 1);
v_trace_5075_ = lean_ctor_get(v_a_5068_, 1);
v_buildTime_5076_ = lean_ctor_get(v_a_5068_, 2);
v_isSharedCheck_5104_ = !lean_is_exclusive(v_a_5068_);
if (v_isSharedCheck_5104_ == 0)
{
v___x_5078_ = v_a_5068_;
v_isShared_5079_ = v_isSharedCheck_5104_;
goto v_resetjp_5077_;
}
else
{
lean_inc(v_buildTime_5076_);
lean_inc(v_trace_5075_);
lean_inc(v_log_5072_);
lean_dec(v_a_5068_);
v___x_5078_ = lean_box(0);
v_isShared_5079_ = v_isSharedCheck_5104_;
goto v_resetjp_5077_;
}
v_resetjp_5077_:
{
lean_object* v___x_5080_; 
v___x_5080_ = l_Lake_removeFileIfExists(v_file_4984_);
if (lean_obj_tag(v___x_5080_) == 0)
{
lean_object* v_descr_5081_; uint64_t v_hash_5082_; lean_object* v_ext_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; uint8_t v___x_5086_; 
lean_dec_ref(v___x_5080_);
lean_del_object(v___x_5078_);
lean_del_object(v___x_5070_);
v_descr_5081_ = lean_ctor_get(v_val_5064_, 0);
v_hash_5082_ = lean_ctor_get_uint64(v_descr_5081_, sizeof(void*)*1);
v_ext_5083_ = lean_ctor_get(v_descr_5081_, 0);
v___x_5084_ = lean_string_utf8_byte_size(v_ext_5083_);
v___x_5085_ = lean_unsigned_to_nat(0u);
v___x_5086_ = lean_nat_dec_eq(v___x_5084_, v___x_5085_);
if (v___x_5086_ == 0)
{
lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; 
v___x_5087_ = l_Lake_Hash_hex(v_hash_5082_);
v___x_5088_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5089_ = lean_string_append(v___x_5087_, v___x_5088_);
v___x_5090_ = lean_string_append(v___x_5089_, v_ext_5083_);
v___y_5040_ = v_trace_5075_;
v___y_5041_ = v_buildTime_5076_;
v___y_5042_ = v_val_5064_;
v___y_5043_ = v_a_5062_;
v___y_5044_ = v_wantsRebuild_5074_;
v___y_5045_ = v_action_5073_;
v___y_5046_ = v_log_5072_;
v___y_5047_ = v___x_5090_;
goto v___jp_5039_;
}
else
{
lean_object* v___x_5091_; 
v___x_5091_ = l_Lake_Hash_hex(v_hash_5082_);
v___y_5040_ = v_trace_5075_;
v___y_5041_ = v_buildTime_5076_;
v___y_5042_ = v_val_5064_;
v___y_5043_ = v_a_5062_;
v___y_5044_ = v_wantsRebuild_5074_;
v___y_5045_ = v_action_5073_;
v___y_5046_ = v_log_5072_;
v___y_5047_ = v___x_5091_;
goto v___jp_5039_;
}
}
else
{
lean_object* v_a_5092_; lean_object* v___x_5093_; uint8_t v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5099_; 
lean_dec(v_val_5064_);
lean_dec_ref(v_a_5062_);
lean_dec_ref(v___x_4985_);
lean_dec_ref(v_file_4984_);
v_a_5092_ = lean_ctor_get(v___x_5080_, 0);
lean_inc(v_a_5092_);
lean_dec_ref(v___x_5080_);
v___x_5093_ = lean_io_error_to_string(v_a_5092_);
v___x_5094_ = 3;
v___x_5095_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5095_, 0, v___x_5093_);
lean_ctor_set_uint8(v___x_5095_, sizeof(void*)*1, v___x_5094_);
v___x_5096_ = lean_array_get_size(v_log_5072_);
v___x_5097_ = lean_array_push(v_log_5072_, v___x_5095_);
if (v_isShared_5079_ == 0)
{
lean_ctor_set(v___x_5078_, 0, v___x_5097_);
v___x_5099_ = v___x_5078_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5103_; 
v_reuseFailAlloc_5103_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5103_, 0, v___x_5097_);
lean_ctor_set(v_reuseFailAlloc_5103_, 1, v_trace_5075_);
lean_ctor_set(v_reuseFailAlloc_5103_, 2, v_buildTime_5076_);
lean_ctor_set_uint8(v_reuseFailAlloc_5103_, sizeof(void*)*3, v_action_5073_);
lean_ctor_set_uint8(v_reuseFailAlloc_5103_, sizeof(void*)*3 + 1, v_wantsRebuild_5074_);
v___x_5099_ = v_reuseFailAlloc_5103_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
lean_object* v___x_5101_; 
if (v_isShared_5071_ == 0)
{
lean_ctor_set_tag(v___x_5070_, 1);
lean_ctor_set(v___x_5070_, 1, v___x_5099_);
lean_ctor_set(v___x_5070_, 0, v___x_5096_);
v___x_5101_ = v___x_5070_;
goto v_reusejp_5100_;
}
else
{
lean_object* v_reuseFailAlloc_5102_; 
v_reuseFailAlloc_5102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5102_, 0, v___x_5096_);
lean_ctor_set(v_reuseFailAlloc_5102_, 1, v___x_5099_);
v___x_5101_ = v_reuseFailAlloc_5102_;
goto v_reusejp_5100_;
}
v_reusejp_5100_:
{
return v___x_5101_;
}
}
}
}
}
}
else
{
lean_object* v_a_5107_; 
lean_dec_ref(v___x_4985_);
v_a_5107_ = lean_ctor_get(v___x_5065_, 1);
lean_inc(v_a_5107_);
lean_dec_ref(v___x_5065_);
v___y_5000_ = v_val_5064_;
v___y_5001_ = v_a_5062_;
v___y_5002_ = v_a_5107_;
goto v___jp_4999_;
}
}
else
{
lean_object* v_a_5108_; lean_object* v_a_5109_; lean_object* v___x_5111_; uint8_t v_isShared_5112_; uint8_t v_isSharedCheck_5116_; 
lean_dec(v_val_5064_);
lean_dec_ref(v_a_5062_);
lean_dec_ref(v___x_4985_);
lean_dec_ref(v_file_4984_);
v_a_5108_ = lean_ctor_get(v___x_5065_, 0);
v_a_5109_ = lean_ctor_get(v___x_5065_, 1);
v_isSharedCheck_5116_ = !lean_is_exclusive(v___x_5065_);
if (v_isSharedCheck_5116_ == 0)
{
v___x_5111_ = v___x_5065_;
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
else
{
lean_inc(v_a_5109_);
lean_inc(v_a_5108_);
lean_dec(v___x_5065_);
v___x_5111_ = lean_box(0);
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
v_resetjp_5110_:
{
lean_object* v___x_5114_; 
if (v_isShared_5112_ == 0)
{
v___x_5114_ = v___x_5111_;
goto v_reusejp_5113_;
}
else
{
lean_object* v_reuseFailAlloc_5115_; 
v_reuseFailAlloc_5115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5115_, 0, v_a_5108_);
lean_ctor_set(v_reuseFailAlloc_5115_, 1, v_a_5109_);
v___x_5114_ = v_reuseFailAlloc_5115_;
goto v_reusejp_5113_;
}
v_reusejp_5113_:
{
return v___x_5114_;
}
}
}
}
else
{
lean_object* v_a_5117_; 
lean_dec(v_a_4986_);
lean_dec_ref(v___x_4985_);
lean_dec_ref(v_file_4984_);
v_a_5117_ = lean_ctor_get(v___y_5061_, 1);
lean_inc(v_a_5117_);
lean_dec_ref(v___y_5061_);
v_a_4996_ = v_a_5117_;
goto v___jp_4995_;
}
}
else
{
lean_dec(v_a_4986_);
lean_dec_ref(v___x_4985_);
lean_dec_ref(v_file_4984_);
return v___y_5061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object* v_exe_5124_, lean_object* v_hash_5125_, lean_object* v_val_5126_, lean_object* v_file_5127_, lean_object* v___x_5128_, lean_object* v_a_5129_, lean_object* v_restore_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_){
_start:
{
uint8_t v_exe_boxed_5138_; uint64_t v_hash_boxed_5139_; uint8_t v_restore_boxed_5140_; lean_object* v_res_5141_; 
v_exe_boxed_5138_ = lean_unbox(v_exe_5124_);
v_hash_boxed_5139_ = lean_unbox_uint64(v_hash_5125_);
lean_dec_ref(v_hash_5125_);
v_restore_boxed_5140_ = lean_unbox(v_restore_5130_);
v_res_5141_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_boxed_5138_, v_hash_boxed_5139_, v_val_5126_, v_file_5127_, v___x_5128_, v_a_5129_, v_restore_boxed_5140_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_);
lean_dec_ref(v___y_5135_);
lean_dec(v___y_5134_);
lean_dec(v___y_5133_);
lean_dec(v___y_5132_);
return v_res_5141_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1(uint8_t v_a_5142_, lean_object* v_file_5143_, lean_object* v_ext_5144_, uint8_t v_text_5145_, uint8_t v_exe_5146_, uint8_t v___y_5147_, lean_object* v_val_5148_, uint64_t v_hash_5149_, lean_object* v_____r_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_){
_start:
{
uint8_t v___x_5158_; uint8_t v___x_5159_; 
v___x_5158_ = 1;
v___x_5159_ = l_Lake_instDecidableEqOutputStatus(v_a_5142_, v___x_5158_);
if (v___x_5159_ == 0)
{
lean_object* v_toContext_5160_; lean_object* v_log_5161_; uint8_t v_action_5162_; uint8_t v_wantsRebuild_5163_; lean_object* v_trace_5164_; lean_object* v_buildTime_5165_; lean_object* v_lakeCache_5166_; lean_object* v___x_5167_; 
v_toContext_5160_ = lean_ctor_get(v___y_5155_, 1);
v_log_5161_ = lean_ctor_get(v___y_5156_, 0);
v_action_5162_ = lean_ctor_get_uint8(v___y_5156_, sizeof(void*)*3);
v_wantsRebuild_5163_ = lean_ctor_get_uint8(v___y_5156_, sizeof(void*)*3 + 1);
v_trace_5164_ = lean_ctor_get(v___y_5156_, 1);
v_buildTime_5165_ = lean_ctor_get(v___y_5156_, 2);
v_lakeCache_5166_ = lean_ctor_get(v_toContext_5160_, 3);
lean_inc_ref(v_lakeCache_5166_);
v___x_5167_ = l_Lake_Cache_saveArtifact(v_lakeCache_5166_, v_file_5143_, v_ext_5144_, v_text_5145_, v_exe_5146_, v___y_5147_);
if (lean_obj_tag(v___x_5167_) == 0)
{
lean_object* v_a_5168_; lean_object* v___x_5170_; uint8_t v_isShared_5171_; uint8_t v_isSharedCheck_5209_; 
v_a_5168_ = lean_ctor_get(v___x_5167_, 0);
v_isSharedCheck_5209_ = !lean_is_exclusive(v___x_5167_);
if (v_isSharedCheck_5209_ == 0)
{
v___x_5170_ = v___x_5167_;
v_isShared_5171_ = v_isSharedCheck_5209_;
goto v_resetjp_5169_;
}
else
{
lean_inc(v_a_5168_);
lean_dec(v___x_5167_);
v___x_5170_ = lean_box(0);
v_isShared_5171_ = v_isSharedCheck_5209_;
goto v_resetjp_5169_;
}
v_resetjp_5169_:
{
lean_object* v_descr_5172_; uint64_t v_hash_5173_; lean_object* v_ext_5174_; lean_object* v___x_5175_; lean_object* v___y_5177_; lean_object* v___x_5201_; lean_object* v___x_5202_; uint8_t v___x_5203_; 
v_descr_5172_ = lean_ctor_get(v_a_5168_, 0);
v_hash_5173_ = lean_ctor_get_uint64(v_descr_5172_, sizeof(void*)*1);
v_ext_5174_ = lean_ctor_get(v_descr_5172_, 0);
v___x_5175_ = l_Lake_Package_cacheScope(v_val_5148_);
v___x_5201_ = lean_string_utf8_byte_size(v_ext_5174_);
v___x_5202_ = lean_unsigned_to_nat(0u);
v___x_5203_ = lean_nat_dec_eq(v___x_5201_, v___x_5202_);
if (v___x_5203_ == 0)
{
lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; 
v___x_5204_ = l_Lake_Hash_hex(v_hash_5173_);
v___x_5205_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5206_ = lean_string_append(v___x_5204_, v___x_5205_);
v___x_5207_ = lean_string_append(v___x_5206_, v_ext_5174_);
v___y_5177_ = v___x_5207_;
goto v___jp_5176_;
}
else
{
lean_object* v___x_5208_; 
v___x_5208_ = l_Lake_Hash_hex(v_hash_5173_);
v___y_5177_ = v___x_5208_;
goto v___jp_5176_;
}
v___jp_5176_:
{
lean_object* v___x_5179_; 
if (v_isShared_5171_ == 0)
{
lean_ctor_set_tag(v___x_5170_, 3);
lean_ctor_set(v___x_5170_, 0, v___y_5177_);
v___x_5179_ = v___x_5170_;
goto v_reusejp_5178_;
}
else
{
lean_object* v_reuseFailAlloc_5200_; 
v_reuseFailAlloc_5200_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5200_, 0, v___y_5177_);
v___x_5179_ = v_reuseFailAlloc_5200_;
goto v_reusejp_5178_;
}
v_reusejp_5178_:
{
lean_object* v___x_5180_; lean_object* v___x_5181_; 
v___x_5180_ = lean_box(0);
lean_inc_ref(v_lakeCache_5166_);
v___x_5181_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_5166_, v___x_5175_, v_hash_5149_, v___x_5179_, v___x_5180_, v___x_5180_);
if (lean_obj_tag(v___x_5181_) == 0)
{
lean_object* v___x_5182_; 
lean_dec_ref(v___x_5181_);
v___x_5182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5182_, 0, v_a_5168_);
lean_ctor_set(v___x_5182_, 1, v___y_5156_);
return v___x_5182_;
}
else
{
lean_object* v___x_5184_; uint8_t v_isShared_5185_; uint8_t v_isSharedCheck_5196_; 
lean_inc(v_buildTime_5165_);
lean_inc_ref(v_trace_5164_);
lean_inc_ref(v_log_5161_);
lean_dec(v_a_5168_);
v_isSharedCheck_5196_ = !lean_is_exclusive(v___y_5156_);
if (v_isSharedCheck_5196_ == 0)
{
lean_object* v_unused_5197_; lean_object* v_unused_5198_; lean_object* v_unused_5199_; 
v_unused_5197_ = lean_ctor_get(v___y_5156_, 2);
lean_dec(v_unused_5197_);
v_unused_5198_ = lean_ctor_get(v___y_5156_, 1);
lean_dec(v_unused_5198_);
v_unused_5199_ = lean_ctor_get(v___y_5156_, 0);
lean_dec(v_unused_5199_);
v___x_5184_ = v___y_5156_;
v_isShared_5185_ = v_isSharedCheck_5196_;
goto v_resetjp_5183_;
}
else
{
lean_dec(v___y_5156_);
v___x_5184_ = lean_box(0);
v_isShared_5185_ = v_isSharedCheck_5196_;
goto v_resetjp_5183_;
}
v_resetjp_5183_:
{
lean_object* v_a_5186_; lean_object* v___x_5187_; uint8_t v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5193_; 
v_a_5186_ = lean_ctor_get(v___x_5181_, 0);
lean_inc(v_a_5186_);
lean_dec_ref(v___x_5181_);
v___x_5187_ = lean_io_error_to_string(v_a_5186_);
v___x_5188_ = 3;
v___x_5189_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5189_, 0, v___x_5187_);
lean_ctor_set_uint8(v___x_5189_, sizeof(void*)*1, v___x_5188_);
v___x_5190_ = lean_array_get_size(v_log_5161_);
v___x_5191_ = lean_array_push(v_log_5161_, v___x_5189_);
if (v_isShared_5185_ == 0)
{
lean_ctor_set(v___x_5184_, 0, v___x_5191_);
v___x_5193_ = v___x_5184_;
goto v_reusejp_5192_;
}
else
{
lean_object* v_reuseFailAlloc_5195_; 
v_reuseFailAlloc_5195_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5195_, 0, v___x_5191_);
lean_ctor_set(v_reuseFailAlloc_5195_, 1, v_trace_5164_);
lean_ctor_set(v_reuseFailAlloc_5195_, 2, v_buildTime_5165_);
lean_ctor_set_uint8(v_reuseFailAlloc_5195_, sizeof(void*)*3, v_action_5162_);
lean_ctor_set_uint8(v_reuseFailAlloc_5195_, sizeof(void*)*3 + 1, v_wantsRebuild_5163_);
v___x_5193_ = v_reuseFailAlloc_5195_;
goto v_reusejp_5192_;
}
v_reusejp_5192_:
{
lean_object* v___x_5194_; 
v___x_5194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5194_, 0, v___x_5190_);
lean_ctor_set(v___x_5194_, 1, v___x_5193_);
return v___x_5194_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5211_; uint8_t v_isShared_5212_; uint8_t v_isSharedCheck_5223_; 
lean_inc(v_buildTime_5165_);
lean_inc_ref(v_trace_5164_);
lean_inc_ref(v_log_5161_);
lean_dec_ref(v_val_5148_);
v_isSharedCheck_5223_ = !lean_is_exclusive(v___y_5156_);
if (v_isSharedCheck_5223_ == 0)
{
lean_object* v_unused_5224_; lean_object* v_unused_5225_; lean_object* v_unused_5226_; 
v_unused_5224_ = lean_ctor_get(v___y_5156_, 2);
lean_dec(v_unused_5224_);
v_unused_5225_ = lean_ctor_get(v___y_5156_, 1);
lean_dec(v_unused_5225_);
v_unused_5226_ = lean_ctor_get(v___y_5156_, 0);
lean_dec(v_unused_5226_);
v___x_5211_ = v___y_5156_;
v_isShared_5212_ = v_isSharedCheck_5223_;
goto v_resetjp_5210_;
}
else
{
lean_dec(v___y_5156_);
v___x_5211_ = lean_box(0);
v_isShared_5212_ = v_isSharedCheck_5223_;
goto v_resetjp_5210_;
}
v_resetjp_5210_:
{
lean_object* v_a_5213_; lean_object* v___x_5214_; uint8_t v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5220_; 
v_a_5213_ = lean_ctor_get(v___x_5167_, 0);
lean_inc(v_a_5213_);
lean_dec_ref(v___x_5167_);
v___x_5214_ = lean_io_error_to_string(v_a_5213_);
v___x_5215_ = 3;
v___x_5216_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5216_, 0, v___x_5214_);
lean_ctor_set_uint8(v___x_5216_, sizeof(void*)*1, v___x_5215_);
v___x_5217_ = lean_array_get_size(v_log_5161_);
v___x_5218_ = lean_array_push(v_log_5161_, v___x_5216_);
if (v_isShared_5212_ == 0)
{
lean_ctor_set(v___x_5211_, 0, v___x_5218_);
v___x_5220_ = v___x_5211_;
goto v_reusejp_5219_;
}
else
{
lean_object* v_reuseFailAlloc_5222_; 
v_reuseFailAlloc_5222_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5222_, 0, v___x_5218_);
lean_ctor_set(v_reuseFailAlloc_5222_, 1, v_trace_5164_);
lean_ctor_set(v_reuseFailAlloc_5222_, 2, v_buildTime_5165_);
lean_ctor_set_uint8(v_reuseFailAlloc_5222_, sizeof(void*)*3, v_action_5162_);
lean_ctor_set_uint8(v_reuseFailAlloc_5222_, sizeof(void*)*3 + 1, v_wantsRebuild_5163_);
v___x_5220_ = v_reuseFailAlloc_5222_;
goto v_reusejp_5219_;
}
v_reusejp_5219_:
{
lean_object* v___x_5221_; 
v___x_5221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5221_, 0, v___x_5217_);
lean_ctor_set(v___x_5221_, 1, v___x_5220_);
return v___x_5221_;
}
}
}
}
else
{
lean_object* v___x_5227_; 
lean_dec_ref(v_val_5148_);
v___x_5227_ = l_Lake_computeArtifact___redArg(v_file_5143_, v_ext_5144_, v_text_5145_, v___y_5155_, v___y_5156_);
return v___x_5227_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___boxed(lean_object* v_a_5228_, lean_object* v_file_5229_, lean_object* v_ext_5230_, lean_object* v_text_5231_, lean_object* v_exe_5232_, lean_object* v___y_5233_, lean_object* v_val_5234_, lean_object* v_hash_5235_, lean_object* v_____r_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_){
_start:
{
uint8_t v_a_295544__boxed_5244_; uint8_t v_text_boxed_5245_; uint8_t v_exe_boxed_5246_; uint8_t v___y_295545__boxed_5247_; uint64_t v_hash_boxed_5248_; lean_object* v_res_5249_; 
v_a_295544__boxed_5244_ = lean_unbox(v_a_5228_);
v_text_boxed_5245_ = lean_unbox(v_text_5231_);
v_exe_boxed_5246_ = lean_unbox(v_exe_5232_);
v___y_295545__boxed_5247_ = lean_unbox(v___y_5233_);
v_hash_boxed_5248_ = lean_unbox_uint64(v_hash_5235_);
lean_dec_ref(v_hash_5235_);
v_res_5249_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v_a_295544__boxed_5244_, v_file_5229_, v_ext_5230_, v_text_boxed_5245_, v_exe_boxed_5246_, v___y_295545__boxed_5247_, v_val_5234_, v_hash_boxed_5248_, v_____r_5236_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_);
lean_dec_ref(v___y_5241_);
lean_dec(v___y_5240_);
lean_dec(v___y_5239_);
lean_dec(v___y_5238_);
lean_dec_ref(v___y_5237_);
return v_res_5249_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object* v_file_5250_, lean_object* v_build_5251_, uint8_t v_text_5252_, lean_object* v_ext_5253_, uint8_t v_restore_5254_, uint8_t v_exe_5255_, uint8_t v_platformIndependent_5256_, lean_object* v_a_5257_, lean_object* v_a_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_, lean_object* v_a_5262_){
_start:
{
lean_object* v_log_5264_; uint8_t v_action_5265_; uint8_t v_wantsRebuild_5266_; lean_object* v_trace_5267_; lean_object* v_buildTime_5268_; lean_object* v___x_5270_; uint8_t v_isShared_5271_; uint8_t v_isSharedCheck_5517_; 
v_log_5264_ = lean_ctor_get(v_a_5262_, 0);
v_action_5265_ = lean_ctor_get_uint8(v_a_5262_, sizeof(void*)*3);
v_wantsRebuild_5266_ = lean_ctor_get_uint8(v_a_5262_, sizeof(void*)*3 + 1);
v_trace_5267_ = lean_ctor_get(v_a_5262_, 1);
v_buildTime_5268_ = lean_ctor_get(v_a_5262_, 2);
v_isSharedCheck_5517_ = !lean_is_exclusive(v_a_5262_);
if (v_isSharedCheck_5517_ == 0)
{
v___x_5270_ = v_a_5262_;
v_isShared_5271_ = v_isSharedCheck_5517_;
goto v_resetjp_5269_;
}
else
{
lean_inc(v_buildTime_5268_);
lean_inc(v_trace_5267_);
lean_inc(v_log_5264_);
lean_dec(v_a_5262_);
v___x_5270_ = lean_box(0);
v_isShared_5271_ = v_isSharedCheck_5517_;
goto v_resetjp_5269_;
}
v_resetjp_5269_:
{
lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v_art_5275_; lean_object* v___y_5276_; lean_object* v___y_5292_; lean_object* v_log_5293_; uint8_t v_action_5294_; uint8_t v_wantsRebuild_5295_; lean_object* v_buildTime_5296_; lean_object* v___x_5302_; 
v___x_5272_ = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(v_file_5250_);
v___x_5273_ = lean_string_append(v_file_5250_, v___x_5272_);
lean_inc_ref(v___x_5273_);
v___x_5302_ = l_Lake_readTraceFile(v___x_5273_, v_log_5264_);
if (lean_obj_tag(v___x_5302_) == 0)
{
if (lean_obj_tag(v_a_5258_) == 1)
{
lean_object* v_a_5303_; lean_object* v_a_5304_; lean_object* v_val_5305_; uint64_t v_hash_5306_; lean_object* v_mtime_5307_; lean_object* v___y_5309_; lean_object* v___y_5310_; lean_object* v___y_5311_; lean_object* v___y_5312_; lean_object* v___y_5313_; uint8_t v___y_5314_; uint8_t v___y_5315_; lean_object* v___y_5316_; lean_object* v___y_5317_; lean_object* v_wsIdx_5321_; lean_object* v_config_5322_; lean_object* v_a_5324_; lean_object* v_a_5325_; lean_object* v___y_5355_; lean_object* v_enableArtifactCache_x3f_5358_; lean_object* v_restoreAllArtifacts_x3f_5359_; uint8_t v___y_5361_; lean_object* v_a_5362_; uint8_t v___y_5379_; uint8_t v_a_5380_; lean_object* v_a_5381_; lean_object* v_a_5384_; lean_object* v___y_5414_; uint8_t v___y_5415_; uint8_t v___y_5454_; uint8_t v_a_5455_; lean_object* v_a_5456_; uint8_t v_a_5458_; lean_object* v_a_5459_; lean_object* v___x_5469_; 
v_a_5303_ = lean_ctor_get(v___x_5302_, 0);
lean_inc(v_a_5303_);
v_a_5304_ = lean_ctor_get(v___x_5302_, 1);
lean_inc(v_a_5304_);
lean_dec_ref(v___x_5302_);
v_val_5305_ = lean_ctor_get(v_a_5258_, 0);
v_hash_5306_ = lean_ctor_get_uint64(v_trace_5267_, sizeof(void*)*3);
v_mtime_5307_ = lean_ctor_get(v_trace_5267_, 2);
v_wsIdx_5321_ = lean_ctor_get(v_val_5305_, 0);
v_config_5322_ = lean_ctor_get(v_val_5305_, 6);
v_enableArtifactCache_x3f_5358_ = lean_ctor_get(v_config_5322_, 24);
v_restoreAllArtifacts_x3f_5359_ = lean_ctor_get(v_config_5322_, 25);
lean_inc_ref(v_trace_5267_);
v___x_5469_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5469_, 0, v_a_5304_);
lean_ctor_set(v___x_5469_, 1, v_trace_5267_);
lean_ctor_set(v___x_5469_, 2, v_buildTime_5268_);
lean_ctor_set_uint8(v___x_5469_, sizeof(void*)*3, v_action_5265_);
lean_ctor_set_uint8(v___x_5469_, sizeof(void*)*3 + 1, v_wantsRebuild_5266_);
if (lean_obj_tag(v_enableArtifactCache_x3f_5358_) == 0)
{
lean_object* v_toContext_5470_; lean_object* v_lakeEnv_5471_; lean_object* v_enableArtifactCache_x3f_5472_; 
v_toContext_5470_ = lean_ctor_get(v_a_5261_, 1);
v_lakeEnv_5471_ = lean_ctor_get(v_toContext_5470_, 1);
v_enableArtifactCache_x3f_5472_ = lean_ctor_get(v_lakeEnv_5471_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_5472_) == 0)
{
lean_object* v_root_5473_; lean_object* v_config_5474_; lean_object* v_enableArtifactCache_x3f_5475_; 
v_root_5473_ = lean_ctor_get(v_toContext_5470_, 0);
v_config_5474_ = lean_ctor_get(v_root_5473_, 6);
v_enableArtifactCache_x3f_5475_ = lean_ctor_get(v_config_5474_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_5475_) == 0)
{
v_a_5384_ = v___x_5469_;
goto v___jp_5383_;
}
else
{
lean_object* v_val_5476_; uint8_t v___x_5477_; 
v_val_5476_ = lean_ctor_get(v_enableArtifactCache_x3f_5475_, 0);
v___x_5477_ = lean_unbox(v_val_5476_);
v_a_5458_ = v___x_5477_;
v_a_5459_ = v___x_5469_;
goto v___jp_5457_;
}
}
else
{
lean_object* v_val_5478_; uint8_t v___x_5479_; 
v_val_5478_ = lean_ctor_get(v_enableArtifactCache_x3f_5472_, 0);
v___x_5479_ = lean_unbox(v_val_5478_);
v_a_5458_ = v___x_5479_;
v_a_5459_ = v___x_5469_;
goto v___jp_5457_;
}
}
else
{
lean_object* v_val_5480_; uint8_t v___x_5481_; 
v_val_5480_ = lean_ctor_get(v_enableArtifactCache_x3f_5358_, 0);
v___x_5481_ = lean_unbox(v_val_5480_);
v_a_5458_ = v___x_5481_;
v_a_5459_ = v___x_5469_;
goto v___jp_5457_;
}
v___jp_5308_:
{
lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; 
lean_dec_ref(v___y_5313_);
v___x_5318_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5318_, 0, v___y_5317_);
v___x_5319_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_hash_5306_, v___x_5318_, v___y_5316_, v_platformIndependent_5256_);
v___x_5320_ = lean_st_ref_set(v___y_5311_, v___x_5319_);
v___y_5292_ = v___y_5310_;
v_log_5293_ = v___y_5309_;
v_action_5294_ = v___y_5314_;
v_wantsRebuild_5295_ = v___y_5315_;
v_buildTime_5296_ = v___y_5312_;
goto v___jp_5291_;
}
v___jp_5323_:
{
lean_object* v___x_5326_; uint8_t v___x_5327_; 
v___x_5326_ = lean_unsigned_to_nat(0u);
v___x_5327_ = lean_nat_dec_eq(v_wsIdx_5321_, v___x_5326_);
if (v___x_5327_ == 0)
{
lean_object* v_log_5328_; uint8_t v_action_5329_; uint8_t v_wantsRebuild_5330_; lean_object* v_buildTime_5331_; 
v_log_5328_ = lean_ctor_get(v_a_5325_, 0);
lean_inc_ref(v_log_5328_);
v_action_5329_ = lean_ctor_get_uint8(v_a_5325_, sizeof(void*)*3);
v_wantsRebuild_5330_ = lean_ctor_get_uint8(v_a_5325_, sizeof(void*)*3 + 1);
v_buildTime_5331_ = lean_ctor_get(v_a_5325_, 2);
lean_inc(v_buildTime_5331_);
lean_dec_ref(v_a_5325_);
v___y_5292_ = v_a_5324_;
v_log_5293_ = v_log_5328_;
v_action_5294_ = v_action_5329_;
v_wantsRebuild_5295_ = v_wantsRebuild_5330_;
v_buildTime_5296_ = v_buildTime_5331_;
goto v___jp_5291_;
}
else
{
lean_object* v_outputsRef_x3f_5332_; 
v_outputsRef_x3f_5332_ = lean_ctor_get(v_a_5261_, 4);
if (lean_obj_tag(v_outputsRef_x3f_5332_) == 1)
{
lean_object* v_log_5333_; uint8_t v_action_5334_; uint8_t v_wantsRebuild_5335_; lean_object* v_trace_5336_; lean_object* v_buildTime_5337_; lean_object* v_val_5338_; lean_object* v___x_5339_; lean_object* v_descr_5340_; uint64_t v_hash_5341_; lean_object* v_ext_5342_; lean_object* v___x_5343_; uint8_t v___x_5344_; 
v_log_5333_ = lean_ctor_get(v_a_5325_, 0);
lean_inc_ref(v_log_5333_);
v_action_5334_ = lean_ctor_get_uint8(v_a_5325_, sizeof(void*)*3);
v_wantsRebuild_5335_ = lean_ctor_get_uint8(v_a_5325_, sizeof(void*)*3 + 1);
v_trace_5336_ = lean_ctor_get(v_a_5325_, 1);
lean_inc_ref(v_trace_5336_);
v_buildTime_5337_ = lean_ctor_get(v_a_5325_, 2);
lean_inc(v_buildTime_5337_);
lean_dec_ref(v_a_5325_);
v_val_5338_ = lean_ctor_get(v_outputsRef_x3f_5332_, 0);
v___x_5339_ = lean_st_ref_take(v_val_5338_);
v_descr_5340_ = lean_ctor_get(v_a_5324_, 0);
v_hash_5341_ = lean_ctor_get_uint64(v_descr_5340_, sizeof(void*)*1);
v_ext_5342_ = lean_ctor_get(v_descr_5340_, 0);
v___x_5343_ = lean_string_utf8_byte_size(v_ext_5342_);
v___x_5344_ = lean_nat_dec_eq(v___x_5343_, v___x_5326_);
if (v___x_5344_ == 0)
{
lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; 
v___x_5345_ = l_Lake_Hash_hex(v_hash_5341_);
v___x_5346_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5347_ = lean_string_append(v___x_5345_, v___x_5346_);
v___x_5348_ = lean_string_append(v___x_5347_, v_ext_5342_);
v___y_5309_ = v_log_5333_;
v___y_5310_ = v_a_5324_;
v___y_5311_ = v_val_5338_;
v___y_5312_ = v_buildTime_5337_;
v___y_5313_ = v_trace_5336_;
v___y_5314_ = v_action_5334_;
v___y_5315_ = v_wantsRebuild_5335_;
v___y_5316_ = v___x_5339_;
v___y_5317_ = v___x_5348_;
goto v___jp_5308_;
}
else
{
lean_object* v___x_5349_; 
v___x_5349_ = l_Lake_Hash_hex(v_hash_5341_);
v___y_5309_ = v_log_5333_;
v___y_5310_ = v_a_5324_;
v___y_5311_ = v_val_5338_;
v___y_5312_ = v_buildTime_5337_;
v___y_5313_ = v_trace_5336_;
v___y_5314_ = v_action_5334_;
v___y_5315_ = v_wantsRebuild_5335_;
v___y_5316_ = v___x_5339_;
v___y_5317_ = v___x_5349_;
goto v___jp_5308_;
}
}
else
{
lean_object* v_log_5350_; uint8_t v_action_5351_; uint8_t v_wantsRebuild_5352_; lean_object* v_buildTime_5353_; 
v_log_5350_ = lean_ctor_get(v_a_5325_, 0);
lean_inc_ref(v_log_5350_);
v_action_5351_ = lean_ctor_get_uint8(v_a_5325_, sizeof(void*)*3);
v_wantsRebuild_5352_ = lean_ctor_get_uint8(v_a_5325_, sizeof(void*)*3 + 1);
v_buildTime_5353_ = lean_ctor_get(v_a_5325_, 2);
lean_inc(v_buildTime_5353_);
lean_dec_ref(v_a_5325_);
v___y_5292_ = v_a_5324_;
v_log_5293_ = v_log_5350_;
v_action_5294_ = v_action_5351_;
v_wantsRebuild_5295_ = v_wantsRebuild_5352_;
v_buildTime_5296_ = v_buildTime_5353_;
goto v___jp_5291_;
}
}
}
v___jp_5354_:
{
if (lean_obj_tag(v___y_5355_) == 0)
{
lean_object* v_a_5356_; lean_object* v_a_5357_; 
v_a_5356_ = lean_ctor_get(v___y_5355_, 0);
lean_inc(v_a_5356_);
v_a_5357_ = lean_ctor_get(v___y_5355_, 1);
lean_inc(v_a_5357_);
lean_dec_ref(v___y_5355_);
v_a_5324_ = v_a_5356_;
v_a_5325_ = v_a_5357_;
goto v___jp_5323_;
}
else
{
lean_dec_ref(v___x_5273_);
lean_del_object(v___x_5270_);
return v___y_5355_;
}
}
v___jp_5360_:
{
lean_object* v___x_5363_; 
lean_inc_ref(v_a_5257_);
lean_inc_ref(v___x_5273_);
lean_inc_ref(v_file_5250_);
lean_inc(v_val_5305_);
v___x_5363_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_5255_, v_hash_5306_, v_val_5305_, v_file_5250_, v___x_5273_, v_a_5303_, v___y_5361_, v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_, v_a_5362_);
if (lean_obj_tag(v___x_5363_) == 0)
{
lean_object* v_a_5364_; 
v_a_5364_ = lean_ctor_get(v___x_5363_, 0);
lean_inc(v_a_5364_);
if (lean_obj_tag(v_a_5364_) == 1)
{
lean_object* v_a_5365_; lean_object* v_val_5366_; 
lean_dec_ref(v_trace_5267_);
lean_dec_ref(v_a_5257_);
lean_dec_ref(v_ext_5253_);
lean_dec_ref(v_build_5251_);
lean_dec_ref(v_file_5250_);
v_a_5365_ = lean_ctor_get(v___x_5363_, 1);
lean_inc(v_a_5365_);
lean_dec_ref(v___x_5363_);
v_val_5366_ = lean_ctor_get(v_a_5364_, 0);
lean_inc(v_val_5366_);
lean_dec_ref(v_a_5364_);
v_a_5324_ = v_val_5366_;
v_a_5325_ = v_a_5365_;
goto v___jp_5323_;
}
else
{
lean_object* v_a_5367_; lean_object* v___x_5368_; 
lean_dec(v_a_5364_);
v_a_5367_ = lean_ctor_get(v___x_5363_, 1);
lean_inc(v_a_5367_);
lean_dec_ref(v___x_5363_);
lean_inc_ref(v___x_5273_);
v___x_5368_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5250_, v_build_5251_, v_text_5252_, v_ext_5253_, v_trace_5267_, v___x_5273_, v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_, v_a_5367_);
lean_dec_ref(v_trace_5267_);
v___y_5355_ = v___x_5368_;
goto v___jp_5354_;
}
}
else
{
lean_object* v_a_5369_; lean_object* v_a_5370_; lean_object* v___x_5372_; uint8_t v_isShared_5373_; uint8_t v_isSharedCheck_5377_; 
lean_dec_ref(v___x_5273_);
lean_del_object(v___x_5270_);
lean_dec_ref(v_trace_5267_);
lean_dec_ref(v_a_5257_);
lean_dec_ref(v_ext_5253_);
lean_dec_ref(v_build_5251_);
lean_dec_ref(v_file_5250_);
v_a_5369_ = lean_ctor_get(v___x_5363_, 0);
v_a_5370_ = lean_ctor_get(v___x_5363_, 1);
v_isSharedCheck_5377_ = !lean_is_exclusive(v___x_5363_);
if (v_isSharedCheck_5377_ == 0)
{
v___x_5372_ = v___x_5363_;
v_isShared_5373_ = v_isSharedCheck_5377_;
goto v_resetjp_5371_;
}
else
{
lean_inc(v_a_5370_);
lean_inc(v_a_5369_);
lean_dec(v___x_5363_);
v___x_5372_ = lean_box(0);
v_isShared_5373_ = v_isSharedCheck_5377_;
goto v_resetjp_5371_;
}
v_resetjp_5371_:
{
lean_object* v___x_5375_; 
if (v_isShared_5373_ == 0)
{
v___x_5375_ = v___x_5372_;
goto v_reusejp_5374_;
}
else
{
lean_object* v_reuseFailAlloc_5376_; 
v_reuseFailAlloc_5376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5376_, 0, v_a_5369_);
lean_ctor_set(v_reuseFailAlloc_5376_, 1, v_a_5370_);
v___x_5375_ = v_reuseFailAlloc_5376_;
goto v_reusejp_5374_;
}
v_reusejp_5374_:
{
return v___x_5375_;
}
}
}
}
v___jp_5378_:
{
if (v_a_5380_ == 0)
{
lean_object* v___x_5382_; 
lean_dec(v_a_5303_);
lean_inc_ref(v___x_5273_);
v___x_5382_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5250_, v_build_5251_, v_text_5252_, v_ext_5253_, v_trace_5267_, v___x_5273_, v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_, v_a_5381_);
lean_dec_ref(v_trace_5267_);
v___y_5355_ = v___x_5382_;
goto v___jp_5354_;
}
else
{
v___y_5361_ = v___y_5379_;
v_a_5362_ = v_a_5381_;
goto v___jp_5360_;
}
}
v___jp_5383_:
{
lean_object* v___x_5385_; 
lean_inc(v_a_5303_);
v___x_5385_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5257_, v_file_5250_, v_trace_5267_, v_a_5303_, v_mtime_5307_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_, v_a_5384_);
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
lean_dec(v_a_5303_);
lean_dec_ref(v_trace_5267_);
lean_dec_ref(v_a_5257_);
lean_dec_ref(v_build_5251_);
v___x_5391_ = l_Lake_computeArtifact___redArg(v_file_5250_, v_ext_5253_, v_text_5252_, v_a_5261_, v_a_5387_);
v___y_5355_ = v___x_5391_;
goto v___jp_5354_;
}
else
{
if (lean_obj_tag(v_enableArtifactCache_x3f_5358_) == 0)
{
lean_object* v_toContext_5392_; lean_object* v_lakeEnv_5393_; lean_object* v_enableArtifactCache_x3f_5394_; 
v_toContext_5392_ = lean_ctor_get(v_a_5261_, 1);
v_lakeEnv_5393_ = lean_ctor_get(v_toContext_5392_, 1);
v_enableArtifactCache_x3f_5394_ = lean_ctor_get(v_lakeEnv_5393_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_5394_) == 0)
{
lean_object* v_root_5395_; lean_object* v_config_5396_; lean_object* v_enableArtifactCache_x3f_5397_; 
v_root_5395_ = lean_ctor_get(v_toContext_5392_, 0);
v_config_5396_ = lean_ctor_get(v_root_5395_, 6);
v_enableArtifactCache_x3f_5397_ = lean_ctor_get(v_config_5396_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_5397_) == 0)
{
v___y_5361_ = v___x_5390_;
v_a_5362_ = v_a_5387_;
goto v___jp_5360_;
}
else
{
lean_object* v_val_5398_; uint8_t v___x_5399_; 
v_val_5398_ = lean_ctor_get(v_enableArtifactCache_x3f_5397_, 0);
v___x_5399_ = lean_unbox(v_val_5398_);
v___y_5379_ = v___x_5390_;
v_a_5380_ = v___x_5399_;
v_a_5381_ = v_a_5387_;
goto v___jp_5378_;
}
}
else
{
lean_object* v_val_5400_; uint8_t v___x_5401_; 
v_val_5400_ = lean_ctor_get(v_enableArtifactCache_x3f_5394_, 0);
v___x_5401_ = lean_unbox(v_val_5400_);
v___y_5379_ = v___x_5390_;
v_a_5380_ = v___x_5401_;
v_a_5381_ = v_a_5387_;
goto v___jp_5378_;
}
}
else
{
lean_object* v_val_5402_; uint8_t v___x_5403_; 
v_val_5402_ = lean_ctor_get(v_enableArtifactCache_x3f_5358_, 0);
v___x_5403_ = lean_unbox(v_val_5402_);
v___y_5379_ = v___x_5390_;
v_a_5380_ = v___x_5403_;
v_a_5381_ = v_a_5387_;
goto v___jp_5378_;
}
}
}
else
{
lean_object* v_a_5404_; lean_object* v_a_5405_; lean_object* v___x_5407_; uint8_t v_isShared_5408_; uint8_t v_isSharedCheck_5412_; 
lean_dec(v_a_5303_);
lean_dec_ref(v___x_5273_);
lean_del_object(v___x_5270_);
lean_dec_ref(v_trace_5267_);
lean_dec_ref(v_a_5257_);
lean_dec_ref(v_ext_5253_);
lean_dec_ref(v_build_5251_);
lean_dec_ref(v_file_5250_);
v_a_5404_ = lean_ctor_get(v___x_5385_, 0);
v_a_5405_ = lean_ctor_get(v___x_5385_, 1);
v_isSharedCheck_5412_ = !lean_is_exclusive(v___x_5385_);
if (v_isSharedCheck_5412_ == 0)
{
v___x_5407_ = v___x_5385_;
v_isShared_5408_ = v_isSharedCheck_5412_;
goto v_resetjp_5406_;
}
else
{
lean_inc(v_a_5405_);
lean_inc(v_a_5404_);
lean_dec(v___x_5385_);
v___x_5407_ = lean_box(0);
v_isShared_5408_ = v_isSharedCheck_5412_;
goto v_resetjp_5406_;
}
v_resetjp_5406_:
{
lean_object* v___x_5410_; 
if (v_isShared_5408_ == 0)
{
v___x_5410_ = v___x_5407_;
goto v_reusejp_5409_;
}
else
{
lean_object* v_reuseFailAlloc_5411_; 
v_reuseFailAlloc_5411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5411_, 0, v_a_5404_);
lean_ctor_set(v_reuseFailAlloc_5411_, 1, v_a_5405_);
v___x_5410_ = v_reuseFailAlloc_5411_;
goto v_reusejp_5409_;
}
v_reusejp_5409_:
{
return v___x_5410_;
}
}
}
}
v___jp_5413_:
{
lean_object* v___x_5416_; 
lean_inc_ref(v_a_5257_);
lean_inc(v_a_5303_);
lean_inc_ref(v___x_5273_);
lean_inc_ref(v_file_5250_);
lean_inc(v_val_5305_);
v___x_5416_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_5255_, v_hash_5306_, v_val_5305_, v_file_5250_, v___x_5273_, v_a_5303_, v___y_5415_, v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_, v___y_5414_);
if (lean_obj_tag(v___x_5416_) == 0)
{
lean_object* v_a_5417_; 
v_a_5417_ = lean_ctor_get(v___x_5416_, 0);
lean_inc(v_a_5417_);
if (lean_obj_tag(v_a_5417_) == 1)
{
lean_object* v_a_5418_; lean_object* v_val_5419_; 
lean_dec(v_a_5303_);
lean_dec_ref(v_trace_5267_);
lean_dec_ref(v_a_5257_);
lean_dec_ref(v_ext_5253_);
lean_dec_ref(v_build_5251_);
lean_dec_ref(v_file_5250_);
v_a_5418_ = lean_ctor_get(v___x_5416_, 1);
lean_inc(v_a_5418_);
lean_dec_ref(v___x_5416_);
v_val_5419_ = lean_ctor_get(v_a_5417_, 0);
lean_inc(v_val_5419_);
lean_dec_ref(v_a_5417_);
v_a_5324_ = v_val_5419_;
v_a_5325_ = v_a_5418_;
goto v___jp_5323_;
}
else
{
lean_object* v_a_5420_; lean_object* v___x_5421_; 
lean_dec(v_a_5417_);
v_a_5420_ = lean_ctor_get(v___x_5416_, 1);
lean_inc(v_a_5420_);
lean_dec_ref(v___x_5416_);
v___x_5421_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5257_, v_file_5250_, v_trace_5267_, v_a_5303_, v_mtime_5307_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_, v_a_5420_);
if (lean_obj_tag(v___x_5421_) == 0)
{
lean_object* v_a_5422_; lean_object* v_a_5423_; uint8_t v___x_5424_; uint8_t v___x_5425_; uint8_t v___x_5426_; 
v_a_5422_ = lean_ctor_get(v___x_5421_, 0);
lean_inc(v_a_5422_);
v_a_5423_ = lean_ctor_get(v___x_5421_, 1);
lean_inc(v_a_5423_);
lean_dec_ref(v___x_5421_);
v___x_5424_ = 0;
v___x_5425_ = lean_unbox(v_a_5422_);
v___x_5426_ = l_Lake_instDecidableEqOutputStatus(v___x_5425_, v___x_5424_);
if (v___x_5426_ == 0)
{
lean_object* v___x_5427_; uint8_t v___x_5428_; lean_object* v___x_5429_; 
lean_dec_ref(v_trace_5267_);
lean_dec_ref(v_build_5251_);
v___x_5427_ = lean_box(0);
v___x_5428_ = lean_unbox(v_a_5422_);
lean_dec(v_a_5422_);
lean_inc(v_val_5305_);
v___x_5429_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v___x_5428_, v_file_5250_, v_ext_5253_, v_text_5252_, v_exe_5255_, v___y_5415_, v_val_5305_, v_hash_5306_, v___x_5427_, v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_, v_a_5423_);
lean_dec_ref(v_a_5257_);
v___y_5355_ = v___x_5429_;
goto v___jp_5354_;
}
else
{
lean_object* v___x_5430_; 
lean_inc_ref(v_a_5257_);
lean_inc_ref(v___x_5273_);
lean_inc_ref(v_ext_5253_);
lean_inc_ref(v_file_5250_);
v___x_5430_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5250_, v_build_5251_, v_text_5252_, v_ext_5253_, v_trace_5267_, v___x_5273_, v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_, v_a_5423_);
lean_dec_ref(v_trace_5267_);
if (lean_obj_tag(v___x_5430_) == 0)
{
lean_object* v_a_5431_; lean_object* v___x_5432_; uint8_t v___x_5433_; lean_object* v___x_5434_; 
v_a_5431_ = lean_ctor_get(v___x_5430_, 1);
lean_inc(v_a_5431_);
lean_dec_ref(v___x_5430_);
v___x_5432_ = lean_box(0);
v___x_5433_ = lean_unbox(v_a_5422_);
lean_dec(v_a_5422_);
lean_inc(v_val_5305_);
v___x_5434_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v___x_5433_, v_file_5250_, v_ext_5253_, v_text_5252_, v_exe_5255_, v___y_5415_, v_val_5305_, v_hash_5306_, v___x_5432_, v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_, v_a_5431_);
lean_dec_ref(v_a_5257_);
v___y_5355_ = v___x_5434_;
goto v___jp_5354_;
}
else
{
lean_dec(v_a_5422_);
lean_dec_ref(v___x_5273_);
lean_del_object(v___x_5270_);
lean_dec_ref(v_a_5257_);
lean_dec_ref(v_ext_5253_);
lean_dec_ref(v_file_5250_);
return v___x_5430_;
}
}
}
else
{
lean_object* v_a_5435_; lean_object* v_a_5436_; lean_object* v___x_5438_; uint8_t v_isShared_5439_; uint8_t v_isSharedCheck_5443_; 
lean_dec_ref(v___x_5273_);
lean_del_object(v___x_5270_);
lean_dec_ref(v_trace_5267_);
lean_dec_ref(v_a_5257_);
lean_dec_ref(v_ext_5253_);
lean_dec_ref(v_build_5251_);
lean_dec_ref(v_file_5250_);
v_a_5435_ = lean_ctor_get(v___x_5421_, 0);
v_a_5436_ = lean_ctor_get(v___x_5421_, 1);
v_isSharedCheck_5443_ = !lean_is_exclusive(v___x_5421_);
if (v_isSharedCheck_5443_ == 0)
{
v___x_5438_ = v___x_5421_;
v_isShared_5439_ = v_isSharedCheck_5443_;
goto v_resetjp_5437_;
}
else
{
lean_inc(v_a_5436_);
lean_inc(v_a_5435_);
lean_dec(v___x_5421_);
v___x_5438_ = lean_box(0);
v_isShared_5439_ = v_isSharedCheck_5443_;
goto v_resetjp_5437_;
}
v_resetjp_5437_:
{
lean_object* v___x_5441_; 
if (v_isShared_5439_ == 0)
{
v___x_5441_ = v___x_5438_;
goto v_reusejp_5440_;
}
else
{
lean_object* v_reuseFailAlloc_5442_; 
v_reuseFailAlloc_5442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5442_, 0, v_a_5435_);
lean_ctor_set(v_reuseFailAlloc_5442_, 1, v_a_5436_);
v___x_5441_ = v_reuseFailAlloc_5442_;
goto v_reusejp_5440_;
}
v_reusejp_5440_:
{
return v___x_5441_;
}
}
}
}
}
else
{
lean_object* v_a_5444_; lean_object* v_a_5445_; lean_object* v___x_5447_; uint8_t v_isShared_5448_; uint8_t v_isSharedCheck_5452_; 
lean_dec(v_a_5303_);
lean_dec_ref(v___x_5273_);
lean_del_object(v___x_5270_);
lean_dec_ref(v_trace_5267_);
lean_dec_ref(v_a_5257_);
lean_dec_ref(v_ext_5253_);
lean_dec_ref(v_build_5251_);
lean_dec_ref(v_file_5250_);
v_a_5444_ = lean_ctor_get(v___x_5416_, 0);
v_a_5445_ = lean_ctor_get(v___x_5416_, 1);
v_isSharedCheck_5452_ = !lean_is_exclusive(v___x_5416_);
if (v_isSharedCheck_5452_ == 0)
{
v___x_5447_ = v___x_5416_;
v_isShared_5448_ = v_isSharedCheck_5452_;
goto v_resetjp_5446_;
}
else
{
lean_inc(v_a_5445_);
lean_inc(v_a_5444_);
lean_dec(v___x_5416_);
v___x_5447_ = lean_box(0);
v_isShared_5448_ = v_isSharedCheck_5452_;
goto v_resetjp_5446_;
}
v_resetjp_5446_:
{
lean_object* v___x_5450_; 
if (v_isShared_5448_ == 0)
{
v___x_5450_ = v___x_5447_;
goto v_reusejp_5449_;
}
else
{
lean_object* v_reuseFailAlloc_5451_; 
v_reuseFailAlloc_5451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5451_, 0, v_a_5444_);
lean_ctor_set(v_reuseFailAlloc_5451_, 1, v_a_5445_);
v___x_5450_ = v_reuseFailAlloc_5451_;
goto v_reusejp_5449_;
}
v_reusejp_5449_:
{
return v___x_5450_;
}
}
}
}
v___jp_5453_:
{
if (v_restore_5254_ == 0)
{
v___y_5414_ = v_a_5456_;
v___y_5415_ = v_a_5455_;
goto v___jp_5413_;
}
else
{
v___y_5414_ = v_a_5456_;
v___y_5415_ = v___y_5454_;
goto v___jp_5413_;
}
}
v___jp_5457_:
{
if (v_a_5458_ == 0)
{
v_a_5384_ = v_a_5459_;
goto v___jp_5383_;
}
else
{
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5359_) == 0)
{
lean_object* v_toContext_5460_; lean_object* v_root_5461_; lean_object* v_config_5462_; lean_object* v_restoreAllArtifacts_x3f_5463_; 
v_toContext_5460_ = lean_ctor_get(v_a_5261_, 1);
v_root_5461_ = lean_ctor_get(v_toContext_5460_, 0);
v_config_5462_ = lean_ctor_get(v_root_5461_, 6);
v_restoreAllArtifacts_x3f_5463_ = lean_ctor_get(v_config_5462_, 25);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5463_) == 0)
{
uint8_t v___x_5464_; 
v___x_5464_ = 0;
v___y_5454_ = v_a_5458_;
v_a_5455_ = v___x_5464_;
v_a_5456_ = v_a_5459_;
goto v___jp_5453_;
}
else
{
lean_object* v_val_5465_; uint8_t v___x_5466_; 
v_val_5465_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5463_, 0);
v___x_5466_ = lean_unbox(v_val_5465_);
v___y_5454_ = v_a_5458_;
v_a_5455_ = v___x_5466_;
v_a_5456_ = v_a_5459_;
goto v___jp_5453_;
}
}
else
{
lean_object* v_val_5467_; uint8_t v___x_5468_; 
v_val_5467_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5359_, 0);
v___x_5468_ = lean_unbox(v_val_5467_);
v___y_5454_ = v_a_5458_;
v_a_5455_ = v___x_5468_;
v_a_5456_ = v_a_5459_;
goto v___jp_5453_;
}
}
}
}
else
{
lean_object* v_a_5482_; lean_object* v_a_5483_; lean_object* v_mtime_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; 
lean_del_object(v___x_5270_);
v_a_5482_ = lean_ctor_get(v___x_5302_, 0);
lean_inc(v_a_5482_);
v_a_5483_ = lean_ctor_get(v___x_5302_, 1);
lean_inc(v_a_5483_);
lean_dec_ref(v___x_5302_);
v_mtime_5484_ = lean_ctor_get(v_trace_5267_, 2);
lean_inc_ref(v_trace_5267_);
v___x_5485_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5485_, 0, v_a_5483_);
lean_ctor_set(v___x_5485_, 1, v_trace_5267_);
lean_ctor_set(v___x_5485_, 2, v_buildTime_5268_);
lean_ctor_set_uint8(v___x_5485_, sizeof(void*)*3, v_action_5265_);
lean_ctor_set_uint8(v___x_5485_, sizeof(void*)*3 + 1, v_wantsRebuild_5266_);
v___x_5486_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5257_, v_file_5250_, v_trace_5267_, v_a_5482_, v_mtime_5484_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_, v___x_5485_);
if (lean_obj_tag(v___x_5486_) == 0)
{
lean_object* v_a_5487_; lean_object* v_a_5488_; uint8_t v___x_5489_; uint8_t v___x_5490_; uint8_t v___x_5491_; 
v_a_5487_ = lean_ctor_get(v___x_5486_, 0);
lean_inc(v_a_5487_);
v_a_5488_ = lean_ctor_get(v___x_5486_, 1);
lean_inc(v_a_5488_);
lean_dec_ref(v___x_5486_);
v___x_5489_ = 0;
v___x_5490_ = lean_unbox(v_a_5487_);
lean_dec(v_a_5487_);
v___x_5491_ = l_Lake_instDecidableEqOutputStatus(v___x_5490_, v___x_5489_);
if (v___x_5491_ == 0)
{
lean_object* v___x_5492_; 
lean_dec_ref(v_trace_5267_);
lean_dec_ref(v_a_5257_);
lean_dec_ref(v_build_5251_);
v___x_5492_ = l_Lake_computeArtifact___redArg(v_file_5250_, v_ext_5253_, v_text_5252_, v_a_5261_, v_a_5488_);
if (lean_obj_tag(v___x_5492_) == 0)
{
lean_object* v_a_5493_; lean_object* v_a_5494_; 
v_a_5493_ = lean_ctor_get(v___x_5492_, 0);
lean_inc(v_a_5493_);
v_a_5494_ = lean_ctor_get(v___x_5492_, 1);
lean_inc(v_a_5494_);
lean_dec_ref(v___x_5492_);
v_art_5275_ = v_a_5493_;
v___y_5276_ = v_a_5494_;
goto v___jp_5274_;
}
else
{
lean_dec_ref(v___x_5273_);
return v___x_5492_;
}
}
else
{
lean_object* v___x_5495_; 
lean_inc_ref(v___x_5273_);
v___x_5495_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5250_, v_build_5251_, v_text_5252_, v_ext_5253_, v_trace_5267_, v___x_5273_, v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_, v_a_5488_);
lean_dec_ref(v_trace_5267_);
if (lean_obj_tag(v___x_5495_) == 0)
{
lean_object* v_a_5496_; lean_object* v_a_5497_; 
v_a_5496_ = lean_ctor_get(v___x_5495_, 0);
lean_inc(v_a_5496_);
v_a_5497_ = lean_ctor_get(v___x_5495_, 1);
lean_inc(v_a_5497_);
lean_dec_ref(v___x_5495_);
v_art_5275_ = v_a_5496_;
v___y_5276_ = v_a_5497_;
goto v___jp_5274_;
}
else
{
lean_dec_ref(v___x_5273_);
return v___x_5495_;
}
}
}
else
{
lean_object* v_a_5498_; lean_object* v_a_5499_; lean_object* v___x_5501_; uint8_t v_isShared_5502_; uint8_t v_isSharedCheck_5506_; 
lean_dec_ref(v___x_5273_);
lean_dec_ref(v_trace_5267_);
lean_dec_ref(v_a_5257_);
lean_dec_ref(v_ext_5253_);
lean_dec_ref(v_build_5251_);
lean_dec_ref(v_file_5250_);
v_a_5498_ = lean_ctor_get(v___x_5486_, 0);
v_a_5499_ = lean_ctor_get(v___x_5486_, 1);
v_isSharedCheck_5506_ = !lean_is_exclusive(v___x_5486_);
if (v_isSharedCheck_5506_ == 0)
{
v___x_5501_ = v___x_5486_;
v_isShared_5502_ = v_isSharedCheck_5506_;
goto v_resetjp_5500_;
}
else
{
lean_inc(v_a_5499_);
lean_inc(v_a_5498_);
lean_dec(v___x_5486_);
v___x_5501_ = lean_box(0);
v_isShared_5502_ = v_isSharedCheck_5506_;
goto v_resetjp_5500_;
}
v_resetjp_5500_:
{
lean_object* v___x_5504_; 
if (v_isShared_5502_ == 0)
{
v___x_5504_ = v___x_5501_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5505_; 
v_reuseFailAlloc_5505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5505_, 0, v_a_5498_);
lean_ctor_set(v_reuseFailAlloc_5505_, 1, v_a_5499_);
v___x_5504_ = v_reuseFailAlloc_5505_;
goto v_reusejp_5503_;
}
v_reusejp_5503_:
{
return v___x_5504_;
}
}
}
}
}
else
{
lean_object* v_a_5507_; lean_object* v_a_5508_; lean_object* v___x_5510_; uint8_t v_isShared_5511_; uint8_t v_isSharedCheck_5516_; 
lean_dec_ref(v___x_5273_);
lean_del_object(v___x_5270_);
lean_dec_ref(v_a_5257_);
lean_dec_ref(v_ext_5253_);
lean_dec_ref(v_build_5251_);
lean_dec_ref(v_file_5250_);
v_a_5507_ = lean_ctor_get(v___x_5302_, 0);
v_a_5508_ = lean_ctor_get(v___x_5302_, 1);
v_isSharedCheck_5516_ = !lean_is_exclusive(v___x_5302_);
if (v_isSharedCheck_5516_ == 0)
{
v___x_5510_ = v___x_5302_;
v_isShared_5511_ = v_isSharedCheck_5516_;
goto v_resetjp_5509_;
}
else
{
lean_inc(v_a_5508_);
lean_inc(v_a_5507_);
lean_dec(v___x_5302_);
v___x_5510_ = lean_box(0);
v_isShared_5511_ = v_isSharedCheck_5516_;
goto v_resetjp_5509_;
}
v_resetjp_5509_:
{
lean_object* v___x_5512_; lean_object* v___x_5514_; 
v___x_5512_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5512_, 0, v_a_5508_);
lean_ctor_set(v___x_5512_, 1, v_trace_5267_);
lean_ctor_set(v___x_5512_, 2, v_buildTime_5268_);
lean_ctor_set_uint8(v___x_5512_, sizeof(void*)*3, v_action_5265_);
lean_ctor_set_uint8(v___x_5512_, sizeof(void*)*3 + 1, v_wantsRebuild_5266_);
if (v_isShared_5511_ == 0)
{
lean_ctor_set(v___x_5510_, 1, v___x_5512_);
v___x_5514_ = v___x_5510_;
goto v_reusejp_5513_;
}
else
{
lean_object* v_reuseFailAlloc_5515_; 
v_reuseFailAlloc_5515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5515_, 0, v_a_5507_);
lean_ctor_set(v_reuseFailAlloc_5515_, 1, v___x_5512_);
v___x_5514_ = v_reuseFailAlloc_5515_;
goto v_reusejp_5513_;
}
v_reusejp_5513_:
{
return v___x_5514_;
}
}
}
v___jp_5274_:
{
lean_object* v_log_5277_; uint8_t v_action_5278_; uint8_t v_wantsRebuild_5279_; lean_object* v_buildTime_5280_; lean_object* v___x_5282_; uint8_t v_isShared_5283_; uint8_t v_isSharedCheck_5289_; 
v_log_5277_ = lean_ctor_get(v___y_5276_, 0);
v_action_5278_ = lean_ctor_get_uint8(v___y_5276_, sizeof(void*)*3);
v_wantsRebuild_5279_ = lean_ctor_get_uint8(v___y_5276_, sizeof(void*)*3 + 1);
v_buildTime_5280_ = lean_ctor_get(v___y_5276_, 2);
v_isSharedCheck_5289_ = !lean_is_exclusive(v___y_5276_);
if (v_isSharedCheck_5289_ == 0)
{
lean_object* v_unused_5290_; 
v_unused_5290_ = lean_ctor_get(v___y_5276_, 1);
lean_dec(v_unused_5290_);
v___x_5282_ = v___y_5276_;
v_isShared_5283_ = v_isSharedCheck_5289_;
goto v_resetjp_5281_;
}
else
{
lean_inc(v_buildTime_5280_);
lean_inc(v_log_5277_);
lean_dec(v___y_5276_);
v___x_5282_ = lean_box(0);
v_isShared_5283_ = v_isSharedCheck_5289_;
goto v_resetjp_5281_;
}
v_resetjp_5281_:
{
lean_object* v___x_5284_; lean_object* v___x_5286_; 
v___x_5284_ = l_Lake_Artifact_trace(v_art_5275_);
if (v_isShared_5283_ == 0)
{
lean_ctor_set(v___x_5282_, 1, v___x_5284_);
v___x_5286_ = v___x_5282_;
goto v_reusejp_5285_;
}
else
{
lean_object* v_reuseFailAlloc_5288_; 
v_reuseFailAlloc_5288_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5288_, 0, v_log_5277_);
lean_ctor_set(v_reuseFailAlloc_5288_, 1, v___x_5284_);
lean_ctor_set(v_reuseFailAlloc_5288_, 2, v_buildTime_5280_);
lean_ctor_set_uint8(v_reuseFailAlloc_5288_, sizeof(void*)*3, v_action_5278_);
lean_ctor_set_uint8(v_reuseFailAlloc_5288_, sizeof(void*)*3 + 1, v_wantsRebuild_5279_);
v___x_5286_ = v_reuseFailAlloc_5288_;
goto v_reusejp_5285_;
}
v_reusejp_5285_:
{
lean_object* v___x_5287_; 
v___x_5287_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_5275_, v___x_5273_, v___x_5286_);
lean_dec_ref(v___x_5273_);
return v___x_5287_;
}
}
}
v___jp_5291_:
{
lean_object* v___x_5297_; lean_object* v___x_5299_; 
v___x_5297_ = l_Lake_Artifact_trace(v___y_5292_);
if (v_isShared_5271_ == 0)
{
lean_ctor_set(v___x_5270_, 2, v_buildTime_5296_);
lean_ctor_set(v___x_5270_, 1, v___x_5297_);
lean_ctor_set(v___x_5270_, 0, v_log_5293_);
v___x_5299_ = v___x_5270_;
goto v_reusejp_5298_;
}
else
{
lean_object* v_reuseFailAlloc_5301_; 
v_reuseFailAlloc_5301_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5301_, 0, v_log_5293_);
lean_ctor_set(v_reuseFailAlloc_5301_, 1, v___x_5297_);
lean_ctor_set(v_reuseFailAlloc_5301_, 2, v_buildTime_5296_);
v___x_5299_ = v_reuseFailAlloc_5301_;
goto v_reusejp_5298_;
}
v_reusejp_5298_:
{
lean_object* v___x_5300_; 
lean_ctor_set_uint8(v___x_5299_, sizeof(void*)*3, v_action_5294_);
lean_ctor_set_uint8(v___x_5299_, sizeof(void*)*3 + 1, v_wantsRebuild_5295_);
v___x_5300_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v___y_5292_, v___x_5273_, v___x_5299_);
lean_dec_ref(v___x_5273_);
return v___x_5300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___boxed(lean_object* v_file_5518_, lean_object* v_build_5519_, lean_object* v_text_5520_, lean_object* v_ext_5521_, lean_object* v_restore_5522_, lean_object* v_exe_5523_, lean_object* v_platformIndependent_5524_, lean_object* v_a_5525_, lean_object* v_a_5526_, lean_object* v_a_5527_, lean_object* v_a_5528_, lean_object* v_a_5529_, lean_object* v_a_5530_, lean_object* v_a_5531_){
_start:
{
uint8_t v_text_boxed_5532_; uint8_t v_restore_boxed_5533_; uint8_t v_exe_boxed_5534_; uint8_t v_platformIndependent_boxed_5535_; lean_object* v_res_5536_; 
v_text_boxed_5532_ = lean_unbox(v_text_5520_);
v_restore_boxed_5533_ = lean_unbox(v_restore_5522_);
v_exe_boxed_5534_ = lean_unbox(v_exe_5523_);
v_platformIndependent_boxed_5535_ = lean_unbox(v_platformIndependent_5524_);
v_res_5536_ = l_Lake_buildArtifactUnlessUpToDate(v_file_5518_, v_build_5519_, v_text_boxed_5532_, v_ext_5521_, v_restore_boxed_5533_, v_exe_boxed_5534_, v_platformIndependent_boxed_5535_, v_a_5525_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_);
lean_dec_ref(v_a_5529_);
lean_dec(v_a_5528_);
lean_dec(v_a_5527_);
lean_dec(v_a_5526_);
return v_res_5536_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0(lean_object* v_extraDepTrace_5538_, lean_object* v_build_5539_, lean_object* v_file_5540_, uint8_t v_text_5541_, lean_object* v_depInfo_5542_, lean_object* v___y_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_, lean_object* v___y_5547_, lean_object* v___y_5548_){
_start:
{
lean_object* v___x_5550_; 
lean_inc_ref(v___y_5547_);
lean_inc(v___y_5546_);
lean_inc(v___y_5545_);
lean_inc(v___y_5544_);
lean_inc_ref(v___y_5543_);
v___x_5550_ = lean_apply_7(v_extraDepTrace_5538_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_, lean_box(0));
if (lean_obj_tag(v___x_5550_) == 0)
{
lean_object* v_a_5551_; lean_object* v_a_5552_; lean_object* v_log_5553_; uint8_t v_action_5554_; uint8_t v_wantsRebuild_5555_; lean_object* v_trace_5556_; lean_object* v_buildTime_5557_; lean_object* v___x_5559_; uint8_t v_isShared_5560_; uint8_t v_isSharedCheck_5588_; 
v_a_5551_ = lean_ctor_get(v___x_5550_, 1);
lean_inc(v_a_5551_);
v_a_5552_ = lean_ctor_get(v___x_5550_, 0);
lean_inc(v_a_5552_);
lean_dec_ref(v___x_5550_);
v_log_5553_ = lean_ctor_get(v_a_5551_, 0);
v_action_5554_ = lean_ctor_get_uint8(v_a_5551_, sizeof(void*)*3);
v_wantsRebuild_5555_ = lean_ctor_get_uint8(v_a_5551_, sizeof(void*)*3 + 1);
v_trace_5556_ = lean_ctor_get(v_a_5551_, 1);
v_buildTime_5557_ = lean_ctor_get(v_a_5551_, 2);
v_isSharedCheck_5588_ = !lean_is_exclusive(v_a_5551_);
if (v_isSharedCheck_5588_ == 0)
{
v___x_5559_ = v_a_5551_;
v_isShared_5560_ = v_isSharedCheck_5588_;
goto v_resetjp_5558_;
}
else
{
lean_inc(v_buildTime_5557_);
lean_inc(v_trace_5556_);
lean_inc(v_log_5553_);
lean_dec(v_a_5551_);
v___x_5559_ = lean_box(0);
v_isShared_5560_ = v_isSharedCheck_5588_;
goto v_resetjp_5558_;
}
v_resetjp_5558_:
{
lean_object* v___x_5561_; lean_object* v___x_5563_; 
v___x_5561_ = l_Lake_BuildTrace_mix(v_trace_5556_, v_a_5552_);
if (v_isShared_5560_ == 0)
{
lean_ctor_set(v___x_5559_, 1, v___x_5561_);
v___x_5563_ = v___x_5559_;
goto v_reusejp_5562_;
}
else
{
lean_object* v_reuseFailAlloc_5587_; 
v_reuseFailAlloc_5587_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5587_, 0, v_log_5553_);
lean_ctor_set(v_reuseFailAlloc_5587_, 1, v___x_5561_);
lean_ctor_set(v_reuseFailAlloc_5587_, 2, v_buildTime_5557_);
lean_ctor_set_uint8(v_reuseFailAlloc_5587_, sizeof(void*)*3, v_action_5554_);
lean_ctor_set_uint8(v_reuseFailAlloc_5587_, sizeof(void*)*3 + 1, v_wantsRebuild_5555_);
v___x_5563_ = v_reuseFailAlloc_5587_;
goto v_reusejp_5562_;
}
v_reusejp_5562_:
{
lean_object* v___x_5564_; lean_object* v___x_5565_; uint8_t v___x_5566_; lean_object* v___x_5567_; 
v___x_5564_ = lean_apply_1(v_build_5539_, v_depInfo_5542_);
v___x_5565_ = ((lean_object*)(l_Lake_buildFileAfterDep___redArg___lam__0___closed__0));
v___x_5566_ = 0;
v___x_5567_ = l_Lake_buildArtifactUnlessUpToDate(v_file_5540_, v___x_5564_, v_text_5541_, v___x_5565_, v___x_5566_, v___x_5566_, v___x_5566_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_, v___y_5547_, v___x_5563_);
if (lean_obj_tag(v___x_5567_) == 0)
{
lean_object* v_a_5568_; lean_object* v_a_5569_; lean_object* v___x_5571_; uint8_t v_isShared_5572_; uint8_t v_isSharedCheck_5577_; 
v_a_5568_ = lean_ctor_get(v___x_5567_, 0);
v_a_5569_ = lean_ctor_get(v___x_5567_, 1);
v_isSharedCheck_5577_ = !lean_is_exclusive(v___x_5567_);
if (v_isSharedCheck_5577_ == 0)
{
v___x_5571_ = v___x_5567_;
v_isShared_5572_ = v_isSharedCheck_5577_;
goto v_resetjp_5570_;
}
else
{
lean_inc(v_a_5569_);
lean_inc(v_a_5568_);
lean_dec(v___x_5567_);
v___x_5571_ = lean_box(0);
v_isShared_5572_ = v_isSharedCheck_5577_;
goto v_resetjp_5570_;
}
v_resetjp_5570_:
{
lean_object* v_path_5573_; lean_object* v___x_5575_; 
v_path_5573_ = lean_ctor_get(v_a_5568_, 1);
lean_inc_ref(v_path_5573_);
lean_dec(v_a_5568_);
if (v_isShared_5572_ == 0)
{
lean_ctor_set(v___x_5571_, 0, v_path_5573_);
v___x_5575_ = v___x_5571_;
goto v_reusejp_5574_;
}
else
{
lean_object* v_reuseFailAlloc_5576_; 
v_reuseFailAlloc_5576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5576_, 0, v_path_5573_);
lean_ctor_set(v_reuseFailAlloc_5576_, 1, v_a_5569_);
v___x_5575_ = v_reuseFailAlloc_5576_;
goto v_reusejp_5574_;
}
v_reusejp_5574_:
{
return v___x_5575_;
}
}
}
else
{
lean_object* v_a_5578_; lean_object* v_a_5579_; lean_object* v___x_5581_; uint8_t v_isShared_5582_; uint8_t v_isSharedCheck_5586_; 
v_a_5578_ = lean_ctor_get(v___x_5567_, 0);
v_a_5579_ = lean_ctor_get(v___x_5567_, 1);
v_isSharedCheck_5586_ = !lean_is_exclusive(v___x_5567_);
if (v_isSharedCheck_5586_ == 0)
{
v___x_5581_ = v___x_5567_;
v_isShared_5582_ = v_isSharedCheck_5586_;
goto v_resetjp_5580_;
}
else
{
lean_inc(v_a_5579_);
lean_inc(v_a_5578_);
lean_dec(v___x_5567_);
v___x_5581_ = lean_box(0);
v_isShared_5582_ = v_isSharedCheck_5586_;
goto v_resetjp_5580_;
}
v_resetjp_5580_:
{
lean_object* v___x_5584_; 
if (v_isShared_5582_ == 0)
{
v___x_5584_ = v___x_5581_;
goto v_reusejp_5583_;
}
else
{
lean_object* v_reuseFailAlloc_5585_; 
v_reuseFailAlloc_5585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5585_, 0, v_a_5578_);
lean_ctor_set(v_reuseFailAlloc_5585_, 1, v_a_5579_);
v___x_5584_ = v_reuseFailAlloc_5585_;
goto v_reusejp_5583_;
}
v_reusejp_5583_:
{
return v___x_5584_;
}
}
}
}
}
}
else
{
lean_object* v_a_5589_; lean_object* v_a_5590_; lean_object* v___x_5592_; uint8_t v_isShared_5593_; uint8_t v_isSharedCheck_5597_; 
lean_dec_ref(v___y_5543_);
lean_dec(v_depInfo_5542_);
lean_dec_ref(v_file_5540_);
lean_dec_ref(v_build_5539_);
v_a_5589_ = lean_ctor_get(v___x_5550_, 0);
v_a_5590_ = lean_ctor_get(v___x_5550_, 1);
v_isSharedCheck_5597_ = !lean_is_exclusive(v___x_5550_);
if (v_isSharedCheck_5597_ == 0)
{
v___x_5592_ = v___x_5550_;
v_isShared_5593_ = v_isSharedCheck_5597_;
goto v_resetjp_5591_;
}
else
{
lean_inc(v_a_5590_);
lean_inc(v_a_5589_);
lean_dec(v___x_5550_);
v___x_5592_ = lean_box(0);
v_isShared_5593_ = v_isSharedCheck_5597_;
goto v_resetjp_5591_;
}
v_resetjp_5591_:
{
lean_object* v___x_5595_; 
if (v_isShared_5593_ == 0)
{
v___x_5595_ = v___x_5592_;
goto v_reusejp_5594_;
}
else
{
lean_object* v_reuseFailAlloc_5596_; 
v_reuseFailAlloc_5596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5596_, 0, v_a_5589_);
lean_ctor_set(v_reuseFailAlloc_5596_, 1, v_a_5590_);
v___x_5595_ = v_reuseFailAlloc_5596_;
goto v_reusejp_5594_;
}
v_reusejp_5594_:
{
return v___x_5595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___boxed(lean_object* v_extraDepTrace_5598_, lean_object* v_build_5599_, lean_object* v_file_5600_, lean_object* v_text_5601_, lean_object* v_depInfo_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_){
_start:
{
uint8_t v_text_boxed_5610_; lean_object* v_res_5611_; 
v_text_boxed_5610_ = lean_unbox(v_text_5601_);
v_res_5611_ = l_Lake_buildFileAfterDep___redArg___lam__0(v_extraDepTrace_5598_, v_build_5599_, v_file_5600_, v_text_boxed_5610_, v_depInfo_5602_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_);
lean_dec_ref(v___y_5607_);
lean_dec(v___y_5606_);
lean_dec(v___y_5605_);
lean_dec(v___y_5604_);
return v_res_5611_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg(lean_object* v_file_5612_, lean_object* v_dep_5613_, lean_object* v_build_5614_, lean_object* v_extraDepTrace_5615_, uint8_t v_text_5616_, lean_object* v_a_5617_, lean_object* v_a_5618_, lean_object* v_a_5619_, lean_object* v_a_5620_, lean_object* v_a_5621_, lean_object* v_a_5622_){
_start:
{
lean_object* v___x_5624_; lean_object* v___f_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; uint8_t v___x_5628_; lean_object* v___x_5629_; 
v___x_5624_ = lean_box(v_text_5616_);
v___f_5625_ = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_5625_, 0, v_extraDepTrace_5615_);
lean_closure_set(v___f_5625_, 1, v_build_5614_);
lean_closure_set(v___f_5625_, 2, v_file_5612_);
lean_closure_set(v___f_5625_, 3, v___x_5624_);
v___x_5626_ = l_Lake_instDataKindFilePath;
v___x_5627_ = lean_unsigned_to_nat(0u);
v___x_5628_ = 0;
v___x_5629_ = l_Lake_Job_mapM___redArg(v___x_5626_, v_dep_5613_, v___f_5625_, v___x_5627_, v___x_5628_, v_a_5617_, v_a_5618_, v_a_5619_, v_a_5620_, v_a_5621_, v_a_5622_);
return v___x_5629_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___boxed(lean_object* v_file_5630_, lean_object* v_dep_5631_, lean_object* v_build_5632_, lean_object* v_extraDepTrace_5633_, lean_object* v_text_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_, lean_object* v_a_5637_, lean_object* v_a_5638_, lean_object* v_a_5639_, lean_object* v_a_5640_, lean_object* v_a_5641_){
_start:
{
uint8_t v_text_boxed_5642_; lean_object* v_res_5643_; 
v_text_boxed_5642_ = lean_unbox(v_text_5634_);
v_res_5643_ = l_Lake_buildFileAfterDep___redArg(v_file_5630_, v_dep_5631_, v_build_5632_, v_extraDepTrace_5633_, v_text_boxed_5642_, v_a_5635_, v_a_5636_, v_a_5637_, v_a_5638_, v_a_5639_, v_a_5640_);
lean_dec_ref(v_a_5640_);
lean_dec_ref(v_a_5639_);
lean_dec(v_a_5638_);
lean_dec(v_a_5637_);
lean_dec(v_a_5636_);
return v_res_5643_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object* v_00_u03b1_5644_, lean_object* v_file_5645_, lean_object* v_dep_5646_, lean_object* v_build_5647_, lean_object* v_extraDepTrace_5648_, uint8_t v_text_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_, lean_object* v_a_5654_, lean_object* v_a_5655_){
_start:
{
lean_object* v___x_5657_; lean_object* v___f_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; uint8_t v___x_5661_; lean_object* v___x_5662_; 
v___x_5657_ = lean_box(v_text_5649_);
v___f_5658_ = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_5658_, 0, v_extraDepTrace_5648_);
lean_closure_set(v___f_5658_, 1, v_build_5647_);
lean_closure_set(v___f_5658_, 2, v_file_5645_);
lean_closure_set(v___f_5658_, 3, v___x_5657_);
v___x_5659_ = l_Lake_instDataKindFilePath;
v___x_5660_ = lean_unsigned_to_nat(0u);
v___x_5661_ = 0;
v___x_5662_ = l_Lake_Job_mapM___redArg(v___x_5659_, v_dep_5646_, v___f_5658_, v___x_5660_, v___x_5661_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_, v_a_5655_);
return v___x_5662_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___boxed(lean_object* v_00_u03b1_5663_, lean_object* v_file_5664_, lean_object* v_dep_5665_, lean_object* v_build_5666_, lean_object* v_extraDepTrace_5667_, lean_object* v_text_5668_, lean_object* v_a_5669_, lean_object* v_a_5670_, lean_object* v_a_5671_, lean_object* v_a_5672_, lean_object* v_a_5673_, lean_object* v_a_5674_, lean_object* v_a_5675_){
_start:
{
uint8_t v_text_boxed_5676_; lean_object* v_res_5677_; 
v_text_boxed_5676_ = lean_unbox(v_text_5668_);
v_res_5677_ = l_Lake_buildFileAfterDep(v_00_u03b1_5663_, v_file_5664_, v_dep_5665_, v_build_5666_, v_extraDepTrace_5667_, v_text_boxed_5676_, v_a_5669_, v_a_5670_, v_a_5671_, v_a_5672_, v_a_5673_, v_a_5674_);
lean_dec_ref(v_a_5674_);
lean_dec_ref(v_a_5673_);
lean_dec(v_a_5672_);
lean_dec(v_a_5671_);
lean_dec(v_a_5670_);
return v_res_5677_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(lean_object* v_info_5678_){
_start:
{
lean_object* v___x_5680_; 
v___x_5680_ = l_Lake_computeBinFileHash(v_info_5678_);
if (lean_obj_tag(v___x_5680_) == 0)
{
lean_object* v_a_5681_; lean_object* v___x_5682_; 
v_a_5681_ = lean_ctor_get(v___x_5680_, 0);
lean_inc(v_a_5681_);
lean_dec_ref(v___x_5680_);
v___x_5682_ = lean_io_metadata(v_info_5678_);
if (lean_obj_tag(v___x_5682_) == 0)
{
lean_object* v_a_5683_; lean_object* v___x_5685_; uint8_t v_isShared_5686_; uint8_t v_isSharedCheck_5694_; 
v_a_5683_ = lean_ctor_get(v___x_5682_, 0);
v_isSharedCheck_5694_ = !lean_is_exclusive(v___x_5682_);
if (v_isSharedCheck_5694_ == 0)
{
v___x_5685_ = v___x_5682_;
v_isShared_5686_ = v_isSharedCheck_5694_;
goto v_resetjp_5684_;
}
else
{
lean_inc(v_a_5683_);
lean_dec(v___x_5682_);
v___x_5685_ = lean_box(0);
v_isShared_5686_ = v_isSharedCheck_5694_;
goto v_resetjp_5684_;
}
v_resetjp_5684_:
{
lean_object* v_modified_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; uint64_t v___x_5690_; lean_object* v___x_5692_; 
v_modified_5687_ = lean_ctor_get(v_a_5683_, 1);
lean_inc_ref(v_modified_5687_);
lean_dec(v_a_5683_);
v___x_5688_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_5689_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_5689_, 0, v_info_5678_);
lean_ctor_set(v___x_5689_, 1, v___x_5688_);
lean_ctor_set(v___x_5689_, 2, v_modified_5687_);
v___x_5690_ = lean_unbox_uint64(v_a_5681_);
lean_dec(v_a_5681_);
lean_ctor_set_uint64(v___x_5689_, sizeof(void*)*3, v___x_5690_);
if (v_isShared_5686_ == 0)
{
lean_ctor_set(v___x_5685_, 0, v___x_5689_);
v___x_5692_ = v___x_5685_;
goto v_reusejp_5691_;
}
else
{
lean_object* v_reuseFailAlloc_5693_; 
v_reuseFailAlloc_5693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5693_, 0, v___x_5689_);
v___x_5692_ = v_reuseFailAlloc_5693_;
goto v_reusejp_5691_;
}
v_reusejp_5691_:
{
return v___x_5692_;
}
}
}
else
{
lean_object* v_a_5695_; lean_object* v___x_5697_; uint8_t v_isShared_5698_; uint8_t v_isSharedCheck_5702_; 
lean_dec(v_a_5681_);
lean_dec_ref(v_info_5678_);
v_a_5695_ = lean_ctor_get(v___x_5682_, 0);
v_isSharedCheck_5702_ = !lean_is_exclusive(v___x_5682_);
if (v_isSharedCheck_5702_ == 0)
{
v___x_5697_ = v___x_5682_;
v_isShared_5698_ = v_isSharedCheck_5702_;
goto v_resetjp_5696_;
}
else
{
lean_inc(v_a_5695_);
lean_dec(v___x_5682_);
v___x_5697_ = lean_box(0);
v_isShared_5698_ = v_isSharedCheck_5702_;
goto v_resetjp_5696_;
}
v_resetjp_5696_:
{
lean_object* v___x_5700_; 
if (v_isShared_5698_ == 0)
{
v___x_5700_ = v___x_5697_;
goto v_reusejp_5699_;
}
else
{
lean_object* v_reuseFailAlloc_5701_; 
v_reuseFailAlloc_5701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5701_, 0, v_a_5695_);
v___x_5700_ = v_reuseFailAlloc_5701_;
goto v_reusejp_5699_;
}
v_reusejp_5699_:
{
return v___x_5700_;
}
}
}
}
else
{
lean_object* v_a_5703_; lean_object* v___x_5705_; uint8_t v_isShared_5706_; uint8_t v_isSharedCheck_5710_; 
lean_dec_ref(v_info_5678_);
v_a_5703_ = lean_ctor_get(v___x_5680_, 0);
v_isSharedCheck_5710_ = !lean_is_exclusive(v___x_5680_);
if (v_isSharedCheck_5710_ == 0)
{
v___x_5705_ = v___x_5680_;
v_isShared_5706_ = v_isSharedCheck_5710_;
goto v_resetjp_5704_;
}
else
{
lean_inc(v_a_5703_);
lean_dec(v___x_5680_);
v___x_5705_ = lean_box(0);
v_isShared_5706_ = v_isSharedCheck_5710_;
goto v_resetjp_5704_;
}
v_resetjp_5704_:
{
lean_object* v___x_5708_; 
if (v_isShared_5706_ == 0)
{
v___x_5708_ = v___x_5705_;
goto v_reusejp_5707_;
}
else
{
lean_object* v_reuseFailAlloc_5709_; 
v_reuseFailAlloc_5709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5709_, 0, v_a_5703_);
v___x_5708_ = v_reuseFailAlloc_5709_;
goto v_reusejp_5707_;
}
v_reusejp_5707_:
{
return v___x_5708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0___boxed(lean_object* v_info_5711_, lean_object* v_a_5712_){
_start:
{
lean_object* v_res_5713_; 
v_res_5713_ = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(v_info_5711_);
return v_res_5713_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0(lean_object* v_path_5714_, lean_object* v___y_5715_, lean_object* v___y_5716_, lean_object* v___y_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_){
_start:
{
lean_object* v_log_5722_; uint8_t v_action_5723_; uint8_t v_wantsRebuild_5724_; lean_object* v_trace_5725_; lean_object* v_buildTime_5726_; lean_object* v___x_5728_; uint8_t v_isShared_5729_; uint8_t v_isSharedCheck_5746_; 
v_log_5722_ = lean_ctor_get(v___y_5720_, 0);
v_action_5723_ = lean_ctor_get_uint8(v___y_5720_, sizeof(void*)*3);
v_wantsRebuild_5724_ = lean_ctor_get_uint8(v___y_5720_, sizeof(void*)*3 + 1);
v_trace_5725_ = lean_ctor_get(v___y_5720_, 1);
v_buildTime_5726_ = lean_ctor_get(v___y_5720_, 2);
v_isSharedCheck_5746_ = !lean_is_exclusive(v___y_5720_);
if (v_isSharedCheck_5746_ == 0)
{
v___x_5728_ = v___y_5720_;
v_isShared_5729_ = v_isSharedCheck_5746_;
goto v_resetjp_5727_;
}
else
{
lean_inc(v_buildTime_5726_);
lean_inc(v_trace_5725_);
lean_inc(v_log_5722_);
lean_dec(v___y_5720_);
v___x_5728_ = lean_box(0);
v_isShared_5729_ = v_isSharedCheck_5746_;
goto v_resetjp_5727_;
}
v_resetjp_5727_:
{
lean_object* v___x_5730_; 
lean_inc_ref(v_path_5714_);
v___x_5730_ = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(v_path_5714_);
if (lean_obj_tag(v___x_5730_) == 0)
{
lean_object* v_a_5731_; lean_object* v___x_5733_; 
lean_dec_ref(v_trace_5725_);
v_a_5731_ = lean_ctor_get(v___x_5730_, 0);
lean_inc(v_a_5731_);
lean_dec_ref(v___x_5730_);
if (v_isShared_5729_ == 0)
{
lean_ctor_set(v___x_5728_, 1, v_a_5731_);
v___x_5733_ = v___x_5728_;
goto v_reusejp_5732_;
}
else
{
lean_object* v_reuseFailAlloc_5735_; 
v_reuseFailAlloc_5735_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5735_, 0, v_log_5722_);
lean_ctor_set(v_reuseFailAlloc_5735_, 1, v_a_5731_);
lean_ctor_set(v_reuseFailAlloc_5735_, 2, v_buildTime_5726_);
lean_ctor_set_uint8(v_reuseFailAlloc_5735_, sizeof(void*)*3, v_action_5723_);
lean_ctor_set_uint8(v_reuseFailAlloc_5735_, sizeof(void*)*3 + 1, v_wantsRebuild_5724_);
v___x_5733_ = v_reuseFailAlloc_5735_;
goto v_reusejp_5732_;
}
v_reusejp_5732_:
{
lean_object* v___x_5734_; 
v___x_5734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5734_, 0, v_path_5714_);
lean_ctor_set(v___x_5734_, 1, v___x_5733_);
return v___x_5734_;
}
}
else
{
lean_object* v_a_5736_; lean_object* v___x_5737_; uint8_t v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5743_; 
lean_dec_ref(v_path_5714_);
v_a_5736_ = lean_ctor_get(v___x_5730_, 0);
lean_inc(v_a_5736_);
lean_dec_ref(v___x_5730_);
v___x_5737_ = lean_io_error_to_string(v_a_5736_);
v___x_5738_ = 3;
v___x_5739_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5739_, 0, v___x_5737_);
lean_ctor_set_uint8(v___x_5739_, sizeof(void*)*1, v___x_5738_);
v___x_5740_ = lean_array_get_size(v_log_5722_);
v___x_5741_ = lean_array_push(v_log_5722_, v___x_5739_);
if (v_isShared_5729_ == 0)
{
lean_ctor_set(v___x_5728_, 0, v___x_5741_);
v___x_5743_ = v___x_5728_;
goto v_reusejp_5742_;
}
else
{
lean_object* v_reuseFailAlloc_5745_; 
v_reuseFailAlloc_5745_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5745_, 0, v___x_5741_);
lean_ctor_set(v_reuseFailAlloc_5745_, 1, v_trace_5725_);
lean_ctor_set(v_reuseFailAlloc_5745_, 2, v_buildTime_5726_);
lean_ctor_set_uint8(v_reuseFailAlloc_5745_, sizeof(void*)*3, v_action_5723_);
lean_ctor_set_uint8(v_reuseFailAlloc_5745_, sizeof(void*)*3 + 1, v_wantsRebuild_5724_);
v___x_5743_ = v_reuseFailAlloc_5745_;
goto v_reusejp_5742_;
}
v_reusejp_5742_:
{
lean_object* v___x_5744_; 
v___x_5744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5744_, 0, v___x_5740_);
lean_ctor_set(v___x_5744_, 1, v___x_5743_);
return v___x_5744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0___boxed(lean_object* v_path_5747_, lean_object* v___y_5748_, lean_object* v___y_5749_, lean_object* v___y_5750_, lean_object* v___y_5751_, lean_object* v___y_5752_, lean_object* v___y_5753_, lean_object* v___y_5754_){
_start:
{
lean_object* v_res_5755_; 
v_res_5755_ = l_Lake_inputBinFile___redArg___lam__0(v_path_5747_, v___y_5748_, v___y_5749_, v___y_5750_, v___y_5751_, v___y_5752_, v___y_5753_);
lean_dec_ref(v___y_5752_);
lean_dec(v___y_5751_);
lean_dec(v___y_5750_);
lean_dec(v___y_5749_);
lean_dec_ref(v___y_5748_);
return v_res_5755_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg(lean_object* v_path_5757_, lean_object* v_a_5758_, lean_object* v_a_5759_, lean_object* v_a_5760_, lean_object* v_a_5761_, lean_object* v_a_5762_){
_start:
{
lean_object* v___f_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; 
v___f_5764_ = lean_alloc_closure((void*)(l_Lake_inputBinFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5764_, 0, v_path_5757_);
v___x_5765_ = l_Lake_instDataKindFilePath;
v___x_5766_ = lean_unsigned_to_nat(0u);
v___x_5767_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
v___x_5768_ = l_Lake_Job_async___redArg(v___x_5765_, v___f_5764_, v___x_5766_, v___x_5767_, v_a_5758_, v_a_5759_, v_a_5760_, v_a_5761_, v_a_5762_);
return v___x_5768_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___boxed(lean_object* v_path_5769_, lean_object* v_a_5770_, lean_object* v_a_5771_, lean_object* v_a_5772_, lean_object* v_a_5773_, lean_object* v_a_5774_, lean_object* v_a_5775_){
_start:
{
lean_object* v_res_5776_; 
v_res_5776_ = l_Lake_inputBinFile___redArg(v_path_5769_, v_a_5770_, v_a_5771_, v_a_5772_, v_a_5773_, v_a_5774_);
lean_dec_ref(v_a_5774_);
lean_dec(v_a_5773_);
lean_dec(v_a_5772_);
lean_dec(v_a_5771_);
return v_res_5776_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object* v_path_5777_, lean_object* v_a_5778_, lean_object* v_a_5779_, lean_object* v_a_5780_, lean_object* v_a_5781_, lean_object* v_a_5782_, lean_object* v_a_5783_){
_start:
{
lean_object* v___x_5785_; 
v___x_5785_ = l_Lake_inputBinFile___redArg(v_path_5777_, v_a_5778_, v_a_5779_, v_a_5780_, v_a_5781_, v_a_5782_);
return v___x_5785_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___boxed(lean_object* v_path_5786_, lean_object* v_a_5787_, lean_object* v_a_5788_, lean_object* v_a_5789_, lean_object* v_a_5790_, lean_object* v_a_5791_, lean_object* v_a_5792_, lean_object* v_a_5793_){
_start:
{
lean_object* v_res_5794_; 
v_res_5794_ = l_Lake_inputBinFile(v_path_5786_, v_a_5787_, v_a_5788_, v_a_5789_, v_a_5790_, v_a_5791_, v_a_5792_);
lean_dec_ref(v_a_5792_);
lean_dec_ref(v_a_5791_);
lean_dec(v_a_5790_);
lean_dec(v_a_5789_);
lean_dec(v_a_5788_);
return v_res_5794_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(lean_object* v_info_5795_){
_start:
{
lean_object* v___x_5797_; 
v___x_5797_ = l_Lake_computeTextFileHash(v_info_5795_);
if (lean_obj_tag(v___x_5797_) == 0)
{
lean_object* v_a_5798_; lean_object* v___x_5799_; 
v_a_5798_ = lean_ctor_get(v___x_5797_, 0);
lean_inc(v_a_5798_);
lean_dec_ref(v___x_5797_);
v___x_5799_ = lean_io_metadata(v_info_5795_);
if (lean_obj_tag(v___x_5799_) == 0)
{
lean_object* v_a_5800_; lean_object* v___x_5802_; uint8_t v_isShared_5803_; uint8_t v_isSharedCheck_5811_; 
v_a_5800_ = lean_ctor_get(v___x_5799_, 0);
v_isSharedCheck_5811_ = !lean_is_exclusive(v___x_5799_);
if (v_isSharedCheck_5811_ == 0)
{
v___x_5802_ = v___x_5799_;
v_isShared_5803_ = v_isSharedCheck_5811_;
goto v_resetjp_5801_;
}
else
{
lean_inc(v_a_5800_);
lean_dec(v___x_5799_);
v___x_5802_ = lean_box(0);
v_isShared_5803_ = v_isSharedCheck_5811_;
goto v_resetjp_5801_;
}
v_resetjp_5801_:
{
lean_object* v_modified_5804_; lean_object* v___x_5805_; lean_object* v___x_5806_; uint64_t v___x_5807_; lean_object* v___x_5809_; 
v_modified_5804_ = lean_ctor_get(v_a_5800_, 1);
lean_inc_ref(v_modified_5804_);
lean_dec(v_a_5800_);
v___x_5805_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_5806_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_5806_, 0, v_info_5795_);
lean_ctor_set(v___x_5806_, 1, v___x_5805_);
lean_ctor_set(v___x_5806_, 2, v_modified_5804_);
v___x_5807_ = lean_unbox_uint64(v_a_5798_);
lean_dec(v_a_5798_);
lean_ctor_set_uint64(v___x_5806_, sizeof(void*)*3, v___x_5807_);
if (v_isShared_5803_ == 0)
{
lean_ctor_set(v___x_5802_, 0, v___x_5806_);
v___x_5809_ = v___x_5802_;
goto v_reusejp_5808_;
}
else
{
lean_object* v_reuseFailAlloc_5810_; 
v_reuseFailAlloc_5810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5810_, 0, v___x_5806_);
v___x_5809_ = v_reuseFailAlloc_5810_;
goto v_reusejp_5808_;
}
v_reusejp_5808_:
{
return v___x_5809_;
}
}
}
else
{
lean_object* v_a_5812_; lean_object* v___x_5814_; uint8_t v_isShared_5815_; uint8_t v_isSharedCheck_5819_; 
lean_dec(v_a_5798_);
lean_dec_ref(v_info_5795_);
v_a_5812_ = lean_ctor_get(v___x_5799_, 0);
v_isSharedCheck_5819_ = !lean_is_exclusive(v___x_5799_);
if (v_isSharedCheck_5819_ == 0)
{
v___x_5814_ = v___x_5799_;
v_isShared_5815_ = v_isSharedCheck_5819_;
goto v_resetjp_5813_;
}
else
{
lean_inc(v_a_5812_);
lean_dec(v___x_5799_);
v___x_5814_ = lean_box(0);
v_isShared_5815_ = v_isSharedCheck_5819_;
goto v_resetjp_5813_;
}
v_resetjp_5813_:
{
lean_object* v___x_5817_; 
if (v_isShared_5815_ == 0)
{
v___x_5817_ = v___x_5814_;
goto v_reusejp_5816_;
}
else
{
lean_object* v_reuseFailAlloc_5818_; 
v_reuseFailAlloc_5818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5818_, 0, v_a_5812_);
v___x_5817_ = v_reuseFailAlloc_5818_;
goto v_reusejp_5816_;
}
v_reusejp_5816_:
{
return v___x_5817_;
}
}
}
}
else
{
lean_object* v_a_5820_; lean_object* v___x_5822_; uint8_t v_isShared_5823_; uint8_t v_isSharedCheck_5827_; 
lean_dec_ref(v_info_5795_);
v_a_5820_ = lean_ctor_get(v___x_5797_, 0);
v_isSharedCheck_5827_ = !lean_is_exclusive(v___x_5797_);
if (v_isSharedCheck_5827_ == 0)
{
v___x_5822_ = v___x_5797_;
v_isShared_5823_ = v_isSharedCheck_5827_;
goto v_resetjp_5821_;
}
else
{
lean_inc(v_a_5820_);
lean_dec(v___x_5797_);
v___x_5822_ = lean_box(0);
v_isShared_5823_ = v_isSharedCheck_5827_;
goto v_resetjp_5821_;
}
v_resetjp_5821_:
{
lean_object* v___x_5825_; 
if (v_isShared_5823_ == 0)
{
v___x_5825_ = v___x_5822_;
goto v_reusejp_5824_;
}
else
{
lean_object* v_reuseFailAlloc_5826_; 
v_reuseFailAlloc_5826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5826_, 0, v_a_5820_);
v___x_5825_ = v_reuseFailAlloc_5826_;
goto v_reusejp_5824_;
}
v_reusejp_5824_:
{
return v___x_5825_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0___boxed(lean_object* v_info_5828_, lean_object* v_a_5829_){
_start:
{
lean_object* v_res_5830_; 
v_res_5830_ = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(v_info_5828_);
return v_res_5830_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0(lean_object* v_path_5831_, lean_object* v___y_5832_, lean_object* v___y_5833_, lean_object* v___y_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_){
_start:
{
lean_object* v_log_5839_; uint8_t v_action_5840_; uint8_t v_wantsRebuild_5841_; lean_object* v_trace_5842_; lean_object* v_buildTime_5843_; lean_object* v___x_5845_; uint8_t v_isShared_5846_; uint8_t v_isSharedCheck_5863_; 
v_log_5839_ = lean_ctor_get(v___y_5837_, 0);
v_action_5840_ = lean_ctor_get_uint8(v___y_5837_, sizeof(void*)*3);
v_wantsRebuild_5841_ = lean_ctor_get_uint8(v___y_5837_, sizeof(void*)*3 + 1);
v_trace_5842_ = lean_ctor_get(v___y_5837_, 1);
v_buildTime_5843_ = lean_ctor_get(v___y_5837_, 2);
v_isSharedCheck_5863_ = !lean_is_exclusive(v___y_5837_);
if (v_isSharedCheck_5863_ == 0)
{
v___x_5845_ = v___y_5837_;
v_isShared_5846_ = v_isSharedCheck_5863_;
goto v_resetjp_5844_;
}
else
{
lean_inc(v_buildTime_5843_);
lean_inc(v_trace_5842_);
lean_inc(v_log_5839_);
lean_dec(v___y_5837_);
v___x_5845_ = lean_box(0);
v_isShared_5846_ = v_isSharedCheck_5863_;
goto v_resetjp_5844_;
}
v_resetjp_5844_:
{
lean_object* v___x_5847_; 
lean_inc_ref(v_path_5831_);
v___x_5847_ = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(v_path_5831_);
if (lean_obj_tag(v___x_5847_) == 0)
{
lean_object* v_a_5848_; lean_object* v___x_5850_; 
lean_dec_ref(v_trace_5842_);
v_a_5848_ = lean_ctor_get(v___x_5847_, 0);
lean_inc(v_a_5848_);
lean_dec_ref(v___x_5847_);
if (v_isShared_5846_ == 0)
{
lean_ctor_set(v___x_5845_, 1, v_a_5848_);
v___x_5850_ = v___x_5845_;
goto v_reusejp_5849_;
}
else
{
lean_object* v_reuseFailAlloc_5852_; 
v_reuseFailAlloc_5852_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5852_, 0, v_log_5839_);
lean_ctor_set(v_reuseFailAlloc_5852_, 1, v_a_5848_);
lean_ctor_set(v_reuseFailAlloc_5852_, 2, v_buildTime_5843_);
lean_ctor_set_uint8(v_reuseFailAlloc_5852_, sizeof(void*)*3, v_action_5840_);
lean_ctor_set_uint8(v_reuseFailAlloc_5852_, sizeof(void*)*3 + 1, v_wantsRebuild_5841_);
v___x_5850_ = v_reuseFailAlloc_5852_;
goto v_reusejp_5849_;
}
v_reusejp_5849_:
{
lean_object* v___x_5851_; 
v___x_5851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5851_, 0, v_path_5831_);
lean_ctor_set(v___x_5851_, 1, v___x_5850_);
return v___x_5851_;
}
}
else
{
lean_object* v_a_5853_; lean_object* v___x_5854_; uint8_t v___x_5855_; lean_object* v___x_5856_; lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v___x_5860_; 
lean_dec_ref(v_path_5831_);
v_a_5853_ = lean_ctor_get(v___x_5847_, 0);
lean_inc(v_a_5853_);
lean_dec_ref(v___x_5847_);
v___x_5854_ = lean_io_error_to_string(v_a_5853_);
v___x_5855_ = 3;
v___x_5856_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5856_, 0, v___x_5854_);
lean_ctor_set_uint8(v___x_5856_, sizeof(void*)*1, v___x_5855_);
v___x_5857_ = lean_array_get_size(v_log_5839_);
v___x_5858_ = lean_array_push(v_log_5839_, v___x_5856_);
if (v_isShared_5846_ == 0)
{
lean_ctor_set(v___x_5845_, 0, v___x_5858_);
v___x_5860_ = v___x_5845_;
goto v_reusejp_5859_;
}
else
{
lean_object* v_reuseFailAlloc_5862_; 
v_reuseFailAlloc_5862_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5862_, 0, v___x_5858_);
lean_ctor_set(v_reuseFailAlloc_5862_, 1, v_trace_5842_);
lean_ctor_set(v_reuseFailAlloc_5862_, 2, v_buildTime_5843_);
lean_ctor_set_uint8(v_reuseFailAlloc_5862_, sizeof(void*)*3, v_action_5840_);
lean_ctor_set_uint8(v_reuseFailAlloc_5862_, sizeof(void*)*3 + 1, v_wantsRebuild_5841_);
v___x_5860_ = v_reuseFailAlloc_5862_;
goto v_reusejp_5859_;
}
v_reusejp_5859_:
{
lean_object* v___x_5861_; 
v___x_5861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5861_, 0, v___x_5857_);
lean_ctor_set(v___x_5861_, 1, v___x_5860_);
return v___x_5861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0___boxed(lean_object* v_path_5864_, lean_object* v___y_5865_, lean_object* v___y_5866_, lean_object* v___y_5867_, lean_object* v___y_5868_, lean_object* v___y_5869_, lean_object* v___y_5870_, lean_object* v___y_5871_){
_start:
{
lean_object* v_res_5872_; 
v_res_5872_ = l_Lake_inputTextFile___redArg___lam__0(v_path_5864_, v___y_5865_, v___y_5866_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_);
lean_dec_ref(v___y_5869_);
lean_dec(v___y_5868_);
lean_dec(v___y_5867_);
lean_dec(v___y_5866_);
lean_dec_ref(v___y_5865_);
return v_res_5872_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg(lean_object* v_path_5873_, lean_object* v_a_5874_, lean_object* v_a_5875_, lean_object* v_a_5876_, lean_object* v_a_5877_, lean_object* v_a_5878_){
_start:
{
lean_object* v___f_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; 
v___f_5880_ = lean_alloc_closure((void*)(l_Lake_inputTextFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5880_, 0, v_path_5873_);
v___x_5881_ = l_Lake_instDataKindFilePath;
v___x_5882_ = lean_unsigned_to_nat(0u);
v___x_5883_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
v___x_5884_ = l_Lake_Job_async___redArg(v___x_5881_, v___f_5880_, v___x_5882_, v___x_5883_, v_a_5874_, v_a_5875_, v_a_5876_, v_a_5877_, v_a_5878_);
return v___x_5884_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___boxed(lean_object* v_path_5885_, lean_object* v_a_5886_, lean_object* v_a_5887_, lean_object* v_a_5888_, lean_object* v_a_5889_, lean_object* v_a_5890_, lean_object* v_a_5891_){
_start:
{
lean_object* v_res_5892_; 
v_res_5892_ = l_Lake_inputTextFile___redArg(v_path_5885_, v_a_5886_, v_a_5887_, v_a_5888_, v_a_5889_, v_a_5890_);
lean_dec_ref(v_a_5890_);
lean_dec(v_a_5889_);
lean_dec(v_a_5888_);
lean_dec(v_a_5887_);
return v_res_5892_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object* v_path_5893_, lean_object* v_a_5894_, lean_object* v_a_5895_, lean_object* v_a_5896_, lean_object* v_a_5897_, lean_object* v_a_5898_, lean_object* v_a_5899_){
_start:
{
lean_object* v___x_5901_; 
v___x_5901_ = l_Lake_inputTextFile___redArg(v_path_5893_, v_a_5894_, v_a_5895_, v_a_5896_, v_a_5897_, v_a_5898_);
return v___x_5901_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___boxed(lean_object* v_path_5902_, lean_object* v_a_5903_, lean_object* v_a_5904_, lean_object* v_a_5905_, lean_object* v_a_5906_, lean_object* v_a_5907_, lean_object* v_a_5908_, lean_object* v_a_5909_){
_start:
{
lean_object* v_res_5910_; 
v_res_5910_ = l_Lake_inputTextFile(v_path_5902_, v_a_5903_, v_a_5904_, v_a_5905_, v_a_5906_, v_a_5907_, v_a_5908_);
lean_dec_ref(v_a_5908_);
lean_dec_ref(v_a_5907_);
lean_dec(v_a_5906_);
lean_dec(v_a_5905_);
lean_dec(v_a_5904_);
return v_res_5910_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg(lean_object* v_path_5911_, uint8_t v_text_5912_, lean_object* v_a_5913_, lean_object* v_a_5914_, lean_object* v_a_5915_, lean_object* v_a_5916_, lean_object* v_a_5917_){
_start:
{
if (v_text_5912_ == 0)
{
lean_object* v___x_5919_; 
v___x_5919_ = l_Lake_inputBinFile___redArg(v_path_5911_, v_a_5913_, v_a_5914_, v_a_5915_, v_a_5916_, v_a_5917_);
return v___x_5919_;
}
else
{
lean_object* v___x_5920_; 
v___x_5920_ = l_Lake_inputTextFile___redArg(v_path_5911_, v_a_5913_, v_a_5914_, v_a_5915_, v_a_5916_, v_a_5917_);
return v___x_5920_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg___boxed(lean_object* v_path_5921_, lean_object* v_text_5922_, lean_object* v_a_5923_, lean_object* v_a_5924_, lean_object* v_a_5925_, lean_object* v_a_5926_, lean_object* v_a_5927_, lean_object* v_a_5928_){
_start:
{
uint8_t v_text_boxed_5929_; lean_object* v_res_5930_; 
v_text_boxed_5929_ = lean_unbox(v_text_5922_);
v_res_5930_ = l_Lake_inputFile___redArg(v_path_5921_, v_text_boxed_5929_, v_a_5923_, v_a_5924_, v_a_5925_, v_a_5926_, v_a_5927_);
lean_dec_ref(v_a_5927_);
lean_dec(v_a_5926_);
lean_dec(v_a_5925_);
lean_dec(v_a_5924_);
return v_res_5930_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object* v_path_5931_, uint8_t v_text_5932_, lean_object* v_a_5933_, lean_object* v_a_5934_, lean_object* v_a_5935_, lean_object* v_a_5936_, lean_object* v_a_5937_, lean_object* v_a_5938_){
_start:
{
if (v_text_5932_ == 0)
{
lean_object* v___x_5940_; 
v___x_5940_ = l_Lake_inputBinFile___redArg(v_path_5931_, v_a_5933_, v_a_5934_, v_a_5935_, v_a_5936_, v_a_5937_);
return v___x_5940_;
}
else
{
lean_object* v___x_5941_; 
v___x_5941_ = l_Lake_inputTextFile___redArg(v_path_5931_, v_a_5933_, v_a_5934_, v_a_5935_, v_a_5936_, v_a_5937_);
return v___x_5941_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object* v_path_5942_, lean_object* v_text_5943_, lean_object* v_a_5944_, lean_object* v_a_5945_, lean_object* v_a_5946_, lean_object* v_a_5947_, lean_object* v_a_5948_, lean_object* v_a_5949_, lean_object* v_a_5950_){
_start:
{
uint8_t v_text_boxed_5951_; lean_object* v_res_5952_; 
v_text_boxed_5951_ = lean_unbox(v_text_5943_);
v_res_5952_ = l_Lake_inputFile(v_path_5942_, v_text_boxed_5951_, v_a_5944_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_);
lean_dec_ref(v_a_5949_);
lean_dec_ref(v_a_5948_);
lean_dec(v_a_5947_);
lean_dec(v_a_5946_);
lean_dec(v_a_5945_);
return v_res_5952_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0(lean_object* v_x_5953_){
_start:
{
uint8_t v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; 
v___x_5955_ = 1;
v___x_5956_ = lean_box(v___x_5955_);
v___x_5957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5957_, 0, v___x_5956_);
return v___x_5957_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0___boxed(lean_object* v_x_5958_, lean_object* v___y_5959_){
_start:
{
lean_object* v_res_5960_; 
v_res_5960_ = l_Lake_inputDir___lam__0(v_x_5958_);
lean_dec_ref(v_x_5958_);
return v_res_5960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(lean_object* v_filter_5961_, lean_object* v_as_5962_, size_t v_i_5963_, size_t v_stop_5964_, lean_object* v_b_5965_, lean_object* v___y_5966_){
_start:
{
lean_object* v_a_5969_; lean_object* v_a_5970_; uint8_t v___x_5974_; 
v___x_5974_ = lean_usize_dec_eq(v_i_5963_, v_stop_5964_);
if (v___x_5974_ == 0)
{
lean_object* v___x_5975_; uint8_t v___x_5976_; 
v___x_5975_ = lean_array_uget_borrowed(v_as_5962_, v_i_5963_);
v___x_5976_ = l_System_FilePath_isDir(v___x_5975_);
if (v___x_5976_ == 0)
{
lean_object* v___x_5977_; uint8_t v___x_5978_; 
lean_inc_ref(v_filter_5961_);
lean_inc(v___x_5975_);
v___x_5977_ = lean_apply_1(v_filter_5961_, v___x_5975_);
v___x_5978_ = lean_unbox(v___x_5977_);
if (v___x_5978_ == 0)
{
v_a_5969_ = v_b_5965_;
v_a_5970_ = v___y_5966_;
goto v___jp_5968_;
}
else
{
lean_object* v___x_5979_; 
lean_inc(v___x_5975_);
v___x_5979_ = lean_array_push(v_b_5965_, v___x_5975_);
v_a_5969_ = v___x_5979_;
v_a_5970_ = v___y_5966_;
goto v___jp_5968_;
}
}
else
{
v_a_5969_ = v_b_5965_;
v_a_5970_ = v___y_5966_;
goto v___jp_5968_;
}
}
else
{
lean_object* v___x_5980_; 
lean_dec_ref(v_filter_5961_);
v___x_5980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5980_, 0, v_b_5965_);
lean_ctor_set(v___x_5980_, 1, v___y_5966_);
return v___x_5980_;
}
v___jp_5968_:
{
size_t v___x_5971_; size_t v___x_5972_; 
v___x_5971_ = ((size_t)1ULL);
v___x_5972_ = lean_usize_add(v_i_5963_, v___x_5971_);
v_i_5963_ = v___x_5972_;
v_b_5965_ = v_a_5969_;
v___y_5966_ = v_a_5970_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg___boxed(lean_object* v_filter_5981_, lean_object* v_as_5982_, lean_object* v_i_5983_, lean_object* v_stop_5984_, lean_object* v_b_5985_, lean_object* v___y_5986_, lean_object* v___y_5987_){
_start:
{
size_t v_i_boxed_5988_; size_t v_stop_boxed_5989_; lean_object* v_res_5990_; 
v_i_boxed_5988_ = lean_unbox_usize(v_i_5983_);
lean_dec(v_i_5983_);
v_stop_boxed_5989_ = lean_unbox_usize(v_stop_5984_);
lean_dec(v_stop_5984_);
v_res_5990_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_5981_, v_as_5982_, v_i_boxed_5988_, v_stop_boxed_5989_, v_b_5985_, v___y_5986_);
lean_dec_ref(v_as_5982_);
return v_res_5990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(lean_object* v_as_5992_, lean_object* v_lo_5993_, lean_object* v_hi_5994_){
_start:
{
uint8_t v___x_5995_; 
v___x_5995_ = lean_nat_dec_lt(v_lo_5993_, v_hi_5994_);
if (v___x_5995_ == 0)
{
lean_dec(v_lo_5993_);
return v_as_5992_;
}
else
{
lean_object* v___f_5996_; lean_object* v___x_5997_; lean_object* v_fst_5998_; lean_object* v_snd_5999_; uint8_t v___x_6000_; 
v___f_5996_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___closed__0));
lean_inc(v_lo_5993_);
v___x_5997_ = l_Array_qpartition___redArg(v_as_5992_, v___f_5996_, v_lo_5993_, v_hi_5994_);
v_fst_5998_ = lean_ctor_get(v___x_5997_, 0);
lean_inc(v_fst_5998_);
v_snd_5999_ = lean_ctor_get(v___x_5997_, 1);
lean_inc(v_snd_5999_);
lean_dec_ref(v___x_5997_);
v___x_6000_ = lean_nat_dec_le(v_hi_5994_, v_fst_5998_);
if (v___x_6000_ == 0)
{
lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; 
v___x_6001_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_snd_5999_, v_lo_5993_, v_fst_5998_);
v___x_6002_ = lean_unsigned_to_nat(1u);
v___x_6003_ = lean_nat_add(v_fst_5998_, v___x_6002_);
lean_dec(v_fst_5998_);
v_as_5992_ = v___x_6001_;
v_lo_5993_ = v___x_6003_;
goto _start;
}
else
{
lean_dec(v_fst_5998_);
lean_dec(v_lo_5993_);
return v_snd_5999_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___boxed(lean_object* v_as_6005_, lean_object* v_lo_6006_, lean_object* v_hi_6007_){
_start:
{
lean_object* v_res_6008_; 
v_res_6008_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_as_6005_, v_lo_6006_, v_hi_6007_);
lean_dec(v_hi_6007_);
return v_res_6008_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1(lean_object* v_path_6011_, lean_object* v___f_6012_, lean_object* v_filter_6013_, lean_object* v___y_6014_, lean_object* v___y_6015_, lean_object* v___y_6016_, lean_object* v___y_6017_, lean_object* v___y_6018_, lean_object* v___y_6019_){
_start:
{
lean_object* v___y_6022_; lean_object* v___y_6023_; lean_object* v___y_6026_; lean_object* v___y_6027_; lean_object* v___y_6028_; lean_object* v___y_6029_; lean_object* v___y_6030_; lean_object* v___y_6033_; lean_object* v___y_6034_; lean_object* v___y_6035_; lean_object* v___y_6036_; lean_object* v___y_6037_; lean_object* v_log_6039_; uint8_t v_action_6040_; uint8_t v_wantsRebuild_6041_; lean_object* v_trace_6042_; lean_object* v_buildTime_6043_; lean_object* v___x_6044_; 
v_log_6039_ = lean_ctor_get(v___y_6019_, 0);
v_action_6040_ = lean_ctor_get_uint8(v___y_6019_, sizeof(void*)*3);
v_wantsRebuild_6041_ = lean_ctor_get_uint8(v___y_6019_, sizeof(void*)*3 + 1);
v_trace_6042_ = lean_ctor_get(v___y_6019_, 1);
v_buildTime_6043_ = lean_ctor_get(v___y_6019_, 2);
v___x_6044_ = l_System_FilePath_walkDir(v_path_6011_, v___f_6012_);
if (lean_obj_tag(v___x_6044_) == 0)
{
lean_object* v_a_6045_; lean_object* v___x_6046_; lean_object* v_a_6048_; lean_object* v_a_6049_; lean_object* v___y_6056_; lean_object* v___x_6059_; lean_object* v___x_6060_; uint8_t v___x_6061_; 
v_a_6045_ = lean_ctor_get(v___x_6044_, 0);
lean_inc(v_a_6045_);
lean_dec_ref(v___x_6044_);
v___x_6046_ = lean_unsigned_to_nat(0u);
v___x_6059_ = lean_array_get_size(v_a_6045_);
v___x_6060_ = ((lean_object*)(l_Lake_inputDir___lam__1___closed__0));
v___x_6061_ = lean_nat_dec_lt(v___x_6046_, v___x_6059_);
if (v___x_6061_ == 0)
{
lean_dec(v_a_6045_);
lean_dec_ref(v_filter_6013_);
v_a_6048_ = v___x_6060_;
v_a_6049_ = v___y_6019_;
goto v___jp_6047_;
}
else
{
uint8_t v___x_6062_; 
v___x_6062_ = lean_nat_dec_le(v___x_6059_, v___x_6059_);
if (v___x_6062_ == 0)
{
if (v___x_6061_ == 0)
{
lean_dec(v_a_6045_);
lean_dec_ref(v_filter_6013_);
v_a_6048_ = v___x_6060_;
v_a_6049_ = v___y_6019_;
goto v___jp_6047_;
}
else
{
size_t v___x_6063_; size_t v___x_6064_; lean_object* v___x_6065_; 
v___x_6063_ = ((size_t)0ULL);
v___x_6064_ = lean_usize_of_nat(v___x_6059_);
v___x_6065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6013_, v_a_6045_, v___x_6063_, v___x_6064_, v___x_6060_, v___y_6019_);
lean_dec(v_a_6045_);
v___y_6056_ = v___x_6065_;
goto v___jp_6055_;
}
}
else
{
size_t v___x_6066_; size_t v___x_6067_; lean_object* v___x_6068_; 
v___x_6066_ = ((size_t)0ULL);
v___x_6067_ = lean_usize_of_nat(v___x_6059_);
v___x_6068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6013_, v_a_6045_, v___x_6066_, v___x_6067_, v___x_6060_, v___y_6019_);
lean_dec(v_a_6045_);
v___y_6056_ = v___x_6068_;
goto v___jp_6055_;
}
}
v___jp_6047_:
{
lean_object* v___x_6050_; uint8_t v___x_6051_; 
v___x_6050_ = lean_array_get_size(v_a_6048_);
v___x_6051_ = lean_nat_dec_eq(v___x_6050_, v___x_6046_);
if (v___x_6051_ == 0)
{
lean_object* v___x_6052_; lean_object* v___x_6053_; uint8_t v___x_6054_; 
v___x_6052_ = lean_unsigned_to_nat(1u);
v___x_6053_ = lean_nat_sub(v___x_6050_, v___x_6052_);
v___x_6054_ = lean_nat_dec_le(v___x_6046_, v___x_6053_);
if (v___x_6054_ == 0)
{
lean_inc(v___x_6053_);
v___y_6033_ = v___x_6053_;
v___y_6034_ = v___x_6050_;
v___y_6035_ = v_a_6048_;
v___y_6036_ = v_a_6049_;
v___y_6037_ = v___x_6053_;
goto v___jp_6032_;
}
else
{
v___y_6033_ = v___x_6053_;
v___y_6034_ = v___x_6050_;
v___y_6035_ = v_a_6048_;
v___y_6036_ = v_a_6049_;
v___y_6037_ = v___x_6046_;
goto v___jp_6032_;
}
}
else
{
v___y_6022_ = v_a_6049_;
v___y_6023_ = v_a_6048_;
goto v___jp_6021_;
}
}
v___jp_6055_:
{
if (lean_obj_tag(v___y_6056_) == 0)
{
lean_object* v_a_6057_; lean_object* v_a_6058_; 
v_a_6057_ = lean_ctor_get(v___y_6056_, 0);
lean_inc(v_a_6057_);
v_a_6058_ = lean_ctor_get(v___y_6056_, 1);
lean_inc(v_a_6058_);
lean_dec_ref(v___y_6056_);
v_a_6048_ = v_a_6057_;
v_a_6049_ = v_a_6058_;
goto v___jp_6047_;
}
else
{
return v___y_6056_;
}
}
}
else
{
lean_object* v___x_6070_; uint8_t v_isShared_6071_; uint8_t v_isSharedCheck_6082_; 
lean_inc(v_buildTime_6043_);
lean_inc_ref(v_trace_6042_);
lean_inc_ref(v_log_6039_);
lean_dec_ref(v_filter_6013_);
v_isSharedCheck_6082_ = !lean_is_exclusive(v___y_6019_);
if (v_isSharedCheck_6082_ == 0)
{
lean_object* v_unused_6083_; lean_object* v_unused_6084_; lean_object* v_unused_6085_; 
v_unused_6083_ = lean_ctor_get(v___y_6019_, 2);
lean_dec(v_unused_6083_);
v_unused_6084_ = lean_ctor_get(v___y_6019_, 1);
lean_dec(v_unused_6084_);
v_unused_6085_ = lean_ctor_get(v___y_6019_, 0);
lean_dec(v_unused_6085_);
v___x_6070_ = v___y_6019_;
v_isShared_6071_ = v_isSharedCheck_6082_;
goto v_resetjp_6069_;
}
else
{
lean_dec(v___y_6019_);
v___x_6070_ = lean_box(0);
v_isShared_6071_ = v_isSharedCheck_6082_;
goto v_resetjp_6069_;
}
v_resetjp_6069_:
{
lean_object* v_a_6072_; lean_object* v___x_6073_; uint8_t v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6079_; 
v_a_6072_ = lean_ctor_get(v___x_6044_, 0);
lean_inc(v_a_6072_);
lean_dec_ref(v___x_6044_);
v___x_6073_ = lean_io_error_to_string(v_a_6072_);
v___x_6074_ = 3;
v___x_6075_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6075_, 0, v___x_6073_);
lean_ctor_set_uint8(v___x_6075_, sizeof(void*)*1, v___x_6074_);
v___x_6076_ = lean_array_get_size(v_log_6039_);
v___x_6077_ = lean_array_push(v_log_6039_, v___x_6075_);
if (v_isShared_6071_ == 0)
{
lean_ctor_set(v___x_6070_, 0, v___x_6077_);
v___x_6079_ = v___x_6070_;
goto v_reusejp_6078_;
}
else
{
lean_object* v_reuseFailAlloc_6081_; 
v_reuseFailAlloc_6081_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6081_, 0, v___x_6077_);
lean_ctor_set(v_reuseFailAlloc_6081_, 1, v_trace_6042_);
lean_ctor_set(v_reuseFailAlloc_6081_, 2, v_buildTime_6043_);
lean_ctor_set_uint8(v_reuseFailAlloc_6081_, sizeof(void*)*3, v_action_6040_);
lean_ctor_set_uint8(v_reuseFailAlloc_6081_, sizeof(void*)*3 + 1, v_wantsRebuild_6041_);
v___x_6079_ = v_reuseFailAlloc_6081_;
goto v_reusejp_6078_;
}
v_reusejp_6078_:
{
lean_object* v___x_6080_; 
v___x_6080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6080_, 0, v___x_6076_);
lean_ctor_set(v___x_6080_, 1, v___x_6079_);
return v___x_6080_;
}
}
}
v___jp_6021_:
{
lean_object* v___x_6024_; 
v___x_6024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6024_, 0, v___y_6023_);
lean_ctor_set(v___x_6024_, 1, v___y_6022_);
return v___x_6024_;
}
v___jp_6025_:
{
lean_object* v___x_6031_; 
lean_dec(v___y_6026_);
v___x_6031_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v___y_6028_, v___y_6027_, v___y_6030_);
lean_dec(v___y_6030_);
v___y_6022_ = v___y_6029_;
v___y_6023_ = v___x_6031_;
goto v___jp_6021_;
}
v___jp_6032_:
{
uint8_t v___x_6038_; 
v___x_6038_ = lean_nat_dec_le(v___y_6037_, v___y_6033_);
if (v___x_6038_ == 0)
{
lean_dec(v___y_6033_);
lean_inc(v___y_6037_);
v___y_6026_ = v___y_6034_;
v___y_6027_ = v___y_6037_;
v___y_6028_ = v___y_6035_;
v___y_6029_ = v___y_6036_;
v___y_6030_ = v___y_6037_;
goto v___jp_6025_;
}
else
{
v___y_6026_ = v___y_6034_;
v___y_6027_ = v___y_6037_;
v___y_6028_ = v___y_6035_;
v___y_6029_ = v___y_6036_;
v___y_6030_ = v___y_6033_;
goto v___jp_6025_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1___boxed(lean_object* v_path_6086_, lean_object* v___f_6087_, lean_object* v_filter_6088_, lean_object* v___y_6089_, lean_object* v___y_6090_, lean_object* v___y_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_){
_start:
{
lean_object* v_res_6096_; 
v_res_6096_ = l_Lake_inputDir___lam__1(v_path_6086_, v___f_6087_, v_filter_6088_, v___y_6089_, v___y_6090_, v___y_6091_, v___y_6092_, v___y_6093_, v___y_6094_);
lean_dec_ref(v___y_6093_);
lean_dec(v___y_6092_);
lean_dec(v___y_6091_);
lean_dec(v___y_6090_);
lean_dec_ref(v___y_6089_);
return v_res_6096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(uint8_t v_text_6097_, size_t v_sz_6098_, size_t v_i_6099_, lean_object* v_bs_6100_, lean_object* v___y_6101_, lean_object* v___y_6102_, lean_object* v___y_6103_, lean_object* v___y_6104_, lean_object* v___y_6105_, lean_object* v___y_6106_){
_start:
{
uint8_t v___x_6108_; 
v___x_6108_ = lean_usize_dec_lt(v_i_6099_, v_sz_6098_);
if (v___x_6108_ == 0)
{
lean_object* v___x_6109_; 
lean_dec_ref(v___y_6101_);
v___x_6109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6109_, 0, v_bs_6100_);
lean_ctor_set(v___x_6109_, 1, v___y_6106_);
return v___x_6109_;
}
else
{
lean_object* v_v_6110_; lean_object* v___x_6111_; lean_object* v_bs_x27_6112_; lean_object* v___y_6114_; 
v_v_6110_ = lean_array_uget(v_bs_6100_, v_i_6099_);
v___x_6111_ = lean_unsigned_to_nat(0u);
v_bs_x27_6112_ = lean_array_uset(v_bs_6100_, v_i_6099_, v___x_6111_);
if (v_text_6097_ == 0)
{
lean_object* v___x_6119_; 
lean_inc_ref(v___y_6101_);
v___x_6119_ = l_Lake_inputBinFile___redArg(v_v_6110_, v___y_6101_, v___y_6102_, v___y_6103_, v___y_6104_, v___y_6105_);
v___y_6114_ = v___x_6119_;
goto v___jp_6113_;
}
else
{
lean_object* v___x_6120_; 
lean_inc_ref(v___y_6101_);
v___x_6120_ = l_Lake_inputTextFile___redArg(v_v_6110_, v___y_6101_, v___y_6102_, v___y_6103_, v___y_6104_, v___y_6105_);
v___y_6114_ = v___x_6120_;
goto v___jp_6113_;
}
v___jp_6113_:
{
size_t v___x_6115_; size_t v___x_6116_; lean_object* v___x_6117_; 
v___x_6115_ = ((size_t)1ULL);
v___x_6116_ = lean_usize_add(v_i_6099_, v___x_6115_);
v___x_6117_ = lean_array_uset(v_bs_x27_6112_, v_i_6099_, v___y_6114_);
v_i_6099_ = v___x_6116_;
v_bs_6100_ = v___x_6117_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0___boxed(lean_object* v_text_6121_, lean_object* v_sz_6122_, lean_object* v_i_6123_, lean_object* v_bs_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_, lean_object* v___y_6129_, lean_object* v___y_6130_, lean_object* v___y_6131_){
_start:
{
uint8_t v_text_boxed_6132_; size_t v_sz_boxed_6133_; size_t v_i_boxed_6134_; lean_object* v_res_6135_; 
v_text_boxed_6132_ = lean_unbox(v_text_6121_);
v_sz_boxed_6133_ = lean_unbox_usize(v_sz_6122_);
lean_dec(v_sz_6122_);
v_i_boxed_6134_ = lean_unbox_usize(v_i_6123_);
lean_dec(v_i_6123_);
v_res_6135_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(v_text_boxed_6132_, v_sz_boxed_6133_, v_i_boxed_6134_, v_bs_6124_, v___y_6125_, v___y_6126_, v___y_6127_, v___y_6128_, v___y_6129_, v___y_6130_);
lean_dec_ref(v___y_6129_);
lean_dec(v___y_6128_);
lean_dec(v___y_6127_);
lean_dec(v___y_6126_);
return v_res_6135_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2(uint8_t v_text_6136_, lean_object* v_path_6137_, lean_object* v_ps_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_, lean_object* v___y_6143_, lean_object* v___y_6144_){
_start:
{
size_t v_sz_6146_; size_t v___x_6147_; lean_object* v___x_6148_; 
v_sz_6146_ = lean_array_size(v_ps_6138_);
v___x_6147_ = ((size_t)0ULL);
v___x_6148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(v_text_6136_, v_sz_6146_, v___x_6147_, v_ps_6138_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_);
if (lean_obj_tag(v___x_6148_) == 0)
{
lean_object* v_a_6149_; lean_object* v_a_6150_; lean_object* v___x_6152_; uint8_t v_isShared_6153_; uint8_t v_isSharedCheck_6158_; 
v_a_6149_ = lean_ctor_get(v___x_6148_, 0);
v_a_6150_ = lean_ctor_get(v___x_6148_, 1);
v_isSharedCheck_6158_ = !lean_is_exclusive(v___x_6148_);
if (v_isSharedCheck_6158_ == 0)
{
v___x_6152_ = v___x_6148_;
v_isShared_6153_ = v_isSharedCheck_6158_;
goto v_resetjp_6151_;
}
else
{
lean_inc(v_a_6150_);
lean_inc(v_a_6149_);
lean_dec(v___x_6148_);
v___x_6152_ = lean_box(0);
v_isShared_6153_ = v_isSharedCheck_6158_;
goto v_resetjp_6151_;
}
v_resetjp_6151_:
{
lean_object* v___x_6154_; lean_object* v___x_6156_; 
v___x_6154_ = l_Lake_Job_collectArray___redArg(v_a_6149_, v_path_6137_);
lean_dec(v_a_6149_);
if (v_isShared_6153_ == 0)
{
lean_ctor_set(v___x_6152_, 0, v___x_6154_);
v___x_6156_ = v___x_6152_;
goto v_reusejp_6155_;
}
else
{
lean_object* v_reuseFailAlloc_6157_; 
v_reuseFailAlloc_6157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6157_, 0, v___x_6154_);
lean_ctor_set(v_reuseFailAlloc_6157_, 1, v_a_6150_);
v___x_6156_ = v_reuseFailAlloc_6157_;
goto v_reusejp_6155_;
}
v_reusejp_6155_:
{
return v___x_6156_;
}
}
}
else
{
lean_object* v_a_6159_; lean_object* v_a_6160_; lean_object* v___x_6162_; uint8_t v_isShared_6163_; uint8_t v_isSharedCheck_6167_; 
lean_dec_ref(v_path_6137_);
v_a_6159_ = lean_ctor_get(v___x_6148_, 0);
v_a_6160_ = lean_ctor_get(v___x_6148_, 1);
v_isSharedCheck_6167_ = !lean_is_exclusive(v___x_6148_);
if (v_isSharedCheck_6167_ == 0)
{
v___x_6162_ = v___x_6148_;
v_isShared_6163_ = v_isSharedCheck_6167_;
goto v_resetjp_6161_;
}
else
{
lean_inc(v_a_6160_);
lean_inc(v_a_6159_);
lean_dec(v___x_6148_);
v___x_6162_ = lean_box(0);
v_isShared_6163_ = v_isSharedCheck_6167_;
goto v_resetjp_6161_;
}
v_resetjp_6161_:
{
lean_object* v___x_6165_; 
if (v_isShared_6163_ == 0)
{
v___x_6165_ = v___x_6162_;
goto v_reusejp_6164_;
}
else
{
lean_object* v_reuseFailAlloc_6166_; 
v_reuseFailAlloc_6166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6166_, 0, v_a_6159_);
lean_ctor_set(v_reuseFailAlloc_6166_, 1, v_a_6160_);
v___x_6165_ = v_reuseFailAlloc_6166_;
goto v_reusejp_6164_;
}
v_reusejp_6164_:
{
return v___x_6165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2___boxed(lean_object* v_text_6168_, lean_object* v_path_6169_, lean_object* v_ps_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_){
_start:
{
uint8_t v_text_boxed_6178_; lean_object* v_res_6179_; 
v_text_boxed_6178_ = lean_unbox(v_text_6168_);
v_res_6179_ = l_Lake_inputDir___lam__2(v_text_boxed_6178_, v_path_6169_, v_ps_6170_, v___y_6171_, v___y_6172_, v___y_6173_, v___y_6174_, v___y_6175_, v___y_6176_);
lean_dec_ref(v___y_6175_);
lean_dec(v___y_6174_);
lean_dec(v___y_6173_);
lean_dec(v___y_6172_);
return v_res_6179_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir(lean_object* v_path_6181_, uint8_t v_text_6182_, lean_object* v_filter_6183_, lean_object* v_a_6184_, lean_object* v_a_6185_, lean_object* v_a_6186_, lean_object* v_a_6187_, lean_object* v_a_6188_, lean_object* v_a_6189_){
_start:
{
lean_object* v___f_6191_; lean_object* v___f_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___f_6198_; uint8_t v___x_6199_; lean_object* v___x_6200_; 
v___f_6191_ = ((lean_object*)(l_Lake_inputDir___closed__0));
lean_inc_ref(v_path_6181_);
v___f_6192_ = lean_alloc_closure((void*)(l_Lake_inputDir___lam__1___boxed), 10, 3);
lean_closure_set(v___f_6192_, 0, v_path_6181_);
lean_closure_set(v___f_6192_, 1, v___f_6191_);
lean_closure_set(v___f_6192_, 2, v_filter_6183_);
v___x_6193_ = lean_box(0);
v___x_6194_ = lean_unsigned_to_nat(0u);
v___x_6195_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
lean_inc_ref(v_a_6184_);
v___x_6196_ = l_Lake_Job_async___redArg(v___x_6193_, v___f_6192_, v___x_6194_, v___x_6195_, v_a_6184_, v_a_6185_, v_a_6186_, v_a_6187_, v_a_6188_);
v___x_6197_ = lean_box(v_text_6182_);
v___f_6198_ = lean_alloc_closure((void*)(l_Lake_inputDir___lam__2___boxed), 10, 2);
lean_closure_set(v___f_6198_, 0, v___x_6197_);
lean_closure_set(v___f_6198_, 1, v_path_6181_);
v___x_6199_ = 0;
v___x_6200_ = l_Lake_Job_bindM___redArg(v___x_6193_, v___x_6196_, v___f_6198_, v___x_6194_, v___x_6199_, v_a_6184_, v_a_6185_, v_a_6186_, v_a_6187_, v_a_6188_, v_a_6189_);
return v___x_6200_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___boxed(lean_object* v_path_6201_, lean_object* v_text_6202_, lean_object* v_filter_6203_, lean_object* v_a_6204_, lean_object* v_a_6205_, lean_object* v_a_6206_, lean_object* v_a_6207_, lean_object* v_a_6208_, lean_object* v_a_6209_, lean_object* v_a_6210_){
_start:
{
uint8_t v_text_boxed_6211_; lean_object* v_res_6212_; 
v_text_boxed_6211_ = lean_unbox(v_text_6202_);
v_res_6212_ = l_Lake_inputDir(v_path_6201_, v_text_boxed_6211_, v_filter_6203_, v_a_6204_, v_a_6205_, v_a_6206_, v_a_6207_, v_a_6208_, v_a_6209_);
lean_dec_ref(v_a_6209_);
lean_dec_ref(v_a_6208_);
lean_dec(v_a_6207_);
lean_dec(v_a_6206_);
lean_dec(v_a_6205_);
return v_res_6212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(lean_object* v_n_6213_, lean_object* v_as_6214_, lean_object* v_lo_6215_, lean_object* v_hi_6216_, lean_object* v_w_6217_, lean_object* v_hlo_6218_, lean_object* v_hhi_6219_){
_start:
{
lean_object* v___x_6220_; 
v___x_6220_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_as_6214_, v_lo_6215_, v_hi_6216_);
return v___x_6220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___boxed(lean_object* v_n_6221_, lean_object* v_as_6222_, lean_object* v_lo_6223_, lean_object* v_hi_6224_, lean_object* v_w_6225_, lean_object* v_hlo_6226_, lean_object* v_hhi_6227_){
_start:
{
lean_object* v_res_6228_; 
v_res_6228_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(v_n_6221_, v_as_6222_, v_lo_6223_, v_hi_6224_, v_w_6225_, v_hlo_6226_, v_hhi_6227_);
lean_dec(v_hi_6224_);
lean_dec(v_n_6221_);
return v_res_6228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(lean_object* v_filter_6229_, lean_object* v_as_6230_, size_t v_i_6231_, size_t v_stop_6232_, lean_object* v_b_6233_, lean_object* v___y_6234_, lean_object* v___y_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_, lean_object* v___y_6238_, lean_object* v___y_6239_){
_start:
{
lean_object* v___x_6241_; 
v___x_6241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6229_, v_as_6230_, v_i_6231_, v_stop_6232_, v_b_6233_, v___y_6239_);
return v___x_6241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___boxed(lean_object* v_filter_6242_, lean_object* v_as_6243_, lean_object* v_i_6244_, lean_object* v_stop_6245_, lean_object* v_b_6246_, lean_object* v___y_6247_, lean_object* v___y_6248_, lean_object* v___y_6249_, lean_object* v___y_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_, lean_object* v___y_6253_){
_start:
{
size_t v_i_boxed_6254_; size_t v_stop_boxed_6255_; lean_object* v_res_6256_; 
v_i_boxed_6254_ = lean_unbox_usize(v_i_6244_);
lean_dec(v_i_6244_);
v_stop_boxed_6255_ = lean_unbox_usize(v_stop_6245_);
lean_dec(v_stop_6245_);
v_res_6256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(v_filter_6242_, v_as_6243_, v_i_boxed_6254_, v_stop_boxed_6255_, v_b_6246_, v___y_6247_, v___y_6248_, v___y_6249_, v___y_6250_, v___y_6251_, v___y_6252_);
lean_dec_ref(v___y_6251_);
lean_dec(v___y_6250_);
lean_dec(v___y_6249_);
lean_dec(v___y_6248_);
lean_dec_ref(v___y_6247_);
lean_dec_ref(v_as_6243_);
return v_res_6256_;
}
}
LEAN_EXPORT uint64_t l_Lake_buildO___lam__0(uint64_t v_ts_6257_, lean_object* v_t_6258_){
_start:
{
uint64_t v___x_6259_; uint64_t v___x_6260_; uint64_t v___x_6261_; uint64_t v___x_6262_; 
v___x_6259_ = l_Lake_Hash_nil;
v___x_6260_ = lean_string_hash(v_t_6258_);
v___x_6261_ = lean_uint64_mix_hash(v___x_6259_, v___x_6260_);
v___x_6262_ = lean_uint64_mix_hash(v_ts_6257_, v___x_6261_);
return v___x_6262_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__0___boxed(lean_object* v_ts_6263_, lean_object* v_t_6264_){
_start:
{
uint64_t v_ts_boxed_6265_; uint64_t v_res_6266_; lean_object* v_r_6267_; 
v_ts_boxed_6265_ = lean_unbox_uint64(v_ts_6263_);
lean_dec_ref(v_ts_6263_);
v_res_6266_ = l_Lake_buildO___lam__0(v_ts_boxed_6265_, v_t_6264_);
lean_dec_ref(v_t_6264_);
v_r_6267_ = lean_box_uint64(v_res_6266_);
return v_r_6267_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1(lean_object* v_oFile_6268_, lean_object* v_srcFile_6269_, lean_object* v___x_6270_, lean_object* v_compiler_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_, lean_object* v___y_6274_, lean_object* v___y_6275_, lean_object* v___y_6276_, lean_object* v___y_6277_){
_start:
{
lean_object* v_log_6279_; uint8_t v_action_6280_; uint8_t v_wantsRebuild_6281_; lean_object* v_trace_6282_; lean_object* v_buildTime_6283_; lean_object* v___x_6285_; uint8_t v_isShared_6286_; uint8_t v_isSharedCheck_6312_; 
v_log_6279_ = lean_ctor_get(v___y_6277_, 0);
v_action_6280_ = lean_ctor_get_uint8(v___y_6277_, sizeof(void*)*3);
v_wantsRebuild_6281_ = lean_ctor_get_uint8(v___y_6277_, sizeof(void*)*3 + 1);
v_trace_6282_ = lean_ctor_get(v___y_6277_, 1);
v_buildTime_6283_ = lean_ctor_get(v___y_6277_, 2);
v_isSharedCheck_6312_ = !lean_is_exclusive(v___y_6277_);
if (v_isSharedCheck_6312_ == 0)
{
v___x_6285_ = v___y_6277_;
v_isShared_6286_ = v_isSharedCheck_6312_;
goto v_resetjp_6284_;
}
else
{
lean_inc(v_buildTime_6283_);
lean_inc(v_trace_6282_);
lean_inc(v_log_6279_);
lean_dec(v___y_6277_);
v___x_6285_ = lean_box(0);
v_isShared_6286_ = v_isSharedCheck_6312_;
goto v_resetjp_6284_;
}
v_resetjp_6284_:
{
lean_object* v___x_6287_; 
v___x_6287_ = l_Lake_compileO(v_oFile_6268_, v_srcFile_6269_, v___x_6270_, v_compiler_6271_, v_log_6279_);
if (lean_obj_tag(v___x_6287_) == 0)
{
lean_object* v_a_6288_; lean_object* v_a_6289_; lean_object* v___x_6291_; uint8_t v_isShared_6292_; uint8_t v_isSharedCheck_6299_; 
v_a_6288_ = lean_ctor_get(v___x_6287_, 0);
v_a_6289_ = lean_ctor_get(v___x_6287_, 1);
v_isSharedCheck_6299_ = !lean_is_exclusive(v___x_6287_);
if (v_isSharedCheck_6299_ == 0)
{
v___x_6291_ = v___x_6287_;
v_isShared_6292_ = v_isSharedCheck_6299_;
goto v_resetjp_6290_;
}
else
{
lean_inc(v_a_6289_);
lean_inc(v_a_6288_);
lean_dec(v___x_6287_);
v___x_6291_ = lean_box(0);
v_isShared_6292_ = v_isSharedCheck_6299_;
goto v_resetjp_6290_;
}
v_resetjp_6290_:
{
lean_object* v___x_6294_; 
if (v_isShared_6286_ == 0)
{
lean_ctor_set(v___x_6285_, 0, v_a_6289_);
v___x_6294_ = v___x_6285_;
goto v_reusejp_6293_;
}
else
{
lean_object* v_reuseFailAlloc_6298_; 
v_reuseFailAlloc_6298_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6298_, 0, v_a_6289_);
lean_ctor_set(v_reuseFailAlloc_6298_, 1, v_trace_6282_);
lean_ctor_set(v_reuseFailAlloc_6298_, 2, v_buildTime_6283_);
lean_ctor_set_uint8(v_reuseFailAlloc_6298_, sizeof(void*)*3, v_action_6280_);
lean_ctor_set_uint8(v_reuseFailAlloc_6298_, sizeof(void*)*3 + 1, v_wantsRebuild_6281_);
v___x_6294_ = v_reuseFailAlloc_6298_;
goto v_reusejp_6293_;
}
v_reusejp_6293_:
{
lean_object* v___x_6296_; 
if (v_isShared_6292_ == 0)
{
lean_ctor_set(v___x_6291_, 1, v___x_6294_);
v___x_6296_ = v___x_6291_;
goto v_reusejp_6295_;
}
else
{
lean_object* v_reuseFailAlloc_6297_; 
v_reuseFailAlloc_6297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6297_, 0, v_a_6288_);
lean_ctor_set(v_reuseFailAlloc_6297_, 1, v___x_6294_);
v___x_6296_ = v_reuseFailAlloc_6297_;
goto v_reusejp_6295_;
}
v_reusejp_6295_:
{
return v___x_6296_;
}
}
}
}
else
{
lean_object* v_a_6300_; lean_object* v_a_6301_; lean_object* v___x_6303_; uint8_t v_isShared_6304_; uint8_t v_isSharedCheck_6311_; 
v_a_6300_ = lean_ctor_get(v___x_6287_, 0);
v_a_6301_ = lean_ctor_get(v___x_6287_, 1);
v_isSharedCheck_6311_ = !lean_is_exclusive(v___x_6287_);
if (v_isSharedCheck_6311_ == 0)
{
v___x_6303_ = v___x_6287_;
v_isShared_6304_ = v_isSharedCheck_6311_;
goto v_resetjp_6302_;
}
else
{
lean_inc(v_a_6301_);
lean_inc(v_a_6300_);
lean_dec(v___x_6287_);
v___x_6303_ = lean_box(0);
v_isShared_6304_ = v_isSharedCheck_6311_;
goto v_resetjp_6302_;
}
v_resetjp_6302_:
{
lean_object* v___x_6306_; 
if (v_isShared_6286_ == 0)
{
lean_ctor_set(v___x_6285_, 0, v_a_6301_);
v___x_6306_ = v___x_6285_;
goto v_reusejp_6305_;
}
else
{
lean_object* v_reuseFailAlloc_6310_; 
v_reuseFailAlloc_6310_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6310_, 0, v_a_6301_);
lean_ctor_set(v_reuseFailAlloc_6310_, 1, v_trace_6282_);
lean_ctor_set(v_reuseFailAlloc_6310_, 2, v_buildTime_6283_);
lean_ctor_set_uint8(v_reuseFailAlloc_6310_, sizeof(void*)*3, v_action_6280_);
lean_ctor_set_uint8(v_reuseFailAlloc_6310_, sizeof(void*)*3 + 1, v_wantsRebuild_6281_);
v___x_6306_ = v_reuseFailAlloc_6310_;
goto v_reusejp_6305_;
}
v_reusejp_6305_:
{
lean_object* v___x_6308_; 
if (v_isShared_6304_ == 0)
{
lean_ctor_set(v___x_6303_, 1, v___x_6306_);
v___x_6308_ = v___x_6303_;
goto v_reusejp_6307_;
}
else
{
lean_object* v_reuseFailAlloc_6309_; 
v_reuseFailAlloc_6309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6309_, 0, v_a_6300_);
lean_ctor_set(v_reuseFailAlloc_6309_, 1, v___x_6306_);
v___x_6308_ = v_reuseFailAlloc_6309_;
goto v_reusejp_6307_;
}
v_reusejp_6307_:
{
return v___x_6308_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1___boxed(lean_object* v_oFile_6313_, lean_object* v_srcFile_6314_, lean_object* v___x_6315_, lean_object* v_compiler_6316_, lean_object* v___y_6317_, lean_object* v___y_6318_, lean_object* v___y_6319_, lean_object* v___y_6320_, lean_object* v___y_6321_, lean_object* v___y_6322_, lean_object* v___y_6323_){
_start:
{
lean_object* v_res_6324_; 
v_res_6324_ = l_Lake_buildO___lam__1(v_oFile_6313_, v_srcFile_6314_, v___x_6315_, v_compiler_6316_, v___y_6317_, v___y_6318_, v___y_6319_, v___y_6320_, v___y_6321_, v___y_6322_);
lean_dec_ref(v___y_6321_);
lean_dec(v___y_6320_);
lean_dec(v___y_6319_);
lean_dec(v___y_6318_);
lean_dec_ref(v___y_6317_);
lean_dec_ref(v___x_6315_);
return v_res_6324_;
}
}
static lean_object* _init_l_Lake_buildO___lam__2___boxed__const__1(void){
_start:
{
uint64_t v___x_6328_; lean_object* v___x_6329_; 
v___x_6328_ = l_Lake_Hash_nil;
v___x_6329_ = lean_box_uint64(v___x_6328_);
return v___x_6329_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2(lean_object* v_traceArgs_6330_, lean_object* v___f_6331_, lean_object* v_extraDepTrace_6332_, lean_object* v_weakArgs_6333_, lean_object* v_oFile_6334_, lean_object* v_compiler_6335_, lean_object* v___x_6336_, lean_object* v___f_6337_, lean_object* v_srcFile_6338_, lean_object* v___y_6339_, lean_object* v___y_6340_, lean_object* v___y_6341_, lean_object* v___y_6342_, lean_object* v___y_6343_, lean_object* v___y_6344_){
_start:
{
lean_object* v_log_6346_; uint8_t v_action_6347_; uint8_t v_wantsRebuild_6348_; lean_object* v_trace_6349_; lean_object* v_buildTime_6350_; lean_object* v___x_6352_; uint8_t v_isShared_6353_; uint8_t v_isSharedCheck_6435_; 
v_log_6346_ = lean_ctor_get(v___y_6344_, 0);
v_action_6347_ = lean_ctor_get_uint8(v___y_6344_, sizeof(void*)*3);
v_wantsRebuild_6348_ = lean_ctor_get_uint8(v___y_6344_, sizeof(void*)*3 + 1);
v_trace_6349_ = lean_ctor_get(v___y_6344_, 1);
v_buildTime_6350_ = lean_ctor_get(v___y_6344_, 2);
v_isSharedCheck_6435_ = !lean_is_exclusive(v___y_6344_);
if (v_isSharedCheck_6435_ == 0)
{
v___x_6352_ = v___y_6344_;
v_isShared_6353_ = v_isSharedCheck_6435_;
goto v_resetjp_6351_;
}
else
{
lean_inc(v_buildTime_6350_);
lean_inc(v_trace_6349_);
lean_inc(v_log_6346_);
lean_dec(v___y_6344_);
v___x_6352_ = lean_box(0);
v_isShared_6353_ = v_isSharedCheck_6435_;
goto v_resetjp_6351_;
}
v_resetjp_6351_:
{
lean_object* v___x_6354_; lean_object* v___x_6355_; uint64_t v___y_6357_; uint64_t v___x_6420_; lean_object* v___x_6421_; lean_object* v___x_6422_; uint8_t v___x_6423_; 
v___x_6354_ = l_Lake_platformTrace;
v___x_6355_ = l_Lake_BuildTrace_mix(v_trace_6349_, v___x_6354_);
v___x_6420_ = l_Lake_Hash_nil;
v___x_6421_ = lean_unsigned_to_nat(0u);
v___x_6422_ = lean_array_get_size(v_traceArgs_6330_);
v___x_6423_ = lean_nat_dec_lt(v___x_6421_, v___x_6422_);
if (v___x_6423_ == 0)
{
lean_dec_ref(v___f_6337_);
lean_dec_ref(v___x_6336_);
v___y_6357_ = v___x_6420_;
goto v___jp_6356_;
}
else
{
uint8_t v___x_6424_; 
v___x_6424_ = lean_nat_dec_le(v___x_6422_, v___x_6422_);
if (v___x_6424_ == 0)
{
if (v___x_6423_ == 0)
{
lean_dec_ref(v___f_6337_);
lean_dec_ref(v___x_6336_);
v___y_6357_ = v___x_6420_;
goto v___jp_6356_;
}
else
{
size_t v___x_6425_; size_t v___x_6426_; lean_object* v___x_6427_; lean_object* v___x_6428_; uint64_t v___x_6429_; 
v___x_6425_ = ((size_t)0ULL);
v___x_6426_ = lean_usize_of_nat(v___x_6422_);
v___x_6427_ = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(v_traceArgs_6330_);
v___x_6428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_6336_, v___f_6337_, v_traceArgs_6330_, v___x_6425_, v___x_6426_, v___x_6427_);
v___x_6429_ = lean_unbox_uint64(v___x_6428_);
lean_dec(v___x_6428_);
v___y_6357_ = v___x_6429_;
goto v___jp_6356_;
}
}
else
{
size_t v___x_6430_; size_t v___x_6431_; lean_object* v___x_6432_; lean_object* v___x_6433_; uint64_t v___x_6434_; 
v___x_6430_ = ((size_t)0ULL);
v___x_6431_ = lean_usize_of_nat(v___x_6422_);
v___x_6432_ = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(v_traceArgs_6330_);
v___x_6433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_6336_, v___f_6337_, v_traceArgs_6330_, v___x_6430_, v___x_6431_, v___x_6432_);
v___x_6434_ = lean_unbox_uint64(v___x_6433_);
lean_dec(v___x_6433_);
v___y_6357_ = v___x_6434_;
goto v___jp_6356_;
}
}
v___jp_6356_:
{
lean_object* v___x_6358_; lean_object* v___x_6359_; lean_object* v___x_6360_; lean_object* v___x_6361_; lean_object* v___x_6362_; lean_object* v___x_6363_; lean_object* v___x_6364_; lean_object* v___x_6365_; lean_object* v___x_6366_; lean_object* v___x_6367_; lean_object* v___x_6369_; 
v___x_6358_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_6359_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_6330_);
v___x_6360_ = lean_array_to_list(v_traceArgs_6330_);
v___x_6361_ = l_List_toString___redArg(v___f_6331_, v___x_6360_);
v___x_6362_ = lean_string_append(v___x_6359_, v___x_6361_);
lean_dec_ref(v___x_6361_);
v___x_6363_ = lean_string_append(v___x_6358_, v___x_6362_);
lean_dec_ref(v___x_6362_);
v___x_6364_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_6365_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_6366_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6366_, 0, v___x_6363_);
lean_ctor_set(v___x_6366_, 1, v___x_6364_);
lean_ctor_set(v___x_6366_, 2, v___x_6365_);
lean_ctor_set_uint64(v___x_6366_, sizeof(void*)*3, v___y_6357_);
v___x_6367_ = l_Lake_BuildTrace_mix(v___x_6355_, v___x_6366_);
if (v_isShared_6353_ == 0)
{
lean_ctor_set(v___x_6352_, 1, v___x_6367_);
v___x_6369_ = v___x_6352_;
goto v_reusejp_6368_;
}
else
{
lean_object* v_reuseFailAlloc_6419_; 
v_reuseFailAlloc_6419_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6419_, 0, v_log_6346_);
lean_ctor_set(v_reuseFailAlloc_6419_, 1, v___x_6367_);
lean_ctor_set(v_reuseFailAlloc_6419_, 2, v_buildTime_6350_);
lean_ctor_set_uint8(v_reuseFailAlloc_6419_, sizeof(void*)*3, v_action_6347_);
lean_ctor_set_uint8(v_reuseFailAlloc_6419_, sizeof(void*)*3 + 1, v_wantsRebuild_6348_);
v___x_6369_ = v_reuseFailAlloc_6419_;
goto v_reusejp_6368_;
}
v_reusejp_6368_:
{
lean_object* v___x_6370_; 
lean_inc_ref(v___y_6343_);
lean_inc(v___y_6342_);
lean_inc(v___y_6341_);
lean_inc(v___y_6340_);
lean_inc_ref(v___y_6339_);
v___x_6370_ = lean_apply_7(v_extraDepTrace_6332_, v___y_6339_, v___y_6340_, v___y_6341_, v___y_6342_, v___y_6343_, v___x_6369_, lean_box(0));
if (lean_obj_tag(v___x_6370_) == 0)
{
lean_object* v_a_6371_; lean_object* v_a_6372_; lean_object* v_log_6373_; uint8_t v_action_6374_; uint8_t v_wantsRebuild_6375_; lean_object* v_trace_6376_; lean_object* v_buildTime_6377_; lean_object* v___x_6379_; uint8_t v_isShared_6380_; uint8_t v_isSharedCheck_6409_; 
v_a_6371_ = lean_ctor_get(v___x_6370_, 1);
lean_inc(v_a_6371_);
v_a_6372_ = lean_ctor_get(v___x_6370_, 0);
lean_inc(v_a_6372_);
lean_dec_ref(v___x_6370_);
v_log_6373_ = lean_ctor_get(v_a_6371_, 0);
v_action_6374_ = lean_ctor_get_uint8(v_a_6371_, sizeof(void*)*3);
v_wantsRebuild_6375_ = lean_ctor_get_uint8(v_a_6371_, sizeof(void*)*3 + 1);
v_trace_6376_ = lean_ctor_get(v_a_6371_, 1);
v_buildTime_6377_ = lean_ctor_get(v_a_6371_, 2);
v_isSharedCheck_6409_ = !lean_is_exclusive(v_a_6371_);
if (v_isSharedCheck_6409_ == 0)
{
v___x_6379_ = v_a_6371_;
v_isShared_6380_ = v_isSharedCheck_6409_;
goto v_resetjp_6378_;
}
else
{
lean_inc(v_buildTime_6377_);
lean_inc(v_trace_6376_);
lean_inc(v_log_6373_);
lean_dec(v_a_6371_);
v___x_6379_ = lean_box(0);
v_isShared_6380_ = v_isSharedCheck_6409_;
goto v_resetjp_6378_;
}
v_resetjp_6378_:
{
lean_object* v___x_6381_; lean_object* v___x_6383_; 
v___x_6381_ = l_Lake_BuildTrace_mix(v_trace_6376_, v_a_6372_);
if (v_isShared_6380_ == 0)
{
lean_ctor_set(v___x_6379_, 1, v___x_6381_);
v___x_6383_ = v___x_6379_;
goto v_reusejp_6382_;
}
else
{
lean_object* v_reuseFailAlloc_6408_; 
v_reuseFailAlloc_6408_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6408_, 0, v_log_6373_);
lean_ctor_set(v_reuseFailAlloc_6408_, 1, v___x_6381_);
lean_ctor_set(v_reuseFailAlloc_6408_, 2, v_buildTime_6377_);
lean_ctor_set_uint8(v_reuseFailAlloc_6408_, sizeof(void*)*3, v_action_6374_);
lean_ctor_set_uint8(v_reuseFailAlloc_6408_, sizeof(void*)*3 + 1, v_wantsRebuild_6375_);
v___x_6383_ = v_reuseFailAlloc_6408_;
goto v_reusejp_6382_;
}
v_reusejp_6382_:
{
lean_object* v___x_6384_; lean_object* v___f_6385_; uint8_t v___x_6386_; lean_object* v___x_6387_; lean_object* v___x_6388_; 
v___x_6384_ = l_Array_append___redArg(v_weakArgs_6333_, v_traceArgs_6330_);
lean_dec_ref(v_traceArgs_6330_);
lean_inc_ref(v_oFile_6334_);
v___f_6385_ = lean_alloc_closure((void*)(l_Lake_buildO___lam__1___boxed), 11, 4);
lean_closure_set(v___f_6385_, 0, v_oFile_6334_);
lean_closure_set(v___f_6385_, 1, v_srcFile_6338_);
lean_closure_set(v___f_6385_, 2, v___x_6384_);
lean_closure_set(v___f_6385_, 3, v_compiler_6335_);
v___x_6386_ = 0;
v___x_6387_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
v___x_6388_ = l_Lake_buildArtifactUnlessUpToDate(v_oFile_6334_, v___f_6385_, v___x_6386_, v___x_6387_, v___x_6386_, v___x_6386_, v___x_6386_, v___y_6339_, v___y_6340_, v___y_6341_, v___y_6342_, v___y_6343_, v___x_6383_);
if (lean_obj_tag(v___x_6388_) == 0)
{
lean_object* v_a_6389_; lean_object* v_a_6390_; lean_object* v___x_6392_; uint8_t v_isShared_6393_; uint8_t v_isSharedCheck_6398_; 
v_a_6389_ = lean_ctor_get(v___x_6388_, 0);
v_a_6390_ = lean_ctor_get(v___x_6388_, 1);
v_isSharedCheck_6398_ = !lean_is_exclusive(v___x_6388_);
if (v_isSharedCheck_6398_ == 0)
{
v___x_6392_ = v___x_6388_;
v_isShared_6393_ = v_isSharedCheck_6398_;
goto v_resetjp_6391_;
}
else
{
lean_inc(v_a_6390_);
lean_inc(v_a_6389_);
lean_dec(v___x_6388_);
v___x_6392_ = lean_box(0);
v_isShared_6393_ = v_isSharedCheck_6398_;
goto v_resetjp_6391_;
}
v_resetjp_6391_:
{
lean_object* v_path_6394_; lean_object* v___x_6396_; 
v_path_6394_ = lean_ctor_get(v_a_6389_, 1);
lean_inc_ref(v_path_6394_);
lean_dec(v_a_6389_);
if (v_isShared_6393_ == 0)
{
lean_ctor_set(v___x_6392_, 0, v_path_6394_);
v___x_6396_ = v___x_6392_;
goto v_reusejp_6395_;
}
else
{
lean_object* v_reuseFailAlloc_6397_; 
v_reuseFailAlloc_6397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6397_, 0, v_path_6394_);
lean_ctor_set(v_reuseFailAlloc_6397_, 1, v_a_6390_);
v___x_6396_ = v_reuseFailAlloc_6397_;
goto v_reusejp_6395_;
}
v_reusejp_6395_:
{
return v___x_6396_;
}
}
}
else
{
lean_object* v_a_6399_; lean_object* v_a_6400_; lean_object* v___x_6402_; uint8_t v_isShared_6403_; uint8_t v_isSharedCheck_6407_; 
v_a_6399_ = lean_ctor_get(v___x_6388_, 0);
v_a_6400_ = lean_ctor_get(v___x_6388_, 1);
v_isSharedCheck_6407_ = !lean_is_exclusive(v___x_6388_);
if (v_isSharedCheck_6407_ == 0)
{
v___x_6402_ = v___x_6388_;
v_isShared_6403_ = v_isSharedCheck_6407_;
goto v_resetjp_6401_;
}
else
{
lean_inc(v_a_6400_);
lean_inc(v_a_6399_);
lean_dec(v___x_6388_);
v___x_6402_ = lean_box(0);
v_isShared_6403_ = v_isSharedCheck_6407_;
goto v_resetjp_6401_;
}
v_resetjp_6401_:
{
lean_object* v___x_6405_; 
if (v_isShared_6403_ == 0)
{
v___x_6405_ = v___x_6402_;
goto v_reusejp_6404_;
}
else
{
lean_object* v_reuseFailAlloc_6406_; 
v_reuseFailAlloc_6406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6406_, 0, v_a_6399_);
lean_ctor_set(v_reuseFailAlloc_6406_, 1, v_a_6400_);
v___x_6405_ = v_reuseFailAlloc_6406_;
goto v_reusejp_6404_;
}
v_reusejp_6404_:
{
return v___x_6405_;
}
}
}
}
}
}
else
{
lean_object* v_a_6410_; lean_object* v_a_6411_; lean_object* v___x_6413_; uint8_t v_isShared_6414_; uint8_t v_isSharedCheck_6418_; 
lean_dec_ref(v___y_6339_);
lean_dec_ref(v_srcFile_6338_);
lean_dec_ref(v_compiler_6335_);
lean_dec_ref(v_oFile_6334_);
lean_dec_ref(v_weakArgs_6333_);
lean_dec_ref(v_traceArgs_6330_);
v_a_6410_ = lean_ctor_get(v___x_6370_, 0);
v_a_6411_ = lean_ctor_get(v___x_6370_, 1);
v_isSharedCheck_6418_ = !lean_is_exclusive(v___x_6370_);
if (v_isSharedCheck_6418_ == 0)
{
v___x_6413_ = v___x_6370_;
v_isShared_6414_ = v_isSharedCheck_6418_;
goto v_resetjp_6412_;
}
else
{
lean_inc(v_a_6411_);
lean_inc(v_a_6410_);
lean_dec(v___x_6370_);
v___x_6413_ = lean_box(0);
v_isShared_6414_ = v_isSharedCheck_6418_;
goto v_resetjp_6412_;
}
v_resetjp_6412_:
{
lean_object* v___x_6416_; 
if (v_isShared_6414_ == 0)
{
v___x_6416_ = v___x_6413_;
goto v_reusejp_6415_;
}
else
{
lean_object* v_reuseFailAlloc_6417_; 
v_reuseFailAlloc_6417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6417_, 0, v_a_6410_);
lean_ctor_set(v_reuseFailAlloc_6417_, 1, v_a_6411_);
v___x_6416_ = v_reuseFailAlloc_6417_;
goto v_reusejp_6415_;
}
v_reusejp_6415_:
{
return v___x_6416_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed(lean_object* v_traceArgs_6436_, lean_object* v___f_6437_, lean_object* v_extraDepTrace_6438_, lean_object* v_weakArgs_6439_, lean_object* v_oFile_6440_, lean_object* v_compiler_6441_, lean_object* v___x_6442_, lean_object* v___f_6443_, lean_object* v_srcFile_6444_, lean_object* v___y_6445_, lean_object* v___y_6446_, lean_object* v___y_6447_, lean_object* v___y_6448_, lean_object* v___y_6449_, lean_object* v___y_6450_, lean_object* v___y_6451_){
_start:
{
lean_object* v_res_6452_; 
v_res_6452_ = l_Lake_buildO___lam__2(v_traceArgs_6436_, v___f_6437_, v_extraDepTrace_6438_, v_weakArgs_6439_, v_oFile_6440_, v_compiler_6441_, v___x_6442_, v___f_6443_, v_srcFile_6444_, v___y_6445_, v___y_6446_, v___y_6447_, v___y_6448_, v___y_6449_, v___y_6450_);
lean_dec_ref(v___y_6449_);
lean_dec(v___y_6448_);
lean_dec(v___y_6447_);
lean_dec(v___y_6446_);
return v_res_6452_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object* v_oFile_6455_, lean_object* v_srcJob_6456_, lean_object* v_weakArgs_6457_, lean_object* v_traceArgs_6458_, lean_object* v_compiler_6459_, lean_object* v_extraDepTrace_6460_, lean_object* v_a_6461_, lean_object* v_a_6462_, lean_object* v_a_6463_, lean_object* v_a_6464_, lean_object* v_a_6465_, lean_object* v_a_6466_){
_start:
{
lean_object* v___f_6468_; lean_object* v___x_6469_; lean_object* v___f_6470_; lean_object* v___x_6471_; lean_object* v___f_6472_; lean_object* v___x_6473_; uint8_t v___x_6474_; lean_object* v___x_6475_; 
v___f_6468_ = ((lean_object*)(l_Lake_buildO___closed__0));
v___x_6469_ = l_Lake_instDataKindFilePath;
v___f_6470_ = ((lean_object*)(l_Lake_buildO___closed__1));
v___x_6471_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__9));
v___f_6472_ = lean_alloc_closure((void*)(l_Lake_buildO___lam__2___boxed), 16, 8);
lean_closure_set(v___f_6472_, 0, v_traceArgs_6458_);
lean_closure_set(v___f_6472_, 1, v___f_6470_);
lean_closure_set(v___f_6472_, 2, v_extraDepTrace_6460_);
lean_closure_set(v___f_6472_, 3, v_weakArgs_6457_);
lean_closure_set(v___f_6472_, 4, v_oFile_6455_);
lean_closure_set(v___f_6472_, 5, v_compiler_6459_);
lean_closure_set(v___f_6472_, 6, v___x_6471_);
lean_closure_set(v___f_6472_, 7, v___f_6468_);
v___x_6473_ = lean_unsigned_to_nat(0u);
v___x_6474_ = 0;
v___x_6475_ = l_Lake_Job_mapM___redArg(v___x_6469_, v_srcJob_6456_, v___f_6472_, v___x_6473_, v___x_6474_, v_a_6461_, v_a_6462_, v_a_6463_, v_a_6464_, v_a_6465_, v_a_6466_);
return v___x_6475_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___boxed(lean_object* v_oFile_6476_, lean_object* v_srcJob_6477_, lean_object* v_weakArgs_6478_, lean_object* v_traceArgs_6479_, lean_object* v_compiler_6480_, lean_object* v_extraDepTrace_6481_, lean_object* v_a_6482_, lean_object* v_a_6483_, lean_object* v_a_6484_, lean_object* v_a_6485_, lean_object* v_a_6486_, lean_object* v_a_6487_, lean_object* v_a_6488_){
_start:
{
lean_object* v_res_6489_; 
v_res_6489_ = l_Lake_buildO(v_oFile_6476_, v_srcJob_6477_, v_weakArgs_6478_, v_traceArgs_6479_, v_compiler_6480_, v_extraDepTrace_6481_, v_a_6482_, v_a_6483_, v_a_6484_, v_a_6485_, v_a_6486_, v_a_6487_);
lean_dec_ref(v_a_6487_);
lean_dec_ref(v_a_6486_);
lean_dec(v_a_6485_);
lean_dec(v_a_6484_);
lean_dec(v_a_6483_);
return v_res_6489_;
}
}
static lean_object* _init_l_Lake_buildLeanO___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6491_; lean_object* v___x_6492_; lean_object* v___x_6493_; lean_object* v___x_6494_; 
v___x_6491_ = ((lean_object*)(l_Lake_buildLeanO___lam__0___closed__0));
v___x_6492_ = lean_unsigned_to_nat(2u);
v___x_6493_ = lean_mk_empty_array_with_capacity(v___x_6492_);
v___x_6494_ = lean_array_push(v___x_6493_, v___x_6491_);
return v___x_6494_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0(lean_object* v_weakArgs_6495_, lean_object* v_traceArgs_6496_, lean_object* v_oFile_6497_, lean_object* v_srcFile_6498_, lean_object* v_leanIncludeDir_x3f_6499_, lean_object* v___y_6500_, lean_object* v___y_6501_, lean_object* v___y_6502_, lean_object* v___y_6503_, lean_object* v___y_6504_, lean_object* v___y_6505_){
_start:
{
lean_object* v_toContext_6507_; lean_object* v_lakeEnv_6508_; lean_object* v_log_6509_; uint8_t v_action_6510_; uint8_t v_wantsRebuild_6511_; lean_object* v_trace_6512_; lean_object* v_buildTime_6513_; lean_object* v___x_6515_; uint8_t v_isShared_6516_; uint8_t v_isSharedCheck_6554_; 
v_toContext_6507_ = lean_ctor_get(v___y_6504_, 1);
v_lakeEnv_6508_ = lean_ctor_get(v_toContext_6507_, 1);
v_log_6509_ = lean_ctor_get(v___y_6505_, 0);
v_action_6510_ = lean_ctor_get_uint8(v___y_6505_, sizeof(void*)*3);
v_wantsRebuild_6511_ = lean_ctor_get_uint8(v___y_6505_, sizeof(void*)*3 + 1);
v_trace_6512_ = lean_ctor_get(v___y_6505_, 1);
v_buildTime_6513_ = lean_ctor_get(v___y_6505_, 2);
v_isSharedCheck_6554_ = !lean_is_exclusive(v___y_6505_);
if (v_isSharedCheck_6554_ == 0)
{
v___x_6515_ = v___y_6505_;
v_isShared_6516_ = v_isSharedCheck_6554_;
goto v_resetjp_6514_;
}
else
{
lean_inc(v_buildTime_6513_);
lean_inc(v_trace_6512_);
lean_inc(v_log_6509_);
lean_dec(v___y_6505_);
v___x_6515_ = lean_box(0);
v_isShared_6516_ = v_isSharedCheck_6554_;
goto v_resetjp_6514_;
}
v_resetjp_6514_:
{
lean_object* v_lean_6517_; lean_object* v___y_6519_; 
v_lean_6517_ = lean_ctor_get(v_lakeEnv_6508_, 1);
if (lean_obj_tag(v_leanIncludeDir_x3f_6499_) == 0)
{
lean_object* v_includeDir_6552_; 
v_includeDir_6552_ = lean_ctor_get(v_lean_6517_, 4);
lean_inc_ref(v_includeDir_6552_);
v___y_6519_ = v_includeDir_6552_;
goto v___jp_6518_;
}
else
{
lean_object* v_val_6553_; 
v_val_6553_ = lean_ctor_get(v_leanIncludeDir_x3f_6499_, 0);
lean_inc(v_val_6553_);
lean_dec_ref(v_leanIncludeDir_x3f_6499_);
v___y_6519_ = v_val_6553_;
goto v___jp_6518_;
}
v___jp_6518_:
{
lean_object* v_cc_6520_; lean_object* v_ccFlags_6521_; lean_object* v___x_6522_; lean_object* v___x_6523_; lean_object* v___x_6524_; lean_object* v___x_6525_; lean_object* v___x_6526_; lean_object* v___x_6527_; 
v_cc_6520_ = lean_ctor_get(v_lean_6517_, 14);
v_ccFlags_6521_ = lean_ctor_get(v_lean_6517_, 18);
v___x_6522_ = lean_obj_once(&l_Lake_buildLeanO___lam__0___closed__1, &l_Lake_buildLeanO___lam__0___closed__1_once, _init_l_Lake_buildLeanO___lam__0___closed__1);
v___x_6523_ = lean_array_push(v___x_6522_, v___y_6519_);
v___x_6524_ = l_Array_append___redArg(v___x_6523_, v_ccFlags_6521_);
v___x_6525_ = l_Array_append___redArg(v___x_6524_, v_weakArgs_6495_);
v___x_6526_ = l_Array_append___redArg(v___x_6525_, v_traceArgs_6496_);
lean_inc_ref(v_cc_6520_);
v___x_6527_ = l_Lake_compileO(v_oFile_6497_, v_srcFile_6498_, v___x_6526_, v_cc_6520_, v_log_6509_);
lean_dec_ref(v___x_6526_);
if (lean_obj_tag(v___x_6527_) == 0)
{
lean_object* v_a_6528_; lean_object* v_a_6529_; lean_object* v___x_6531_; uint8_t v_isShared_6532_; uint8_t v_isSharedCheck_6539_; 
v_a_6528_ = lean_ctor_get(v___x_6527_, 0);
v_a_6529_ = lean_ctor_get(v___x_6527_, 1);
v_isSharedCheck_6539_ = !lean_is_exclusive(v___x_6527_);
if (v_isSharedCheck_6539_ == 0)
{
v___x_6531_ = v___x_6527_;
v_isShared_6532_ = v_isSharedCheck_6539_;
goto v_resetjp_6530_;
}
else
{
lean_inc(v_a_6529_);
lean_inc(v_a_6528_);
lean_dec(v___x_6527_);
v___x_6531_ = lean_box(0);
v_isShared_6532_ = v_isSharedCheck_6539_;
goto v_resetjp_6530_;
}
v_resetjp_6530_:
{
lean_object* v___x_6534_; 
if (v_isShared_6516_ == 0)
{
lean_ctor_set(v___x_6515_, 0, v_a_6529_);
v___x_6534_ = v___x_6515_;
goto v_reusejp_6533_;
}
else
{
lean_object* v_reuseFailAlloc_6538_; 
v_reuseFailAlloc_6538_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6538_, 0, v_a_6529_);
lean_ctor_set(v_reuseFailAlloc_6538_, 1, v_trace_6512_);
lean_ctor_set(v_reuseFailAlloc_6538_, 2, v_buildTime_6513_);
lean_ctor_set_uint8(v_reuseFailAlloc_6538_, sizeof(void*)*3, v_action_6510_);
lean_ctor_set_uint8(v_reuseFailAlloc_6538_, sizeof(void*)*3 + 1, v_wantsRebuild_6511_);
v___x_6534_ = v_reuseFailAlloc_6538_;
goto v_reusejp_6533_;
}
v_reusejp_6533_:
{
lean_object* v___x_6536_; 
if (v_isShared_6532_ == 0)
{
lean_ctor_set(v___x_6531_, 1, v___x_6534_);
v___x_6536_ = v___x_6531_;
goto v_reusejp_6535_;
}
else
{
lean_object* v_reuseFailAlloc_6537_; 
v_reuseFailAlloc_6537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6537_, 0, v_a_6528_);
lean_ctor_set(v_reuseFailAlloc_6537_, 1, v___x_6534_);
v___x_6536_ = v_reuseFailAlloc_6537_;
goto v_reusejp_6535_;
}
v_reusejp_6535_:
{
return v___x_6536_;
}
}
}
}
else
{
lean_object* v_a_6540_; lean_object* v_a_6541_; lean_object* v___x_6543_; uint8_t v_isShared_6544_; uint8_t v_isSharedCheck_6551_; 
v_a_6540_ = lean_ctor_get(v___x_6527_, 0);
v_a_6541_ = lean_ctor_get(v___x_6527_, 1);
v_isSharedCheck_6551_ = !lean_is_exclusive(v___x_6527_);
if (v_isSharedCheck_6551_ == 0)
{
v___x_6543_ = v___x_6527_;
v_isShared_6544_ = v_isSharedCheck_6551_;
goto v_resetjp_6542_;
}
else
{
lean_inc(v_a_6541_);
lean_inc(v_a_6540_);
lean_dec(v___x_6527_);
v___x_6543_ = lean_box(0);
v_isShared_6544_ = v_isSharedCheck_6551_;
goto v_resetjp_6542_;
}
v_resetjp_6542_:
{
lean_object* v___x_6546_; 
if (v_isShared_6516_ == 0)
{
lean_ctor_set(v___x_6515_, 0, v_a_6541_);
v___x_6546_ = v___x_6515_;
goto v_reusejp_6545_;
}
else
{
lean_object* v_reuseFailAlloc_6550_; 
v_reuseFailAlloc_6550_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6550_, 0, v_a_6541_);
lean_ctor_set(v_reuseFailAlloc_6550_, 1, v_trace_6512_);
lean_ctor_set(v_reuseFailAlloc_6550_, 2, v_buildTime_6513_);
lean_ctor_set_uint8(v_reuseFailAlloc_6550_, sizeof(void*)*3, v_action_6510_);
lean_ctor_set_uint8(v_reuseFailAlloc_6550_, sizeof(void*)*3 + 1, v_wantsRebuild_6511_);
v___x_6546_ = v_reuseFailAlloc_6550_;
goto v_reusejp_6545_;
}
v_reusejp_6545_:
{
lean_object* v___x_6548_; 
if (v_isShared_6544_ == 0)
{
lean_ctor_set(v___x_6543_, 1, v___x_6546_);
v___x_6548_ = v___x_6543_;
goto v_reusejp_6547_;
}
else
{
lean_object* v_reuseFailAlloc_6549_; 
v_reuseFailAlloc_6549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6549_, 0, v_a_6540_);
lean_ctor_set(v_reuseFailAlloc_6549_, 1, v___x_6546_);
v___x_6548_ = v_reuseFailAlloc_6549_;
goto v_reusejp_6547_;
}
v_reusejp_6547_:
{
return v___x_6548_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0___boxed(lean_object* v_weakArgs_6555_, lean_object* v_traceArgs_6556_, lean_object* v_oFile_6557_, lean_object* v_srcFile_6558_, lean_object* v_leanIncludeDir_x3f_6559_, lean_object* v___y_6560_, lean_object* v___y_6561_, lean_object* v___y_6562_, lean_object* v___y_6563_, lean_object* v___y_6564_, lean_object* v___y_6565_, lean_object* v___y_6566_){
_start:
{
lean_object* v_res_6567_; 
v_res_6567_ = l_Lake_buildLeanO___lam__0(v_weakArgs_6555_, v_traceArgs_6556_, v_oFile_6557_, v_srcFile_6558_, v_leanIncludeDir_x3f_6559_, v___y_6560_, v___y_6561_, v___y_6562_, v___y_6563_, v___y_6564_, v___y_6565_);
lean_dec_ref(v___y_6564_);
lean_dec(v___y_6563_);
lean_dec(v___y_6562_);
lean_dec(v___y_6561_);
lean_dec_ref(v___y_6560_);
lean_dec_ref(v_traceArgs_6556_);
lean_dec_ref(v_weakArgs_6555_);
return v_res_6567_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(lean_object* v_as_6568_, size_t v_i_6569_, size_t v_stop_6570_, uint64_t v_b_6571_){
_start:
{
uint8_t v___x_6572_; 
v___x_6572_ = lean_usize_dec_eq(v_i_6569_, v_stop_6570_);
if (v___x_6572_ == 0)
{
lean_object* v___x_6573_; uint64_t v___x_6574_; uint64_t v___x_6575_; uint64_t v___x_6576_; uint64_t v___x_6577_; size_t v___x_6578_; size_t v___x_6579_; 
v___x_6573_ = lean_array_uget_borrowed(v_as_6568_, v_i_6569_);
v___x_6574_ = l_Lake_Hash_nil;
v___x_6575_ = lean_string_hash(v___x_6573_);
v___x_6576_ = lean_uint64_mix_hash(v___x_6574_, v___x_6575_);
v___x_6577_ = lean_uint64_mix_hash(v_b_6571_, v___x_6576_);
v___x_6578_ = ((size_t)1ULL);
v___x_6579_ = lean_usize_add(v_i_6569_, v___x_6578_);
v_i_6569_ = v___x_6579_;
v_b_6571_ = v___x_6577_;
goto _start;
}
else
{
return v_b_6571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1___boxed(lean_object* v_as_6581_, lean_object* v_i_6582_, lean_object* v_stop_6583_, lean_object* v_b_6584_){
_start:
{
size_t v_i_boxed_6585_; size_t v_stop_boxed_6586_; uint64_t v_b_boxed_6587_; uint64_t v_res_6588_; lean_object* v_r_6589_; 
v_i_boxed_6585_ = lean_unbox_usize(v_i_6582_);
lean_dec(v_i_6582_);
v_stop_boxed_6586_ = lean_unbox_usize(v_stop_6583_);
lean_dec(v_stop_6583_);
v_b_boxed_6587_ = lean_unbox_uint64(v_b_6584_);
lean_dec_ref(v_b_6584_);
v_res_6588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_as_6581_, v_i_boxed_6585_, v_stop_boxed_6586_, v_b_boxed_6587_);
lean_dec_ref(v_as_6581_);
v_r_6589_ = lean_box_uint64(v_res_6588_);
return v_r_6589_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(lean_object* v_x_6591_, lean_object* v_x_6592_){
_start:
{
if (lean_obj_tag(v_x_6592_) == 0)
{
return v_x_6591_;
}
else
{
lean_object* v_head_6593_; lean_object* v_tail_6594_; lean_object* v___x_6595_; lean_object* v___x_6596_; lean_object* v___x_6597_; 
v_head_6593_ = lean_ctor_get(v_x_6592_, 0);
v_tail_6594_ = lean_ctor_get(v_x_6592_, 1);
v___x_6595_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0));
v___x_6596_ = lean_string_append(v_x_6591_, v___x_6595_);
v___x_6597_ = lean_string_append(v___x_6596_, v_head_6593_);
v_x_6591_ = v___x_6597_;
v_x_6592_ = v_tail_6594_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___boxed(lean_object* v_x_6599_, lean_object* v_x_6600_){
_start:
{
lean_object* v_res_6601_; 
v_res_6601_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(v_x_6599_, v_x_6600_);
lean_dec(v_x_6600_);
return v_res_6601_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0(lean_object* v_x_6605_){
_start:
{
if (lean_obj_tag(v_x_6605_) == 0)
{
lean_object* v___x_6606_; 
v___x_6606_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0));
return v___x_6606_;
}
else
{
lean_object* v_tail_6607_; 
v_tail_6607_ = lean_ctor_get(v_x_6605_, 1);
if (lean_obj_tag(v_tail_6607_) == 0)
{
lean_object* v_head_6608_; lean_object* v___x_6609_; lean_object* v___x_6610_; lean_object* v___x_6611_; lean_object* v___x_6612_; 
v_head_6608_ = lean_ctor_get(v_x_6605_, 0);
v___x_6609_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1));
v___x_6610_ = lean_string_append(v___x_6609_, v_head_6608_);
v___x_6611_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2));
v___x_6612_ = lean_string_append(v___x_6610_, v___x_6611_);
return v___x_6612_;
}
else
{
lean_object* v_head_6613_; lean_object* v___x_6614_; lean_object* v___x_6615_; lean_object* v___x_6616_; uint32_t v___x_6617_; lean_object* v___x_6618_; 
v_head_6613_ = lean_ctor_get(v_x_6605_, 0);
v___x_6614_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1));
v___x_6615_ = lean_string_append(v___x_6614_, v_head_6613_);
v___x_6616_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(v___x_6615_, v_tail_6607_);
v___x_6617_ = 93;
v___x_6618_ = lean_string_push(v___x_6616_, v___x_6617_);
return v___x_6618_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___boxed(lean_object* v_x_6619_){
_start:
{
lean_object* v_res_6620_; 
v_res_6620_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v_x_6619_);
lean_dec(v_x_6619_);
return v_res_6620_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1(lean_object* v_weakArgs_6621_, lean_object* v_traceArgs_6622_, lean_object* v_oFile_6623_, lean_object* v_leanIncludeDir_x3f_6624_, lean_object* v_srcFile_6625_, lean_object* v___y_6626_, lean_object* v___y_6627_, lean_object* v___y_6628_, lean_object* v___y_6629_, lean_object* v___y_6630_, lean_object* v___y_6631_){
_start:
{
lean_object* v_log_6633_; uint8_t v_action_6634_; uint8_t v_wantsRebuild_6635_; lean_object* v_trace_6636_; lean_object* v_buildTime_6637_; lean_object* v___x_6639_; uint8_t v_isShared_6640_; uint8_t v_isSharedCheck_6694_; 
v_log_6633_ = lean_ctor_get(v___y_6631_, 0);
v_action_6634_ = lean_ctor_get_uint8(v___y_6631_, sizeof(void*)*3);
v_wantsRebuild_6635_ = lean_ctor_get_uint8(v___y_6631_, sizeof(void*)*3 + 1);
v_trace_6636_ = lean_ctor_get(v___y_6631_, 1);
v_buildTime_6637_ = lean_ctor_get(v___y_6631_, 2);
v_isSharedCheck_6694_ = !lean_is_exclusive(v___y_6631_);
if (v_isSharedCheck_6694_ == 0)
{
v___x_6639_ = v___y_6631_;
v_isShared_6640_ = v_isSharedCheck_6694_;
goto v_resetjp_6638_;
}
else
{
lean_inc(v_buildTime_6637_);
lean_inc(v_trace_6636_);
lean_inc(v_log_6633_);
lean_dec(v___y_6631_);
v___x_6639_ = lean_box(0);
v_isShared_6640_ = v_isSharedCheck_6694_;
goto v_resetjp_6638_;
}
v_resetjp_6638_:
{
lean_object* v_leanTrace_6641_; lean_object* v___f_6642_; lean_object* v___x_6643_; uint64_t v___y_6645_; uint64_t v___x_6683_; lean_object* v___x_6684_; lean_object* v___x_6685_; uint8_t v___x_6686_; 
v_leanTrace_6641_ = lean_ctor_get(v___y_6630_, 2);
lean_inc_ref(v_oFile_6623_);
lean_inc_ref(v_traceArgs_6622_);
v___f_6642_ = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__0___boxed), 12, 5);
lean_closure_set(v___f_6642_, 0, v_weakArgs_6621_);
lean_closure_set(v___f_6642_, 1, v_traceArgs_6622_);
lean_closure_set(v___f_6642_, 2, v_oFile_6623_);
lean_closure_set(v___f_6642_, 3, v_srcFile_6625_);
lean_closure_set(v___f_6642_, 4, v_leanIncludeDir_x3f_6624_);
lean_inc_ref(v_leanTrace_6641_);
v___x_6643_ = l_Lake_BuildTrace_mix(v_trace_6636_, v_leanTrace_6641_);
v___x_6683_ = l_Lake_Hash_nil;
v___x_6684_ = lean_unsigned_to_nat(0u);
v___x_6685_ = lean_array_get_size(v_traceArgs_6622_);
v___x_6686_ = lean_nat_dec_lt(v___x_6684_, v___x_6685_);
if (v___x_6686_ == 0)
{
v___y_6645_ = v___x_6683_;
goto v___jp_6644_;
}
else
{
uint8_t v___x_6687_; 
v___x_6687_ = lean_nat_dec_le(v___x_6685_, v___x_6685_);
if (v___x_6687_ == 0)
{
if (v___x_6686_ == 0)
{
v___y_6645_ = v___x_6683_;
goto v___jp_6644_;
}
else
{
size_t v___x_6688_; size_t v___x_6689_; uint64_t v___x_6690_; 
v___x_6688_ = ((size_t)0ULL);
v___x_6689_ = lean_usize_of_nat(v___x_6685_);
v___x_6690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_6622_, v___x_6688_, v___x_6689_, v___x_6683_);
v___y_6645_ = v___x_6690_;
goto v___jp_6644_;
}
}
else
{
size_t v___x_6691_; size_t v___x_6692_; uint64_t v___x_6693_; 
v___x_6691_ = ((size_t)0ULL);
v___x_6692_ = lean_usize_of_nat(v___x_6685_);
v___x_6693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_6622_, v___x_6691_, v___x_6692_, v___x_6683_);
v___y_6645_ = v___x_6693_;
goto v___jp_6644_;
}
}
v___jp_6644_:
{
lean_object* v___x_6646_; lean_object* v___x_6647_; lean_object* v___x_6648_; lean_object* v___x_6649_; lean_object* v___x_6650_; lean_object* v___x_6651_; lean_object* v___x_6652_; lean_object* v___x_6653_; lean_object* v___x_6654_; lean_object* v___x_6655_; lean_object* v___x_6656_; lean_object* v___x_6657_; lean_object* v___x_6659_; 
v___x_6646_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_6647_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_6648_ = lean_array_to_list(v_traceArgs_6622_);
v___x_6649_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_6648_);
lean_dec(v___x_6648_);
v___x_6650_ = lean_string_append(v___x_6647_, v___x_6649_);
lean_dec_ref(v___x_6649_);
v___x_6651_ = lean_string_append(v___x_6646_, v___x_6650_);
lean_dec_ref(v___x_6650_);
v___x_6652_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_6653_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_6654_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6654_, 0, v___x_6651_);
lean_ctor_set(v___x_6654_, 1, v___x_6652_);
lean_ctor_set(v___x_6654_, 2, v___x_6653_);
lean_ctor_set_uint64(v___x_6654_, sizeof(void*)*3, v___y_6645_);
v___x_6655_ = l_Lake_BuildTrace_mix(v___x_6643_, v___x_6654_);
v___x_6656_ = l_Lake_platformTrace;
v___x_6657_ = l_Lake_BuildTrace_mix(v___x_6655_, v___x_6656_);
if (v_isShared_6640_ == 0)
{
lean_ctor_set(v___x_6639_, 1, v___x_6657_);
v___x_6659_ = v___x_6639_;
goto v_reusejp_6658_;
}
else
{
lean_object* v_reuseFailAlloc_6682_; 
v_reuseFailAlloc_6682_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6682_, 0, v_log_6633_);
lean_ctor_set(v_reuseFailAlloc_6682_, 1, v___x_6657_);
lean_ctor_set(v_reuseFailAlloc_6682_, 2, v_buildTime_6637_);
lean_ctor_set_uint8(v_reuseFailAlloc_6682_, sizeof(void*)*3, v_action_6634_);
lean_ctor_set_uint8(v_reuseFailAlloc_6682_, sizeof(void*)*3 + 1, v_wantsRebuild_6635_);
v___x_6659_ = v_reuseFailAlloc_6682_;
goto v_reusejp_6658_;
}
v_reusejp_6658_:
{
uint8_t v___x_6660_; lean_object* v___x_6661_; lean_object* v___x_6662_; 
v___x_6660_ = 0;
v___x_6661_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
v___x_6662_ = l_Lake_buildArtifactUnlessUpToDate(v_oFile_6623_, v___f_6642_, v___x_6660_, v___x_6661_, v___x_6660_, v___x_6660_, v___x_6660_, v___y_6626_, v___y_6627_, v___y_6628_, v___y_6629_, v___y_6630_, v___x_6659_);
if (lean_obj_tag(v___x_6662_) == 0)
{
lean_object* v_a_6663_; lean_object* v_a_6664_; lean_object* v___x_6666_; uint8_t v_isShared_6667_; uint8_t v_isSharedCheck_6672_; 
v_a_6663_ = lean_ctor_get(v___x_6662_, 0);
v_a_6664_ = lean_ctor_get(v___x_6662_, 1);
v_isSharedCheck_6672_ = !lean_is_exclusive(v___x_6662_);
if (v_isSharedCheck_6672_ == 0)
{
v___x_6666_ = v___x_6662_;
v_isShared_6667_ = v_isSharedCheck_6672_;
goto v_resetjp_6665_;
}
else
{
lean_inc(v_a_6664_);
lean_inc(v_a_6663_);
lean_dec(v___x_6662_);
v___x_6666_ = lean_box(0);
v_isShared_6667_ = v_isSharedCheck_6672_;
goto v_resetjp_6665_;
}
v_resetjp_6665_:
{
lean_object* v_path_6668_; lean_object* v___x_6670_; 
v_path_6668_ = lean_ctor_get(v_a_6663_, 1);
lean_inc_ref(v_path_6668_);
lean_dec(v_a_6663_);
if (v_isShared_6667_ == 0)
{
lean_ctor_set(v___x_6666_, 0, v_path_6668_);
v___x_6670_ = v___x_6666_;
goto v_reusejp_6669_;
}
else
{
lean_object* v_reuseFailAlloc_6671_; 
v_reuseFailAlloc_6671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6671_, 0, v_path_6668_);
lean_ctor_set(v_reuseFailAlloc_6671_, 1, v_a_6664_);
v___x_6670_ = v_reuseFailAlloc_6671_;
goto v_reusejp_6669_;
}
v_reusejp_6669_:
{
return v___x_6670_;
}
}
}
else
{
lean_object* v_a_6673_; lean_object* v_a_6674_; lean_object* v___x_6676_; uint8_t v_isShared_6677_; uint8_t v_isSharedCheck_6681_; 
v_a_6673_ = lean_ctor_get(v___x_6662_, 0);
v_a_6674_ = lean_ctor_get(v___x_6662_, 1);
v_isSharedCheck_6681_ = !lean_is_exclusive(v___x_6662_);
if (v_isSharedCheck_6681_ == 0)
{
v___x_6676_ = v___x_6662_;
v_isShared_6677_ = v_isSharedCheck_6681_;
goto v_resetjp_6675_;
}
else
{
lean_inc(v_a_6674_);
lean_inc(v_a_6673_);
lean_dec(v___x_6662_);
v___x_6676_ = lean_box(0);
v_isShared_6677_ = v_isSharedCheck_6681_;
goto v_resetjp_6675_;
}
v_resetjp_6675_:
{
lean_object* v___x_6679_; 
if (v_isShared_6677_ == 0)
{
v___x_6679_ = v___x_6676_;
goto v_reusejp_6678_;
}
else
{
lean_object* v_reuseFailAlloc_6680_; 
v_reuseFailAlloc_6680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6680_, 0, v_a_6673_);
lean_ctor_set(v_reuseFailAlloc_6680_, 1, v_a_6674_);
v___x_6679_ = v_reuseFailAlloc_6680_;
goto v_reusejp_6678_;
}
v_reusejp_6678_:
{
return v___x_6679_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1___boxed(lean_object* v_weakArgs_6695_, lean_object* v_traceArgs_6696_, lean_object* v_oFile_6697_, lean_object* v_leanIncludeDir_x3f_6698_, lean_object* v_srcFile_6699_, lean_object* v___y_6700_, lean_object* v___y_6701_, lean_object* v___y_6702_, lean_object* v___y_6703_, lean_object* v___y_6704_, lean_object* v___y_6705_, lean_object* v___y_6706_){
_start:
{
lean_object* v_res_6707_; 
v_res_6707_ = l_Lake_buildLeanO___lam__1(v_weakArgs_6695_, v_traceArgs_6696_, v_oFile_6697_, v_leanIncludeDir_x3f_6698_, v_srcFile_6699_, v___y_6700_, v___y_6701_, v___y_6702_, v___y_6703_, v___y_6704_, v___y_6705_);
lean_dec_ref(v___y_6704_);
lean_dec(v___y_6703_);
lean_dec(v___y_6702_);
lean_dec(v___y_6701_);
return v_res_6707_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object* v_oFile_6708_, lean_object* v_srcJob_6709_, lean_object* v_weakArgs_6710_, lean_object* v_traceArgs_6711_, lean_object* v_leanIncludeDir_x3f_6712_, lean_object* v_a_6713_, lean_object* v_a_6714_, lean_object* v_a_6715_, lean_object* v_a_6716_, lean_object* v_a_6717_, lean_object* v_a_6718_){
_start:
{
lean_object* v___f_6720_; lean_object* v___x_6721_; lean_object* v___x_6722_; uint8_t v___x_6723_; lean_object* v___x_6724_; 
v___f_6720_ = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__1___boxed), 12, 4);
lean_closure_set(v___f_6720_, 0, v_weakArgs_6710_);
lean_closure_set(v___f_6720_, 1, v_traceArgs_6711_);
lean_closure_set(v___f_6720_, 2, v_oFile_6708_);
lean_closure_set(v___f_6720_, 3, v_leanIncludeDir_x3f_6712_);
v___x_6721_ = l_Lake_instDataKindFilePath;
v___x_6722_ = lean_unsigned_to_nat(0u);
v___x_6723_ = 0;
v___x_6724_ = l_Lake_Job_mapM___redArg(v___x_6721_, v_srcJob_6709_, v___f_6720_, v___x_6722_, v___x_6723_, v_a_6713_, v_a_6714_, v_a_6715_, v_a_6716_, v_a_6717_, v_a_6718_);
return v___x_6724_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___boxed(lean_object* v_oFile_6725_, lean_object* v_srcJob_6726_, lean_object* v_weakArgs_6727_, lean_object* v_traceArgs_6728_, lean_object* v_leanIncludeDir_x3f_6729_, lean_object* v_a_6730_, lean_object* v_a_6731_, lean_object* v_a_6732_, lean_object* v_a_6733_, lean_object* v_a_6734_, lean_object* v_a_6735_, lean_object* v_a_6736_){
_start:
{
lean_object* v_res_6737_; 
v_res_6737_ = l_Lake_buildLeanO(v_oFile_6725_, v_srcJob_6726_, v_weakArgs_6727_, v_traceArgs_6728_, v_leanIncludeDir_x3f_6729_, v_a_6730_, v_a_6731_, v_a_6732_, v_a_6733_, v_a_6734_, v_a_6735_);
lean_dec_ref(v_a_6735_);
lean_dec_ref(v_a_6734_);
lean_dec(v_a_6733_);
lean_dec(v_a_6732_);
lean_dec(v_a_6731_);
return v_res_6737_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0(lean_object* v_libFile_6738_, lean_object* v_oFiles_6739_, uint8_t v_thin_6740_, lean_object* v___y_6741_, lean_object* v___y_6742_, lean_object* v___y_6743_, lean_object* v___y_6744_, lean_object* v___y_6745_, lean_object* v___y_6746_){
_start:
{
lean_object* v_toContext_6748_; lean_object* v_lakeEnv_6749_; lean_object* v_lean_6750_; lean_object* v_log_6751_; uint8_t v_action_6752_; uint8_t v_wantsRebuild_6753_; lean_object* v_trace_6754_; lean_object* v_buildTime_6755_; lean_object* v___x_6757_; uint8_t v_isShared_6758_; uint8_t v_isSharedCheck_6785_; 
v_toContext_6748_ = lean_ctor_get(v___y_6745_, 1);
v_lakeEnv_6749_ = lean_ctor_get(v_toContext_6748_, 1);
v_lean_6750_ = lean_ctor_get(v_lakeEnv_6749_, 1);
v_log_6751_ = lean_ctor_get(v___y_6746_, 0);
v_action_6752_ = lean_ctor_get_uint8(v___y_6746_, sizeof(void*)*3);
v_wantsRebuild_6753_ = lean_ctor_get_uint8(v___y_6746_, sizeof(void*)*3 + 1);
v_trace_6754_ = lean_ctor_get(v___y_6746_, 1);
v_buildTime_6755_ = lean_ctor_get(v___y_6746_, 2);
v_isSharedCheck_6785_ = !lean_is_exclusive(v___y_6746_);
if (v_isSharedCheck_6785_ == 0)
{
v___x_6757_ = v___y_6746_;
v_isShared_6758_ = v_isSharedCheck_6785_;
goto v_resetjp_6756_;
}
else
{
lean_inc(v_buildTime_6755_);
lean_inc(v_trace_6754_);
lean_inc(v_log_6751_);
lean_dec(v___y_6746_);
v___x_6757_ = lean_box(0);
v_isShared_6758_ = v_isSharedCheck_6785_;
goto v_resetjp_6756_;
}
v_resetjp_6756_:
{
lean_object* v_ar_6759_; lean_object* v___x_6760_; 
v_ar_6759_ = lean_ctor_get(v_lean_6750_, 13);
lean_inc_ref(v_ar_6759_);
v___x_6760_ = l_Lake_compileStaticLib(v_libFile_6738_, v_oFiles_6739_, v_ar_6759_, v_thin_6740_, v_log_6751_);
if (lean_obj_tag(v___x_6760_) == 0)
{
lean_object* v_a_6761_; lean_object* v_a_6762_; lean_object* v___x_6764_; uint8_t v_isShared_6765_; uint8_t v_isSharedCheck_6772_; 
v_a_6761_ = lean_ctor_get(v___x_6760_, 0);
v_a_6762_ = lean_ctor_get(v___x_6760_, 1);
v_isSharedCheck_6772_ = !lean_is_exclusive(v___x_6760_);
if (v_isSharedCheck_6772_ == 0)
{
v___x_6764_ = v___x_6760_;
v_isShared_6765_ = v_isSharedCheck_6772_;
goto v_resetjp_6763_;
}
else
{
lean_inc(v_a_6762_);
lean_inc(v_a_6761_);
lean_dec(v___x_6760_);
v___x_6764_ = lean_box(0);
v_isShared_6765_ = v_isSharedCheck_6772_;
goto v_resetjp_6763_;
}
v_resetjp_6763_:
{
lean_object* v___x_6767_; 
if (v_isShared_6758_ == 0)
{
lean_ctor_set(v___x_6757_, 0, v_a_6762_);
v___x_6767_ = v___x_6757_;
goto v_reusejp_6766_;
}
else
{
lean_object* v_reuseFailAlloc_6771_; 
v_reuseFailAlloc_6771_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6771_, 0, v_a_6762_);
lean_ctor_set(v_reuseFailAlloc_6771_, 1, v_trace_6754_);
lean_ctor_set(v_reuseFailAlloc_6771_, 2, v_buildTime_6755_);
lean_ctor_set_uint8(v_reuseFailAlloc_6771_, sizeof(void*)*3, v_action_6752_);
lean_ctor_set_uint8(v_reuseFailAlloc_6771_, sizeof(void*)*3 + 1, v_wantsRebuild_6753_);
v___x_6767_ = v_reuseFailAlloc_6771_;
goto v_reusejp_6766_;
}
v_reusejp_6766_:
{
lean_object* v___x_6769_; 
if (v_isShared_6765_ == 0)
{
lean_ctor_set(v___x_6764_, 1, v___x_6767_);
v___x_6769_ = v___x_6764_;
goto v_reusejp_6768_;
}
else
{
lean_object* v_reuseFailAlloc_6770_; 
v_reuseFailAlloc_6770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6770_, 0, v_a_6761_);
lean_ctor_set(v_reuseFailAlloc_6770_, 1, v___x_6767_);
v___x_6769_ = v_reuseFailAlloc_6770_;
goto v_reusejp_6768_;
}
v_reusejp_6768_:
{
return v___x_6769_;
}
}
}
}
else
{
lean_object* v_a_6773_; lean_object* v_a_6774_; lean_object* v___x_6776_; uint8_t v_isShared_6777_; uint8_t v_isSharedCheck_6784_; 
v_a_6773_ = lean_ctor_get(v___x_6760_, 0);
v_a_6774_ = lean_ctor_get(v___x_6760_, 1);
v_isSharedCheck_6784_ = !lean_is_exclusive(v___x_6760_);
if (v_isSharedCheck_6784_ == 0)
{
v___x_6776_ = v___x_6760_;
v_isShared_6777_ = v_isSharedCheck_6784_;
goto v_resetjp_6775_;
}
else
{
lean_inc(v_a_6774_);
lean_inc(v_a_6773_);
lean_dec(v___x_6760_);
v___x_6776_ = lean_box(0);
v_isShared_6777_ = v_isSharedCheck_6784_;
goto v_resetjp_6775_;
}
v_resetjp_6775_:
{
lean_object* v___x_6779_; 
if (v_isShared_6758_ == 0)
{
lean_ctor_set(v___x_6757_, 0, v_a_6774_);
v___x_6779_ = v___x_6757_;
goto v_reusejp_6778_;
}
else
{
lean_object* v_reuseFailAlloc_6783_; 
v_reuseFailAlloc_6783_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6783_, 0, v_a_6774_);
lean_ctor_set(v_reuseFailAlloc_6783_, 1, v_trace_6754_);
lean_ctor_set(v_reuseFailAlloc_6783_, 2, v_buildTime_6755_);
lean_ctor_set_uint8(v_reuseFailAlloc_6783_, sizeof(void*)*3, v_action_6752_);
lean_ctor_set_uint8(v_reuseFailAlloc_6783_, sizeof(void*)*3 + 1, v_wantsRebuild_6753_);
v___x_6779_ = v_reuseFailAlloc_6783_;
goto v_reusejp_6778_;
}
v_reusejp_6778_:
{
lean_object* v___x_6781_; 
if (v_isShared_6777_ == 0)
{
lean_ctor_set(v___x_6776_, 1, v___x_6779_);
v___x_6781_ = v___x_6776_;
goto v_reusejp_6780_;
}
else
{
lean_object* v_reuseFailAlloc_6782_; 
v_reuseFailAlloc_6782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6782_, 0, v_a_6773_);
lean_ctor_set(v_reuseFailAlloc_6782_, 1, v___x_6779_);
v___x_6781_ = v_reuseFailAlloc_6782_;
goto v_reusejp_6780_;
}
v_reusejp_6780_:
{
return v___x_6781_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0___boxed(lean_object* v_libFile_6786_, lean_object* v_oFiles_6787_, lean_object* v_thin_6788_, lean_object* v___y_6789_, lean_object* v___y_6790_, lean_object* v___y_6791_, lean_object* v___y_6792_, lean_object* v___y_6793_, lean_object* v___y_6794_, lean_object* v___y_6795_){
_start:
{
uint8_t v_thin_boxed_6796_; lean_object* v_res_6797_; 
v_thin_boxed_6796_ = lean_unbox(v_thin_6788_);
v_res_6797_ = l_Lake_buildStaticLib___lam__0(v_libFile_6786_, v_oFiles_6787_, v_thin_boxed_6796_, v___y_6789_, v___y_6790_, v___y_6791_, v___y_6792_, v___y_6793_, v___y_6794_);
lean_dec_ref(v___y_6793_);
lean_dec(v___y_6792_);
lean_dec(v___y_6791_);
lean_dec(v___y_6790_);
lean_dec_ref(v___y_6789_);
return v_res_6797_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1(lean_object* v_libFile_6799_, uint8_t v_thin_6800_, lean_object* v_oFiles_6801_, lean_object* v___y_6802_, lean_object* v___y_6803_, lean_object* v___y_6804_, lean_object* v___y_6805_, lean_object* v___y_6806_, lean_object* v___y_6807_){
_start:
{
lean_object* v___x_6809_; lean_object* v___f_6810_; uint8_t v___x_6811_; lean_object* v___x_6812_; uint8_t v___x_6813_; lean_object* v___x_6814_; 
v___x_6809_ = lean_box(v_thin_6800_);
lean_inc_ref(v_libFile_6799_);
v___f_6810_ = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6810_, 0, v_libFile_6799_);
lean_closure_set(v___f_6810_, 1, v_oFiles_6801_);
lean_closure_set(v___f_6810_, 2, v___x_6809_);
v___x_6811_ = 0;
v___x_6812_ = ((lean_object*)(l_Lake_buildStaticLib___lam__1___closed__0));
v___x_6813_ = 1;
v___x_6814_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_6799_, v___f_6810_, v___x_6811_, v___x_6812_, v___x_6813_, v___x_6811_, v___x_6811_, v___y_6802_, v___y_6803_, v___y_6804_, v___y_6805_, v___y_6806_, v___y_6807_);
if (lean_obj_tag(v___x_6814_) == 0)
{
lean_object* v_a_6815_; lean_object* v_a_6816_; lean_object* v___x_6818_; uint8_t v_isShared_6819_; uint8_t v_isSharedCheck_6824_; 
v_a_6815_ = lean_ctor_get(v___x_6814_, 0);
v_a_6816_ = lean_ctor_get(v___x_6814_, 1);
v_isSharedCheck_6824_ = !lean_is_exclusive(v___x_6814_);
if (v_isSharedCheck_6824_ == 0)
{
v___x_6818_ = v___x_6814_;
v_isShared_6819_ = v_isSharedCheck_6824_;
goto v_resetjp_6817_;
}
else
{
lean_inc(v_a_6816_);
lean_inc(v_a_6815_);
lean_dec(v___x_6814_);
v___x_6818_ = lean_box(0);
v_isShared_6819_ = v_isSharedCheck_6824_;
goto v_resetjp_6817_;
}
v_resetjp_6817_:
{
lean_object* v_path_6820_; lean_object* v___x_6822_; 
v_path_6820_ = lean_ctor_get(v_a_6815_, 1);
lean_inc_ref(v_path_6820_);
lean_dec(v_a_6815_);
if (v_isShared_6819_ == 0)
{
lean_ctor_set(v___x_6818_, 0, v_path_6820_);
v___x_6822_ = v___x_6818_;
goto v_reusejp_6821_;
}
else
{
lean_object* v_reuseFailAlloc_6823_; 
v_reuseFailAlloc_6823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6823_, 0, v_path_6820_);
lean_ctor_set(v_reuseFailAlloc_6823_, 1, v_a_6816_);
v___x_6822_ = v_reuseFailAlloc_6823_;
goto v_reusejp_6821_;
}
v_reusejp_6821_:
{
return v___x_6822_;
}
}
}
else
{
lean_object* v_a_6825_; lean_object* v_a_6826_; lean_object* v___x_6828_; uint8_t v_isShared_6829_; uint8_t v_isSharedCheck_6833_; 
v_a_6825_ = lean_ctor_get(v___x_6814_, 0);
v_a_6826_ = lean_ctor_get(v___x_6814_, 1);
v_isSharedCheck_6833_ = !lean_is_exclusive(v___x_6814_);
if (v_isSharedCheck_6833_ == 0)
{
v___x_6828_ = v___x_6814_;
v_isShared_6829_ = v_isSharedCheck_6833_;
goto v_resetjp_6827_;
}
else
{
lean_inc(v_a_6826_);
lean_inc(v_a_6825_);
lean_dec(v___x_6814_);
v___x_6828_ = lean_box(0);
v_isShared_6829_ = v_isSharedCheck_6833_;
goto v_resetjp_6827_;
}
v_resetjp_6827_:
{
lean_object* v___x_6831_; 
if (v_isShared_6829_ == 0)
{
v___x_6831_ = v___x_6828_;
goto v_reusejp_6830_;
}
else
{
lean_object* v_reuseFailAlloc_6832_; 
v_reuseFailAlloc_6832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6832_, 0, v_a_6825_);
lean_ctor_set(v_reuseFailAlloc_6832_, 1, v_a_6826_);
v___x_6831_ = v_reuseFailAlloc_6832_;
goto v_reusejp_6830_;
}
v_reusejp_6830_:
{
return v___x_6831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1___boxed(lean_object* v_libFile_6834_, lean_object* v_thin_6835_, lean_object* v_oFiles_6836_, lean_object* v___y_6837_, lean_object* v___y_6838_, lean_object* v___y_6839_, lean_object* v___y_6840_, lean_object* v___y_6841_, lean_object* v___y_6842_, lean_object* v___y_6843_){
_start:
{
uint8_t v_thin_boxed_6844_; lean_object* v_res_6845_; 
v_thin_boxed_6844_ = lean_unbox(v_thin_6835_);
v_res_6845_ = l_Lake_buildStaticLib___lam__1(v_libFile_6834_, v_thin_boxed_6844_, v_oFiles_6836_, v___y_6837_, v___y_6838_, v___y_6839_, v___y_6840_, v___y_6841_, v___y_6842_);
lean_dec_ref(v___y_6841_);
lean_dec(v___y_6840_);
lean_dec(v___y_6839_);
lean_dec(v___y_6838_);
return v_res_6845_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object* v_libFile_6847_, lean_object* v_oFileJobs_6848_, uint8_t v_thin_6849_, lean_object* v_a_6850_, lean_object* v_a_6851_, lean_object* v_a_6852_, lean_object* v_a_6853_, lean_object* v_a_6854_, lean_object* v_a_6855_){
_start:
{
lean_object* v___x_6857_; lean_object* v___f_6858_; lean_object* v___x_6859_; lean_object* v___x_6860_; lean_object* v___x_6861_; lean_object* v___x_6862_; uint8_t v___x_6863_; lean_object* v___x_6864_; 
v___x_6857_ = lean_box(v_thin_6849_);
v___f_6858_ = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__1___boxed), 10, 2);
lean_closure_set(v___f_6858_, 0, v_libFile_6847_);
lean_closure_set(v___f_6858_, 1, v___x_6857_);
v___x_6859_ = l_Lake_instDataKindFilePath;
v___x_6860_ = ((lean_object*)(l_Lake_buildStaticLib___closed__0));
v___x_6861_ = l_Lake_Job_collectArray___redArg(v_oFileJobs_6848_, v___x_6860_);
v___x_6862_ = lean_unsigned_to_nat(0u);
v___x_6863_ = 0;
v___x_6864_ = l_Lake_Job_mapM___redArg(v___x_6859_, v___x_6861_, v___f_6858_, v___x_6862_, v___x_6863_, v_a_6850_, v_a_6851_, v_a_6852_, v_a_6853_, v_a_6854_, v_a_6855_);
return v___x_6864_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object* v_libFile_6865_, lean_object* v_oFileJobs_6866_, lean_object* v_thin_6867_, lean_object* v_a_6868_, lean_object* v_a_6869_, lean_object* v_a_6870_, lean_object* v_a_6871_, lean_object* v_a_6872_, lean_object* v_a_6873_, lean_object* v_a_6874_){
_start:
{
uint8_t v_thin_boxed_6875_; lean_object* v_res_6876_; 
v_thin_boxed_6875_ = lean_unbox(v_thin_6867_);
v_res_6876_ = l_Lake_buildStaticLib(v_libFile_6865_, v_oFileJobs_6866_, v_thin_boxed_6875_, v_a_6868_, v_a_6869_, v_a_6870_, v_a_6871_, v_a_6872_, v_a_6873_);
lean_dec_ref(v_a_6873_);
lean_dec_ref(v_a_6872_);
lean_dec(v_a_6871_);
lean_dec(v_a_6870_);
lean_dec(v_a_6869_);
lean_dec_ref(v_oFileJobs_6866_);
return v_res_6876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(lean_object* v_as_6877_, size_t v_sz_6878_, size_t v_i_6879_, lean_object* v_b_6880_){
_start:
{
uint8_t v___x_6881_; 
v___x_6881_ = lean_usize_dec_lt(v_i_6879_, v_sz_6878_);
if (v___x_6881_ == 0)
{
return v_b_6880_;
}
else
{
lean_object* v_a_6882_; lean_object* v___x_6883_; size_t v___x_6884_; size_t v___x_6885_; 
v_a_6882_ = lean_array_uget_borrowed(v_as_6877_, v_i_6879_);
lean_inc(v_a_6882_);
v___x_6883_ = lean_array_push(v_b_6880_, v_a_6882_);
v___x_6884_ = ((size_t)1ULL);
v___x_6885_ = lean_usize_add(v_i_6879_, v___x_6884_);
v_i_6879_ = v___x_6885_;
v_b_6880_ = v___x_6883_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0___boxed(lean_object* v_as_6887_, lean_object* v_sz_6888_, lean_object* v_i_6889_, lean_object* v_b_6890_){
_start:
{
size_t v_sz_boxed_6891_; size_t v_i_boxed_6892_; lean_object* v_res_6893_; 
v_sz_boxed_6891_ = lean_unbox_usize(v_sz_6888_);
lean_dec(v_sz_6888_);
v_i_boxed_6892_ = lean_unbox_usize(v_i_6889_);
lean_dec(v_i_6889_);
v_res_6893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(v_as_6887_, v_sz_boxed_6891_, v_i_boxed_6892_, v_b_6890_);
lean_dec_ref(v_as_6887_);
return v_res_6893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(lean_object* v_as_6896_, size_t v_sz_6897_, size_t v_i_6898_, lean_object* v_b_6899_){
_start:
{
uint8_t v___x_6900_; 
v___x_6900_ = lean_usize_dec_lt(v_i_6898_, v_sz_6897_);
if (v___x_6900_ == 0)
{
return v_b_6899_;
}
else
{
lean_object* v_a_6901_; lean_object* v_args_6903_; lean_object* v___x_6911_; 
v_a_6901_ = lean_array_uget_borrowed(v_as_6896_, v_i_6898_);
lean_inc(v_a_6901_);
v___x_6911_ = l_Lake_Dynlib_dir_x3f(v_a_6901_);
if (lean_obj_tag(v___x_6911_) == 1)
{
lean_object* v_val_6912_; lean_object* v___x_6913_; lean_object* v___x_6914_; lean_object* v___x_6915_; 
v_val_6912_ = lean_ctor_get(v___x_6911_, 0);
lean_inc(v_val_6912_);
lean_dec_ref(v___x_6911_);
v___x_6913_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
v___x_6914_ = lean_string_append(v___x_6913_, v_val_6912_);
lean_dec(v_val_6912_);
v___x_6915_ = lean_array_push(v_b_6899_, v___x_6914_);
v_args_6903_ = v___x_6915_;
goto v___jp_6902_;
}
else
{
lean_dec(v___x_6911_);
v_args_6903_ = v_b_6899_;
goto v___jp_6902_;
}
v___jp_6902_:
{
lean_object* v_name_6904_; lean_object* v___x_6905_; lean_object* v___x_6906_; lean_object* v___x_6907_; size_t v___x_6908_; size_t v___x_6909_; 
v_name_6904_ = lean_ctor_get(v_a_6901_, 1);
v___x_6905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0));
v___x_6906_ = lean_string_append(v___x_6905_, v_name_6904_);
v___x_6907_ = lean_array_push(v_args_6903_, v___x_6906_);
v___x_6908_ = ((size_t)1ULL);
v___x_6909_ = lean_usize_add(v_i_6898_, v___x_6908_);
v_i_6898_ = v___x_6909_;
v_b_6899_ = v___x_6907_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___boxed(lean_object* v_as_6916_, lean_object* v_sz_6917_, lean_object* v_i_6918_, lean_object* v_b_6919_){
_start:
{
size_t v_sz_boxed_6920_; size_t v_i_boxed_6921_; lean_object* v_res_6922_; 
v_sz_boxed_6920_ = lean_unbox_usize(v_sz_6917_);
lean_dec(v_sz_6917_);
v_i_boxed_6921_ = lean_unbox_usize(v_i_6918_);
lean_dec(v_i_6918_);
v_res_6922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(v_as_6916_, v_sz_boxed_6920_, v_i_boxed_6921_, v_b_6919_);
lean_dec_ref(v_as_6916_);
return v_res_6922_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(lean_object* v_objs_6923_, lean_object* v_libs_6924_){
_start:
{
lean_object* v_args_6925_; size_t v_sz_6926_; size_t v___x_6927_; lean_object* v___x_6928_; size_t v_sz_6929_; lean_object* v___x_6930_; 
v_args_6925_ = ((lean_object*)(l_Lake_inputDir___lam__1___closed__0));
v_sz_6926_ = lean_array_size(v_objs_6923_);
v___x_6927_ = ((size_t)0ULL);
v___x_6928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(v_objs_6923_, v_sz_6926_, v___x_6927_, v_args_6925_);
v_sz_6929_ = lean_array_size(v_libs_6924_);
v___x_6930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(v_libs_6924_, v_sz_6929_, v___x_6927_, v___x_6928_);
return v___x_6930_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs___boxed(lean_object* v_objs_6931_, lean_object* v_libs_6932_){
_start:
{
lean_object* v_res_6933_; 
v_res_6933_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_6931_, v_libs_6932_);
lean_dec_ref(v_libs_6932_);
lean_dec_ref(v_objs_6931_);
return v_res_6933_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(lean_object* v_k_6934_, lean_object* v_t_6935_){
_start:
{
if (lean_obj_tag(v_t_6935_) == 0)
{
lean_object* v_k_6936_; lean_object* v_l_6937_; lean_object* v_r_6938_; uint8_t v___x_6939_; 
v_k_6936_ = lean_ctor_get(v_t_6935_, 1);
v_l_6937_ = lean_ctor_get(v_t_6935_, 3);
v_r_6938_ = lean_ctor_get(v_t_6935_, 4);
v___x_6939_ = lean_string_dec_lt(v_k_6934_, v_k_6936_);
if (v___x_6939_ == 0)
{
uint8_t v___x_6940_; 
v___x_6940_ = lean_string_dec_eq(v_k_6934_, v_k_6936_);
if (v___x_6940_ == 0)
{
v_t_6935_ = v_r_6938_;
goto _start;
}
else
{
return v___x_6940_;
}
}
else
{
v_t_6935_ = v_l_6937_;
goto _start;
}
}
else
{
uint8_t v___x_6943_; 
v___x_6943_ = 0;
return v___x_6943_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg___boxed(lean_object* v_k_6944_, lean_object* v_t_6945_){
_start:
{
uint8_t v_res_6946_; lean_object* v_r_6947_; 
v_res_6946_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_k_6944_, v_t_6945_);
lean_dec(v_t_6945_);
lean_dec_ref(v_k_6944_);
v_r_6947_ = lean_box(v_res_6946_);
return v_r_6947_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(lean_object* v_a_6948_, lean_object* v_x_6949_){
_start:
{
if (lean_obj_tag(v_x_6949_) == 0)
{
uint8_t v___x_6950_; 
v___x_6950_ = 0;
return v___x_6950_;
}
else
{
lean_object* v_head_6951_; lean_object* v_tail_6952_; uint8_t v___x_6953_; 
v_head_6951_ = lean_ctor_get(v_x_6949_, 0);
v_tail_6952_ = lean_ctor_get(v_x_6949_, 1);
v___x_6953_ = lean_string_dec_eq(v_a_6948_, v_head_6951_);
if (v___x_6953_ == 0)
{
v_x_6949_ = v_tail_6952_;
goto _start;
}
else
{
return v___x_6953_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1___boxed(lean_object* v_a_6955_, lean_object* v_x_6956_){
_start:
{
uint8_t v_res_6957_; lean_object* v_r_6958_; 
v_res_6957_ = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(v_a_6955_, v_x_6956_);
lean_dec(v_x_6956_);
lean_dec_ref(v_a_6955_);
v_r_6958_ = lean_box(v_res_6957_);
return v_r_6958_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(lean_object* v_k_6959_, lean_object* v_v_6960_, lean_object* v_t_6961_){
_start:
{
if (lean_obj_tag(v_t_6961_) == 0)
{
lean_object* v_size_6962_; lean_object* v_k_6963_; lean_object* v_v_6964_; lean_object* v_l_6965_; lean_object* v_r_6966_; lean_object* v___x_6968_; uint8_t v_isShared_6969_; uint8_t v_isSharedCheck_7247_; 
v_size_6962_ = lean_ctor_get(v_t_6961_, 0);
v_k_6963_ = lean_ctor_get(v_t_6961_, 1);
v_v_6964_ = lean_ctor_get(v_t_6961_, 2);
v_l_6965_ = lean_ctor_get(v_t_6961_, 3);
v_r_6966_ = lean_ctor_get(v_t_6961_, 4);
v_isSharedCheck_7247_ = !lean_is_exclusive(v_t_6961_);
if (v_isSharedCheck_7247_ == 0)
{
v___x_6968_ = v_t_6961_;
v_isShared_6969_ = v_isSharedCheck_7247_;
goto v_resetjp_6967_;
}
else
{
lean_inc(v_r_6966_);
lean_inc(v_l_6965_);
lean_inc(v_v_6964_);
lean_inc(v_k_6963_);
lean_inc(v_size_6962_);
lean_dec(v_t_6961_);
v___x_6968_ = lean_box(0);
v_isShared_6969_ = v_isSharedCheck_7247_;
goto v_resetjp_6967_;
}
v_resetjp_6967_:
{
uint8_t v___x_6970_; 
v___x_6970_ = lean_string_dec_lt(v_k_6959_, v_k_6963_);
if (v___x_6970_ == 0)
{
uint8_t v___x_6971_; 
v___x_6971_ = lean_string_dec_eq(v_k_6959_, v_k_6963_);
if (v___x_6971_ == 0)
{
lean_object* v_impl_6972_; lean_object* v___x_6973_; 
lean_dec(v_size_6962_);
v_impl_6972_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_6959_, v_v_6960_, v_r_6966_);
v___x_6973_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_6965_) == 0)
{
lean_object* v_size_6974_; lean_object* v_size_6975_; lean_object* v_k_6976_; lean_object* v_v_6977_; lean_object* v_l_6978_; lean_object* v_r_6979_; lean_object* v___x_6980_; lean_object* v___x_6981_; uint8_t v___x_6982_; 
v_size_6974_ = lean_ctor_get(v_l_6965_, 0);
v_size_6975_ = lean_ctor_get(v_impl_6972_, 0);
lean_inc(v_size_6975_);
v_k_6976_ = lean_ctor_get(v_impl_6972_, 1);
lean_inc(v_k_6976_);
v_v_6977_ = lean_ctor_get(v_impl_6972_, 2);
lean_inc(v_v_6977_);
v_l_6978_ = lean_ctor_get(v_impl_6972_, 3);
lean_inc(v_l_6978_);
v_r_6979_ = lean_ctor_get(v_impl_6972_, 4);
lean_inc(v_r_6979_);
v___x_6980_ = lean_unsigned_to_nat(3u);
v___x_6981_ = lean_nat_mul(v___x_6980_, v_size_6974_);
v___x_6982_ = lean_nat_dec_lt(v___x_6981_, v_size_6975_);
lean_dec(v___x_6981_);
if (v___x_6982_ == 0)
{
lean_object* v___x_6983_; lean_object* v___x_6984_; lean_object* v___x_6986_; 
lean_dec(v_r_6979_);
lean_dec(v_l_6978_);
lean_dec(v_v_6977_);
lean_dec(v_k_6976_);
v___x_6983_ = lean_nat_add(v___x_6973_, v_size_6974_);
v___x_6984_ = lean_nat_add(v___x_6983_, v_size_6975_);
lean_dec(v_size_6975_);
lean_dec(v___x_6983_);
if (v_isShared_6969_ == 0)
{
lean_ctor_set(v___x_6968_, 4, v_impl_6972_);
lean_ctor_set(v___x_6968_, 0, v___x_6984_);
v___x_6986_ = v___x_6968_;
goto v_reusejp_6985_;
}
else
{
lean_object* v_reuseFailAlloc_6987_; 
v_reuseFailAlloc_6987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6987_, 0, v___x_6984_);
lean_ctor_set(v_reuseFailAlloc_6987_, 1, v_k_6963_);
lean_ctor_set(v_reuseFailAlloc_6987_, 2, v_v_6964_);
lean_ctor_set(v_reuseFailAlloc_6987_, 3, v_l_6965_);
lean_ctor_set(v_reuseFailAlloc_6987_, 4, v_impl_6972_);
v___x_6986_ = v_reuseFailAlloc_6987_;
goto v_reusejp_6985_;
}
v_reusejp_6985_:
{
return v___x_6986_;
}
}
else
{
lean_object* v___x_6989_; uint8_t v_isShared_6990_; uint8_t v_isSharedCheck_7051_; 
v_isSharedCheck_7051_ = !lean_is_exclusive(v_impl_6972_);
if (v_isSharedCheck_7051_ == 0)
{
lean_object* v_unused_7052_; lean_object* v_unused_7053_; lean_object* v_unused_7054_; lean_object* v_unused_7055_; lean_object* v_unused_7056_; 
v_unused_7052_ = lean_ctor_get(v_impl_6972_, 4);
lean_dec(v_unused_7052_);
v_unused_7053_ = lean_ctor_get(v_impl_6972_, 3);
lean_dec(v_unused_7053_);
v_unused_7054_ = lean_ctor_get(v_impl_6972_, 2);
lean_dec(v_unused_7054_);
v_unused_7055_ = lean_ctor_get(v_impl_6972_, 1);
lean_dec(v_unused_7055_);
v_unused_7056_ = lean_ctor_get(v_impl_6972_, 0);
lean_dec(v_unused_7056_);
v___x_6989_ = v_impl_6972_;
v_isShared_6990_ = v_isSharedCheck_7051_;
goto v_resetjp_6988_;
}
else
{
lean_dec(v_impl_6972_);
v___x_6989_ = lean_box(0);
v_isShared_6990_ = v_isSharedCheck_7051_;
goto v_resetjp_6988_;
}
v_resetjp_6988_:
{
lean_object* v_size_6991_; lean_object* v_k_6992_; lean_object* v_v_6993_; lean_object* v_l_6994_; lean_object* v_r_6995_; lean_object* v_size_6996_; lean_object* v___x_6997_; lean_object* v___x_6998_; uint8_t v___x_6999_; 
v_size_6991_ = lean_ctor_get(v_l_6978_, 0);
v_k_6992_ = lean_ctor_get(v_l_6978_, 1);
v_v_6993_ = lean_ctor_get(v_l_6978_, 2);
v_l_6994_ = lean_ctor_get(v_l_6978_, 3);
v_r_6995_ = lean_ctor_get(v_l_6978_, 4);
v_size_6996_ = lean_ctor_get(v_r_6979_, 0);
v___x_6997_ = lean_unsigned_to_nat(2u);
v___x_6998_ = lean_nat_mul(v___x_6997_, v_size_6996_);
v___x_6999_ = lean_nat_dec_lt(v_size_6991_, v___x_6998_);
lean_dec(v___x_6998_);
if (v___x_6999_ == 0)
{
lean_object* v___x_7001_; uint8_t v_isShared_7002_; uint8_t v_isSharedCheck_7027_; 
lean_inc(v_r_6995_);
lean_inc(v_l_6994_);
lean_inc(v_v_6993_);
lean_inc(v_k_6992_);
v_isSharedCheck_7027_ = !lean_is_exclusive(v_l_6978_);
if (v_isSharedCheck_7027_ == 0)
{
lean_object* v_unused_7028_; lean_object* v_unused_7029_; lean_object* v_unused_7030_; lean_object* v_unused_7031_; lean_object* v_unused_7032_; 
v_unused_7028_ = lean_ctor_get(v_l_6978_, 4);
lean_dec(v_unused_7028_);
v_unused_7029_ = lean_ctor_get(v_l_6978_, 3);
lean_dec(v_unused_7029_);
v_unused_7030_ = lean_ctor_get(v_l_6978_, 2);
lean_dec(v_unused_7030_);
v_unused_7031_ = lean_ctor_get(v_l_6978_, 1);
lean_dec(v_unused_7031_);
v_unused_7032_ = lean_ctor_get(v_l_6978_, 0);
lean_dec(v_unused_7032_);
v___x_7001_ = v_l_6978_;
v_isShared_7002_ = v_isSharedCheck_7027_;
goto v_resetjp_7000_;
}
else
{
lean_dec(v_l_6978_);
v___x_7001_ = lean_box(0);
v_isShared_7002_ = v_isSharedCheck_7027_;
goto v_resetjp_7000_;
}
v_resetjp_7000_:
{
lean_object* v___x_7003_; lean_object* v___x_7004_; lean_object* v___y_7006_; lean_object* v___y_7007_; lean_object* v___y_7008_; lean_object* v___y_7017_; 
v___x_7003_ = lean_nat_add(v___x_6973_, v_size_6974_);
v___x_7004_ = lean_nat_add(v___x_7003_, v_size_6975_);
lean_dec(v_size_6975_);
if (lean_obj_tag(v_l_6994_) == 0)
{
lean_object* v_size_7025_; 
v_size_7025_ = lean_ctor_get(v_l_6994_, 0);
lean_inc(v_size_7025_);
v___y_7017_ = v_size_7025_;
goto v___jp_7016_;
}
else
{
lean_object* v___x_7026_; 
v___x_7026_ = lean_unsigned_to_nat(0u);
v___y_7017_ = v___x_7026_;
goto v___jp_7016_;
}
v___jp_7005_:
{
lean_object* v___x_7009_; lean_object* v___x_7011_; 
v___x_7009_ = lean_nat_add(v___y_7007_, v___y_7008_);
lean_dec(v___y_7008_);
lean_dec(v___y_7007_);
if (v_isShared_7002_ == 0)
{
lean_ctor_set(v___x_7001_, 4, v_r_6979_);
lean_ctor_set(v___x_7001_, 3, v_r_6995_);
lean_ctor_set(v___x_7001_, 2, v_v_6977_);
lean_ctor_set(v___x_7001_, 1, v_k_6976_);
lean_ctor_set(v___x_7001_, 0, v___x_7009_);
v___x_7011_ = v___x_7001_;
goto v_reusejp_7010_;
}
else
{
lean_object* v_reuseFailAlloc_7015_; 
v_reuseFailAlloc_7015_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7015_, 0, v___x_7009_);
lean_ctor_set(v_reuseFailAlloc_7015_, 1, v_k_6976_);
lean_ctor_set(v_reuseFailAlloc_7015_, 2, v_v_6977_);
lean_ctor_set(v_reuseFailAlloc_7015_, 3, v_r_6995_);
lean_ctor_set(v_reuseFailAlloc_7015_, 4, v_r_6979_);
v___x_7011_ = v_reuseFailAlloc_7015_;
goto v_reusejp_7010_;
}
v_reusejp_7010_:
{
lean_object* v___x_7013_; 
if (v_isShared_6990_ == 0)
{
lean_ctor_set(v___x_6989_, 4, v___x_7011_);
lean_ctor_set(v___x_6989_, 3, v___y_7006_);
lean_ctor_set(v___x_6989_, 2, v_v_6993_);
lean_ctor_set(v___x_6989_, 1, v_k_6992_);
lean_ctor_set(v___x_6989_, 0, v___x_7004_);
v___x_7013_ = v___x_6989_;
goto v_reusejp_7012_;
}
else
{
lean_object* v_reuseFailAlloc_7014_; 
v_reuseFailAlloc_7014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7014_, 0, v___x_7004_);
lean_ctor_set(v_reuseFailAlloc_7014_, 1, v_k_6992_);
lean_ctor_set(v_reuseFailAlloc_7014_, 2, v_v_6993_);
lean_ctor_set(v_reuseFailAlloc_7014_, 3, v___y_7006_);
lean_ctor_set(v_reuseFailAlloc_7014_, 4, v___x_7011_);
v___x_7013_ = v_reuseFailAlloc_7014_;
goto v_reusejp_7012_;
}
v_reusejp_7012_:
{
return v___x_7013_;
}
}
}
v___jp_7016_:
{
lean_object* v___x_7018_; lean_object* v___x_7020_; 
v___x_7018_ = lean_nat_add(v___x_7003_, v___y_7017_);
lean_dec(v___y_7017_);
lean_dec(v___x_7003_);
if (v_isShared_6969_ == 0)
{
lean_ctor_set(v___x_6968_, 4, v_l_6994_);
lean_ctor_set(v___x_6968_, 0, v___x_7018_);
v___x_7020_ = v___x_6968_;
goto v_reusejp_7019_;
}
else
{
lean_object* v_reuseFailAlloc_7024_; 
v_reuseFailAlloc_7024_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7024_, 0, v___x_7018_);
lean_ctor_set(v_reuseFailAlloc_7024_, 1, v_k_6963_);
lean_ctor_set(v_reuseFailAlloc_7024_, 2, v_v_6964_);
lean_ctor_set(v_reuseFailAlloc_7024_, 3, v_l_6965_);
lean_ctor_set(v_reuseFailAlloc_7024_, 4, v_l_6994_);
v___x_7020_ = v_reuseFailAlloc_7024_;
goto v_reusejp_7019_;
}
v_reusejp_7019_:
{
lean_object* v___x_7021_; 
v___x_7021_ = lean_nat_add(v___x_6973_, v_size_6996_);
if (lean_obj_tag(v_r_6995_) == 0)
{
lean_object* v_size_7022_; 
v_size_7022_ = lean_ctor_get(v_r_6995_, 0);
lean_inc(v_size_7022_);
v___y_7006_ = v___x_7020_;
v___y_7007_ = v___x_7021_;
v___y_7008_ = v_size_7022_;
goto v___jp_7005_;
}
else
{
lean_object* v___x_7023_; 
v___x_7023_ = lean_unsigned_to_nat(0u);
v___y_7006_ = v___x_7020_;
v___y_7007_ = v___x_7021_;
v___y_7008_ = v___x_7023_;
goto v___jp_7005_;
}
}
}
}
}
else
{
lean_object* v___x_7033_; lean_object* v___x_7034_; lean_object* v___x_7035_; lean_object* v___x_7037_; 
lean_del_object(v___x_6968_);
v___x_7033_ = lean_nat_add(v___x_6973_, v_size_6974_);
v___x_7034_ = lean_nat_add(v___x_7033_, v_size_6975_);
lean_dec(v_size_6975_);
v___x_7035_ = lean_nat_add(v___x_7033_, v_size_6991_);
lean_dec(v___x_7033_);
lean_inc_ref(v_l_6965_);
if (v_isShared_6990_ == 0)
{
lean_ctor_set(v___x_6989_, 4, v_l_6978_);
lean_ctor_set(v___x_6989_, 3, v_l_6965_);
lean_ctor_set(v___x_6989_, 2, v_v_6964_);
lean_ctor_set(v___x_6989_, 1, v_k_6963_);
lean_ctor_set(v___x_6989_, 0, v___x_7035_);
v___x_7037_ = v___x_6989_;
goto v_reusejp_7036_;
}
else
{
lean_object* v_reuseFailAlloc_7050_; 
v_reuseFailAlloc_7050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7050_, 0, v___x_7035_);
lean_ctor_set(v_reuseFailAlloc_7050_, 1, v_k_6963_);
lean_ctor_set(v_reuseFailAlloc_7050_, 2, v_v_6964_);
lean_ctor_set(v_reuseFailAlloc_7050_, 3, v_l_6965_);
lean_ctor_set(v_reuseFailAlloc_7050_, 4, v_l_6978_);
v___x_7037_ = v_reuseFailAlloc_7050_;
goto v_reusejp_7036_;
}
v_reusejp_7036_:
{
lean_object* v___x_7039_; uint8_t v_isShared_7040_; uint8_t v_isSharedCheck_7044_; 
v_isSharedCheck_7044_ = !lean_is_exclusive(v_l_6965_);
if (v_isSharedCheck_7044_ == 0)
{
lean_object* v_unused_7045_; lean_object* v_unused_7046_; lean_object* v_unused_7047_; lean_object* v_unused_7048_; lean_object* v_unused_7049_; 
v_unused_7045_ = lean_ctor_get(v_l_6965_, 4);
lean_dec(v_unused_7045_);
v_unused_7046_ = lean_ctor_get(v_l_6965_, 3);
lean_dec(v_unused_7046_);
v_unused_7047_ = lean_ctor_get(v_l_6965_, 2);
lean_dec(v_unused_7047_);
v_unused_7048_ = lean_ctor_get(v_l_6965_, 1);
lean_dec(v_unused_7048_);
v_unused_7049_ = lean_ctor_get(v_l_6965_, 0);
lean_dec(v_unused_7049_);
v___x_7039_ = v_l_6965_;
v_isShared_7040_ = v_isSharedCheck_7044_;
goto v_resetjp_7038_;
}
else
{
lean_dec(v_l_6965_);
v___x_7039_ = lean_box(0);
v_isShared_7040_ = v_isSharedCheck_7044_;
goto v_resetjp_7038_;
}
v_resetjp_7038_:
{
lean_object* v___x_7042_; 
if (v_isShared_7040_ == 0)
{
lean_ctor_set(v___x_7039_, 4, v_r_6979_);
lean_ctor_set(v___x_7039_, 3, v___x_7037_);
lean_ctor_set(v___x_7039_, 2, v_v_6977_);
lean_ctor_set(v___x_7039_, 1, v_k_6976_);
lean_ctor_set(v___x_7039_, 0, v___x_7034_);
v___x_7042_ = v___x_7039_;
goto v_reusejp_7041_;
}
else
{
lean_object* v_reuseFailAlloc_7043_; 
v_reuseFailAlloc_7043_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7043_, 0, v___x_7034_);
lean_ctor_set(v_reuseFailAlloc_7043_, 1, v_k_6976_);
lean_ctor_set(v_reuseFailAlloc_7043_, 2, v_v_6977_);
lean_ctor_set(v_reuseFailAlloc_7043_, 3, v___x_7037_);
lean_ctor_set(v_reuseFailAlloc_7043_, 4, v_r_6979_);
v___x_7042_ = v_reuseFailAlloc_7043_;
goto v_reusejp_7041_;
}
v_reusejp_7041_:
{
return v___x_7042_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_7057_; 
v_l_7057_ = lean_ctor_get(v_impl_6972_, 3);
lean_inc(v_l_7057_);
if (lean_obj_tag(v_l_7057_) == 0)
{
lean_object* v_r_7058_; lean_object* v_k_7059_; lean_object* v_v_7060_; lean_object* v___x_7062_; uint8_t v_isShared_7063_; uint8_t v_isSharedCheck_7083_; 
v_r_7058_ = lean_ctor_get(v_impl_6972_, 4);
v_k_7059_ = lean_ctor_get(v_impl_6972_, 1);
v_v_7060_ = lean_ctor_get(v_impl_6972_, 2);
v_isSharedCheck_7083_ = !lean_is_exclusive(v_impl_6972_);
if (v_isSharedCheck_7083_ == 0)
{
lean_object* v_unused_7084_; lean_object* v_unused_7085_; 
v_unused_7084_ = lean_ctor_get(v_impl_6972_, 3);
lean_dec(v_unused_7084_);
v_unused_7085_ = lean_ctor_get(v_impl_6972_, 0);
lean_dec(v_unused_7085_);
v___x_7062_ = v_impl_6972_;
v_isShared_7063_ = v_isSharedCheck_7083_;
goto v_resetjp_7061_;
}
else
{
lean_inc(v_r_7058_);
lean_inc(v_v_7060_);
lean_inc(v_k_7059_);
lean_dec(v_impl_6972_);
v___x_7062_ = lean_box(0);
v_isShared_7063_ = v_isSharedCheck_7083_;
goto v_resetjp_7061_;
}
v_resetjp_7061_:
{
lean_object* v_k_7064_; lean_object* v_v_7065_; lean_object* v___x_7067_; uint8_t v_isShared_7068_; uint8_t v_isSharedCheck_7079_; 
v_k_7064_ = lean_ctor_get(v_l_7057_, 1);
v_v_7065_ = lean_ctor_get(v_l_7057_, 2);
v_isSharedCheck_7079_ = !lean_is_exclusive(v_l_7057_);
if (v_isSharedCheck_7079_ == 0)
{
lean_object* v_unused_7080_; lean_object* v_unused_7081_; lean_object* v_unused_7082_; 
v_unused_7080_ = lean_ctor_get(v_l_7057_, 4);
lean_dec(v_unused_7080_);
v_unused_7081_ = lean_ctor_get(v_l_7057_, 3);
lean_dec(v_unused_7081_);
v_unused_7082_ = lean_ctor_get(v_l_7057_, 0);
lean_dec(v_unused_7082_);
v___x_7067_ = v_l_7057_;
v_isShared_7068_ = v_isSharedCheck_7079_;
goto v_resetjp_7066_;
}
else
{
lean_inc(v_v_7065_);
lean_inc(v_k_7064_);
lean_dec(v_l_7057_);
v___x_7067_ = lean_box(0);
v_isShared_7068_ = v_isSharedCheck_7079_;
goto v_resetjp_7066_;
}
v_resetjp_7066_:
{
lean_object* v___x_7069_; lean_object* v___x_7071_; 
v___x_7069_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_7058_, 2);
if (v_isShared_7068_ == 0)
{
lean_ctor_set(v___x_7067_, 4, v_r_7058_);
lean_ctor_set(v___x_7067_, 3, v_r_7058_);
lean_ctor_set(v___x_7067_, 2, v_v_6964_);
lean_ctor_set(v___x_7067_, 1, v_k_6963_);
lean_ctor_set(v___x_7067_, 0, v___x_6973_);
v___x_7071_ = v___x_7067_;
goto v_reusejp_7070_;
}
else
{
lean_object* v_reuseFailAlloc_7078_; 
v_reuseFailAlloc_7078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7078_, 0, v___x_6973_);
lean_ctor_set(v_reuseFailAlloc_7078_, 1, v_k_6963_);
lean_ctor_set(v_reuseFailAlloc_7078_, 2, v_v_6964_);
lean_ctor_set(v_reuseFailAlloc_7078_, 3, v_r_7058_);
lean_ctor_set(v_reuseFailAlloc_7078_, 4, v_r_7058_);
v___x_7071_ = v_reuseFailAlloc_7078_;
goto v_reusejp_7070_;
}
v_reusejp_7070_:
{
lean_object* v___x_7073_; 
lean_inc(v_r_7058_);
if (v_isShared_7063_ == 0)
{
lean_ctor_set(v___x_7062_, 3, v_r_7058_);
lean_ctor_set(v___x_7062_, 0, v___x_6973_);
v___x_7073_ = v___x_7062_;
goto v_reusejp_7072_;
}
else
{
lean_object* v_reuseFailAlloc_7077_; 
v_reuseFailAlloc_7077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7077_, 0, v___x_6973_);
lean_ctor_set(v_reuseFailAlloc_7077_, 1, v_k_7059_);
lean_ctor_set(v_reuseFailAlloc_7077_, 2, v_v_7060_);
lean_ctor_set(v_reuseFailAlloc_7077_, 3, v_r_7058_);
lean_ctor_set(v_reuseFailAlloc_7077_, 4, v_r_7058_);
v___x_7073_ = v_reuseFailAlloc_7077_;
goto v_reusejp_7072_;
}
v_reusejp_7072_:
{
lean_object* v___x_7075_; 
if (v_isShared_6969_ == 0)
{
lean_ctor_set(v___x_6968_, 4, v___x_7073_);
lean_ctor_set(v___x_6968_, 3, v___x_7071_);
lean_ctor_set(v___x_6968_, 2, v_v_7065_);
lean_ctor_set(v___x_6968_, 1, v_k_7064_);
lean_ctor_set(v___x_6968_, 0, v___x_7069_);
v___x_7075_ = v___x_6968_;
goto v_reusejp_7074_;
}
else
{
lean_object* v_reuseFailAlloc_7076_; 
v_reuseFailAlloc_7076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7076_, 0, v___x_7069_);
lean_ctor_set(v_reuseFailAlloc_7076_, 1, v_k_7064_);
lean_ctor_set(v_reuseFailAlloc_7076_, 2, v_v_7065_);
lean_ctor_set(v_reuseFailAlloc_7076_, 3, v___x_7071_);
lean_ctor_set(v_reuseFailAlloc_7076_, 4, v___x_7073_);
v___x_7075_ = v_reuseFailAlloc_7076_;
goto v_reusejp_7074_;
}
v_reusejp_7074_:
{
return v___x_7075_;
}
}
}
}
}
}
else
{
lean_object* v_r_7086_; 
v_r_7086_ = lean_ctor_get(v_impl_6972_, 4);
lean_inc(v_r_7086_);
if (lean_obj_tag(v_r_7086_) == 0)
{
lean_object* v_k_7087_; lean_object* v_v_7088_; lean_object* v___x_7090_; uint8_t v_isShared_7091_; uint8_t v_isSharedCheck_7099_; 
v_k_7087_ = lean_ctor_get(v_impl_6972_, 1);
v_v_7088_ = lean_ctor_get(v_impl_6972_, 2);
v_isSharedCheck_7099_ = !lean_is_exclusive(v_impl_6972_);
if (v_isSharedCheck_7099_ == 0)
{
lean_object* v_unused_7100_; lean_object* v_unused_7101_; lean_object* v_unused_7102_; 
v_unused_7100_ = lean_ctor_get(v_impl_6972_, 4);
lean_dec(v_unused_7100_);
v_unused_7101_ = lean_ctor_get(v_impl_6972_, 3);
lean_dec(v_unused_7101_);
v_unused_7102_ = lean_ctor_get(v_impl_6972_, 0);
lean_dec(v_unused_7102_);
v___x_7090_ = v_impl_6972_;
v_isShared_7091_ = v_isSharedCheck_7099_;
goto v_resetjp_7089_;
}
else
{
lean_inc(v_v_7088_);
lean_inc(v_k_7087_);
lean_dec(v_impl_6972_);
v___x_7090_ = lean_box(0);
v_isShared_7091_ = v_isSharedCheck_7099_;
goto v_resetjp_7089_;
}
v_resetjp_7089_:
{
lean_object* v___x_7092_; lean_object* v___x_7094_; 
v___x_7092_ = lean_unsigned_to_nat(3u);
if (v_isShared_7091_ == 0)
{
lean_ctor_set(v___x_7090_, 4, v_l_7057_);
lean_ctor_set(v___x_7090_, 2, v_v_6964_);
lean_ctor_set(v___x_7090_, 1, v_k_6963_);
lean_ctor_set(v___x_7090_, 0, v___x_6973_);
v___x_7094_ = v___x_7090_;
goto v_reusejp_7093_;
}
else
{
lean_object* v_reuseFailAlloc_7098_; 
v_reuseFailAlloc_7098_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7098_, 0, v___x_6973_);
lean_ctor_set(v_reuseFailAlloc_7098_, 1, v_k_6963_);
lean_ctor_set(v_reuseFailAlloc_7098_, 2, v_v_6964_);
lean_ctor_set(v_reuseFailAlloc_7098_, 3, v_l_7057_);
lean_ctor_set(v_reuseFailAlloc_7098_, 4, v_l_7057_);
v___x_7094_ = v_reuseFailAlloc_7098_;
goto v_reusejp_7093_;
}
v_reusejp_7093_:
{
lean_object* v___x_7096_; 
if (v_isShared_6969_ == 0)
{
lean_ctor_set(v___x_6968_, 4, v_r_7086_);
lean_ctor_set(v___x_6968_, 3, v___x_7094_);
lean_ctor_set(v___x_6968_, 2, v_v_7088_);
lean_ctor_set(v___x_6968_, 1, v_k_7087_);
lean_ctor_set(v___x_6968_, 0, v___x_7092_);
v___x_7096_ = v___x_6968_;
goto v_reusejp_7095_;
}
else
{
lean_object* v_reuseFailAlloc_7097_; 
v_reuseFailAlloc_7097_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7097_, 0, v___x_7092_);
lean_ctor_set(v_reuseFailAlloc_7097_, 1, v_k_7087_);
lean_ctor_set(v_reuseFailAlloc_7097_, 2, v_v_7088_);
lean_ctor_set(v_reuseFailAlloc_7097_, 3, v___x_7094_);
lean_ctor_set(v_reuseFailAlloc_7097_, 4, v_r_7086_);
v___x_7096_ = v_reuseFailAlloc_7097_;
goto v_reusejp_7095_;
}
v_reusejp_7095_:
{
return v___x_7096_;
}
}
}
}
else
{
lean_object* v___x_7103_; lean_object* v___x_7105_; 
v___x_7103_ = lean_unsigned_to_nat(2u);
if (v_isShared_6969_ == 0)
{
lean_ctor_set(v___x_6968_, 4, v_impl_6972_);
lean_ctor_set(v___x_6968_, 3, v_r_7086_);
lean_ctor_set(v___x_6968_, 0, v___x_7103_);
v___x_7105_ = v___x_6968_;
goto v_reusejp_7104_;
}
else
{
lean_object* v_reuseFailAlloc_7106_; 
v_reuseFailAlloc_7106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7106_, 0, v___x_7103_);
lean_ctor_set(v_reuseFailAlloc_7106_, 1, v_k_6963_);
lean_ctor_set(v_reuseFailAlloc_7106_, 2, v_v_6964_);
lean_ctor_set(v_reuseFailAlloc_7106_, 3, v_r_7086_);
lean_ctor_set(v_reuseFailAlloc_7106_, 4, v_impl_6972_);
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
}
else
{
lean_object* v___x_7108_; 
lean_dec(v_v_6964_);
lean_dec(v_k_6963_);
if (v_isShared_6969_ == 0)
{
lean_ctor_set(v___x_6968_, 2, v_v_6960_);
lean_ctor_set(v___x_6968_, 1, v_k_6959_);
v___x_7108_ = v___x_6968_;
goto v_reusejp_7107_;
}
else
{
lean_object* v_reuseFailAlloc_7109_; 
v_reuseFailAlloc_7109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7109_, 0, v_size_6962_);
lean_ctor_set(v_reuseFailAlloc_7109_, 1, v_k_6959_);
lean_ctor_set(v_reuseFailAlloc_7109_, 2, v_v_6960_);
lean_ctor_set(v_reuseFailAlloc_7109_, 3, v_l_6965_);
lean_ctor_set(v_reuseFailAlloc_7109_, 4, v_r_6966_);
v___x_7108_ = v_reuseFailAlloc_7109_;
goto v_reusejp_7107_;
}
v_reusejp_7107_:
{
return v___x_7108_;
}
}
}
else
{
lean_object* v_impl_7110_; lean_object* v___x_7111_; 
lean_dec(v_size_6962_);
v_impl_7110_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_6959_, v_v_6960_, v_l_6965_);
v___x_7111_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_6966_) == 0)
{
lean_object* v_size_7112_; lean_object* v_size_7113_; lean_object* v_k_7114_; lean_object* v_v_7115_; lean_object* v_l_7116_; lean_object* v_r_7117_; lean_object* v___x_7118_; lean_object* v___x_7119_; uint8_t v___x_7120_; 
v_size_7112_ = lean_ctor_get(v_r_6966_, 0);
v_size_7113_ = lean_ctor_get(v_impl_7110_, 0);
lean_inc(v_size_7113_);
v_k_7114_ = lean_ctor_get(v_impl_7110_, 1);
lean_inc(v_k_7114_);
v_v_7115_ = lean_ctor_get(v_impl_7110_, 2);
lean_inc(v_v_7115_);
v_l_7116_ = lean_ctor_get(v_impl_7110_, 3);
lean_inc(v_l_7116_);
v_r_7117_ = lean_ctor_get(v_impl_7110_, 4);
lean_inc(v_r_7117_);
v___x_7118_ = lean_unsigned_to_nat(3u);
v___x_7119_ = lean_nat_mul(v___x_7118_, v_size_7112_);
v___x_7120_ = lean_nat_dec_lt(v___x_7119_, v_size_7113_);
lean_dec(v___x_7119_);
if (v___x_7120_ == 0)
{
lean_object* v___x_7121_; lean_object* v___x_7122_; lean_object* v___x_7124_; 
lean_dec(v_r_7117_);
lean_dec(v_l_7116_);
lean_dec(v_v_7115_);
lean_dec(v_k_7114_);
v___x_7121_ = lean_nat_add(v___x_7111_, v_size_7113_);
lean_dec(v_size_7113_);
v___x_7122_ = lean_nat_add(v___x_7121_, v_size_7112_);
lean_dec(v___x_7121_);
if (v_isShared_6969_ == 0)
{
lean_ctor_set(v___x_6968_, 3, v_impl_7110_);
lean_ctor_set(v___x_6968_, 0, v___x_7122_);
v___x_7124_ = v___x_6968_;
goto v_reusejp_7123_;
}
else
{
lean_object* v_reuseFailAlloc_7125_; 
v_reuseFailAlloc_7125_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7125_, 0, v___x_7122_);
lean_ctor_set(v_reuseFailAlloc_7125_, 1, v_k_6963_);
lean_ctor_set(v_reuseFailAlloc_7125_, 2, v_v_6964_);
lean_ctor_set(v_reuseFailAlloc_7125_, 3, v_impl_7110_);
lean_ctor_set(v_reuseFailAlloc_7125_, 4, v_r_6966_);
v___x_7124_ = v_reuseFailAlloc_7125_;
goto v_reusejp_7123_;
}
v_reusejp_7123_:
{
return v___x_7124_;
}
}
else
{
lean_object* v___x_7127_; uint8_t v_isShared_7128_; uint8_t v_isSharedCheck_7191_; 
v_isSharedCheck_7191_ = !lean_is_exclusive(v_impl_7110_);
if (v_isSharedCheck_7191_ == 0)
{
lean_object* v_unused_7192_; lean_object* v_unused_7193_; lean_object* v_unused_7194_; lean_object* v_unused_7195_; lean_object* v_unused_7196_; 
v_unused_7192_ = lean_ctor_get(v_impl_7110_, 4);
lean_dec(v_unused_7192_);
v_unused_7193_ = lean_ctor_get(v_impl_7110_, 3);
lean_dec(v_unused_7193_);
v_unused_7194_ = lean_ctor_get(v_impl_7110_, 2);
lean_dec(v_unused_7194_);
v_unused_7195_ = lean_ctor_get(v_impl_7110_, 1);
lean_dec(v_unused_7195_);
v_unused_7196_ = lean_ctor_get(v_impl_7110_, 0);
lean_dec(v_unused_7196_);
v___x_7127_ = v_impl_7110_;
v_isShared_7128_ = v_isSharedCheck_7191_;
goto v_resetjp_7126_;
}
else
{
lean_dec(v_impl_7110_);
v___x_7127_ = lean_box(0);
v_isShared_7128_ = v_isSharedCheck_7191_;
goto v_resetjp_7126_;
}
v_resetjp_7126_:
{
lean_object* v_size_7129_; lean_object* v_size_7130_; lean_object* v_k_7131_; lean_object* v_v_7132_; lean_object* v_l_7133_; lean_object* v_r_7134_; lean_object* v___x_7135_; lean_object* v___x_7136_; uint8_t v___x_7137_; 
v_size_7129_ = lean_ctor_get(v_l_7116_, 0);
v_size_7130_ = lean_ctor_get(v_r_7117_, 0);
v_k_7131_ = lean_ctor_get(v_r_7117_, 1);
v_v_7132_ = lean_ctor_get(v_r_7117_, 2);
v_l_7133_ = lean_ctor_get(v_r_7117_, 3);
v_r_7134_ = lean_ctor_get(v_r_7117_, 4);
v___x_7135_ = lean_unsigned_to_nat(2u);
v___x_7136_ = lean_nat_mul(v___x_7135_, v_size_7129_);
v___x_7137_ = lean_nat_dec_lt(v_size_7130_, v___x_7136_);
lean_dec(v___x_7136_);
if (v___x_7137_ == 0)
{
lean_object* v___x_7139_; uint8_t v_isShared_7140_; uint8_t v_isSharedCheck_7166_; 
lean_inc(v_r_7134_);
lean_inc(v_l_7133_);
lean_inc(v_v_7132_);
lean_inc(v_k_7131_);
v_isSharedCheck_7166_ = !lean_is_exclusive(v_r_7117_);
if (v_isSharedCheck_7166_ == 0)
{
lean_object* v_unused_7167_; lean_object* v_unused_7168_; lean_object* v_unused_7169_; lean_object* v_unused_7170_; lean_object* v_unused_7171_; 
v_unused_7167_ = lean_ctor_get(v_r_7117_, 4);
lean_dec(v_unused_7167_);
v_unused_7168_ = lean_ctor_get(v_r_7117_, 3);
lean_dec(v_unused_7168_);
v_unused_7169_ = lean_ctor_get(v_r_7117_, 2);
lean_dec(v_unused_7169_);
v_unused_7170_ = lean_ctor_get(v_r_7117_, 1);
lean_dec(v_unused_7170_);
v_unused_7171_ = lean_ctor_get(v_r_7117_, 0);
lean_dec(v_unused_7171_);
v___x_7139_ = v_r_7117_;
v_isShared_7140_ = v_isSharedCheck_7166_;
goto v_resetjp_7138_;
}
else
{
lean_dec(v_r_7117_);
v___x_7139_ = lean_box(0);
v_isShared_7140_ = v_isSharedCheck_7166_;
goto v_resetjp_7138_;
}
v_resetjp_7138_:
{
lean_object* v___x_7141_; lean_object* v___x_7142_; lean_object* v___y_7144_; lean_object* v___y_7145_; lean_object* v___y_7146_; lean_object* v___x_7154_; lean_object* v___y_7156_; 
v___x_7141_ = lean_nat_add(v___x_7111_, v_size_7113_);
lean_dec(v_size_7113_);
v___x_7142_ = lean_nat_add(v___x_7141_, v_size_7112_);
lean_dec(v___x_7141_);
v___x_7154_ = lean_nat_add(v___x_7111_, v_size_7129_);
if (lean_obj_tag(v_l_7133_) == 0)
{
lean_object* v_size_7164_; 
v_size_7164_ = lean_ctor_get(v_l_7133_, 0);
lean_inc(v_size_7164_);
v___y_7156_ = v_size_7164_;
goto v___jp_7155_;
}
else
{
lean_object* v___x_7165_; 
v___x_7165_ = lean_unsigned_to_nat(0u);
v___y_7156_ = v___x_7165_;
goto v___jp_7155_;
}
v___jp_7143_:
{
lean_object* v___x_7147_; lean_object* v___x_7149_; 
v___x_7147_ = lean_nat_add(v___y_7145_, v___y_7146_);
lean_dec(v___y_7146_);
lean_dec(v___y_7145_);
if (v_isShared_7140_ == 0)
{
lean_ctor_set(v___x_7139_, 4, v_r_6966_);
lean_ctor_set(v___x_7139_, 3, v_r_7134_);
lean_ctor_set(v___x_7139_, 2, v_v_6964_);
lean_ctor_set(v___x_7139_, 1, v_k_6963_);
lean_ctor_set(v___x_7139_, 0, v___x_7147_);
v___x_7149_ = v___x_7139_;
goto v_reusejp_7148_;
}
else
{
lean_object* v_reuseFailAlloc_7153_; 
v_reuseFailAlloc_7153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7153_, 0, v___x_7147_);
lean_ctor_set(v_reuseFailAlloc_7153_, 1, v_k_6963_);
lean_ctor_set(v_reuseFailAlloc_7153_, 2, v_v_6964_);
lean_ctor_set(v_reuseFailAlloc_7153_, 3, v_r_7134_);
lean_ctor_set(v_reuseFailAlloc_7153_, 4, v_r_6966_);
v___x_7149_ = v_reuseFailAlloc_7153_;
goto v_reusejp_7148_;
}
v_reusejp_7148_:
{
lean_object* v___x_7151_; 
if (v_isShared_7128_ == 0)
{
lean_ctor_set(v___x_7127_, 4, v___x_7149_);
lean_ctor_set(v___x_7127_, 3, v___y_7144_);
lean_ctor_set(v___x_7127_, 2, v_v_7132_);
lean_ctor_set(v___x_7127_, 1, v_k_7131_);
lean_ctor_set(v___x_7127_, 0, v___x_7142_);
v___x_7151_ = v___x_7127_;
goto v_reusejp_7150_;
}
else
{
lean_object* v_reuseFailAlloc_7152_; 
v_reuseFailAlloc_7152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7152_, 0, v___x_7142_);
lean_ctor_set(v_reuseFailAlloc_7152_, 1, v_k_7131_);
lean_ctor_set(v_reuseFailAlloc_7152_, 2, v_v_7132_);
lean_ctor_set(v_reuseFailAlloc_7152_, 3, v___y_7144_);
lean_ctor_set(v_reuseFailAlloc_7152_, 4, v___x_7149_);
v___x_7151_ = v_reuseFailAlloc_7152_;
goto v_reusejp_7150_;
}
v_reusejp_7150_:
{
return v___x_7151_;
}
}
}
v___jp_7155_:
{
lean_object* v___x_7157_; lean_object* v___x_7159_; 
v___x_7157_ = lean_nat_add(v___x_7154_, v___y_7156_);
lean_dec(v___y_7156_);
lean_dec(v___x_7154_);
if (v_isShared_6969_ == 0)
{
lean_ctor_set(v___x_6968_, 4, v_l_7133_);
lean_ctor_set(v___x_6968_, 3, v_l_7116_);
lean_ctor_set(v___x_6968_, 2, v_v_7115_);
lean_ctor_set(v___x_6968_, 1, v_k_7114_);
lean_ctor_set(v___x_6968_, 0, v___x_7157_);
v___x_7159_ = v___x_6968_;
goto v_reusejp_7158_;
}
else
{
lean_object* v_reuseFailAlloc_7163_; 
v_reuseFailAlloc_7163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7163_, 0, v___x_7157_);
lean_ctor_set(v_reuseFailAlloc_7163_, 1, v_k_7114_);
lean_ctor_set(v_reuseFailAlloc_7163_, 2, v_v_7115_);
lean_ctor_set(v_reuseFailAlloc_7163_, 3, v_l_7116_);
lean_ctor_set(v_reuseFailAlloc_7163_, 4, v_l_7133_);
v___x_7159_ = v_reuseFailAlloc_7163_;
goto v_reusejp_7158_;
}
v_reusejp_7158_:
{
lean_object* v___x_7160_; 
v___x_7160_ = lean_nat_add(v___x_7111_, v_size_7112_);
if (lean_obj_tag(v_r_7134_) == 0)
{
lean_object* v_size_7161_; 
v_size_7161_ = lean_ctor_get(v_r_7134_, 0);
lean_inc(v_size_7161_);
v___y_7144_ = v___x_7159_;
v___y_7145_ = v___x_7160_;
v___y_7146_ = v_size_7161_;
goto v___jp_7143_;
}
else
{
lean_object* v___x_7162_; 
v___x_7162_ = lean_unsigned_to_nat(0u);
v___y_7144_ = v___x_7159_;
v___y_7145_ = v___x_7160_;
v___y_7146_ = v___x_7162_;
goto v___jp_7143_;
}
}
}
}
}
else
{
lean_object* v___x_7172_; lean_object* v___x_7173_; lean_object* v___x_7174_; lean_object* v___x_7175_; lean_object* v___x_7177_; 
lean_del_object(v___x_6968_);
v___x_7172_ = lean_nat_add(v___x_7111_, v_size_7113_);
lean_dec(v_size_7113_);
v___x_7173_ = lean_nat_add(v___x_7172_, v_size_7112_);
lean_dec(v___x_7172_);
v___x_7174_ = lean_nat_add(v___x_7111_, v_size_7112_);
v___x_7175_ = lean_nat_add(v___x_7174_, v_size_7130_);
lean_dec(v___x_7174_);
lean_inc_ref(v_r_6966_);
if (v_isShared_7128_ == 0)
{
lean_ctor_set(v___x_7127_, 4, v_r_6966_);
lean_ctor_set(v___x_7127_, 3, v_r_7117_);
lean_ctor_set(v___x_7127_, 2, v_v_6964_);
lean_ctor_set(v___x_7127_, 1, v_k_6963_);
lean_ctor_set(v___x_7127_, 0, v___x_7175_);
v___x_7177_ = v___x_7127_;
goto v_reusejp_7176_;
}
else
{
lean_object* v_reuseFailAlloc_7190_; 
v_reuseFailAlloc_7190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7190_, 0, v___x_7175_);
lean_ctor_set(v_reuseFailAlloc_7190_, 1, v_k_6963_);
lean_ctor_set(v_reuseFailAlloc_7190_, 2, v_v_6964_);
lean_ctor_set(v_reuseFailAlloc_7190_, 3, v_r_7117_);
lean_ctor_set(v_reuseFailAlloc_7190_, 4, v_r_6966_);
v___x_7177_ = v_reuseFailAlloc_7190_;
goto v_reusejp_7176_;
}
v_reusejp_7176_:
{
lean_object* v___x_7179_; uint8_t v_isShared_7180_; uint8_t v_isSharedCheck_7184_; 
v_isSharedCheck_7184_ = !lean_is_exclusive(v_r_6966_);
if (v_isSharedCheck_7184_ == 0)
{
lean_object* v_unused_7185_; lean_object* v_unused_7186_; lean_object* v_unused_7187_; lean_object* v_unused_7188_; lean_object* v_unused_7189_; 
v_unused_7185_ = lean_ctor_get(v_r_6966_, 4);
lean_dec(v_unused_7185_);
v_unused_7186_ = lean_ctor_get(v_r_6966_, 3);
lean_dec(v_unused_7186_);
v_unused_7187_ = lean_ctor_get(v_r_6966_, 2);
lean_dec(v_unused_7187_);
v_unused_7188_ = lean_ctor_get(v_r_6966_, 1);
lean_dec(v_unused_7188_);
v_unused_7189_ = lean_ctor_get(v_r_6966_, 0);
lean_dec(v_unused_7189_);
v___x_7179_ = v_r_6966_;
v_isShared_7180_ = v_isSharedCheck_7184_;
goto v_resetjp_7178_;
}
else
{
lean_dec(v_r_6966_);
v___x_7179_ = lean_box(0);
v_isShared_7180_ = v_isSharedCheck_7184_;
goto v_resetjp_7178_;
}
v_resetjp_7178_:
{
lean_object* v___x_7182_; 
if (v_isShared_7180_ == 0)
{
lean_ctor_set(v___x_7179_, 4, v___x_7177_);
lean_ctor_set(v___x_7179_, 3, v_l_7116_);
lean_ctor_set(v___x_7179_, 2, v_v_7115_);
lean_ctor_set(v___x_7179_, 1, v_k_7114_);
lean_ctor_set(v___x_7179_, 0, v___x_7173_);
v___x_7182_ = v___x_7179_;
goto v_reusejp_7181_;
}
else
{
lean_object* v_reuseFailAlloc_7183_; 
v_reuseFailAlloc_7183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7183_, 0, v___x_7173_);
lean_ctor_set(v_reuseFailAlloc_7183_, 1, v_k_7114_);
lean_ctor_set(v_reuseFailAlloc_7183_, 2, v_v_7115_);
lean_ctor_set(v_reuseFailAlloc_7183_, 3, v_l_7116_);
lean_ctor_set(v_reuseFailAlloc_7183_, 4, v___x_7177_);
v___x_7182_ = v_reuseFailAlloc_7183_;
goto v_reusejp_7181_;
}
v_reusejp_7181_:
{
return v___x_7182_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_7197_; 
v_l_7197_ = lean_ctor_get(v_impl_7110_, 3);
lean_inc(v_l_7197_);
if (lean_obj_tag(v_l_7197_) == 0)
{
lean_object* v_r_7198_; lean_object* v_k_7199_; lean_object* v_v_7200_; lean_object* v___x_7202_; uint8_t v_isShared_7203_; uint8_t v_isSharedCheck_7211_; 
v_r_7198_ = lean_ctor_get(v_impl_7110_, 4);
v_k_7199_ = lean_ctor_get(v_impl_7110_, 1);
v_v_7200_ = lean_ctor_get(v_impl_7110_, 2);
v_isSharedCheck_7211_ = !lean_is_exclusive(v_impl_7110_);
if (v_isSharedCheck_7211_ == 0)
{
lean_object* v_unused_7212_; lean_object* v_unused_7213_; 
v_unused_7212_ = lean_ctor_get(v_impl_7110_, 3);
lean_dec(v_unused_7212_);
v_unused_7213_ = lean_ctor_get(v_impl_7110_, 0);
lean_dec(v_unused_7213_);
v___x_7202_ = v_impl_7110_;
v_isShared_7203_ = v_isSharedCheck_7211_;
goto v_resetjp_7201_;
}
else
{
lean_inc(v_r_7198_);
lean_inc(v_v_7200_);
lean_inc(v_k_7199_);
lean_dec(v_impl_7110_);
v___x_7202_ = lean_box(0);
v_isShared_7203_ = v_isSharedCheck_7211_;
goto v_resetjp_7201_;
}
v_resetjp_7201_:
{
lean_object* v___x_7204_; lean_object* v___x_7206_; 
v___x_7204_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_7198_);
if (v_isShared_7203_ == 0)
{
lean_ctor_set(v___x_7202_, 3, v_r_7198_);
lean_ctor_set(v___x_7202_, 2, v_v_6964_);
lean_ctor_set(v___x_7202_, 1, v_k_6963_);
lean_ctor_set(v___x_7202_, 0, v___x_7111_);
v___x_7206_ = v___x_7202_;
goto v_reusejp_7205_;
}
else
{
lean_object* v_reuseFailAlloc_7210_; 
v_reuseFailAlloc_7210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7210_, 0, v___x_7111_);
lean_ctor_set(v_reuseFailAlloc_7210_, 1, v_k_6963_);
lean_ctor_set(v_reuseFailAlloc_7210_, 2, v_v_6964_);
lean_ctor_set(v_reuseFailAlloc_7210_, 3, v_r_7198_);
lean_ctor_set(v_reuseFailAlloc_7210_, 4, v_r_7198_);
v___x_7206_ = v_reuseFailAlloc_7210_;
goto v_reusejp_7205_;
}
v_reusejp_7205_:
{
lean_object* v___x_7208_; 
if (v_isShared_6969_ == 0)
{
lean_ctor_set(v___x_6968_, 4, v___x_7206_);
lean_ctor_set(v___x_6968_, 3, v_l_7197_);
lean_ctor_set(v___x_6968_, 2, v_v_7200_);
lean_ctor_set(v___x_6968_, 1, v_k_7199_);
lean_ctor_set(v___x_6968_, 0, v___x_7204_);
v___x_7208_ = v___x_6968_;
goto v_reusejp_7207_;
}
else
{
lean_object* v_reuseFailAlloc_7209_; 
v_reuseFailAlloc_7209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7209_, 0, v___x_7204_);
lean_ctor_set(v_reuseFailAlloc_7209_, 1, v_k_7199_);
lean_ctor_set(v_reuseFailAlloc_7209_, 2, v_v_7200_);
lean_ctor_set(v_reuseFailAlloc_7209_, 3, v_l_7197_);
lean_ctor_set(v_reuseFailAlloc_7209_, 4, v___x_7206_);
v___x_7208_ = v_reuseFailAlloc_7209_;
goto v_reusejp_7207_;
}
v_reusejp_7207_:
{
return v___x_7208_;
}
}
}
}
else
{
lean_object* v_r_7214_; 
v_r_7214_ = lean_ctor_get(v_impl_7110_, 4);
lean_inc(v_r_7214_);
if (lean_obj_tag(v_r_7214_) == 0)
{
lean_object* v_k_7215_; lean_object* v_v_7216_; lean_object* v___x_7218_; uint8_t v_isShared_7219_; uint8_t v_isSharedCheck_7239_; 
v_k_7215_ = lean_ctor_get(v_impl_7110_, 1);
v_v_7216_ = lean_ctor_get(v_impl_7110_, 2);
v_isSharedCheck_7239_ = !lean_is_exclusive(v_impl_7110_);
if (v_isSharedCheck_7239_ == 0)
{
lean_object* v_unused_7240_; lean_object* v_unused_7241_; lean_object* v_unused_7242_; 
v_unused_7240_ = lean_ctor_get(v_impl_7110_, 4);
lean_dec(v_unused_7240_);
v_unused_7241_ = lean_ctor_get(v_impl_7110_, 3);
lean_dec(v_unused_7241_);
v_unused_7242_ = lean_ctor_get(v_impl_7110_, 0);
lean_dec(v_unused_7242_);
v___x_7218_ = v_impl_7110_;
v_isShared_7219_ = v_isSharedCheck_7239_;
goto v_resetjp_7217_;
}
else
{
lean_inc(v_v_7216_);
lean_inc(v_k_7215_);
lean_dec(v_impl_7110_);
v___x_7218_ = lean_box(0);
v_isShared_7219_ = v_isSharedCheck_7239_;
goto v_resetjp_7217_;
}
v_resetjp_7217_:
{
lean_object* v_k_7220_; lean_object* v_v_7221_; lean_object* v___x_7223_; uint8_t v_isShared_7224_; uint8_t v_isSharedCheck_7235_; 
v_k_7220_ = lean_ctor_get(v_r_7214_, 1);
v_v_7221_ = lean_ctor_get(v_r_7214_, 2);
v_isSharedCheck_7235_ = !lean_is_exclusive(v_r_7214_);
if (v_isSharedCheck_7235_ == 0)
{
lean_object* v_unused_7236_; lean_object* v_unused_7237_; lean_object* v_unused_7238_; 
v_unused_7236_ = lean_ctor_get(v_r_7214_, 4);
lean_dec(v_unused_7236_);
v_unused_7237_ = lean_ctor_get(v_r_7214_, 3);
lean_dec(v_unused_7237_);
v_unused_7238_ = lean_ctor_get(v_r_7214_, 0);
lean_dec(v_unused_7238_);
v___x_7223_ = v_r_7214_;
v_isShared_7224_ = v_isSharedCheck_7235_;
goto v_resetjp_7222_;
}
else
{
lean_inc(v_v_7221_);
lean_inc(v_k_7220_);
lean_dec(v_r_7214_);
v___x_7223_ = lean_box(0);
v_isShared_7224_ = v_isSharedCheck_7235_;
goto v_resetjp_7222_;
}
v_resetjp_7222_:
{
lean_object* v___x_7225_; lean_object* v___x_7227_; 
v___x_7225_ = lean_unsigned_to_nat(3u);
if (v_isShared_7224_ == 0)
{
lean_ctor_set(v___x_7223_, 4, v_l_7197_);
lean_ctor_set(v___x_7223_, 3, v_l_7197_);
lean_ctor_set(v___x_7223_, 2, v_v_7216_);
lean_ctor_set(v___x_7223_, 1, v_k_7215_);
lean_ctor_set(v___x_7223_, 0, v___x_7111_);
v___x_7227_ = v___x_7223_;
goto v_reusejp_7226_;
}
else
{
lean_object* v_reuseFailAlloc_7234_; 
v_reuseFailAlloc_7234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7234_, 0, v___x_7111_);
lean_ctor_set(v_reuseFailAlloc_7234_, 1, v_k_7215_);
lean_ctor_set(v_reuseFailAlloc_7234_, 2, v_v_7216_);
lean_ctor_set(v_reuseFailAlloc_7234_, 3, v_l_7197_);
lean_ctor_set(v_reuseFailAlloc_7234_, 4, v_l_7197_);
v___x_7227_ = v_reuseFailAlloc_7234_;
goto v_reusejp_7226_;
}
v_reusejp_7226_:
{
lean_object* v___x_7229_; 
if (v_isShared_7219_ == 0)
{
lean_ctor_set(v___x_7218_, 4, v_l_7197_);
lean_ctor_set(v___x_7218_, 2, v_v_6964_);
lean_ctor_set(v___x_7218_, 1, v_k_6963_);
lean_ctor_set(v___x_7218_, 0, v___x_7111_);
v___x_7229_ = v___x_7218_;
goto v_reusejp_7228_;
}
else
{
lean_object* v_reuseFailAlloc_7233_; 
v_reuseFailAlloc_7233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7233_, 0, v___x_7111_);
lean_ctor_set(v_reuseFailAlloc_7233_, 1, v_k_6963_);
lean_ctor_set(v_reuseFailAlloc_7233_, 2, v_v_6964_);
lean_ctor_set(v_reuseFailAlloc_7233_, 3, v_l_7197_);
lean_ctor_set(v_reuseFailAlloc_7233_, 4, v_l_7197_);
v___x_7229_ = v_reuseFailAlloc_7233_;
goto v_reusejp_7228_;
}
v_reusejp_7228_:
{
lean_object* v___x_7231_; 
if (v_isShared_6969_ == 0)
{
lean_ctor_set(v___x_6968_, 4, v___x_7229_);
lean_ctor_set(v___x_6968_, 3, v___x_7227_);
lean_ctor_set(v___x_6968_, 2, v_v_7221_);
lean_ctor_set(v___x_6968_, 1, v_k_7220_);
lean_ctor_set(v___x_6968_, 0, v___x_7225_);
v___x_7231_ = v___x_6968_;
goto v_reusejp_7230_;
}
else
{
lean_object* v_reuseFailAlloc_7232_; 
v_reuseFailAlloc_7232_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7232_, 0, v___x_7225_);
lean_ctor_set(v_reuseFailAlloc_7232_, 1, v_k_7220_);
lean_ctor_set(v_reuseFailAlloc_7232_, 2, v_v_7221_);
lean_ctor_set(v_reuseFailAlloc_7232_, 3, v___x_7227_);
lean_ctor_set(v_reuseFailAlloc_7232_, 4, v___x_7229_);
v___x_7231_ = v_reuseFailAlloc_7232_;
goto v_reusejp_7230_;
}
v_reusejp_7230_:
{
return v___x_7231_;
}
}
}
}
}
}
else
{
lean_object* v___x_7243_; lean_object* v___x_7245_; 
v___x_7243_ = lean_unsigned_to_nat(2u);
if (v_isShared_6969_ == 0)
{
lean_ctor_set(v___x_6968_, 4, v_r_7214_);
lean_ctor_set(v___x_6968_, 3, v_impl_7110_);
lean_ctor_set(v___x_6968_, 0, v___x_7243_);
v___x_7245_ = v___x_6968_;
goto v_reusejp_7244_;
}
else
{
lean_object* v_reuseFailAlloc_7246_; 
v_reuseFailAlloc_7246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7246_, 0, v___x_7243_);
lean_ctor_set(v_reuseFailAlloc_7246_, 1, v_k_6963_);
lean_ctor_set(v_reuseFailAlloc_7246_, 2, v_v_6964_);
lean_ctor_set(v_reuseFailAlloc_7246_, 3, v_impl_7110_);
lean_ctor_set(v_reuseFailAlloc_7246_, 4, v_r_7214_);
v___x_7245_ = v_reuseFailAlloc_7246_;
goto v_reusejp_7244_;
}
v_reusejp_7244_:
{
return v___x_7245_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_7248_; lean_object* v___x_7249_; 
v___x_7248_ = lean_unsigned_to_nat(1u);
v___x_7249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_7249_, 0, v___x_7248_);
lean_ctor_set(v___x_7249_, 1, v_k_6959_);
lean_ctor_set(v___x_7249_, 2, v_v_6960_);
lean_ctor_set(v___x_7249_, 3, v_t_6961_);
lean_ctor_set(v___x_7249_, 4, v_t_6961_);
return v___x_7249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(lean_object* v_lib_7250_, lean_object* v_ps_7251_, lean_object* v_v_7252_, lean_object* v_o_7253_){
_start:
{
lean_object* v_name_7254_; lean_object* v_deps_7255_; lean_object* v_o_7256_; uint8_t v___x_7257_; 
v_name_7254_ = lean_ctor_get(v_lib_7250_, 1);
lean_inc_ref(v_name_7254_);
v_deps_7255_ = lean_ctor_get(v_lib_7250_, 2);
lean_inc_ref(v_deps_7255_);
v_o_7256_ = lean_array_push(v_o_7253_, v_lib_7250_);
v___x_7257_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_name_7254_, v_v_7252_);
if (v___x_7257_ == 0)
{
uint8_t v___x_7258_; 
v___x_7258_ = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(v_name_7254_, v_ps_7251_);
if (v___x_7258_ == 0)
{
lean_object* v_ps_7259_; lean_object* v___y_7261_; 
lean_inc_ref(v_name_7254_);
v_ps_7259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_ps_7259_, 0, v_name_7254_);
lean_ctor_set(v_ps_7259_, 1, v_ps_7251_);
if (v___x_7257_ == 0)
{
lean_object* v___x_7275_; lean_object* v___x_7276_; 
v___x_7275_ = lean_box(0);
v___x_7276_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_name_7254_, v___x_7275_, v_v_7252_);
v___y_7261_ = v___x_7276_;
goto v___jp_7260_;
}
else
{
lean_dec_ref(v_name_7254_);
v___y_7261_ = v_v_7252_;
goto v___jp_7260_;
}
v___jp_7260_:
{
lean_object* v___x_7262_; lean_object* v___x_7263_; lean_object* v___x_7264_; uint8_t v___x_7265_; 
v___x_7262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7262_, 0, v___y_7261_);
lean_ctor_set(v___x_7262_, 1, v_o_7256_);
v___x_7263_ = lean_unsigned_to_nat(0u);
v___x_7264_ = lean_array_get_size(v_deps_7255_);
v___x_7265_ = lean_nat_dec_lt(v___x_7263_, v___x_7264_);
if (v___x_7265_ == 0)
{
lean_object* v___x_7266_; 
lean_dec_ref(v_ps_7259_);
lean_dec_ref(v_deps_7255_);
v___x_7266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7266_, 0, v___x_7262_);
return v___x_7266_;
}
else
{
uint8_t v___x_7267_; 
v___x_7267_ = lean_nat_dec_le(v___x_7264_, v___x_7264_);
if (v___x_7267_ == 0)
{
if (v___x_7265_ == 0)
{
lean_object* v___x_7268_; 
lean_dec_ref(v_ps_7259_);
lean_dec_ref(v_deps_7255_);
v___x_7268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7268_, 0, v___x_7262_);
return v___x_7268_;
}
else
{
size_t v___x_7269_; size_t v___x_7270_; lean_object* v___x_7271_; 
v___x_7269_ = ((size_t)0ULL);
v___x_7270_ = lean_usize_of_nat(v___x_7264_);
v___x_7271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7259_, v_deps_7255_, v___x_7269_, v___x_7270_, v___x_7262_);
lean_dec_ref(v_deps_7255_);
return v___x_7271_;
}
}
else
{
size_t v___x_7272_; size_t v___x_7273_; lean_object* v___x_7274_; 
v___x_7272_ = ((size_t)0ULL);
v___x_7273_ = lean_usize_of_nat(v___x_7264_);
v___x_7274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7259_, v_deps_7255_, v___x_7272_, v___x_7273_, v___x_7262_);
lean_dec_ref(v_deps_7255_);
return v___x_7274_;
}
}
}
}
else
{
lean_object* v___x_7277_; lean_object* v___x_7278_; 
lean_dec_ref(v_o_7256_);
lean_dec_ref(v_deps_7255_);
lean_dec(v_v_7252_);
v___x_7277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7277_, 0, v_name_7254_);
lean_ctor_set(v___x_7277_, 1, v_ps_7251_);
v___x_7278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7278_, 0, v___x_7277_);
return v___x_7278_;
}
}
else
{
lean_object* v___x_7279_; lean_object* v___x_7280_; 
lean_dec_ref(v_deps_7255_);
lean_dec_ref(v_name_7254_);
lean_dec(v_ps_7251_);
v___x_7279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7279_, 0, v_v_7252_);
lean_ctor_set(v___x_7279_, 1, v_o_7256_);
v___x_7280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7280_, 0, v___x_7279_);
return v___x_7280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(lean_object* v_ps_7281_, lean_object* v_as_7282_, size_t v_i_7283_, size_t v_stop_7284_, lean_object* v_b_7285_){
_start:
{
uint8_t v___x_7286_; 
v___x_7286_ = lean_usize_dec_eq(v_i_7283_, v_stop_7284_);
if (v___x_7286_ == 0)
{
lean_object* v_fst_7287_; lean_object* v_snd_7288_; lean_object* v___x_7289_; lean_object* v___x_7290_; 
v_fst_7287_ = lean_ctor_get(v_b_7285_, 0);
lean_inc(v_fst_7287_);
v_snd_7288_ = lean_ctor_get(v_b_7285_, 1);
lean_inc(v_snd_7288_);
lean_dec_ref(v_b_7285_);
v___x_7289_ = lean_array_uget_borrowed(v_as_7282_, v_i_7283_);
lean_inc(v_ps_7281_);
lean_inc(v___x_7289_);
v___x_7290_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(v___x_7289_, v_ps_7281_, v_fst_7287_, v_snd_7288_);
if (lean_obj_tag(v___x_7290_) == 0)
{
lean_dec(v_ps_7281_);
return v___x_7290_;
}
else
{
lean_object* v_a_7291_; size_t v___x_7292_; size_t v___x_7293_; 
v_a_7291_ = lean_ctor_get(v___x_7290_, 0);
lean_inc(v_a_7291_);
lean_dec_ref(v___x_7290_);
v___x_7292_ = ((size_t)1ULL);
v___x_7293_ = lean_usize_add(v_i_7283_, v___x_7292_);
v_i_7283_ = v___x_7293_;
v_b_7285_ = v_a_7291_;
goto _start;
}
}
else
{
lean_object* v___x_7295_; 
lean_dec(v_ps_7281_);
v___x_7295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7295_, 0, v_b_7285_);
return v___x_7295_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2___boxed(lean_object* v_ps_7296_, lean_object* v_as_7297_, lean_object* v_i_7298_, lean_object* v_stop_7299_, lean_object* v_b_7300_){
_start:
{
size_t v_i_boxed_7301_; size_t v_stop_boxed_7302_; lean_object* v_res_7303_; 
v_i_boxed_7301_ = lean_unbox_usize(v_i_7298_);
lean_dec(v_i_7298_);
v_stop_boxed_7302_ = lean_unbox_usize(v_stop_7299_);
lean_dec(v_stop_7299_);
v_res_7303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7296_, v_as_7297_, v_i_boxed_7301_, v_stop_boxed_7302_, v_b_7300_);
lean_dec_ref(v_as_7297_);
return v_res_7303_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(lean_object* v_00_u03b2_7304_, lean_object* v_k_7305_, lean_object* v_t_7306_){
_start:
{
uint8_t v___x_7307_; 
v___x_7307_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_k_7305_, v_t_7306_);
return v___x_7307_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___boxed(lean_object* v_00_u03b2_7308_, lean_object* v_k_7309_, lean_object* v_t_7310_){
_start:
{
uint8_t v_res_7311_; lean_object* v_r_7312_; 
v_res_7311_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(v_00_u03b2_7308_, v_k_7309_, v_t_7310_);
lean_dec(v_t_7310_);
lean_dec_ref(v_k_7309_);
v_r_7312_ = lean_box(v_res_7311_);
return v_r_7312_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3(lean_object* v_00_u03b2_7313_, lean_object* v_k_7314_, lean_object* v_v_7315_, lean_object* v_t_7316_, lean_object* v_hl_7317_){
_start:
{
lean_object* v___x_7318_; 
v___x_7318_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7314_, v_v_7315_, v_t_7316_);
return v___x_7318_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0(lean_object* v_a_7320_, lean_object* v_a_7321_){
_start:
{
if (lean_obj_tag(v_a_7320_) == 0)
{
lean_object* v___x_7322_; 
v___x_7322_ = l_List_reverse___redArg(v_a_7321_);
return v___x_7322_;
}
else
{
lean_object* v_head_7323_; lean_object* v_tail_7324_; lean_object* v___x_7326_; uint8_t v_isShared_7327_; uint8_t v_isSharedCheck_7334_; 
v_head_7323_ = lean_ctor_get(v_a_7320_, 0);
v_tail_7324_ = lean_ctor_get(v_a_7320_, 1);
v_isSharedCheck_7334_ = !lean_is_exclusive(v_a_7320_);
if (v_isSharedCheck_7334_ == 0)
{
v___x_7326_ = v_a_7320_;
v_isShared_7327_ = v_isSharedCheck_7334_;
goto v_resetjp_7325_;
}
else
{
lean_inc(v_tail_7324_);
lean_inc(v_head_7323_);
lean_dec(v_a_7320_);
v___x_7326_ = lean_box(0);
v_isShared_7327_ = v_isSharedCheck_7334_;
goto v_resetjp_7325_;
}
v_resetjp_7325_:
{
lean_object* v___x_7328_; lean_object* v___x_7329_; lean_object* v___x_7331_; 
v___x_7328_ = ((lean_object*)(l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0));
v___x_7329_ = lean_string_append(v___x_7328_, v_head_7323_);
lean_dec(v_head_7323_);
if (v_isShared_7327_ == 0)
{
lean_ctor_set(v___x_7326_, 1, v_a_7321_);
lean_ctor_set(v___x_7326_, 0, v___x_7329_);
v___x_7331_ = v___x_7326_;
goto v_reusejp_7330_;
}
else
{
lean_object* v_reuseFailAlloc_7333_; 
v_reuseFailAlloc_7333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7333_, 0, v___x_7329_);
lean_ctor_set(v_reuseFailAlloc_7333_, 1, v_a_7321_);
v___x_7331_ = v_reuseFailAlloc_7333_;
goto v_reusejp_7330_;
}
v_reusejp_7330_:
{
v_a_7320_ = v_tail_7324_;
v_a_7321_ = v___x_7331_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(lean_object* v_cycle_7335_){
_start:
{
lean_object* v___x_7336_; lean_object* v___x_7337_; lean_object* v___x_7338_; lean_object* v___x_7339_; 
v___x_7336_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__1));
v___x_7337_ = lean_box(0);
v___x_7338_ = l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0(v_cycle_7335_, v___x_7337_);
v___x_7339_ = l_String_intercalate(v___x_7336_, v___x_7338_);
return v___x_7339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(lean_object* v_as_7340_, size_t v_i_7341_, size_t v_stop_7342_, lean_object* v_b_7343_){
_start:
{
uint8_t v___x_7344_; 
v___x_7344_ = lean_usize_dec_eq(v_i_7341_, v_stop_7342_);
if (v___x_7344_ == 0)
{
lean_object* v_fst_7345_; lean_object* v_snd_7346_; lean_object* v___x_7347_; lean_object* v___x_7348_; lean_object* v___x_7349_; 
v_fst_7345_ = lean_ctor_get(v_b_7343_, 0);
lean_inc(v_fst_7345_);
v_snd_7346_ = lean_ctor_get(v_b_7343_, 1);
lean_inc(v_snd_7346_);
lean_dec_ref(v_b_7343_);
v___x_7347_ = lean_array_uget_borrowed(v_as_7340_, v_i_7341_);
v___x_7348_ = lean_box(0);
lean_inc(v___x_7347_);
v___x_7349_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(v___x_7347_, v___x_7348_, v_fst_7345_, v_snd_7346_);
if (lean_obj_tag(v___x_7349_) == 0)
{
return v___x_7349_;
}
else
{
lean_object* v_a_7350_; size_t v___x_7351_; size_t v___x_7352_; 
v_a_7350_ = lean_ctor_get(v___x_7349_, 0);
lean_inc(v_a_7350_);
lean_dec_ref(v___x_7349_);
v___x_7351_ = ((size_t)1ULL);
v___x_7352_ = lean_usize_add(v_i_7341_, v___x_7351_);
v_i_7341_ = v___x_7352_;
v_b_7343_ = v_a_7350_;
goto _start;
}
}
else
{
lean_object* v___x_7354_; 
v___x_7354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7354_, 0, v_b_7343_);
return v___x_7354_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1___boxed(lean_object* v_as_7355_, lean_object* v_i_7356_, lean_object* v_stop_7357_, lean_object* v_b_7358_){
_start:
{
size_t v_i_boxed_7359_; size_t v_stop_boxed_7360_; lean_object* v_res_7361_; 
v_i_boxed_7359_ = lean_unbox_usize(v_i_7356_);
lean_dec(v_i_7356_);
v_stop_boxed_7360_ = lean_unbox_usize(v_stop_7357_);
lean_dec(v_stop_7357_);
v_res_7361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(v_as_7355_, v_i_boxed_7359_, v_stop_boxed_7360_, v_b_7358_);
lean_dec_ref(v_as_7355_);
return v_res_7361_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(lean_object* v_libs_7368_, lean_object* v_a_7369_){
_start:
{
lean_object* v_snd_7372_; lean_object* v___y_7375_; lean_object* v___x_7399_; lean_object* v___x_7400_; lean_object* v___x_7401_; uint8_t v___x_7402_; 
v___x_7399_ = lean_unsigned_to_nat(0u);
v___x_7400_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1));
v___x_7401_ = lean_array_get_size(v_libs_7368_);
v___x_7402_ = lean_nat_dec_lt(v___x_7399_, v___x_7401_);
if (v___x_7402_ == 0)
{
v_snd_7372_ = v___x_7400_;
goto v___jp_7371_;
}
else
{
lean_object* v___x_7403_; uint8_t v___x_7404_; 
v___x_7403_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2));
v___x_7404_ = lean_nat_dec_le(v___x_7401_, v___x_7401_);
if (v___x_7404_ == 0)
{
if (v___x_7402_ == 0)
{
v_snd_7372_ = v___x_7400_;
goto v___jp_7371_;
}
else
{
size_t v___x_7405_; size_t v___x_7406_; lean_object* v___x_7407_; 
v___x_7405_ = ((size_t)0ULL);
v___x_7406_ = lean_usize_of_nat(v___x_7401_);
v___x_7407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(v_libs_7368_, v___x_7405_, v___x_7406_, v___x_7403_);
v___y_7375_ = v___x_7407_;
goto v___jp_7374_;
}
}
else
{
size_t v___x_7408_; size_t v___x_7409_; lean_object* v___x_7410_; 
v___x_7408_ = ((size_t)0ULL);
v___x_7409_ = lean_usize_of_nat(v___x_7401_);
v___x_7410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(v_libs_7368_, v___x_7408_, v___x_7409_, v___x_7403_);
v___y_7375_ = v___x_7410_;
goto v___jp_7374_;
}
}
v___jp_7371_:
{
lean_object* v___x_7373_; 
v___x_7373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7373_, 0, v_snd_7372_);
lean_ctor_set(v___x_7373_, 1, v_a_7369_);
return v___x_7373_;
}
v___jp_7374_:
{
if (lean_obj_tag(v___y_7375_) == 0)
{
lean_object* v_a_7376_; lean_object* v_log_7377_; uint8_t v_action_7378_; uint8_t v_wantsRebuild_7379_; lean_object* v_trace_7380_; lean_object* v_buildTime_7381_; lean_object* v___x_7383_; uint8_t v_isShared_7384_; uint8_t v_isSharedCheck_7396_; 
v_a_7376_ = lean_ctor_get(v___y_7375_, 0);
lean_inc(v_a_7376_);
lean_dec_ref(v___y_7375_);
v_log_7377_ = lean_ctor_get(v_a_7369_, 0);
v_action_7378_ = lean_ctor_get_uint8(v_a_7369_, sizeof(void*)*3);
v_wantsRebuild_7379_ = lean_ctor_get_uint8(v_a_7369_, sizeof(void*)*3 + 1);
v_trace_7380_ = lean_ctor_get(v_a_7369_, 1);
v_buildTime_7381_ = lean_ctor_get(v_a_7369_, 2);
v_isSharedCheck_7396_ = !lean_is_exclusive(v_a_7369_);
if (v_isSharedCheck_7396_ == 0)
{
v___x_7383_ = v_a_7369_;
v_isShared_7384_ = v_isSharedCheck_7396_;
goto v_resetjp_7382_;
}
else
{
lean_inc(v_buildTime_7381_);
lean_inc(v_trace_7380_);
lean_inc(v_log_7377_);
lean_dec(v_a_7369_);
v___x_7383_ = lean_box(0);
v_isShared_7384_ = v_isSharedCheck_7396_;
goto v_resetjp_7382_;
}
v_resetjp_7382_:
{
lean_object* v___x_7385_; lean_object* v___x_7386_; lean_object* v___x_7387_; uint8_t v___x_7388_; lean_object* v___x_7389_; lean_object* v___x_7390_; lean_object* v___x_7391_; lean_object* v___x_7393_; 
v___x_7385_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0));
v___x_7386_ = l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(v_a_7376_);
v___x_7387_ = lean_string_append(v___x_7385_, v___x_7386_);
lean_dec_ref(v___x_7386_);
v___x_7388_ = 3;
v___x_7389_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7389_, 0, v___x_7387_);
lean_ctor_set_uint8(v___x_7389_, sizeof(void*)*1, v___x_7388_);
v___x_7390_ = lean_array_get_size(v_log_7377_);
v___x_7391_ = lean_array_push(v_log_7377_, v___x_7389_);
if (v_isShared_7384_ == 0)
{
lean_ctor_set(v___x_7383_, 0, v___x_7391_);
v___x_7393_ = v___x_7383_;
goto v_reusejp_7392_;
}
else
{
lean_object* v_reuseFailAlloc_7395_; 
v_reuseFailAlloc_7395_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7395_, 0, v___x_7391_);
lean_ctor_set(v_reuseFailAlloc_7395_, 1, v_trace_7380_);
lean_ctor_set(v_reuseFailAlloc_7395_, 2, v_buildTime_7381_);
lean_ctor_set_uint8(v_reuseFailAlloc_7395_, sizeof(void*)*3, v_action_7378_);
lean_ctor_set_uint8(v_reuseFailAlloc_7395_, sizeof(void*)*3 + 1, v_wantsRebuild_7379_);
v___x_7393_ = v_reuseFailAlloc_7395_;
goto v_reusejp_7392_;
}
v_reusejp_7392_:
{
lean_object* v___x_7394_; 
v___x_7394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7394_, 0, v___x_7390_);
lean_ctor_set(v___x_7394_, 1, v___x_7393_);
return v___x_7394_;
}
}
}
else
{
lean_object* v_a_7397_; lean_object* v_snd_7398_; 
v_a_7397_ = lean_ctor_get(v___y_7375_, 0);
lean_inc(v_a_7397_);
lean_dec_ref(v___y_7375_);
v_snd_7398_ = lean_ctor_get(v_a_7397_, 1);
lean_inc(v_snd_7398_);
lean_dec(v_a_7397_);
v_snd_7372_ = v_snd_7398_;
goto v___jp_7371_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___boxed(lean_object* v_libs_7411_, lean_object* v_a_7412_, lean_object* v_a_7413_){
_start:
{
lean_object* v_res_7414_; 
v_res_7414_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7411_, v_a_7412_);
lean_dec_ref(v_libs_7411_);
return v_res_7414_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder(lean_object* v_libs_7415_, lean_object* v_a_7416_, lean_object* v_a_7417_, lean_object* v_a_7418_, lean_object* v_a_7419_, lean_object* v_a_7420_, lean_object* v_a_7421_){
_start:
{
lean_object* v___x_7423_; 
v___x_7423_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7415_, v_a_7421_);
return v___x_7423_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___boxed(lean_object* v_libs_7424_, lean_object* v_a_7425_, lean_object* v_a_7426_, lean_object* v_a_7427_, lean_object* v_a_7428_, lean_object* v_a_7429_, lean_object* v_a_7430_, lean_object* v_a_7431_){
_start:
{
lean_object* v_res_7432_; 
v_res_7432_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder(v_libs_7424_, v_a_7425_, v_a_7426_, v_a_7427_, v_a_7428_, v_a_7429_, v_a_7430_);
lean_dec_ref(v_a_7429_);
lean_dec(v_a_7428_);
lean_dec(v_a_7427_);
lean_dec(v_a_7426_);
lean_dec_ref(v_a_7425_);
lean_dec_ref(v_libs_7424_);
return v_res_7432_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0(lean_object* v_objs_7433_, lean_object* v_weakArgs_7434_, lean_object* v_traceArgs_7435_, lean_object* v_libFile_7436_, lean_object* v_linker_7437_, lean_object* v_libs_7438_, lean_object* v___y_7439_, lean_object* v___y_7440_, lean_object* v___y_7441_, lean_object* v___y_7442_, lean_object* v___y_7443_, lean_object* v___y_7444_){
_start:
{
lean_object* v_log_7446_; uint8_t v_action_7447_; uint8_t v_wantsRebuild_7448_; lean_object* v_trace_7449_; lean_object* v_buildTime_7450_; lean_object* v___x_7452_; uint8_t v_isShared_7453_; uint8_t v_isSharedCheck_7482_; 
v_log_7446_ = lean_ctor_get(v___y_7444_, 0);
v_action_7447_ = lean_ctor_get_uint8(v___y_7444_, sizeof(void*)*3);
v_wantsRebuild_7448_ = lean_ctor_get_uint8(v___y_7444_, sizeof(void*)*3 + 1);
v_trace_7449_ = lean_ctor_get(v___y_7444_, 1);
v_buildTime_7450_ = lean_ctor_get(v___y_7444_, 2);
v_isSharedCheck_7482_ = !lean_is_exclusive(v___y_7444_);
if (v_isSharedCheck_7482_ == 0)
{
v___x_7452_ = v___y_7444_;
v_isShared_7453_ = v_isSharedCheck_7482_;
goto v_resetjp_7451_;
}
else
{
lean_inc(v_buildTime_7450_);
lean_inc(v_trace_7449_);
lean_inc(v_log_7446_);
lean_dec(v___y_7444_);
v___x_7452_ = lean_box(0);
v_isShared_7453_ = v_isSharedCheck_7482_;
goto v_resetjp_7451_;
}
v_resetjp_7451_:
{
lean_object* v___x_7454_; lean_object* v___x_7455_; lean_object* v___x_7456_; lean_object* v___x_7457_; 
v___x_7454_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7433_, v_libs_7438_);
v___x_7455_ = l_Array_append___redArg(v___x_7454_, v_weakArgs_7434_);
v___x_7456_ = l_Array_append___redArg(v___x_7455_, v_traceArgs_7435_);
v___x_7457_ = l_Lake_compileSharedLib(v_libFile_7436_, v___x_7456_, v_linker_7437_, v_log_7446_);
lean_dec_ref(v___x_7456_);
if (lean_obj_tag(v___x_7457_) == 0)
{
lean_object* v_a_7458_; lean_object* v_a_7459_; lean_object* v___x_7461_; uint8_t v_isShared_7462_; uint8_t v_isSharedCheck_7469_; 
v_a_7458_ = lean_ctor_get(v___x_7457_, 0);
v_a_7459_ = lean_ctor_get(v___x_7457_, 1);
v_isSharedCheck_7469_ = !lean_is_exclusive(v___x_7457_);
if (v_isSharedCheck_7469_ == 0)
{
v___x_7461_ = v___x_7457_;
v_isShared_7462_ = v_isSharedCheck_7469_;
goto v_resetjp_7460_;
}
else
{
lean_inc(v_a_7459_);
lean_inc(v_a_7458_);
lean_dec(v___x_7457_);
v___x_7461_ = lean_box(0);
v_isShared_7462_ = v_isSharedCheck_7469_;
goto v_resetjp_7460_;
}
v_resetjp_7460_:
{
lean_object* v___x_7464_; 
if (v_isShared_7453_ == 0)
{
lean_ctor_set(v___x_7452_, 0, v_a_7459_);
v___x_7464_ = v___x_7452_;
goto v_reusejp_7463_;
}
else
{
lean_object* v_reuseFailAlloc_7468_; 
v_reuseFailAlloc_7468_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7468_, 0, v_a_7459_);
lean_ctor_set(v_reuseFailAlloc_7468_, 1, v_trace_7449_);
lean_ctor_set(v_reuseFailAlloc_7468_, 2, v_buildTime_7450_);
lean_ctor_set_uint8(v_reuseFailAlloc_7468_, sizeof(void*)*3, v_action_7447_);
lean_ctor_set_uint8(v_reuseFailAlloc_7468_, sizeof(void*)*3 + 1, v_wantsRebuild_7448_);
v___x_7464_ = v_reuseFailAlloc_7468_;
goto v_reusejp_7463_;
}
v_reusejp_7463_:
{
lean_object* v___x_7466_; 
if (v_isShared_7462_ == 0)
{
lean_ctor_set(v___x_7461_, 1, v___x_7464_);
v___x_7466_ = v___x_7461_;
goto v_reusejp_7465_;
}
else
{
lean_object* v_reuseFailAlloc_7467_; 
v_reuseFailAlloc_7467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7467_, 0, v_a_7458_);
lean_ctor_set(v_reuseFailAlloc_7467_, 1, v___x_7464_);
v___x_7466_ = v_reuseFailAlloc_7467_;
goto v_reusejp_7465_;
}
v_reusejp_7465_:
{
return v___x_7466_;
}
}
}
}
else
{
lean_object* v_a_7470_; lean_object* v_a_7471_; lean_object* v___x_7473_; uint8_t v_isShared_7474_; uint8_t v_isSharedCheck_7481_; 
v_a_7470_ = lean_ctor_get(v___x_7457_, 0);
v_a_7471_ = lean_ctor_get(v___x_7457_, 1);
v_isSharedCheck_7481_ = !lean_is_exclusive(v___x_7457_);
if (v_isSharedCheck_7481_ == 0)
{
v___x_7473_ = v___x_7457_;
v_isShared_7474_ = v_isSharedCheck_7481_;
goto v_resetjp_7472_;
}
else
{
lean_inc(v_a_7471_);
lean_inc(v_a_7470_);
lean_dec(v___x_7457_);
v___x_7473_ = lean_box(0);
v_isShared_7474_ = v_isSharedCheck_7481_;
goto v_resetjp_7472_;
}
v_resetjp_7472_:
{
lean_object* v___x_7476_; 
if (v_isShared_7453_ == 0)
{
lean_ctor_set(v___x_7452_, 0, v_a_7471_);
v___x_7476_ = v___x_7452_;
goto v_reusejp_7475_;
}
else
{
lean_object* v_reuseFailAlloc_7480_; 
v_reuseFailAlloc_7480_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7480_, 0, v_a_7471_);
lean_ctor_set(v_reuseFailAlloc_7480_, 1, v_trace_7449_);
lean_ctor_set(v_reuseFailAlloc_7480_, 2, v_buildTime_7450_);
lean_ctor_set_uint8(v_reuseFailAlloc_7480_, sizeof(void*)*3, v_action_7447_);
lean_ctor_set_uint8(v_reuseFailAlloc_7480_, sizeof(void*)*3 + 1, v_wantsRebuild_7448_);
v___x_7476_ = v_reuseFailAlloc_7480_;
goto v_reusejp_7475_;
}
v_reusejp_7475_:
{
lean_object* v___x_7478_; 
if (v_isShared_7474_ == 0)
{
lean_ctor_set(v___x_7473_, 1, v___x_7476_);
v___x_7478_ = v___x_7473_;
goto v_reusejp_7477_;
}
else
{
lean_object* v_reuseFailAlloc_7479_; 
v_reuseFailAlloc_7479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7479_, 0, v_a_7470_);
lean_ctor_set(v_reuseFailAlloc_7479_, 1, v___x_7476_);
v___x_7478_ = v_reuseFailAlloc_7479_;
goto v_reusejp_7477_;
}
v_reusejp_7477_:
{
return v___x_7478_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object* v_objs_7483_, lean_object* v_weakArgs_7484_, lean_object* v_traceArgs_7485_, lean_object* v_libFile_7486_, lean_object* v_linker_7487_, lean_object* v_libs_7488_, lean_object* v___y_7489_, lean_object* v___y_7490_, lean_object* v___y_7491_, lean_object* v___y_7492_, lean_object* v___y_7493_, lean_object* v___y_7494_, lean_object* v___y_7495_){
_start:
{
lean_object* v_res_7496_; 
v_res_7496_ = l_Lake_buildSharedLib___lam__0(v_objs_7483_, v_weakArgs_7484_, v_traceArgs_7485_, v_libFile_7486_, v_linker_7487_, v_libs_7488_, v___y_7489_, v___y_7490_, v___y_7491_, v___y_7492_, v___y_7493_, v___y_7494_);
lean_dec_ref(v___y_7493_);
lean_dec(v___y_7492_);
lean_dec(v___y_7491_);
lean_dec(v___y_7490_);
lean_dec_ref(v___y_7489_);
lean_dec_ref(v_libs_7488_);
lean_dec_ref(v_traceArgs_7485_);
lean_dec_ref(v_weakArgs_7484_);
lean_dec_ref(v_objs_7483_);
return v_res_7496_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1(uint8_t v_linkDeps_7497_, lean_object* v___x_7498_, lean_object* v___f_7499_, lean_object* v_libs_7500_, lean_object* v___y_7501_, lean_object* v___y_7502_, lean_object* v___y_7503_, lean_object* v___y_7504_, lean_object* v___y_7505_, lean_object* v___y_7506_){
_start:
{
if (v_linkDeps_7497_ == 0)
{
lean_object* v___x_7508_; lean_object* v___x_7509_; 
v___x_7508_ = lean_mk_empty_array_with_capacity(v___x_7498_);
lean_inc_ref(v___y_7505_);
lean_inc(v___y_7504_);
lean_inc(v___y_7503_);
lean_inc(v___y_7502_);
v___x_7509_ = lean_apply_8(v___f_7499_, v___x_7508_, v___y_7501_, v___y_7502_, v___y_7503_, v___y_7504_, v___y_7505_, v___y_7506_, lean_box(0));
return v___x_7509_;
}
else
{
lean_object* v___x_7510_; 
v___x_7510_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7500_, v___y_7506_);
if (lean_obj_tag(v___x_7510_) == 0)
{
lean_object* v_a_7511_; lean_object* v_a_7512_; lean_object* v___x_7513_; 
v_a_7511_ = lean_ctor_get(v___x_7510_, 0);
lean_inc(v_a_7511_);
v_a_7512_ = lean_ctor_get(v___x_7510_, 1);
lean_inc(v_a_7512_);
lean_dec_ref(v___x_7510_);
lean_inc_ref(v___y_7505_);
lean_inc(v___y_7504_);
lean_inc(v___y_7503_);
lean_inc(v___y_7502_);
v___x_7513_ = lean_apply_8(v___f_7499_, v_a_7511_, v___y_7501_, v___y_7502_, v___y_7503_, v___y_7504_, v___y_7505_, v_a_7512_, lean_box(0));
return v___x_7513_;
}
else
{
lean_object* v_a_7514_; lean_object* v_a_7515_; lean_object* v___x_7517_; uint8_t v_isShared_7518_; uint8_t v_isSharedCheck_7522_; 
lean_dec_ref(v___y_7501_);
lean_dec_ref(v___f_7499_);
v_a_7514_ = lean_ctor_get(v___x_7510_, 0);
v_a_7515_ = lean_ctor_get(v___x_7510_, 1);
v_isSharedCheck_7522_ = !lean_is_exclusive(v___x_7510_);
if (v_isSharedCheck_7522_ == 0)
{
v___x_7517_ = v___x_7510_;
v_isShared_7518_ = v_isSharedCheck_7522_;
goto v_resetjp_7516_;
}
else
{
lean_inc(v_a_7515_);
lean_inc(v_a_7514_);
lean_dec(v___x_7510_);
v___x_7517_ = lean_box(0);
v_isShared_7518_ = v_isSharedCheck_7522_;
goto v_resetjp_7516_;
}
v_resetjp_7516_:
{
lean_object* v___x_7520_; 
if (v_isShared_7518_ == 0)
{
v___x_7520_ = v___x_7517_;
goto v_reusejp_7519_;
}
else
{
lean_object* v_reuseFailAlloc_7521_; 
v_reuseFailAlloc_7521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7521_, 0, v_a_7514_);
lean_ctor_set(v_reuseFailAlloc_7521_, 1, v_a_7515_);
v___x_7520_ = v_reuseFailAlloc_7521_;
goto v_reusejp_7519_;
}
v_reusejp_7519_:
{
return v___x_7520_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1___boxed(lean_object* v_linkDeps_7523_, lean_object* v___x_7524_, lean_object* v___f_7525_, lean_object* v_libs_7526_, lean_object* v___y_7527_, lean_object* v___y_7528_, lean_object* v___y_7529_, lean_object* v___y_7530_, lean_object* v___y_7531_, lean_object* v___y_7532_, lean_object* v___y_7533_){
_start:
{
uint8_t v_linkDeps_boxed_7534_; lean_object* v_res_7535_; 
v_linkDeps_boxed_7534_ = lean_unbox(v_linkDeps_7523_);
v_res_7535_ = l_Lake_buildSharedLib___lam__1(v_linkDeps_boxed_7534_, v___x_7524_, v___f_7525_, v_libs_7526_, v___y_7527_, v___y_7528_, v___y_7529_, v___y_7530_, v___y_7531_, v___y_7532_);
lean_dec_ref(v___y_7531_);
lean_dec(v___y_7530_);
lean_dec(v___y_7529_);
lean_dec(v___y_7528_);
lean_dec_ref(v_libs_7526_);
lean_dec(v___x_7524_);
return v_res_7535_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2(lean_object* v_traceArgs_7536_, lean_object* v_extraDepTrace_7537_, uint8_t v_linkDeps_7538_, lean_object* v___f_7539_, lean_object* v_libFile_7540_, lean_object* v_libName_7541_, uint8_t v_plugin_7542_, lean_object* v_libs_7543_, lean_object* v___y_7544_, lean_object* v___y_7545_, lean_object* v___y_7546_, lean_object* v___y_7547_, lean_object* v___y_7548_, lean_object* v___y_7549_){
_start:
{
uint64_t v___y_7552_; uint64_t v___x_7629_; lean_object* v___x_7630_; lean_object* v___x_7631_; uint8_t v___x_7632_; 
v___x_7629_ = l_Lake_Hash_nil;
v___x_7630_ = lean_unsigned_to_nat(0u);
v___x_7631_ = lean_array_get_size(v_traceArgs_7536_);
v___x_7632_ = lean_nat_dec_lt(v___x_7630_, v___x_7631_);
if (v___x_7632_ == 0)
{
v___y_7552_ = v___x_7629_;
goto v___jp_7551_;
}
else
{
uint8_t v___x_7633_; 
v___x_7633_ = lean_nat_dec_le(v___x_7631_, v___x_7631_);
if (v___x_7633_ == 0)
{
if (v___x_7632_ == 0)
{
v___y_7552_ = v___x_7629_;
goto v___jp_7551_;
}
else
{
size_t v___x_7634_; size_t v___x_7635_; uint64_t v___x_7636_; 
v___x_7634_ = ((size_t)0ULL);
v___x_7635_ = lean_usize_of_nat(v___x_7631_);
v___x_7636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7536_, v___x_7634_, v___x_7635_, v___x_7629_);
v___y_7552_ = v___x_7636_;
goto v___jp_7551_;
}
}
else
{
size_t v___x_7637_; size_t v___x_7638_; uint64_t v___x_7639_; 
v___x_7637_ = ((size_t)0ULL);
v___x_7638_ = lean_usize_of_nat(v___x_7631_);
v___x_7639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7536_, v___x_7637_, v___x_7638_, v___x_7629_);
v___y_7552_ = v___x_7639_;
goto v___jp_7551_;
}
}
v___jp_7551_:
{
lean_object* v_log_7553_; uint8_t v_action_7554_; uint8_t v_wantsRebuild_7555_; lean_object* v_trace_7556_; lean_object* v_buildTime_7557_; lean_object* v___x_7559_; uint8_t v_isShared_7560_; uint8_t v_isSharedCheck_7628_; 
v_log_7553_ = lean_ctor_get(v___y_7549_, 0);
v_action_7554_ = lean_ctor_get_uint8(v___y_7549_, sizeof(void*)*3);
v_wantsRebuild_7555_ = lean_ctor_get_uint8(v___y_7549_, sizeof(void*)*3 + 1);
v_trace_7556_ = lean_ctor_get(v___y_7549_, 1);
v_buildTime_7557_ = lean_ctor_get(v___y_7549_, 2);
v_isSharedCheck_7628_ = !lean_is_exclusive(v___y_7549_);
if (v_isSharedCheck_7628_ == 0)
{
v___x_7559_ = v___y_7549_;
v_isShared_7560_ = v_isSharedCheck_7628_;
goto v_resetjp_7558_;
}
else
{
lean_inc(v_buildTime_7557_);
lean_inc(v_trace_7556_);
lean_inc(v_log_7553_);
lean_dec(v___y_7549_);
v___x_7559_ = lean_box(0);
v_isShared_7560_ = v_isSharedCheck_7628_;
goto v_resetjp_7558_;
}
v_resetjp_7558_:
{
lean_object* v___x_7561_; lean_object* v___x_7562_; lean_object* v___x_7563_; lean_object* v___x_7564_; lean_object* v___x_7565_; lean_object* v___x_7566_; lean_object* v___x_7567_; lean_object* v___x_7568_; lean_object* v___x_7569_; lean_object* v___x_7570_; lean_object* v___x_7571_; lean_object* v___x_7572_; lean_object* v___x_7573_; lean_object* v___x_7575_; 
v___x_7561_ = lean_unsigned_to_nat(0u);
v___x_7562_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_7563_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_7564_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_7565_ = lean_array_to_list(v_traceArgs_7536_);
v___x_7566_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_7565_);
lean_dec(v___x_7565_);
v___x_7567_ = lean_string_append(v___x_7564_, v___x_7566_);
lean_dec_ref(v___x_7566_);
v___x_7568_ = lean_string_append(v___x_7563_, v___x_7567_);
lean_dec_ref(v___x_7567_);
v___x_7569_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_7570_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_7570_, 0, v___x_7568_);
lean_ctor_set(v___x_7570_, 1, v___x_7562_);
lean_ctor_set(v___x_7570_, 2, v___x_7569_);
lean_ctor_set_uint64(v___x_7570_, sizeof(void*)*3, v___y_7552_);
v___x_7571_ = l_Lake_BuildTrace_mix(v_trace_7556_, v___x_7570_);
v___x_7572_ = l_Lake_platformTrace;
v___x_7573_ = l_Lake_BuildTrace_mix(v___x_7571_, v___x_7572_);
if (v_isShared_7560_ == 0)
{
lean_ctor_set(v___x_7559_, 1, v___x_7573_);
v___x_7575_ = v___x_7559_;
goto v_reusejp_7574_;
}
else
{
lean_object* v_reuseFailAlloc_7627_; 
v_reuseFailAlloc_7627_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7627_, 0, v_log_7553_);
lean_ctor_set(v_reuseFailAlloc_7627_, 1, v___x_7573_);
lean_ctor_set(v_reuseFailAlloc_7627_, 2, v_buildTime_7557_);
lean_ctor_set_uint8(v_reuseFailAlloc_7627_, sizeof(void*)*3, v_action_7554_);
lean_ctor_set_uint8(v_reuseFailAlloc_7627_, sizeof(void*)*3 + 1, v_wantsRebuild_7555_);
v___x_7575_ = v_reuseFailAlloc_7627_;
goto v_reusejp_7574_;
}
v_reusejp_7574_:
{
lean_object* v___x_7576_; 
lean_inc_ref(v___y_7548_);
lean_inc(v___y_7547_);
lean_inc(v___y_7546_);
lean_inc(v___y_7545_);
lean_inc_ref(v___y_7544_);
v___x_7576_ = lean_apply_7(v_extraDepTrace_7537_, v___y_7544_, v___y_7545_, v___y_7546_, v___y_7547_, v___y_7548_, v___x_7575_, lean_box(0));
if (lean_obj_tag(v___x_7576_) == 0)
{
lean_object* v_a_7577_; lean_object* v_a_7578_; lean_object* v_log_7579_; uint8_t v_action_7580_; uint8_t v_wantsRebuild_7581_; lean_object* v_trace_7582_; lean_object* v_buildTime_7583_; lean_object* v___x_7585_; uint8_t v_isShared_7586_; uint8_t v_isSharedCheck_7617_; 
v_a_7577_ = lean_ctor_get(v___x_7576_, 1);
lean_inc(v_a_7577_);
v_a_7578_ = lean_ctor_get(v___x_7576_, 0);
lean_inc(v_a_7578_);
lean_dec_ref(v___x_7576_);
v_log_7579_ = lean_ctor_get(v_a_7577_, 0);
v_action_7580_ = lean_ctor_get_uint8(v_a_7577_, sizeof(void*)*3);
v_wantsRebuild_7581_ = lean_ctor_get_uint8(v_a_7577_, sizeof(void*)*3 + 1);
v_trace_7582_ = lean_ctor_get(v_a_7577_, 1);
v_buildTime_7583_ = lean_ctor_get(v_a_7577_, 2);
v_isSharedCheck_7617_ = !lean_is_exclusive(v_a_7577_);
if (v_isSharedCheck_7617_ == 0)
{
v___x_7585_ = v_a_7577_;
v_isShared_7586_ = v_isSharedCheck_7617_;
goto v_resetjp_7584_;
}
else
{
lean_inc(v_buildTime_7583_);
lean_inc(v_trace_7582_);
lean_inc(v_log_7579_);
lean_dec(v_a_7577_);
v___x_7585_ = lean_box(0);
v_isShared_7586_ = v_isSharedCheck_7617_;
goto v_resetjp_7584_;
}
v_resetjp_7584_:
{
lean_object* v___x_7587_; lean_object* v___y_7588_; lean_object* v___x_7589_; lean_object* v___x_7591_; 
v___x_7587_ = lean_box(v_linkDeps_7538_);
lean_inc_ref(v_libs_7543_);
v___y_7588_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__1___boxed), 11, 4);
lean_closure_set(v___y_7588_, 0, v___x_7587_);
lean_closure_set(v___y_7588_, 1, v___x_7561_);
lean_closure_set(v___y_7588_, 2, v___f_7539_);
lean_closure_set(v___y_7588_, 3, v_libs_7543_);
v___x_7589_ = l_Lake_BuildTrace_mix(v_trace_7582_, v_a_7578_);
if (v_isShared_7586_ == 0)
{
lean_ctor_set(v___x_7585_, 1, v___x_7589_);
v___x_7591_ = v___x_7585_;
goto v_reusejp_7590_;
}
else
{
lean_object* v_reuseFailAlloc_7616_; 
v_reuseFailAlloc_7616_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7616_, 0, v_log_7579_);
lean_ctor_set(v_reuseFailAlloc_7616_, 1, v___x_7589_);
lean_ctor_set(v_reuseFailAlloc_7616_, 2, v_buildTime_7583_);
lean_ctor_set_uint8(v_reuseFailAlloc_7616_, sizeof(void*)*3, v_action_7580_);
lean_ctor_set_uint8(v_reuseFailAlloc_7616_, sizeof(void*)*3 + 1, v_wantsRebuild_7581_);
v___x_7591_ = v_reuseFailAlloc_7616_;
goto v_reusejp_7590_;
}
v_reusejp_7590_:
{
uint8_t v___x_7592_; uint8_t v___x_7593_; lean_object* v___x_7594_; lean_object* v___x_7595_; 
v___x_7592_ = 1;
v___x_7593_ = 0;
v___x_7594_ = l_Lake_sharedLibExt;
v___x_7595_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_7540_, v___y_7588_, v___x_7593_, v___x_7594_, v___x_7592_, v___x_7593_, v___x_7593_, v___y_7544_, v___y_7545_, v___y_7546_, v___y_7547_, v___y_7548_, v___x_7591_);
if (lean_obj_tag(v___x_7595_) == 0)
{
lean_object* v_a_7596_; lean_object* v_a_7597_; lean_object* v___x_7599_; uint8_t v_isShared_7600_; uint8_t v_isSharedCheck_7606_; 
v_a_7596_ = lean_ctor_get(v___x_7595_, 0);
v_a_7597_ = lean_ctor_get(v___x_7595_, 1);
v_isSharedCheck_7606_ = !lean_is_exclusive(v___x_7595_);
if (v_isSharedCheck_7606_ == 0)
{
v___x_7599_ = v___x_7595_;
v_isShared_7600_ = v_isSharedCheck_7606_;
goto v_resetjp_7598_;
}
else
{
lean_inc(v_a_7597_);
lean_inc(v_a_7596_);
lean_dec(v___x_7595_);
v___x_7599_ = lean_box(0);
v_isShared_7600_ = v_isSharedCheck_7606_;
goto v_resetjp_7598_;
}
v_resetjp_7598_:
{
lean_object* v_path_7601_; lean_object* v___x_7602_; lean_object* v___x_7604_; 
v_path_7601_ = lean_ctor_get(v_a_7596_, 1);
lean_inc_ref(v_path_7601_);
lean_dec(v_a_7596_);
v___x_7602_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_7602_, 0, v_path_7601_);
lean_ctor_set(v___x_7602_, 1, v_libName_7541_);
lean_ctor_set(v___x_7602_, 2, v_libs_7543_);
lean_ctor_set_uint8(v___x_7602_, sizeof(void*)*3, v_plugin_7542_);
if (v_isShared_7600_ == 0)
{
lean_ctor_set(v___x_7599_, 0, v___x_7602_);
v___x_7604_ = v___x_7599_;
goto v_reusejp_7603_;
}
else
{
lean_object* v_reuseFailAlloc_7605_; 
v_reuseFailAlloc_7605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7605_, 0, v___x_7602_);
lean_ctor_set(v_reuseFailAlloc_7605_, 1, v_a_7597_);
v___x_7604_ = v_reuseFailAlloc_7605_;
goto v_reusejp_7603_;
}
v_reusejp_7603_:
{
return v___x_7604_;
}
}
}
else
{
lean_object* v_a_7607_; lean_object* v_a_7608_; lean_object* v___x_7610_; uint8_t v_isShared_7611_; uint8_t v_isSharedCheck_7615_; 
lean_dec_ref(v_libs_7543_);
lean_dec_ref(v_libName_7541_);
v_a_7607_ = lean_ctor_get(v___x_7595_, 0);
v_a_7608_ = lean_ctor_get(v___x_7595_, 1);
v_isSharedCheck_7615_ = !lean_is_exclusive(v___x_7595_);
if (v_isSharedCheck_7615_ == 0)
{
v___x_7610_ = v___x_7595_;
v_isShared_7611_ = v_isSharedCheck_7615_;
goto v_resetjp_7609_;
}
else
{
lean_inc(v_a_7608_);
lean_inc(v_a_7607_);
lean_dec(v___x_7595_);
v___x_7610_ = lean_box(0);
v_isShared_7611_ = v_isSharedCheck_7615_;
goto v_resetjp_7609_;
}
v_resetjp_7609_:
{
lean_object* v___x_7613_; 
if (v_isShared_7611_ == 0)
{
v___x_7613_ = v___x_7610_;
goto v_reusejp_7612_;
}
else
{
lean_object* v_reuseFailAlloc_7614_; 
v_reuseFailAlloc_7614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7614_, 0, v_a_7607_);
lean_ctor_set(v_reuseFailAlloc_7614_, 1, v_a_7608_);
v___x_7613_ = v_reuseFailAlloc_7614_;
goto v_reusejp_7612_;
}
v_reusejp_7612_:
{
return v___x_7613_;
}
}
}
}
}
}
else
{
lean_object* v_a_7618_; lean_object* v_a_7619_; lean_object* v___x_7621_; uint8_t v_isShared_7622_; uint8_t v_isSharedCheck_7626_; 
lean_dec_ref(v___y_7544_);
lean_dec_ref(v_libs_7543_);
lean_dec_ref(v_libName_7541_);
lean_dec_ref(v_libFile_7540_);
lean_dec_ref(v___f_7539_);
v_a_7618_ = lean_ctor_get(v___x_7576_, 0);
v_a_7619_ = lean_ctor_get(v___x_7576_, 1);
v_isSharedCheck_7626_ = !lean_is_exclusive(v___x_7576_);
if (v_isSharedCheck_7626_ == 0)
{
v___x_7621_ = v___x_7576_;
v_isShared_7622_ = v_isSharedCheck_7626_;
goto v_resetjp_7620_;
}
else
{
lean_inc(v_a_7619_);
lean_inc(v_a_7618_);
lean_dec(v___x_7576_);
v___x_7621_ = lean_box(0);
v_isShared_7622_ = v_isSharedCheck_7626_;
goto v_resetjp_7620_;
}
v_resetjp_7620_:
{
lean_object* v___x_7624_; 
if (v_isShared_7622_ == 0)
{
v___x_7624_ = v___x_7621_;
goto v_reusejp_7623_;
}
else
{
lean_object* v_reuseFailAlloc_7625_; 
v_reuseFailAlloc_7625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7625_, 0, v_a_7618_);
lean_ctor_set(v_reuseFailAlloc_7625_, 1, v_a_7619_);
v___x_7624_ = v_reuseFailAlloc_7625_;
goto v_reusejp_7623_;
}
v_reusejp_7623_:
{
return v___x_7624_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2___boxed(lean_object* v_traceArgs_7640_, lean_object* v_extraDepTrace_7641_, lean_object* v_linkDeps_7642_, lean_object* v___f_7643_, lean_object* v_libFile_7644_, lean_object* v_libName_7645_, lean_object* v_plugin_7646_, lean_object* v_libs_7647_, lean_object* v___y_7648_, lean_object* v___y_7649_, lean_object* v___y_7650_, lean_object* v___y_7651_, lean_object* v___y_7652_, lean_object* v___y_7653_, lean_object* v___y_7654_){
_start:
{
uint8_t v_linkDeps_boxed_7655_; uint8_t v_plugin_boxed_7656_; lean_object* v_res_7657_; 
v_linkDeps_boxed_7655_ = lean_unbox(v_linkDeps_7642_);
v_plugin_boxed_7656_ = lean_unbox(v_plugin_7646_);
v_res_7657_ = l_Lake_buildSharedLib___lam__2(v_traceArgs_7640_, v_extraDepTrace_7641_, v_linkDeps_boxed_7655_, v___f_7643_, v_libFile_7644_, v_libName_7645_, v_plugin_boxed_7656_, v_libs_7647_, v___y_7648_, v___y_7649_, v___y_7650_, v___y_7651_, v___y_7652_, v___y_7653_);
lean_dec_ref(v___y_7652_);
lean_dec(v___y_7651_);
lean_dec(v___y_7650_);
lean_dec(v___y_7649_);
return v_res_7657_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3(lean_object* v_weakArgs_7659_, lean_object* v_traceArgs_7660_, lean_object* v_libFile_7661_, lean_object* v_linker_7662_, lean_object* v_extraDepTrace_7663_, uint8_t v_linkDeps_7664_, lean_object* v_libName_7665_, uint8_t v_plugin_7666_, lean_object* v_linkLibs_7667_, lean_object* v___x_7668_, lean_object* v_objs_7669_, lean_object* v___y_7670_, lean_object* v___y_7671_, lean_object* v___y_7672_, lean_object* v___y_7673_, lean_object* v___y_7674_, lean_object* v___y_7675_){
_start:
{
lean_object* v_trace_7677_; lean_object* v___f_7678_; lean_object* v___x_7679_; lean_object* v___x_7680_; lean_object* v___f_7681_; lean_object* v___x_7682_; lean_object* v___x_7683_; lean_object* v___x_7684_; uint8_t v___x_7685_; lean_object* v___x_7686_; lean_object* v___x_7687_; 
v_trace_7677_ = lean_ctor_get(v___y_7675_, 1);
lean_inc_ref(v_libFile_7661_);
lean_inc_ref(v_traceArgs_7660_);
v___f_7678_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__0___boxed), 13, 5);
lean_closure_set(v___f_7678_, 0, v_objs_7669_);
lean_closure_set(v___f_7678_, 1, v_weakArgs_7659_);
lean_closure_set(v___f_7678_, 2, v_traceArgs_7660_);
lean_closure_set(v___f_7678_, 3, v_libFile_7661_);
lean_closure_set(v___f_7678_, 4, v_linker_7662_);
v___x_7679_ = lean_box(v_linkDeps_7664_);
v___x_7680_ = lean_box(v_plugin_7666_);
v___f_7681_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__2___boxed), 15, 7);
lean_closure_set(v___f_7681_, 0, v_traceArgs_7660_);
lean_closure_set(v___f_7681_, 1, v_extraDepTrace_7663_);
lean_closure_set(v___f_7681_, 2, v___x_7679_);
lean_closure_set(v___f_7681_, 3, v___f_7678_);
lean_closure_set(v___f_7681_, 4, v_libFile_7661_);
lean_closure_set(v___f_7681_, 5, v_libName_7665_);
lean_closure_set(v___f_7681_, 6, v___x_7680_);
v___x_7682_ = ((lean_object*)(l_Lake_buildSharedLib___lam__3___closed__0));
v___x_7683_ = l_Lake_Job_collectArray___redArg(v_linkLibs_7667_, v___x_7682_);
v___x_7684_ = lean_unsigned_to_nat(0u);
v___x_7685_ = 0;
v___x_7686_ = l_Lake_Job_mapM___redArg(v___x_7668_, v___x_7683_, v___f_7681_, v___x_7684_, v___x_7685_, v___y_7670_, v___y_7671_, v___y_7672_, v___y_7673_, v___y_7674_, v_trace_7677_);
v___x_7687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7687_, 0, v___x_7686_);
lean_ctor_set(v___x_7687_, 1, v___y_7675_);
return v___x_7687_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3___boxed(lean_object** _args){
lean_object* v_weakArgs_7688_ = _args[0];
lean_object* v_traceArgs_7689_ = _args[1];
lean_object* v_libFile_7690_ = _args[2];
lean_object* v_linker_7691_ = _args[3];
lean_object* v_extraDepTrace_7692_ = _args[4];
lean_object* v_linkDeps_7693_ = _args[5];
lean_object* v_libName_7694_ = _args[6];
lean_object* v_plugin_7695_ = _args[7];
lean_object* v_linkLibs_7696_ = _args[8];
lean_object* v___x_7697_ = _args[9];
lean_object* v_objs_7698_ = _args[10];
lean_object* v___y_7699_ = _args[11];
lean_object* v___y_7700_ = _args[12];
lean_object* v___y_7701_ = _args[13];
lean_object* v___y_7702_ = _args[14];
lean_object* v___y_7703_ = _args[15];
lean_object* v___y_7704_ = _args[16];
lean_object* v___y_7705_ = _args[17];
_start:
{
uint8_t v_linkDeps_boxed_7706_; uint8_t v_plugin_boxed_7707_; lean_object* v_res_7708_; 
v_linkDeps_boxed_7706_ = lean_unbox(v_linkDeps_7693_);
v_plugin_boxed_7707_ = lean_unbox(v_plugin_7695_);
v_res_7708_ = l_Lake_buildSharedLib___lam__3(v_weakArgs_7688_, v_traceArgs_7689_, v_libFile_7690_, v_linker_7691_, v_extraDepTrace_7692_, v_linkDeps_boxed_7706_, v_libName_7694_, v_plugin_boxed_7707_, v_linkLibs_7696_, v___x_7697_, v_objs_7698_, v___y_7699_, v___y_7700_, v___y_7701_, v___y_7702_, v___y_7703_, v___y_7704_);
lean_dec_ref(v___y_7703_);
lean_dec(v___y_7702_);
lean_dec(v___y_7701_);
lean_dec(v___y_7700_);
lean_dec_ref(v_linkLibs_7696_);
return v_res_7708_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib(lean_object* v_libName_7710_, lean_object* v_libFile_7711_, lean_object* v_linkObjs_7712_, lean_object* v_linkLibs_7713_, lean_object* v_weakArgs_7714_, lean_object* v_traceArgs_7715_, lean_object* v_linker_7716_, lean_object* v_extraDepTrace_7717_, uint8_t v_plugin_7718_, uint8_t v_linkDeps_7719_, lean_object* v_a_7720_, lean_object* v_a_7721_, lean_object* v_a_7722_, lean_object* v_a_7723_, lean_object* v_a_7724_, lean_object* v_a_7725_){
_start:
{
lean_object* v___x_7727_; lean_object* v___x_7728_; lean_object* v___x_7729_; lean_object* v___f_7730_; lean_object* v___x_7731_; lean_object* v___x_7732_; lean_object* v___x_7733_; uint8_t v___x_7734_; lean_object* v___x_7735_; 
v___x_7727_ = l_Lake_instDataKindDynlib;
v___x_7728_ = lean_box(v_linkDeps_7719_);
v___x_7729_ = lean_box(v_plugin_7718_);
v___f_7730_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__3___boxed), 18, 10);
lean_closure_set(v___f_7730_, 0, v_weakArgs_7714_);
lean_closure_set(v___f_7730_, 1, v_traceArgs_7715_);
lean_closure_set(v___f_7730_, 2, v_libFile_7711_);
lean_closure_set(v___f_7730_, 3, v_linker_7716_);
lean_closure_set(v___f_7730_, 4, v_extraDepTrace_7717_);
lean_closure_set(v___f_7730_, 5, v___x_7728_);
lean_closure_set(v___f_7730_, 6, v_libName_7710_);
lean_closure_set(v___f_7730_, 7, v___x_7729_);
lean_closure_set(v___f_7730_, 8, v_linkLibs_7713_);
lean_closure_set(v___f_7730_, 9, v___x_7727_);
v___x_7731_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_7732_ = l_Lake_Job_collectArray___redArg(v_linkObjs_7712_, v___x_7731_);
v___x_7733_ = lean_unsigned_to_nat(0u);
v___x_7734_ = 1;
v___x_7735_ = l_Lake_Job_bindM___redArg(v___x_7727_, v___x_7732_, v___f_7730_, v___x_7733_, v___x_7734_, v_a_7720_, v_a_7721_, v_a_7722_, v_a_7723_, v_a_7724_, v_a_7725_);
return v___x_7735_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___boxed(lean_object** _args){
lean_object* v_libName_7736_ = _args[0];
lean_object* v_libFile_7737_ = _args[1];
lean_object* v_linkObjs_7738_ = _args[2];
lean_object* v_linkLibs_7739_ = _args[3];
lean_object* v_weakArgs_7740_ = _args[4];
lean_object* v_traceArgs_7741_ = _args[5];
lean_object* v_linker_7742_ = _args[6];
lean_object* v_extraDepTrace_7743_ = _args[7];
lean_object* v_plugin_7744_ = _args[8];
lean_object* v_linkDeps_7745_ = _args[9];
lean_object* v_a_7746_ = _args[10];
lean_object* v_a_7747_ = _args[11];
lean_object* v_a_7748_ = _args[12];
lean_object* v_a_7749_ = _args[13];
lean_object* v_a_7750_ = _args[14];
lean_object* v_a_7751_ = _args[15];
lean_object* v_a_7752_ = _args[16];
_start:
{
uint8_t v_plugin_boxed_7753_; uint8_t v_linkDeps_boxed_7754_; lean_object* v_res_7755_; 
v_plugin_boxed_7753_ = lean_unbox(v_plugin_7744_);
v_linkDeps_boxed_7754_ = lean_unbox(v_linkDeps_7745_);
v_res_7755_ = l_Lake_buildSharedLib(v_libName_7736_, v_libFile_7737_, v_linkObjs_7738_, v_linkLibs_7739_, v_weakArgs_7740_, v_traceArgs_7741_, v_linker_7742_, v_extraDepTrace_7743_, v_plugin_boxed_7753_, v_linkDeps_boxed_7754_, v_a_7746_, v_a_7747_, v_a_7748_, v_a_7749_, v_a_7750_, v_a_7751_);
lean_dec_ref(v_a_7751_);
lean_dec_ref(v_a_7750_);
lean_dec(v_a_7749_);
lean_dec(v_a_7748_);
lean_dec(v_a_7747_);
lean_dec_ref(v_linkObjs_7738_);
return v_res_7755_;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLib___lam__0___closed__0(void){
_start:
{
lean_object* v___x_7756_; lean_object* v___x_7757_; lean_object* v___x_7758_; lean_object* v___x_7759_; 
v___x_7756_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
v___x_7757_ = lean_unsigned_to_nat(2u);
v___x_7758_ = lean_mk_empty_array_with_capacity(v___x_7757_);
v___x_7759_ = lean_array_push(v___x_7758_, v___x_7756_);
return v___x_7759_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object* v_objs_7760_, lean_object* v_weakArgs_7761_, lean_object* v_traceArgs_7762_, lean_object* v_libFile_7763_, uint8_t v_linkDeps_7764_, lean_object* v_libs_7765_, lean_object* v___y_7766_, lean_object* v___y_7767_, lean_object* v___y_7768_, lean_object* v___y_7769_, lean_object* v___y_7770_, lean_object* v___y_7771_){
_start:
{
lean_object* v_toContext_7773_; lean_object* v_lakeEnv_7774_; lean_object* v_lean_7775_; lean_object* v_libs_7777_; lean_object* v___y_7778_; 
v_toContext_7773_ = lean_ctor_get(v___y_7770_, 1);
v_lakeEnv_7774_ = lean_ctor_get(v_toContext_7773_, 1);
v_lean_7775_ = lean_ctor_get(v_lakeEnv_7774_, 1);
if (v_linkDeps_7764_ == 0)
{
lean_object* v___x_7823_; 
v___x_7823_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1));
v_libs_7777_ = v___x_7823_;
v___y_7778_ = v___y_7771_;
goto v___jp_7776_;
}
else
{
lean_object* v___x_7824_; 
v___x_7824_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7765_, v___y_7771_);
if (lean_obj_tag(v___x_7824_) == 0)
{
lean_object* v_a_7825_; lean_object* v_a_7826_; 
v_a_7825_ = lean_ctor_get(v___x_7824_, 0);
lean_inc(v_a_7825_);
v_a_7826_ = lean_ctor_get(v___x_7824_, 1);
lean_inc(v_a_7826_);
lean_dec_ref(v___x_7824_);
v_libs_7777_ = v_a_7825_;
v___y_7778_ = v_a_7826_;
goto v___jp_7776_;
}
else
{
lean_object* v_a_7827_; lean_object* v_a_7828_; lean_object* v___x_7830_; uint8_t v_isShared_7831_; uint8_t v_isSharedCheck_7835_; 
lean_dec_ref(v_libFile_7763_);
v_a_7827_ = lean_ctor_get(v___x_7824_, 0);
v_a_7828_ = lean_ctor_get(v___x_7824_, 1);
v_isSharedCheck_7835_ = !lean_is_exclusive(v___x_7824_);
if (v_isSharedCheck_7835_ == 0)
{
v___x_7830_ = v___x_7824_;
v_isShared_7831_ = v_isSharedCheck_7835_;
goto v_resetjp_7829_;
}
else
{
lean_inc(v_a_7828_);
lean_inc(v_a_7827_);
lean_dec(v___x_7824_);
v___x_7830_ = lean_box(0);
v_isShared_7831_ = v_isSharedCheck_7835_;
goto v_resetjp_7829_;
}
v_resetjp_7829_:
{
lean_object* v___x_7833_; 
if (v_isShared_7831_ == 0)
{
v___x_7833_ = v___x_7830_;
goto v_reusejp_7832_;
}
else
{
lean_object* v_reuseFailAlloc_7834_; 
v_reuseFailAlloc_7834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7834_, 0, v_a_7827_);
lean_ctor_set(v_reuseFailAlloc_7834_, 1, v_a_7828_);
v___x_7833_ = v_reuseFailAlloc_7834_;
goto v_reusejp_7832_;
}
v_reusejp_7832_:
{
return v___x_7833_;
}
}
}
}
v___jp_7776_:
{
lean_object* v_leanLibDir_7779_; lean_object* v_cc_7780_; lean_object* v_ccLinkSharedFlags_7781_; lean_object* v_log_7782_; uint8_t v_action_7783_; uint8_t v_wantsRebuild_7784_; lean_object* v_trace_7785_; lean_object* v_buildTime_7786_; lean_object* v___x_7788_; uint8_t v_isShared_7789_; uint8_t v_isSharedCheck_7822_; 
v_leanLibDir_7779_ = lean_ctor_get(v_lean_7775_, 3);
v_cc_7780_ = lean_ctor_get(v_lean_7775_, 14);
v_ccLinkSharedFlags_7781_ = lean_ctor_get(v_lean_7775_, 20);
v_log_7782_ = lean_ctor_get(v___y_7778_, 0);
v_action_7783_ = lean_ctor_get_uint8(v___y_7778_, sizeof(void*)*3);
v_wantsRebuild_7784_ = lean_ctor_get_uint8(v___y_7778_, sizeof(void*)*3 + 1);
v_trace_7785_ = lean_ctor_get(v___y_7778_, 1);
v_buildTime_7786_ = lean_ctor_get(v___y_7778_, 2);
v_isSharedCheck_7822_ = !lean_is_exclusive(v___y_7778_);
if (v_isSharedCheck_7822_ == 0)
{
v___x_7788_ = v___y_7778_;
v_isShared_7789_ = v_isSharedCheck_7822_;
goto v_resetjp_7787_;
}
else
{
lean_inc(v_buildTime_7786_);
lean_inc(v_trace_7785_);
lean_inc(v_log_7782_);
lean_dec(v___y_7778_);
v___x_7788_ = lean_box(0);
v_isShared_7789_ = v_isSharedCheck_7822_;
goto v_resetjp_7787_;
}
v_resetjp_7787_:
{
lean_object* v___x_7790_; lean_object* v___x_7791_; lean_object* v___x_7792_; lean_object* v___x_7793_; lean_object* v___x_7794_; lean_object* v___x_7795_; lean_object* v___x_7796_; lean_object* v___x_7797_; 
v___x_7790_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7760_, v_libs_7777_);
lean_dec_ref(v_libs_7777_);
v___x_7791_ = l_Array_append___redArg(v___x_7790_, v_weakArgs_7761_);
v___x_7792_ = l_Array_append___redArg(v___x_7791_, v_traceArgs_7762_);
v___x_7793_ = lean_obj_once(&l_Lake_buildLeanSharedLib___lam__0___closed__0, &l_Lake_buildLeanSharedLib___lam__0___closed__0_once, _init_l_Lake_buildLeanSharedLib___lam__0___closed__0);
lean_inc_ref(v_leanLibDir_7779_);
v___x_7794_ = lean_array_push(v___x_7793_, v_leanLibDir_7779_);
v___x_7795_ = l_Array_append___redArg(v___x_7792_, v___x_7794_);
lean_dec_ref(v___x_7794_);
v___x_7796_ = l_Array_append___redArg(v___x_7795_, v_ccLinkSharedFlags_7781_);
lean_inc_ref(v_cc_7780_);
v___x_7797_ = l_Lake_compileSharedLib(v_libFile_7763_, v___x_7796_, v_cc_7780_, v_log_7782_);
lean_dec_ref(v___x_7796_);
if (lean_obj_tag(v___x_7797_) == 0)
{
lean_object* v_a_7798_; lean_object* v_a_7799_; lean_object* v___x_7801_; uint8_t v_isShared_7802_; uint8_t v_isSharedCheck_7809_; 
v_a_7798_ = lean_ctor_get(v___x_7797_, 0);
v_a_7799_ = lean_ctor_get(v___x_7797_, 1);
v_isSharedCheck_7809_ = !lean_is_exclusive(v___x_7797_);
if (v_isSharedCheck_7809_ == 0)
{
v___x_7801_ = v___x_7797_;
v_isShared_7802_ = v_isSharedCheck_7809_;
goto v_resetjp_7800_;
}
else
{
lean_inc(v_a_7799_);
lean_inc(v_a_7798_);
lean_dec(v___x_7797_);
v___x_7801_ = lean_box(0);
v_isShared_7802_ = v_isSharedCheck_7809_;
goto v_resetjp_7800_;
}
v_resetjp_7800_:
{
lean_object* v___x_7804_; 
if (v_isShared_7789_ == 0)
{
lean_ctor_set(v___x_7788_, 0, v_a_7799_);
v___x_7804_ = v___x_7788_;
goto v_reusejp_7803_;
}
else
{
lean_object* v_reuseFailAlloc_7808_; 
v_reuseFailAlloc_7808_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7808_, 0, v_a_7799_);
lean_ctor_set(v_reuseFailAlloc_7808_, 1, v_trace_7785_);
lean_ctor_set(v_reuseFailAlloc_7808_, 2, v_buildTime_7786_);
lean_ctor_set_uint8(v_reuseFailAlloc_7808_, sizeof(void*)*3, v_action_7783_);
lean_ctor_set_uint8(v_reuseFailAlloc_7808_, sizeof(void*)*3 + 1, v_wantsRebuild_7784_);
v___x_7804_ = v_reuseFailAlloc_7808_;
goto v_reusejp_7803_;
}
v_reusejp_7803_:
{
lean_object* v___x_7806_; 
if (v_isShared_7802_ == 0)
{
lean_ctor_set(v___x_7801_, 1, v___x_7804_);
v___x_7806_ = v___x_7801_;
goto v_reusejp_7805_;
}
else
{
lean_object* v_reuseFailAlloc_7807_; 
v_reuseFailAlloc_7807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7807_, 0, v_a_7798_);
lean_ctor_set(v_reuseFailAlloc_7807_, 1, v___x_7804_);
v___x_7806_ = v_reuseFailAlloc_7807_;
goto v_reusejp_7805_;
}
v_reusejp_7805_:
{
return v___x_7806_;
}
}
}
}
else
{
lean_object* v_a_7810_; lean_object* v_a_7811_; lean_object* v___x_7813_; uint8_t v_isShared_7814_; uint8_t v_isSharedCheck_7821_; 
v_a_7810_ = lean_ctor_get(v___x_7797_, 0);
v_a_7811_ = lean_ctor_get(v___x_7797_, 1);
v_isSharedCheck_7821_ = !lean_is_exclusive(v___x_7797_);
if (v_isSharedCheck_7821_ == 0)
{
v___x_7813_ = v___x_7797_;
v_isShared_7814_ = v_isSharedCheck_7821_;
goto v_resetjp_7812_;
}
else
{
lean_inc(v_a_7811_);
lean_inc(v_a_7810_);
lean_dec(v___x_7797_);
v___x_7813_ = lean_box(0);
v_isShared_7814_ = v_isSharedCheck_7821_;
goto v_resetjp_7812_;
}
v_resetjp_7812_:
{
lean_object* v___x_7816_; 
if (v_isShared_7789_ == 0)
{
lean_ctor_set(v___x_7788_, 0, v_a_7811_);
v___x_7816_ = v___x_7788_;
goto v_reusejp_7815_;
}
else
{
lean_object* v_reuseFailAlloc_7820_; 
v_reuseFailAlloc_7820_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7820_, 0, v_a_7811_);
lean_ctor_set(v_reuseFailAlloc_7820_, 1, v_trace_7785_);
lean_ctor_set(v_reuseFailAlloc_7820_, 2, v_buildTime_7786_);
lean_ctor_set_uint8(v_reuseFailAlloc_7820_, sizeof(void*)*3, v_action_7783_);
lean_ctor_set_uint8(v_reuseFailAlloc_7820_, sizeof(void*)*3 + 1, v_wantsRebuild_7784_);
v___x_7816_ = v_reuseFailAlloc_7820_;
goto v_reusejp_7815_;
}
v_reusejp_7815_:
{
lean_object* v___x_7818_; 
if (v_isShared_7814_ == 0)
{
lean_ctor_set(v___x_7813_, 1, v___x_7816_);
v___x_7818_ = v___x_7813_;
goto v_reusejp_7817_;
}
else
{
lean_object* v_reuseFailAlloc_7819_; 
v_reuseFailAlloc_7819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7819_, 0, v_a_7810_);
lean_ctor_set(v_reuseFailAlloc_7819_, 1, v___x_7816_);
v___x_7818_ = v_reuseFailAlloc_7819_;
goto v_reusejp_7817_;
}
v_reusejp_7817_:
{
return v___x_7818_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object* v_objs_7836_, lean_object* v_weakArgs_7837_, lean_object* v_traceArgs_7838_, lean_object* v_libFile_7839_, lean_object* v_linkDeps_7840_, lean_object* v_libs_7841_, lean_object* v___y_7842_, lean_object* v___y_7843_, lean_object* v___y_7844_, lean_object* v___y_7845_, lean_object* v___y_7846_, lean_object* v___y_7847_, lean_object* v___y_7848_){
_start:
{
uint8_t v_linkDeps_boxed_7849_; lean_object* v_res_7850_; 
v_linkDeps_boxed_7849_ = lean_unbox(v_linkDeps_7840_);
v_res_7850_ = l_Lake_buildLeanSharedLib___lam__0(v_objs_7836_, v_weakArgs_7837_, v_traceArgs_7838_, v_libFile_7839_, v_linkDeps_boxed_7849_, v_libs_7841_, v___y_7842_, v___y_7843_, v___y_7844_, v___y_7845_, v___y_7846_, v___y_7847_);
lean_dec_ref(v___y_7846_);
lean_dec(v___y_7845_);
lean_dec(v___y_7844_);
lean_dec(v___y_7843_);
lean_dec_ref(v___y_7842_);
lean_dec_ref(v_libs_7841_);
lean_dec_ref(v_traceArgs_7838_);
lean_dec_ref(v_weakArgs_7837_);
lean_dec_ref(v_objs_7836_);
return v_res_7850_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object* v_objs_7851_, lean_object* v_weakArgs_7852_, lean_object* v_traceArgs_7853_, lean_object* v_libFile_7854_, uint8_t v_linkDeps_7855_, lean_object* v_libName_7856_, uint8_t v_plugin_7857_, lean_object* v_libs_7858_, lean_object* v___y_7859_, lean_object* v___y_7860_, lean_object* v___y_7861_, lean_object* v___y_7862_, lean_object* v___y_7863_, lean_object* v___y_7864_){
_start:
{
lean_object* v_log_7866_; uint8_t v_action_7867_; uint8_t v_wantsRebuild_7868_; lean_object* v_trace_7869_; lean_object* v_buildTime_7870_; lean_object* v___x_7872_; uint8_t v_isShared_7873_; uint8_t v_isSharedCheck_7930_; 
v_log_7866_ = lean_ctor_get(v___y_7864_, 0);
v_action_7867_ = lean_ctor_get_uint8(v___y_7864_, sizeof(void*)*3);
v_wantsRebuild_7868_ = lean_ctor_get_uint8(v___y_7864_, sizeof(void*)*3 + 1);
v_trace_7869_ = lean_ctor_get(v___y_7864_, 1);
v_buildTime_7870_ = lean_ctor_get(v___y_7864_, 2);
v_isSharedCheck_7930_ = !lean_is_exclusive(v___y_7864_);
if (v_isSharedCheck_7930_ == 0)
{
v___x_7872_ = v___y_7864_;
v_isShared_7873_ = v_isSharedCheck_7930_;
goto v_resetjp_7871_;
}
else
{
lean_inc(v_buildTime_7870_);
lean_inc(v_trace_7869_);
lean_inc(v_log_7866_);
lean_dec(v___y_7864_);
v___x_7872_ = lean_box(0);
v_isShared_7873_ = v_isSharedCheck_7930_;
goto v_resetjp_7871_;
}
v_resetjp_7871_:
{
lean_object* v_leanTrace_7874_; lean_object* v___x_7875_; lean_object* v___f_7876_; lean_object* v___x_7877_; uint64_t v___y_7879_; uint64_t v___x_7919_; lean_object* v___x_7920_; lean_object* v___x_7921_; uint8_t v___x_7922_; 
v_leanTrace_7874_ = lean_ctor_get(v___y_7863_, 2);
v___x_7875_ = lean_box(v_linkDeps_7855_);
lean_inc_ref(v_libs_7858_);
lean_inc_ref(v_libFile_7854_);
lean_inc_ref(v_traceArgs_7853_);
v___f_7876_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__0___boxed), 13, 6);
lean_closure_set(v___f_7876_, 0, v_objs_7851_);
lean_closure_set(v___f_7876_, 1, v_weakArgs_7852_);
lean_closure_set(v___f_7876_, 2, v_traceArgs_7853_);
lean_closure_set(v___f_7876_, 3, v_libFile_7854_);
lean_closure_set(v___f_7876_, 4, v___x_7875_);
lean_closure_set(v___f_7876_, 5, v_libs_7858_);
lean_inc_ref(v_leanTrace_7874_);
v___x_7877_ = l_Lake_BuildTrace_mix(v_trace_7869_, v_leanTrace_7874_);
v___x_7919_ = l_Lake_Hash_nil;
v___x_7920_ = lean_unsigned_to_nat(0u);
v___x_7921_ = lean_array_get_size(v_traceArgs_7853_);
v___x_7922_ = lean_nat_dec_lt(v___x_7920_, v___x_7921_);
if (v___x_7922_ == 0)
{
v___y_7879_ = v___x_7919_;
goto v___jp_7878_;
}
else
{
uint8_t v___x_7923_; 
v___x_7923_ = lean_nat_dec_le(v___x_7921_, v___x_7921_);
if (v___x_7923_ == 0)
{
if (v___x_7922_ == 0)
{
v___y_7879_ = v___x_7919_;
goto v___jp_7878_;
}
else
{
size_t v___x_7924_; size_t v___x_7925_; uint64_t v___x_7926_; 
v___x_7924_ = ((size_t)0ULL);
v___x_7925_ = lean_usize_of_nat(v___x_7921_);
v___x_7926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7853_, v___x_7924_, v___x_7925_, v___x_7919_);
v___y_7879_ = v___x_7926_;
goto v___jp_7878_;
}
}
else
{
size_t v___x_7927_; size_t v___x_7928_; uint64_t v___x_7929_; 
v___x_7927_ = ((size_t)0ULL);
v___x_7928_ = lean_usize_of_nat(v___x_7921_);
v___x_7929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7853_, v___x_7927_, v___x_7928_, v___x_7919_);
v___y_7879_ = v___x_7929_;
goto v___jp_7878_;
}
}
v___jp_7878_:
{
lean_object* v___x_7880_; lean_object* v___x_7881_; lean_object* v___x_7882_; lean_object* v___x_7883_; lean_object* v___x_7884_; lean_object* v___x_7885_; lean_object* v___x_7886_; lean_object* v___x_7887_; lean_object* v___x_7888_; lean_object* v___x_7889_; lean_object* v___x_7890_; lean_object* v___x_7891_; lean_object* v___x_7893_; 
v___x_7880_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_7881_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_7882_ = lean_array_to_list(v_traceArgs_7853_);
v___x_7883_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_7882_);
lean_dec(v___x_7882_);
v___x_7884_ = lean_string_append(v___x_7881_, v___x_7883_);
lean_dec_ref(v___x_7883_);
v___x_7885_ = lean_string_append(v___x_7880_, v___x_7884_);
lean_dec_ref(v___x_7884_);
v___x_7886_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_7887_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_7888_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_7888_, 0, v___x_7885_);
lean_ctor_set(v___x_7888_, 1, v___x_7886_);
lean_ctor_set(v___x_7888_, 2, v___x_7887_);
lean_ctor_set_uint64(v___x_7888_, sizeof(void*)*3, v___y_7879_);
v___x_7889_ = l_Lake_BuildTrace_mix(v___x_7877_, v___x_7888_);
v___x_7890_ = l_Lake_platformTrace;
v___x_7891_ = l_Lake_BuildTrace_mix(v___x_7889_, v___x_7890_);
if (v_isShared_7873_ == 0)
{
lean_ctor_set(v___x_7872_, 1, v___x_7891_);
v___x_7893_ = v___x_7872_;
goto v_reusejp_7892_;
}
else
{
lean_object* v_reuseFailAlloc_7918_; 
v_reuseFailAlloc_7918_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7918_, 0, v_log_7866_);
lean_ctor_set(v_reuseFailAlloc_7918_, 1, v___x_7891_);
lean_ctor_set(v_reuseFailAlloc_7918_, 2, v_buildTime_7870_);
lean_ctor_set_uint8(v_reuseFailAlloc_7918_, sizeof(void*)*3, v_action_7867_);
lean_ctor_set_uint8(v_reuseFailAlloc_7918_, sizeof(void*)*3 + 1, v_wantsRebuild_7868_);
v___x_7893_ = v_reuseFailAlloc_7918_;
goto v_reusejp_7892_;
}
v_reusejp_7892_:
{
uint8_t v___x_7894_; lean_object* v___x_7895_; uint8_t v___x_7896_; lean_object* v___x_7897_; 
v___x_7894_ = 0;
v___x_7895_ = l_Lake_sharedLibExt;
v___x_7896_ = 1;
v___x_7897_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_7854_, v___f_7876_, v___x_7894_, v___x_7895_, v___x_7896_, v___x_7894_, v___x_7894_, v___y_7859_, v___y_7860_, v___y_7861_, v___y_7862_, v___y_7863_, v___x_7893_);
if (lean_obj_tag(v___x_7897_) == 0)
{
lean_object* v_a_7898_; lean_object* v_a_7899_; lean_object* v___x_7901_; uint8_t v_isShared_7902_; uint8_t v_isSharedCheck_7908_; 
v_a_7898_ = lean_ctor_get(v___x_7897_, 0);
v_a_7899_ = lean_ctor_get(v___x_7897_, 1);
v_isSharedCheck_7908_ = !lean_is_exclusive(v___x_7897_);
if (v_isSharedCheck_7908_ == 0)
{
v___x_7901_ = v___x_7897_;
v_isShared_7902_ = v_isSharedCheck_7908_;
goto v_resetjp_7900_;
}
else
{
lean_inc(v_a_7899_);
lean_inc(v_a_7898_);
lean_dec(v___x_7897_);
v___x_7901_ = lean_box(0);
v_isShared_7902_ = v_isSharedCheck_7908_;
goto v_resetjp_7900_;
}
v_resetjp_7900_:
{
lean_object* v_path_7903_; lean_object* v___x_7904_; lean_object* v___x_7906_; 
v_path_7903_ = lean_ctor_get(v_a_7898_, 1);
lean_inc_ref(v_path_7903_);
lean_dec(v_a_7898_);
v___x_7904_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_7904_, 0, v_path_7903_);
lean_ctor_set(v___x_7904_, 1, v_libName_7856_);
lean_ctor_set(v___x_7904_, 2, v_libs_7858_);
lean_ctor_set_uint8(v___x_7904_, sizeof(void*)*3, v_plugin_7857_);
if (v_isShared_7902_ == 0)
{
lean_ctor_set(v___x_7901_, 0, v___x_7904_);
v___x_7906_ = v___x_7901_;
goto v_reusejp_7905_;
}
else
{
lean_object* v_reuseFailAlloc_7907_; 
v_reuseFailAlloc_7907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7907_, 0, v___x_7904_);
lean_ctor_set(v_reuseFailAlloc_7907_, 1, v_a_7899_);
v___x_7906_ = v_reuseFailAlloc_7907_;
goto v_reusejp_7905_;
}
v_reusejp_7905_:
{
return v___x_7906_;
}
}
}
else
{
lean_object* v_a_7909_; lean_object* v_a_7910_; lean_object* v___x_7912_; uint8_t v_isShared_7913_; uint8_t v_isSharedCheck_7917_; 
lean_dec_ref(v_libs_7858_);
lean_dec_ref(v_libName_7856_);
v_a_7909_ = lean_ctor_get(v___x_7897_, 0);
v_a_7910_ = lean_ctor_get(v___x_7897_, 1);
v_isSharedCheck_7917_ = !lean_is_exclusive(v___x_7897_);
if (v_isSharedCheck_7917_ == 0)
{
v___x_7912_ = v___x_7897_;
v_isShared_7913_ = v_isSharedCheck_7917_;
goto v_resetjp_7911_;
}
else
{
lean_inc(v_a_7910_);
lean_inc(v_a_7909_);
lean_dec(v___x_7897_);
v___x_7912_ = lean_box(0);
v_isShared_7913_ = v_isSharedCheck_7917_;
goto v_resetjp_7911_;
}
v_resetjp_7911_:
{
lean_object* v___x_7915_; 
if (v_isShared_7913_ == 0)
{
v___x_7915_ = v___x_7912_;
goto v_reusejp_7914_;
}
else
{
lean_object* v_reuseFailAlloc_7916_; 
v_reuseFailAlloc_7916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7916_, 0, v_a_7909_);
lean_ctor_set(v_reuseFailAlloc_7916_, 1, v_a_7910_);
v___x_7915_ = v_reuseFailAlloc_7916_;
goto v_reusejp_7914_;
}
v_reusejp_7914_:
{
return v___x_7915_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1___boxed(lean_object* v_objs_7931_, lean_object* v_weakArgs_7932_, lean_object* v_traceArgs_7933_, lean_object* v_libFile_7934_, lean_object* v_linkDeps_7935_, lean_object* v_libName_7936_, lean_object* v_plugin_7937_, lean_object* v_libs_7938_, lean_object* v___y_7939_, lean_object* v___y_7940_, lean_object* v___y_7941_, lean_object* v___y_7942_, lean_object* v___y_7943_, lean_object* v___y_7944_, lean_object* v___y_7945_){
_start:
{
uint8_t v_linkDeps_boxed_7946_; uint8_t v_plugin_boxed_7947_; lean_object* v_res_7948_; 
v_linkDeps_boxed_7946_ = lean_unbox(v_linkDeps_7935_);
v_plugin_boxed_7947_ = lean_unbox(v_plugin_7937_);
v_res_7948_ = l_Lake_buildLeanSharedLib___lam__1(v_objs_7931_, v_weakArgs_7932_, v_traceArgs_7933_, v_libFile_7934_, v_linkDeps_boxed_7946_, v_libName_7936_, v_plugin_boxed_7947_, v_libs_7938_, v___y_7939_, v___y_7940_, v___y_7941_, v___y_7942_, v___y_7943_, v___y_7944_);
lean_dec_ref(v___y_7943_);
lean_dec(v___y_7942_);
lean_dec(v___y_7941_);
lean_dec(v___y_7940_);
return v_res_7948_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2(lean_object* v_weakArgs_7949_, lean_object* v_traceArgs_7950_, lean_object* v_libFile_7951_, uint8_t v_linkDeps_7952_, lean_object* v_libName_7953_, uint8_t v_plugin_7954_, lean_object* v_linkLibs_7955_, lean_object* v___x_7956_, lean_object* v_objs_7957_, lean_object* v___y_7958_, lean_object* v___y_7959_, lean_object* v___y_7960_, lean_object* v___y_7961_, lean_object* v___y_7962_, lean_object* v___y_7963_){
_start:
{
lean_object* v_trace_7965_; lean_object* v___x_7966_; lean_object* v___x_7967_; lean_object* v___f_7968_; lean_object* v___x_7969_; lean_object* v___x_7970_; lean_object* v___x_7971_; uint8_t v___x_7972_; lean_object* v___x_7973_; lean_object* v___x_7974_; 
v_trace_7965_ = lean_ctor_get(v___y_7963_, 1);
v___x_7966_ = lean_box(v_linkDeps_7952_);
v___x_7967_ = lean_box(v_plugin_7954_);
v___f_7968_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__1___boxed), 15, 7);
lean_closure_set(v___f_7968_, 0, v_objs_7957_);
lean_closure_set(v___f_7968_, 1, v_weakArgs_7949_);
lean_closure_set(v___f_7968_, 2, v_traceArgs_7950_);
lean_closure_set(v___f_7968_, 3, v_libFile_7951_);
lean_closure_set(v___f_7968_, 4, v___x_7966_);
lean_closure_set(v___f_7968_, 5, v_libName_7953_);
lean_closure_set(v___f_7968_, 6, v___x_7967_);
v___x_7969_ = ((lean_object*)(l_Lake_buildSharedLib___lam__3___closed__0));
v___x_7970_ = l_Lake_Job_collectArray___redArg(v_linkLibs_7955_, v___x_7969_);
v___x_7971_ = lean_unsigned_to_nat(0u);
v___x_7972_ = 0;
v___x_7973_ = l_Lake_Job_mapM___redArg(v___x_7956_, v___x_7970_, v___f_7968_, v___x_7971_, v___x_7972_, v___y_7958_, v___y_7959_, v___y_7960_, v___y_7961_, v___y_7962_, v_trace_7965_);
v___x_7974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7974_, 0, v___x_7973_);
lean_ctor_set(v___x_7974_, 1, v___y_7963_);
return v___x_7974_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2___boxed(lean_object* v_weakArgs_7975_, lean_object* v_traceArgs_7976_, lean_object* v_libFile_7977_, lean_object* v_linkDeps_7978_, lean_object* v_libName_7979_, lean_object* v_plugin_7980_, lean_object* v_linkLibs_7981_, lean_object* v___x_7982_, lean_object* v_objs_7983_, lean_object* v___y_7984_, lean_object* v___y_7985_, lean_object* v___y_7986_, lean_object* v___y_7987_, lean_object* v___y_7988_, lean_object* v___y_7989_, lean_object* v___y_7990_){
_start:
{
uint8_t v_linkDeps_boxed_7991_; uint8_t v_plugin_boxed_7992_; lean_object* v_res_7993_; 
v_linkDeps_boxed_7991_ = lean_unbox(v_linkDeps_7978_);
v_plugin_boxed_7992_ = lean_unbox(v_plugin_7980_);
v_res_7993_ = l_Lake_buildLeanSharedLib___lam__2(v_weakArgs_7975_, v_traceArgs_7976_, v_libFile_7977_, v_linkDeps_boxed_7991_, v_libName_7979_, v_plugin_boxed_7992_, v_linkLibs_7981_, v___x_7982_, v_objs_7983_, v___y_7984_, v___y_7985_, v___y_7986_, v___y_7987_, v___y_7988_, v___y_7989_);
lean_dec_ref(v___y_7988_);
lean_dec(v___y_7987_);
lean_dec(v___y_7986_);
lean_dec(v___y_7985_);
lean_dec_ref(v_linkLibs_7981_);
return v_res_7993_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object* v_libName_7994_, lean_object* v_libFile_7995_, lean_object* v_linkObjs_7996_, lean_object* v_linkLibs_7997_, lean_object* v_weakArgs_7998_, lean_object* v_traceArgs_7999_, uint8_t v_plugin_8000_, uint8_t v_linkDeps_8001_, lean_object* v_a_8002_, lean_object* v_a_8003_, lean_object* v_a_8004_, lean_object* v_a_8005_, lean_object* v_a_8006_, lean_object* v_a_8007_){
_start:
{
lean_object* v___x_8009_; lean_object* v___x_8010_; lean_object* v___x_8011_; lean_object* v___f_8012_; lean_object* v___x_8013_; lean_object* v___x_8014_; lean_object* v___x_8015_; uint8_t v___x_8016_; lean_object* v___x_8017_; 
v___x_8009_ = l_Lake_instDataKindDynlib;
v___x_8010_ = lean_box(v_linkDeps_8001_);
v___x_8011_ = lean_box(v_plugin_8000_);
v___f_8012_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__2___boxed), 16, 8);
lean_closure_set(v___f_8012_, 0, v_weakArgs_7998_);
lean_closure_set(v___f_8012_, 1, v_traceArgs_7999_);
lean_closure_set(v___f_8012_, 2, v_libFile_7995_);
lean_closure_set(v___f_8012_, 3, v___x_8010_);
lean_closure_set(v___f_8012_, 4, v_libName_7994_);
lean_closure_set(v___f_8012_, 5, v___x_8011_);
lean_closure_set(v___f_8012_, 6, v_linkLibs_7997_);
lean_closure_set(v___f_8012_, 7, v___x_8009_);
v___x_8013_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8014_ = l_Lake_Job_collectArray___redArg(v_linkObjs_7996_, v___x_8013_);
v___x_8015_ = lean_unsigned_to_nat(0u);
v___x_8016_ = 1;
v___x_8017_ = l_Lake_Job_bindM___redArg(v___x_8009_, v___x_8014_, v___f_8012_, v___x_8015_, v___x_8016_, v_a_8002_, v_a_8003_, v_a_8004_, v_a_8005_, v_a_8006_, v_a_8007_);
return v___x_8017_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object* v_libName_8018_, lean_object* v_libFile_8019_, lean_object* v_linkObjs_8020_, lean_object* v_linkLibs_8021_, lean_object* v_weakArgs_8022_, lean_object* v_traceArgs_8023_, lean_object* v_plugin_8024_, lean_object* v_linkDeps_8025_, lean_object* v_a_8026_, lean_object* v_a_8027_, lean_object* v_a_8028_, lean_object* v_a_8029_, lean_object* v_a_8030_, lean_object* v_a_8031_, lean_object* v_a_8032_){
_start:
{
uint8_t v_plugin_boxed_8033_; uint8_t v_linkDeps_boxed_8034_; lean_object* v_res_8035_; 
v_plugin_boxed_8033_ = lean_unbox(v_plugin_8024_);
v_linkDeps_boxed_8034_ = lean_unbox(v_linkDeps_8025_);
v_res_8035_ = l_Lake_buildLeanSharedLib(v_libName_8018_, v_libFile_8019_, v_linkObjs_8020_, v_linkLibs_8021_, v_weakArgs_8022_, v_traceArgs_8023_, v_plugin_boxed_8033_, v_linkDeps_boxed_8034_, v_a_8026_, v_a_8027_, v_a_8028_, v_a_8029_, v_a_8030_, v_a_8031_);
lean_dec_ref(v_a_8031_);
lean_dec_ref(v_a_8030_);
lean_dec(v_a_8029_);
lean_dec(v_a_8028_);
lean_dec(v_a_8027_);
lean_dec_ref(v_linkObjs_8020_);
return v_res_8035_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0(lean_object* v_libs_8036_, lean_object* v_objs_8037_, lean_object* v_weakArgs_8038_, lean_object* v_traceArgs_8039_, uint8_t v_sharedLean_8040_, lean_object* v_exeFile_8041_, lean_object* v___y_8042_, lean_object* v___y_8043_, lean_object* v___y_8044_, lean_object* v___y_8045_, lean_object* v___y_8046_, lean_object* v___y_8047_){
_start:
{
lean_object* v___x_8049_; 
v___x_8049_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_8036_, v___y_8047_);
if (lean_obj_tag(v___x_8049_) == 0)
{
lean_object* v_toContext_8050_; lean_object* v_lakeEnv_8051_; lean_object* v_lean_8052_; lean_object* v_a_8053_; lean_object* v_a_8054_; lean_object* v_leanLibDir_8055_; lean_object* v_cc_8056_; lean_object* v_log_8057_; uint8_t v_action_8058_; uint8_t v_wantsRebuild_8059_; lean_object* v_trace_8060_; lean_object* v_buildTime_8061_; lean_object* v___x_8063_; uint8_t v_isShared_8064_; uint8_t v_isSharedCheck_8100_; 
v_toContext_8050_ = lean_ctor_get(v___y_8046_, 1);
v_lakeEnv_8051_ = lean_ctor_get(v_toContext_8050_, 1);
v_lean_8052_ = lean_ctor_get(v_lakeEnv_8051_, 1);
v_a_8053_ = lean_ctor_get(v___x_8049_, 1);
lean_inc(v_a_8053_);
v_a_8054_ = lean_ctor_get(v___x_8049_, 0);
lean_inc(v_a_8054_);
lean_dec_ref(v___x_8049_);
v_leanLibDir_8055_ = lean_ctor_get(v_lean_8052_, 3);
v_cc_8056_ = lean_ctor_get(v_lean_8052_, 14);
v_log_8057_ = lean_ctor_get(v_a_8053_, 0);
v_action_8058_ = lean_ctor_get_uint8(v_a_8053_, sizeof(void*)*3);
v_wantsRebuild_8059_ = lean_ctor_get_uint8(v_a_8053_, sizeof(void*)*3 + 1);
v_trace_8060_ = lean_ctor_get(v_a_8053_, 1);
v_buildTime_8061_ = lean_ctor_get(v_a_8053_, 2);
v_isSharedCheck_8100_ = !lean_is_exclusive(v_a_8053_);
if (v_isSharedCheck_8100_ == 0)
{
v___x_8063_ = v_a_8053_;
v_isShared_8064_ = v_isSharedCheck_8100_;
goto v_resetjp_8062_;
}
else
{
lean_inc(v_buildTime_8061_);
lean_inc(v_trace_8060_);
lean_inc(v_log_8057_);
lean_dec(v_a_8053_);
v___x_8063_ = lean_box(0);
v_isShared_8064_ = v_isSharedCheck_8100_;
goto v_resetjp_8062_;
}
v_resetjp_8062_:
{
lean_object* v___x_8065_; lean_object* v___x_8066_; lean_object* v___x_8067_; lean_object* v___x_8068_; lean_object* v___x_8069_; lean_object* v___x_8070_; lean_object* v___x_8071_; lean_object* v___x_8072_; lean_object* v___x_8073_; lean_object* v___x_8074_; lean_object* v___x_8075_; 
v___x_8065_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_8037_, v_a_8054_);
lean_dec(v_a_8054_);
v___x_8066_ = l_Array_append___redArg(v___x_8065_, v_weakArgs_8038_);
v___x_8067_ = l_Array_append___redArg(v___x_8066_, v_traceArgs_8039_);
v___x_8068_ = lean_unsigned_to_nat(2u);
v___x_8069_ = lean_mk_empty_array_with_capacity(v___x_8068_);
lean_dec_ref(v___x_8069_);
v___x_8070_ = lean_obj_once(&l_Lake_buildLeanSharedLib___lam__0___closed__0, &l_Lake_buildLeanSharedLib___lam__0___closed__0_once, _init_l_Lake_buildLeanSharedLib___lam__0___closed__0);
lean_inc_ref(v_leanLibDir_8055_);
v___x_8071_ = lean_array_push(v___x_8070_, v_leanLibDir_8055_);
v___x_8072_ = l_Array_append___redArg(v___x_8067_, v___x_8071_);
lean_dec_ref(v___x_8071_);
v___x_8073_ = l_Lake_LeanInstall_ccLinkFlags(v_sharedLean_8040_, v_lean_8052_);
v___x_8074_ = l_Array_append___redArg(v___x_8072_, v___x_8073_);
lean_dec_ref(v___x_8073_);
lean_inc_ref(v_cc_8056_);
v___x_8075_ = l_Lake_compileExe(v_exeFile_8041_, v___x_8074_, v_cc_8056_, v_log_8057_);
lean_dec_ref(v___x_8074_);
if (lean_obj_tag(v___x_8075_) == 0)
{
lean_object* v_a_8076_; lean_object* v_a_8077_; lean_object* v___x_8079_; uint8_t v_isShared_8080_; uint8_t v_isSharedCheck_8087_; 
v_a_8076_ = lean_ctor_get(v___x_8075_, 0);
v_a_8077_ = lean_ctor_get(v___x_8075_, 1);
v_isSharedCheck_8087_ = !lean_is_exclusive(v___x_8075_);
if (v_isSharedCheck_8087_ == 0)
{
v___x_8079_ = v___x_8075_;
v_isShared_8080_ = v_isSharedCheck_8087_;
goto v_resetjp_8078_;
}
else
{
lean_inc(v_a_8077_);
lean_inc(v_a_8076_);
lean_dec(v___x_8075_);
v___x_8079_ = lean_box(0);
v_isShared_8080_ = v_isSharedCheck_8087_;
goto v_resetjp_8078_;
}
v_resetjp_8078_:
{
lean_object* v___x_8082_; 
if (v_isShared_8064_ == 0)
{
lean_ctor_set(v___x_8063_, 0, v_a_8077_);
v___x_8082_ = v___x_8063_;
goto v_reusejp_8081_;
}
else
{
lean_object* v_reuseFailAlloc_8086_; 
v_reuseFailAlloc_8086_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8086_, 0, v_a_8077_);
lean_ctor_set(v_reuseFailAlloc_8086_, 1, v_trace_8060_);
lean_ctor_set(v_reuseFailAlloc_8086_, 2, v_buildTime_8061_);
lean_ctor_set_uint8(v_reuseFailAlloc_8086_, sizeof(void*)*3, v_action_8058_);
lean_ctor_set_uint8(v_reuseFailAlloc_8086_, sizeof(void*)*3 + 1, v_wantsRebuild_8059_);
v___x_8082_ = v_reuseFailAlloc_8086_;
goto v_reusejp_8081_;
}
v_reusejp_8081_:
{
lean_object* v___x_8084_; 
if (v_isShared_8080_ == 0)
{
lean_ctor_set(v___x_8079_, 1, v___x_8082_);
v___x_8084_ = v___x_8079_;
goto v_reusejp_8083_;
}
else
{
lean_object* v_reuseFailAlloc_8085_; 
v_reuseFailAlloc_8085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8085_, 0, v_a_8076_);
lean_ctor_set(v_reuseFailAlloc_8085_, 1, v___x_8082_);
v___x_8084_ = v_reuseFailAlloc_8085_;
goto v_reusejp_8083_;
}
v_reusejp_8083_:
{
return v___x_8084_;
}
}
}
}
else
{
lean_object* v_a_8088_; lean_object* v_a_8089_; lean_object* v___x_8091_; uint8_t v_isShared_8092_; uint8_t v_isSharedCheck_8099_; 
v_a_8088_ = lean_ctor_get(v___x_8075_, 0);
v_a_8089_ = lean_ctor_get(v___x_8075_, 1);
v_isSharedCheck_8099_ = !lean_is_exclusive(v___x_8075_);
if (v_isSharedCheck_8099_ == 0)
{
v___x_8091_ = v___x_8075_;
v_isShared_8092_ = v_isSharedCheck_8099_;
goto v_resetjp_8090_;
}
else
{
lean_inc(v_a_8089_);
lean_inc(v_a_8088_);
lean_dec(v___x_8075_);
v___x_8091_ = lean_box(0);
v_isShared_8092_ = v_isSharedCheck_8099_;
goto v_resetjp_8090_;
}
v_resetjp_8090_:
{
lean_object* v___x_8094_; 
if (v_isShared_8064_ == 0)
{
lean_ctor_set(v___x_8063_, 0, v_a_8089_);
v___x_8094_ = v___x_8063_;
goto v_reusejp_8093_;
}
else
{
lean_object* v_reuseFailAlloc_8098_; 
v_reuseFailAlloc_8098_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8098_, 0, v_a_8089_);
lean_ctor_set(v_reuseFailAlloc_8098_, 1, v_trace_8060_);
lean_ctor_set(v_reuseFailAlloc_8098_, 2, v_buildTime_8061_);
lean_ctor_set_uint8(v_reuseFailAlloc_8098_, sizeof(void*)*3, v_action_8058_);
lean_ctor_set_uint8(v_reuseFailAlloc_8098_, sizeof(void*)*3 + 1, v_wantsRebuild_8059_);
v___x_8094_ = v_reuseFailAlloc_8098_;
goto v_reusejp_8093_;
}
v_reusejp_8093_:
{
lean_object* v___x_8096_; 
if (v_isShared_8092_ == 0)
{
lean_ctor_set(v___x_8091_, 1, v___x_8094_);
v___x_8096_ = v___x_8091_;
goto v_reusejp_8095_;
}
else
{
lean_object* v_reuseFailAlloc_8097_; 
v_reuseFailAlloc_8097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8097_, 0, v_a_8088_);
lean_ctor_set(v_reuseFailAlloc_8097_, 1, v___x_8094_);
v___x_8096_ = v_reuseFailAlloc_8097_;
goto v_reusejp_8095_;
}
v_reusejp_8095_:
{
return v___x_8096_;
}
}
}
}
}
}
else
{
lean_object* v_a_8101_; lean_object* v_a_8102_; lean_object* v___x_8104_; uint8_t v_isShared_8105_; uint8_t v_isSharedCheck_8109_; 
lean_dec_ref(v_exeFile_8041_);
v_a_8101_ = lean_ctor_get(v___x_8049_, 0);
v_a_8102_ = lean_ctor_get(v___x_8049_, 1);
v_isSharedCheck_8109_ = !lean_is_exclusive(v___x_8049_);
if (v_isSharedCheck_8109_ == 0)
{
v___x_8104_ = v___x_8049_;
v_isShared_8105_ = v_isSharedCheck_8109_;
goto v_resetjp_8103_;
}
else
{
lean_inc(v_a_8102_);
lean_inc(v_a_8101_);
lean_dec(v___x_8049_);
v___x_8104_ = lean_box(0);
v_isShared_8105_ = v_isSharedCheck_8109_;
goto v_resetjp_8103_;
}
v_resetjp_8103_:
{
lean_object* v___x_8107_; 
if (v_isShared_8105_ == 0)
{
v___x_8107_ = v___x_8104_;
goto v_reusejp_8106_;
}
else
{
lean_object* v_reuseFailAlloc_8108_; 
v_reuseFailAlloc_8108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8108_, 0, v_a_8101_);
lean_ctor_set(v_reuseFailAlloc_8108_, 1, v_a_8102_);
v___x_8107_ = v_reuseFailAlloc_8108_;
goto v_reusejp_8106_;
}
v_reusejp_8106_:
{
return v___x_8107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object* v_libs_8110_, lean_object* v_objs_8111_, lean_object* v_weakArgs_8112_, lean_object* v_traceArgs_8113_, lean_object* v_sharedLean_8114_, lean_object* v_exeFile_8115_, lean_object* v___y_8116_, lean_object* v___y_8117_, lean_object* v___y_8118_, lean_object* v___y_8119_, lean_object* v___y_8120_, lean_object* v___y_8121_, lean_object* v___y_8122_){
_start:
{
uint8_t v_sharedLean_boxed_8123_; lean_object* v_res_8124_; 
v_sharedLean_boxed_8123_ = lean_unbox(v_sharedLean_8114_);
v_res_8124_ = l_Lake_buildLeanExe___lam__0(v_libs_8110_, v_objs_8111_, v_weakArgs_8112_, v_traceArgs_8113_, v_sharedLean_boxed_8123_, v_exeFile_8115_, v___y_8116_, v___y_8117_, v___y_8118_, v___y_8119_, v___y_8120_, v___y_8121_);
lean_dec_ref(v___y_8120_);
lean_dec(v___y_8119_);
lean_dec(v___y_8118_);
lean_dec(v___y_8117_);
lean_dec_ref(v___y_8116_);
lean_dec_ref(v_traceArgs_8113_);
lean_dec_ref(v_weakArgs_8112_);
lean_dec_ref(v_objs_8111_);
lean_dec_ref(v_libs_8110_);
return v_res_8124_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object* v_objs_8125_, lean_object* v_weakArgs_8126_, lean_object* v_traceArgs_8127_, uint8_t v_sharedLean_8128_, lean_object* v_exeFile_8129_, lean_object* v_libs_8130_, lean_object* v___y_8131_, lean_object* v___y_8132_, lean_object* v___y_8133_, lean_object* v___y_8134_, lean_object* v___y_8135_, lean_object* v___y_8136_){
_start:
{
lean_object* v_log_8138_; uint8_t v_action_8139_; uint8_t v_wantsRebuild_8140_; lean_object* v_trace_8141_; lean_object* v_buildTime_8142_; lean_object* v___x_8144_; uint8_t v_isShared_8145_; uint8_t v_isSharedCheck_8201_; 
v_log_8138_ = lean_ctor_get(v___y_8136_, 0);
v_action_8139_ = lean_ctor_get_uint8(v___y_8136_, sizeof(void*)*3);
v_wantsRebuild_8140_ = lean_ctor_get_uint8(v___y_8136_, sizeof(void*)*3 + 1);
v_trace_8141_ = lean_ctor_get(v___y_8136_, 1);
v_buildTime_8142_ = lean_ctor_get(v___y_8136_, 2);
v_isSharedCheck_8201_ = !lean_is_exclusive(v___y_8136_);
if (v_isSharedCheck_8201_ == 0)
{
v___x_8144_ = v___y_8136_;
v_isShared_8145_ = v_isSharedCheck_8201_;
goto v_resetjp_8143_;
}
else
{
lean_inc(v_buildTime_8142_);
lean_inc(v_trace_8141_);
lean_inc(v_log_8138_);
lean_dec(v___y_8136_);
v___x_8144_ = lean_box(0);
v_isShared_8145_ = v_isSharedCheck_8201_;
goto v_resetjp_8143_;
}
v_resetjp_8143_:
{
lean_object* v_leanTrace_8146_; lean_object* v___x_8147_; lean_object* v___f_8148_; lean_object* v___x_8149_; uint64_t v___y_8151_; uint64_t v___x_8190_; lean_object* v___x_8191_; lean_object* v___x_8192_; uint8_t v___x_8193_; 
v_leanTrace_8146_ = lean_ctor_get(v___y_8135_, 2);
v___x_8147_ = lean_box(v_sharedLean_8128_);
lean_inc_ref(v_exeFile_8129_);
lean_inc_ref(v_traceArgs_8127_);
v___f_8148_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__0___boxed), 13, 6);
lean_closure_set(v___f_8148_, 0, v_libs_8130_);
lean_closure_set(v___f_8148_, 1, v_objs_8125_);
lean_closure_set(v___f_8148_, 2, v_weakArgs_8126_);
lean_closure_set(v___f_8148_, 3, v_traceArgs_8127_);
lean_closure_set(v___f_8148_, 4, v___x_8147_);
lean_closure_set(v___f_8148_, 5, v_exeFile_8129_);
lean_inc_ref(v_leanTrace_8146_);
v___x_8149_ = l_Lake_BuildTrace_mix(v_trace_8141_, v_leanTrace_8146_);
v___x_8190_ = l_Lake_Hash_nil;
v___x_8191_ = lean_unsigned_to_nat(0u);
v___x_8192_ = lean_array_get_size(v_traceArgs_8127_);
v___x_8193_ = lean_nat_dec_lt(v___x_8191_, v___x_8192_);
if (v___x_8193_ == 0)
{
v___y_8151_ = v___x_8190_;
goto v___jp_8150_;
}
else
{
uint8_t v___x_8194_; 
v___x_8194_ = lean_nat_dec_le(v___x_8192_, v___x_8192_);
if (v___x_8194_ == 0)
{
if (v___x_8193_ == 0)
{
v___y_8151_ = v___x_8190_;
goto v___jp_8150_;
}
else
{
size_t v___x_8195_; size_t v___x_8196_; uint64_t v___x_8197_; 
v___x_8195_ = ((size_t)0ULL);
v___x_8196_ = lean_usize_of_nat(v___x_8192_);
v___x_8197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8127_, v___x_8195_, v___x_8196_, v___x_8190_);
v___y_8151_ = v___x_8197_;
goto v___jp_8150_;
}
}
else
{
size_t v___x_8198_; size_t v___x_8199_; uint64_t v___x_8200_; 
v___x_8198_ = ((size_t)0ULL);
v___x_8199_ = lean_usize_of_nat(v___x_8192_);
v___x_8200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8127_, v___x_8198_, v___x_8199_, v___x_8190_);
v___y_8151_ = v___x_8200_;
goto v___jp_8150_;
}
}
v___jp_8150_:
{
lean_object* v___x_8152_; lean_object* v___x_8153_; lean_object* v___x_8154_; lean_object* v___x_8155_; lean_object* v___x_8156_; lean_object* v___x_8157_; lean_object* v___x_8158_; lean_object* v___x_8159_; lean_object* v___x_8160_; lean_object* v___x_8161_; lean_object* v___x_8162_; lean_object* v___x_8163_; lean_object* v___x_8165_; 
v___x_8152_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_8153_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_8154_ = lean_array_to_list(v_traceArgs_8127_);
v___x_8155_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_8154_);
lean_dec(v___x_8154_);
v___x_8156_ = lean_string_append(v___x_8153_, v___x_8155_);
lean_dec_ref(v___x_8155_);
v___x_8157_ = lean_string_append(v___x_8152_, v___x_8156_);
lean_dec_ref(v___x_8156_);
v___x_8158_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_8159_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_8160_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_8160_, 0, v___x_8157_);
lean_ctor_set(v___x_8160_, 1, v___x_8158_);
lean_ctor_set(v___x_8160_, 2, v___x_8159_);
lean_ctor_set_uint64(v___x_8160_, sizeof(void*)*3, v___y_8151_);
v___x_8161_ = l_Lake_BuildTrace_mix(v___x_8149_, v___x_8160_);
v___x_8162_ = l_Lake_platformTrace;
v___x_8163_ = l_Lake_BuildTrace_mix(v___x_8161_, v___x_8162_);
if (v_isShared_8145_ == 0)
{
lean_ctor_set(v___x_8144_, 1, v___x_8163_);
v___x_8165_ = v___x_8144_;
goto v_reusejp_8164_;
}
else
{
lean_object* v_reuseFailAlloc_8189_; 
v_reuseFailAlloc_8189_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8189_, 0, v_log_8138_);
lean_ctor_set(v_reuseFailAlloc_8189_, 1, v___x_8163_);
lean_ctor_set(v_reuseFailAlloc_8189_, 2, v_buildTime_8142_);
lean_ctor_set_uint8(v_reuseFailAlloc_8189_, sizeof(void*)*3, v_action_8139_);
lean_ctor_set_uint8(v_reuseFailAlloc_8189_, sizeof(void*)*3 + 1, v_wantsRebuild_8140_);
v___x_8165_ = v_reuseFailAlloc_8189_;
goto v_reusejp_8164_;
}
v_reusejp_8164_:
{
uint8_t v___x_8166_; lean_object* v___x_8167_; uint8_t v___x_8168_; lean_object* v___x_8169_; 
v___x_8166_ = 0;
v___x_8167_ = l_System_FilePath_exeExtension;
v___x_8168_ = 1;
v___x_8169_ = l_Lake_buildArtifactUnlessUpToDate(v_exeFile_8129_, v___f_8148_, v___x_8166_, v___x_8167_, v___x_8168_, v___x_8168_, v___x_8166_, v___y_8131_, v___y_8132_, v___y_8133_, v___y_8134_, v___y_8135_, v___x_8165_);
if (lean_obj_tag(v___x_8169_) == 0)
{
lean_object* v_a_8170_; lean_object* v_a_8171_; lean_object* v___x_8173_; uint8_t v_isShared_8174_; uint8_t v_isSharedCheck_8179_; 
v_a_8170_ = lean_ctor_get(v___x_8169_, 0);
v_a_8171_ = lean_ctor_get(v___x_8169_, 1);
v_isSharedCheck_8179_ = !lean_is_exclusive(v___x_8169_);
if (v_isSharedCheck_8179_ == 0)
{
v___x_8173_ = v___x_8169_;
v_isShared_8174_ = v_isSharedCheck_8179_;
goto v_resetjp_8172_;
}
else
{
lean_inc(v_a_8171_);
lean_inc(v_a_8170_);
lean_dec(v___x_8169_);
v___x_8173_ = lean_box(0);
v_isShared_8174_ = v_isSharedCheck_8179_;
goto v_resetjp_8172_;
}
v_resetjp_8172_:
{
lean_object* v_path_8175_; lean_object* v___x_8177_; 
v_path_8175_ = lean_ctor_get(v_a_8170_, 1);
lean_inc_ref(v_path_8175_);
lean_dec(v_a_8170_);
if (v_isShared_8174_ == 0)
{
lean_ctor_set(v___x_8173_, 0, v_path_8175_);
v___x_8177_ = v___x_8173_;
goto v_reusejp_8176_;
}
else
{
lean_object* v_reuseFailAlloc_8178_; 
v_reuseFailAlloc_8178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8178_, 0, v_path_8175_);
lean_ctor_set(v_reuseFailAlloc_8178_, 1, v_a_8171_);
v___x_8177_ = v_reuseFailAlloc_8178_;
goto v_reusejp_8176_;
}
v_reusejp_8176_:
{
return v___x_8177_;
}
}
}
else
{
lean_object* v_a_8180_; lean_object* v_a_8181_; lean_object* v___x_8183_; uint8_t v_isShared_8184_; uint8_t v_isSharedCheck_8188_; 
v_a_8180_ = lean_ctor_get(v___x_8169_, 0);
v_a_8181_ = lean_ctor_get(v___x_8169_, 1);
v_isSharedCheck_8188_ = !lean_is_exclusive(v___x_8169_);
if (v_isSharedCheck_8188_ == 0)
{
v___x_8183_ = v___x_8169_;
v_isShared_8184_ = v_isSharedCheck_8188_;
goto v_resetjp_8182_;
}
else
{
lean_inc(v_a_8181_);
lean_inc(v_a_8180_);
lean_dec(v___x_8169_);
v___x_8183_ = lean_box(0);
v_isShared_8184_ = v_isSharedCheck_8188_;
goto v_resetjp_8182_;
}
v_resetjp_8182_:
{
lean_object* v___x_8186_; 
if (v_isShared_8184_ == 0)
{
v___x_8186_ = v___x_8183_;
goto v_reusejp_8185_;
}
else
{
lean_object* v_reuseFailAlloc_8187_; 
v_reuseFailAlloc_8187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8187_, 0, v_a_8180_);
lean_ctor_set(v_reuseFailAlloc_8187_, 1, v_a_8181_);
v___x_8186_ = v_reuseFailAlloc_8187_;
goto v_reusejp_8185_;
}
v_reusejp_8185_:
{
return v___x_8186_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object* v_objs_8202_, lean_object* v_weakArgs_8203_, lean_object* v_traceArgs_8204_, lean_object* v_sharedLean_8205_, lean_object* v_exeFile_8206_, lean_object* v_libs_8207_, lean_object* v___y_8208_, lean_object* v___y_8209_, lean_object* v___y_8210_, lean_object* v___y_8211_, lean_object* v___y_8212_, lean_object* v___y_8213_, lean_object* v___y_8214_){
_start:
{
uint8_t v_sharedLean_boxed_8215_; lean_object* v_res_8216_; 
v_sharedLean_boxed_8215_ = lean_unbox(v_sharedLean_8205_);
v_res_8216_ = l_Lake_buildLeanExe___lam__1(v_objs_8202_, v_weakArgs_8203_, v_traceArgs_8204_, v_sharedLean_boxed_8215_, v_exeFile_8206_, v_libs_8207_, v___y_8208_, v___y_8209_, v___y_8210_, v___y_8211_, v___y_8212_, v___y_8213_);
lean_dec_ref(v___y_8212_);
lean_dec(v___y_8211_);
lean_dec(v___y_8210_);
lean_dec(v___y_8209_);
return v_res_8216_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2(lean_object* v_weakArgs_8217_, lean_object* v_traceArgs_8218_, uint8_t v_sharedLean_8219_, lean_object* v_exeFile_8220_, lean_object* v_linkLibs_8221_, lean_object* v___x_8222_, lean_object* v_objs_8223_, lean_object* v___y_8224_, lean_object* v___y_8225_, lean_object* v___y_8226_, lean_object* v___y_8227_, lean_object* v___y_8228_, lean_object* v___y_8229_){
_start:
{
lean_object* v_trace_8231_; lean_object* v___x_8232_; lean_object* v___f_8233_; lean_object* v___x_8234_; lean_object* v___x_8235_; lean_object* v___x_8236_; uint8_t v___x_8237_; lean_object* v___x_8238_; lean_object* v___x_8239_; 
v_trace_8231_ = lean_ctor_get(v___y_8229_, 1);
v___x_8232_ = lean_box(v_sharedLean_8219_);
v___f_8233_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__1___boxed), 13, 5);
lean_closure_set(v___f_8233_, 0, v_objs_8223_);
lean_closure_set(v___f_8233_, 1, v_weakArgs_8217_);
lean_closure_set(v___f_8233_, 2, v_traceArgs_8218_);
lean_closure_set(v___f_8233_, 3, v___x_8232_);
lean_closure_set(v___f_8233_, 4, v_exeFile_8220_);
v___x_8234_ = ((lean_object*)(l_Lake_buildSharedLib___lam__3___closed__0));
v___x_8235_ = l_Lake_Job_collectArray___redArg(v_linkLibs_8221_, v___x_8234_);
v___x_8236_ = lean_unsigned_to_nat(0u);
v___x_8237_ = 0;
v___x_8238_ = l_Lake_Job_mapM___redArg(v___x_8222_, v___x_8235_, v___f_8233_, v___x_8236_, v___x_8237_, v___y_8224_, v___y_8225_, v___y_8226_, v___y_8227_, v___y_8228_, v_trace_8231_);
v___x_8239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8239_, 0, v___x_8238_);
lean_ctor_set(v___x_8239_, 1, v___y_8229_);
return v___x_8239_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2___boxed(lean_object* v_weakArgs_8240_, lean_object* v_traceArgs_8241_, lean_object* v_sharedLean_8242_, lean_object* v_exeFile_8243_, lean_object* v_linkLibs_8244_, lean_object* v___x_8245_, lean_object* v_objs_8246_, lean_object* v___y_8247_, lean_object* v___y_8248_, lean_object* v___y_8249_, lean_object* v___y_8250_, lean_object* v___y_8251_, lean_object* v___y_8252_, lean_object* v___y_8253_){
_start:
{
uint8_t v_sharedLean_boxed_8254_; lean_object* v_res_8255_; 
v_sharedLean_boxed_8254_ = lean_unbox(v_sharedLean_8242_);
v_res_8255_ = l_Lake_buildLeanExe___lam__2(v_weakArgs_8240_, v_traceArgs_8241_, v_sharedLean_boxed_8254_, v_exeFile_8243_, v_linkLibs_8244_, v___x_8245_, v_objs_8246_, v___y_8247_, v___y_8248_, v___y_8249_, v___y_8250_, v___y_8251_, v___y_8252_);
lean_dec_ref(v___y_8251_);
lean_dec(v___y_8250_);
lean_dec(v___y_8249_);
lean_dec(v___y_8248_);
lean_dec_ref(v_linkLibs_8244_);
return v_res_8255_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object* v_exeFile_8256_, lean_object* v_linkObjs_8257_, lean_object* v_linkLibs_8258_, lean_object* v_weakArgs_8259_, lean_object* v_traceArgs_8260_, uint8_t v_sharedLean_8261_, lean_object* v_a_8262_, lean_object* v_a_8263_, lean_object* v_a_8264_, lean_object* v_a_8265_, lean_object* v_a_8266_, lean_object* v_a_8267_){
_start:
{
lean_object* v___x_8269_; lean_object* v___x_8270_; lean_object* v___f_8271_; lean_object* v___x_8272_; lean_object* v___x_8273_; lean_object* v___x_8274_; uint8_t v___x_8275_; lean_object* v___x_8276_; 
v___x_8269_ = l_Lake_instDataKindFilePath;
v___x_8270_ = lean_box(v_sharedLean_8261_);
v___f_8271_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__2___boxed), 14, 6);
lean_closure_set(v___f_8271_, 0, v_weakArgs_8259_);
lean_closure_set(v___f_8271_, 1, v_traceArgs_8260_);
lean_closure_set(v___f_8271_, 2, v___x_8270_);
lean_closure_set(v___f_8271_, 3, v_exeFile_8256_);
lean_closure_set(v___f_8271_, 4, v_linkLibs_8258_);
lean_closure_set(v___f_8271_, 5, v___x_8269_);
v___x_8272_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8273_ = l_Lake_Job_collectArray___redArg(v_linkObjs_8257_, v___x_8272_);
v___x_8274_ = lean_unsigned_to_nat(0u);
v___x_8275_ = 1;
v___x_8276_ = l_Lake_Job_bindM___redArg(v___x_8269_, v___x_8273_, v___f_8271_, v___x_8274_, v___x_8275_, v_a_8262_, v_a_8263_, v_a_8264_, v_a_8265_, v_a_8266_, v_a_8267_);
return v___x_8276_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object* v_exeFile_8277_, lean_object* v_linkObjs_8278_, lean_object* v_linkLibs_8279_, lean_object* v_weakArgs_8280_, lean_object* v_traceArgs_8281_, lean_object* v_sharedLean_8282_, lean_object* v_a_8283_, lean_object* v_a_8284_, lean_object* v_a_8285_, lean_object* v_a_8286_, lean_object* v_a_8287_, lean_object* v_a_8288_, lean_object* v_a_8289_){
_start:
{
uint8_t v_sharedLean_boxed_8290_; lean_object* v_res_8291_; 
v_sharedLean_boxed_8290_ = lean_unbox(v_sharedLean_8282_);
v_res_8291_ = l_Lake_buildLeanExe(v_exeFile_8277_, v_linkObjs_8278_, v_linkLibs_8279_, v_weakArgs_8280_, v_traceArgs_8281_, v_sharedLean_boxed_8290_, v_a_8283_, v_a_8284_, v_a_8285_, v_a_8286_, v_a_8287_, v_a_8288_);
lean_dec_ref(v_a_8288_);
lean_dec_ref(v_a_8287_);
lean_dec(v_a_8286_);
lean_dec(v_a_8285_);
lean_dec(v_a_8284_);
lean_dec_ref(v_linkObjs_8278_);
return v_res_8291_;
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
