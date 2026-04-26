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
lean_object* l_Lake_lowerHexUInt64(uint64_t);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
extern lean_object* l_System_Platform_target;
uint64_t lean_string_hash(lean_object*);
extern uint64_t l_Lake_Hash_nil;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
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
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_401_ = l_Lake_lowerHexUInt64(v_depHash_394_);
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
lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; uint64_t v___y_656_; uint8_t v_a_657_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; uint64_t v___y_664_; lean_object* v___y_667_; lean_object* v___y_668_; uint64_t v___y_669_; lean_object* v_a_670_; lean_object* v___y_697_; lean_object* v___y_698_; uint64_t v___y_699_; lean_object* v___y_702_; uint64_t v___y_703_; lean_object* v_a_704_; lean_object* v___y_730_; uint64_t v___y_731_; uint64_t v___y_734_; lean_object* v_a_735_; uint64_t v___y_761_; uint64_t v_depHash_764_; lean_object* v___x_789_; lean_object* v___x_790_; 
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
lean_ctor_set(v___x_658_, 0, v___y_654_);
lean_ctor_set(v___x_658_, 1, v___y_655_);
lean_ctor_set(v___x_658_, 2, v___y_653_);
lean_ctor_set_uint64(v___x_658_, sizeof(void*)*3, v___y_656_);
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
v___y_661_ = v_a_670_;
v___y_662_ = v___y_667_;
v___y_663_ = v___y_668_;
v___y_664_ = v___y_669_;
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
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
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
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
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
v___y_661_ = v_a_670_;
v___y_662_ = v___y_667_;
v___y_663_ = v___y_668_;
v___y_664_ = v___y_669_;
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
v___y_653_ = v_a_670_;
v___y_654_ = v___y_667_;
v___y_655_ = v___y_668_;
v___y_656_ = v___y_669_;
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
v___y_697_ = v___y_702_;
v___y_698_ = v_a_704_;
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
lean_dec_ref(v___y_702_);
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
lean_dec_ref(v___y_702_);
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
v___y_697_ = v___y_702_;
v___y_698_ = v_a_704_;
v___y_699_ = v___y_703_;
goto v___jp_696_;
}
else
{
lean_object* v_val_728_; 
v_val_728_ = lean_ctor_get(v_a_727_, 0);
lean_inc(v_val_728_);
lean_dec_ref(v_a_727_);
v___y_667_ = v___y_702_;
v___y_668_ = v_a_704_;
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
v___y_730_ = v_a_735_;
v___y_731_ = v___y_734_;
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
v___y_730_ = v_a_735_;
v___y_731_ = v___y_734_;
goto v___jp_729_;
}
else
{
lean_object* v_val_759_; 
v_val_759_ = lean_ctor_get(v_a_758_, 0);
lean_inc(v_val_759_);
lean_dec_ref(v_a_758_);
v___y_702_ = v_a_735_;
v___y_703_ = v___y_734_;
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
v___x_951_ = l_Lake_lowerHexUInt64(v_hash_945_);
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
v___x_1580_ = 2;
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
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(uint64_t v_inputHash_1770_, lean_object* v_self_1771_, lean_object* v_a_1772_){
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
v___x_1851_ = 1;
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
v___x_1823_ = 2;
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
v___x_1784_ = 1;
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
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate___redArg___boxed(lean_object* v_inputHash_1857_, lean_object* v_self_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
uint64_t v_inputHash_boxed_1861_; lean_object* v_res_1862_; 
v_inputHash_boxed_1861_ = lean_unbox_uint64(v_inputHash_1857_);
lean_dec_ref(v_inputHash_1857_);
v_res_1862_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_inputHash_boxed_1861_, v_self_1858_, v_a_1859_);
lean_dec(v_self_1858_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate(uint64_t v_inputHash_1863_, lean_object* v_self_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_inputHash_1863_, v_self_1864_, v_a_1870_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate___boxed(lean_object* v_inputHash_1873_, lean_object* v_self_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_){
_start:
{
uint64_t v_inputHash_boxed_1882_; lean_object* v_res_1883_; 
v_inputHash_boxed_1882_ = lean_unbox_uint64(v_inputHash_1873_);
lean_dec_ref(v_inputHash_1873_);
v_res_1883_ = l_Lake_SavedTrace_replayCachedIfUpToDate(v_inputHash_boxed_1882_, v_self_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
lean_dec_ref(v_a_1879_);
lean_dec(v_a_1878_);
lean_dec(v_a_1877_);
lean_dec(v_a_1876_);
lean_dec_ref(v_a_1875_);
lean_dec(v_self_1874_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(uint64_t v_inputHash_1884_, lean_object* v_self_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_inputHash_1884_, v_self_1885_, v_a_1886_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg___boxed(lean_object* v_inputHash_1889_, lean_object* v_self_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_){
_start:
{
uint64_t v_inputHash_boxed_1893_; lean_object* v_res_1894_; 
v_inputHash_boxed_1893_ = lean_unbox_uint64(v_inputHash_1889_);
lean_dec_ref(v_inputHash_1889_);
v_res_1894_ = l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(v_inputHash_boxed_1893_, v_self_1890_, v_a_1891_);
lean_dec(v_self_1890_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate(uint64_t v_inputHash_1895_, lean_object* v_self_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_inputHash_1895_, v_self_1896_, v_a_1902_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___boxed(lean_object* v_inputHash_1905_, lean_object* v_self_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_){
_start:
{
uint64_t v_inputHash_boxed_1914_; lean_object* v_res_1915_; 
v_inputHash_boxed_1914_ = lean_unbox_uint64(v_inputHash_1905_);
lean_dec_ref(v_inputHash_1905_);
v_res_1915_ = l_Lake_SavedTrace_replayOrFetchIfUpToDate(v_inputHash_boxed_1914_, v_self_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
lean_dec_ref(v_a_1911_);
lean_dec(v_a_1910_);
lean_dec(v_a_1909_);
lean_dec(v_a_1908_);
lean_dec_ref(v_a_1907_);
lean_dec(v_self_1906_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonPUnit___lam__0(lean_object* v_x_1916_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_box(0);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0(lean_object* v_x_1921_){
_start:
{
lean_object* v_descr_1922_; uint64_t v_hash_1923_; lean_object* v_ext_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; 
v_descr_1922_ = lean_ctor_get(v_x_1921_, 0);
v_hash_1923_ = lean_ctor_get_uint64(v_descr_1922_, sizeof(void*)*1);
v_ext_1924_ = lean_ctor_get(v_descr_1922_, 0);
v___x_1925_ = lean_string_utf8_byte_size(v_ext_1924_);
v___x_1926_ = lean_unsigned_to_nat(0u);
v___x_1927_ = lean_nat_dec_eq(v___x_1925_, v___x_1926_);
if (v___x_1927_ == 0)
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1928_ = l_Lake_lowerHexUInt64(v_hash_1923_);
v___x_1929_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_1930_ = lean_string_append(v___x_1928_, v___x_1929_);
v___x_1931_ = lean_string_append(v___x_1930_, v_ext_1924_);
v___x_1932_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
return v___x_1932_;
}
else
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = l_Lake_lowerHexUInt64(v_hash_1923_);
v___x_1934_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
return v___x_1934_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0___boxed(lean_object* v_x_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lake_instToOutputJsonArtifact___lam__0(v_x_1935_);
lean_dec_ref(v_x_1935_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0(lean_object* v_val_1939_, lean_object* v_a_x3f_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v___x_1943_; lean_object* v_log_1944_; uint8_t v_action_1945_; uint8_t v_wantsRebuild_1946_; lean_object* v_trace_1947_; lean_object* v_buildTime_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1959_; 
v___x_1943_ = lean_io_mono_ms_now();
v_log_1944_ = lean_ctor_get(v___y_1941_, 0);
v_action_1945_ = lean_ctor_get_uint8(v___y_1941_, sizeof(void*)*3);
v_wantsRebuild_1946_ = lean_ctor_get_uint8(v___y_1941_, sizeof(void*)*3 + 1);
v_trace_1947_ = lean_ctor_get(v___y_1941_, 1);
v_buildTime_1948_ = lean_ctor_get(v___y_1941_, 2);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___y_1941_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1950_ = v___y_1941_;
v_isShared_1951_ = v_isSharedCheck_1959_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_buildTime_1948_);
lean_inc(v_trace_1947_);
lean_inc(v_log_1944_);
lean_dec(v___y_1941_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1959_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1956_; 
v___x_1952_ = lean_nat_sub(v___x_1943_, v_val_1939_);
lean_dec(v___x_1943_);
v___x_1953_ = lean_box(0);
v___x_1954_ = lean_nat_add(v_buildTime_1948_, v___x_1952_);
lean_dec(v___x_1952_);
lean_dec(v_buildTime_1948_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 2, v___x_1954_);
v___x_1956_ = v___x_1950_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_log_1944_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_trace_1947_);
lean_ctor_set(v_reuseFailAlloc_1958_, 2, v___x_1954_);
lean_ctor_set_uint8(v_reuseFailAlloc_1958_, sizeof(void*)*3, v_action_1945_);
lean_ctor_set_uint8(v_reuseFailAlloc_1958_, sizeof(void*)*3 + 1, v_wantsRebuild_1946_);
v___x_1956_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
lean_object* v___x_1957_; 
v___x_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1953_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
return v___x_1957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0___boxed(lean_object* v_val_1960_, lean_object* v_a_x3f_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lake_buildAction___redArg___lam__0(v_val_1960_, v_a_x3f_1961_, v___y_1962_);
lean_dec(v_a_x3f_1961_);
lean_dec(v_val_1960_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg(lean_object* v_inst_1970_, lean_object* v_depTrace_1971_, lean_object* v_traceFile_1972_, lean_object* v_build_1973_, uint8_t v_action_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v_a_1983_; lean_object* v_a_1984_; lean_object* v_log_1987_; uint8_t v_action_1988_; uint8_t v_wantsRebuild_1989_; lean_object* v_trace_1990_; lean_object* v_buildTime_1991_; lean_object* v_toBuildConfig_1997_; lean_object* v_log_1998_; uint8_t v_action_1999_; uint8_t v_wantsRebuild_2000_; lean_object* v_trace_2001_; lean_object* v_buildTime_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2108_; 
v_toBuildConfig_1997_ = lean_ctor_get(v_a_1979_, 0);
v_log_1998_ = lean_ctor_get(v_a_1980_, 0);
v_action_1999_ = lean_ctor_get_uint8(v_a_1980_, sizeof(void*)*3);
v_wantsRebuild_2000_ = lean_ctor_get_uint8(v_a_1980_, sizeof(void*)*3 + 1);
v_trace_2001_ = lean_ctor_get(v_a_1980_, 1);
v_buildTime_2002_ = lean_ctor_get(v_a_1980_, 2);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_a_1980_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2004_ = v_a_1980_;
v_isShared_2005_ = v_isSharedCheck_2108_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_buildTime_2002_);
lean_inc(v_trace_2001_);
lean_inc(v_log_1998_);
lean_dec(v_a_1980_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2108_;
goto v_resetjp_2003_;
}
v___jp_1982_:
{
lean_object* v___x_1985_; 
v___x_1985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1985_, 0, v_a_1983_);
lean_ctor_set(v___x_1985_, 1, v_a_1984_);
return v___x_1985_;
}
v___jp_1986_:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1992_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_1993_ = lean_array_get_size(v_log_1987_);
v___x_1994_ = lean_array_push(v_log_1987_, v___x_1992_);
v___x_1995_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1995_, 0, v___x_1994_);
lean_ctor_set(v___x_1995_, 1, v_trace_1990_);
lean_ctor_set(v___x_1995_, 2, v_buildTime_1991_);
lean_ctor_set_uint8(v___x_1995_, sizeof(void*)*3, v_action_1988_);
lean_ctor_set_uint8(v___x_1995_, sizeof(void*)*3 + 1, v_wantsRebuild_1989_);
v___x_1996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1993_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
return v___x_1996_;
}
v_resetjp_2003_:
{
uint8_t v_noBuild_2006_; uint8_t v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v_noBuild_2006_ = lean_ctor_get_uint8(v_toBuildConfig_1997_, sizeof(void*)*2 + 2);
v___x_2007_ = l_Lake_JobAction_merge(v_action_1999_, v_action_1974_);
v___x_2008_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_1972_);
v___x_2009_ = l_System_FilePath_addExtension(v_traceFile_1972_, v___x_2008_);
if (v_noBuild_2006_ == 0)
{
lean_object* v___x_2010_; lean_object* v___x_2012_; 
v___x_2010_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_1998_);
if (v_isShared_2005_ == 0)
{
v___x_2012_ = v___x_2004_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_log_1998_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_trace_2001_);
lean_ctor_set(v_reuseFailAlloc_2092_, 2, v_buildTime_2002_);
lean_ctor_set_uint8(v_reuseFailAlloc_2092_, sizeof(void*)*3 + 1, v_wantsRebuild_2000_);
v___x_2012_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2013_; lean_object* v_a_2015_; lean_object* v_a_2016_; 
lean_ctor_set_uint8(v___x_2012_, sizeof(void*)*3, v___x_2007_);
lean_inc_ref(v_a_1979_);
lean_inc(v_a_1978_);
lean_inc(v_a_1977_);
lean_inc(v_a_1976_);
v___x_2013_ = lean_apply_7(v_build_1973_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v___x_2012_, lean_box(0));
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2020_; lean_object* v_a_2021_; lean_object* v_log_2022_; uint8_t v_action_2023_; uint8_t v_wantsRebuild_2024_; lean_object* v_trace_2025_; lean_object* v_buildTime_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v_a_2020_ = lean_ctor_get(v___x_2013_, 1);
lean_inc(v_a_2020_);
v_a_2021_ = lean_ctor_get(v___x_2013_, 0);
lean_inc_n(v_a_2021_, 2);
lean_dec_ref(v___x_2013_);
v_log_2022_ = lean_ctor_get(v_a_2020_, 0);
v_action_2023_ = lean_ctor_get_uint8(v_a_2020_, sizeof(void*)*3);
v_wantsRebuild_2024_ = lean_ctor_get_uint8(v_a_2020_, sizeof(void*)*3 + 1);
v_trace_2025_ = lean_ctor_get(v_a_2020_, 1);
v_buildTime_2026_ = lean_ctor_get(v_a_2020_, 2);
v___x_2027_ = lean_array_get_size(v_log_1998_);
lean_dec_ref(v_log_1998_);
v___x_2028_ = lean_array_get_size(v_log_2022_);
v___x_2029_ = l_Array_extract___redArg(v_log_2022_, v___x_2027_, v___x_2028_);
v___x_2030_ = lean_apply_1(v_inst_1970_, v_a_2021_);
v___x_2031_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1971_, v___x_2030_, v___x_2029_);
v___x_2032_ = l_Lake_BuildMetadata_writeFile(v_traceFile_1972_, v___x_2031_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2073_; 
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2073_ == 0)
{
lean_object* v_unused_2074_; 
v_unused_2074_ = lean_ctor_get(v___x_2032_, 0);
lean_dec(v_unused_2074_);
v___x_2034_ = v___x_2032_;
v_isShared_2035_ = v_isSharedCheck_2073_;
goto v_resetjp_2033_;
}
else
{
lean_dec(v___x_2032_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2073_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Lake_removeFileIfExists(v___x_2009_);
lean_dec_ref(v___x_2009_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2056_; 
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2056_ == 0)
{
lean_object* v_unused_2057_; 
v_unused_2057_ = lean_ctor_get(v___x_2036_, 0);
lean_dec(v_unused_2057_);
v___x_2038_ = v___x_2036_;
v_isShared_2039_ = v_isSharedCheck_2056_;
goto v_resetjp_2037_;
}
else
{
lean_dec(v___x_2036_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2056_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
lean_inc(v_a_2021_);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v_a_2021_);
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2021_);
v___x_2041_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v___x_2043_; 
if (v_isShared_2035_ == 0)
{
lean_ctor_set_tag(v___x_2034_, 1);
lean_ctor_set(v___x_2034_, 0, v___x_2041_);
v___x_2043_ = v___x_2034_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2041_);
v___x_2043_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v___x_2044_; lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
v___x_2044_ = l_Lake_buildAction___redArg___lam__0(v___x_2010_, v___x_2043_, v_a_2020_);
lean_dec_ref(v___x_2043_);
lean_dec(v___x_2010_);
v_a_2045_ = lean_ctor_get(v___x_2044_, 1);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2052_ == 0)
{
lean_object* v_unused_2053_; 
v_unused_2053_ = lean_ctor_get(v___x_2044_, 0);
lean_dec(v_unused_2053_);
v___x_2047_ = v___x_2044_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2044_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 0, v_a_2021_);
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2021_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
}
}
else
{
lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2069_; 
lean_inc(v_buildTime_2026_);
lean_inc_ref(v_trace_2025_);
lean_inc_ref(v_log_2022_);
lean_del_object(v___x_2034_);
lean_dec(v_a_2021_);
v_isSharedCheck_2069_ = !lean_is_exclusive(v_a_2020_);
if (v_isSharedCheck_2069_ == 0)
{
lean_object* v_unused_2070_; lean_object* v_unused_2071_; lean_object* v_unused_2072_; 
v_unused_2070_ = lean_ctor_get(v_a_2020_, 2);
lean_dec(v_unused_2070_);
v_unused_2071_ = lean_ctor_get(v_a_2020_, 1);
lean_dec(v_unused_2071_);
v_unused_2072_ = lean_ctor_get(v_a_2020_, 0);
lean_dec(v_unused_2072_);
v___x_2059_ = v_a_2020_;
v_isShared_2060_ = v_isSharedCheck_2069_;
goto v_resetjp_2058_;
}
else
{
lean_dec(v_a_2020_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2069_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v_a_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2067_; 
v_a_2061_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2061_);
lean_dec_ref(v___x_2036_);
v___x_2062_ = lean_io_error_to_string(v_a_2061_);
v___x_2063_ = 3;
v___x_2064_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2064_, 0, v___x_2062_);
lean_ctor_set_uint8(v___x_2064_, sizeof(void*)*1, v___x_2063_);
v___x_2065_ = lean_array_push(v_log_2022_, v___x_2064_);
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
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v_trace_2025_);
lean_ctor_set(v_reuseFailAlloc_2068_, 2, v_buildTime_2026_);
lean_ctor_set_uint8(v_reuseFailAlloc_2068_, sizeof(void*)*3, v_action_2023_);
lean_ctor_set_uint8(v_reuseFailAlloc_2068_, sizeof(void*)*3 + 1, v_wantsRebuild_2024_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
v_a_2015_ = v___x_2028_;
v_a_2016_ = v___x_2067_;
goto v___jp_2014_;
}
}
}
}
}
else
{
lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2086_; 
lean_inc(v_buildTime_2026_);
lean_inc_ref(v_trace_2025_);
lean_inc_ref(v_log_2022_);
lean_dec(v_a_2021_);
lean_dec_ref(v___x_2009_);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_a_2020_);
if (v_isSharedCheck_2086_ == 0)
{
lean_object* v_unused_2087_; lean_object* v_unused_2088_; lean_object* v_unused_2089_; 
v_unused_2087_ = lean_ctor_get(v_a_2020_, 2);
lean_dec(v_unused_2087_);
v_unused_2088_ = lean_ctor_get(v_a_2020_, 1);
lean_dec(v_unused_2088_);
v_unused_2089_ = lean_ctor_get(v_a_2020_, 0);
lean_dec(v_unused_2089_);
v___x_2076_ = v_a_2020_;
v_isShared_2077_ = v_isSharedCheck_2086_;
goto v_resetjp_2075_;
}
else
{
lean_dec(v_a_2020_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2086_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v_a_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2084_; 
v_a_2078_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2078_);
lean_dec_ref(v___x_2032_);
v___x_2079_ = lean_io_error_to_string(v_a_2078_);
v___x_2080_ = 3;
v___x_2081_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2081_, 0, v___x_2079_);
lean_ctor_set_uint8(v___x_2081_, sizeof(void*)*1, v___x_2080_);
v___x_2082_ = lean_array_push(v_log_2022_, v___x_2081_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v___x_2082_);
v___x_2084_ = v___x_2076_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2082_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_trace_2025_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v_buildTime_2026_);
lean_ctor_set_uint8(v_reuseFailAlloc_2085_, sizeof(void*)*3, v_action_2023_);
lean_ctor_set_uint8(v_reuseFailAlloc_2085_, sizeof(void*)*3 + 1, v_wantsRebuild_2024_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
v_a_2015_ = v___x_2028_;
v_a_2016_ = v___x_2084_;
goto v___jp_2014_;
}
}
}
}
else
{
lean_object* v_a_2090_; lean_object* v_a_2091_; 
lean_dec_ref(v___x_2009_);
lean_dec_ref(v_log_1998_);
lean_dec_ref(v_traceFile_1972_);
lean_dec_ref(v_inst_1970_);
v_a_2090_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2090_);
v_a_2091_ = lean_ctor_get(v___x_2013_, 1);
lean_inc(v_a_2091_);
lean_dec_ref(v___x_2013_);
v_a_2015_ = v_a_2090_;
v_a_2016_ = v_a_2091_;
goto v___jp_2014_;
}
v___jp_2014_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v_a_2019_; 
v___x_2017_ = lean_box(0);
v___x_2018_ = l_Lake_buildAction___redArg___lam__0(v___x_2010_, v___x_2017_, v_a_2016_);
lean_dec(v___x_2010_);
v_a_2019_ = lean_ctor_get(v___x_2018_, 1);
lean_inc(v_a_2019_);
lean_dec_ref(v___x_2018_);
v_a_1983_ = v_a_2015_;
v_a_1984_ = v_a_2019_;
goto v___jp_1982_;
}
}
}
else
{
uint8_t v___x_2093_; 
lean_dec_ref(v_a_1975_);
lean_dec_ref(v_build_1973_);
lean_dec_ref(v_inst_1970_);
v___x_2093_ = l_System_FilePath_pathExists(v_traceFile_1972_);
lean_dec_ref(v_traceFile_1972_);
if (v___x_2093_ == 0)
{
lean_dec_ref(v___x_2009_);
lean_del_object(v___x_2004_);
v_log_1987_ = v_log_1998_;
v_action_1988_ = v___x_2007_;
v_wantsRebuild_1989_ = v_noBuild_2006_;
v_trace_1990_ = v_trace_2001_;
v_buildTime_1991_ = v_buildTime_2002_;
goto v___jp_1986_;
}
else
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2094_ = lean_box(0);
v___x_2095_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_2096_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1971_, v___x_2094_, v___x_2095_);
v___x_2097_ = l_Lake_BuildMetadata_writeFile(v___x_2009_, v___x_2096_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_dec_ref(v___x_2097_);
lean_del_object(v___x_2004_);
v_log_1987_ = v_log_1998_;
v_action_1988_ = v___x_2007_;
v_wantsRebuild_1989_ = v_noBuild_2006_;
v_trace_1990_ = v_trace_2001_;
v_buildTime_1991_ = v_buildTime_2002_;
goto v___jp_1986_;
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2099_; uint8_t v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2105_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
lean_dec_ref(v___x_2097_);
v___x_2099_ = lean_io_error_to_string(v_a_2098_);
v___x_2100_ = 3;
v___x_2101_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2101_, 0, v___x_2099_);
lean_ctor_set_uint8(v___x_2101_, sizeof(void*)*1, v___x_2100_);
v___x_2102_ = lean_array_get_size(v_log_1998_);
v___x_2103_ = lean_array_push(v_log_1998_, v___x_2101_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 0, v___x_2103_);
v___x_2105_ = v___x_2004_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2103_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v_trace_2001_);
lean_ctor_set(v_reuseFailAlloc_2107_, 2, v_buildTime_2002_);
v___x_2105_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
lean_object* v___x_2106_; 
lean_ctor_set_uint8(v___x_2105_, sizeof(void*)*3, v___x_2007_);
lean_ctor_set_uint8(v___x_2105_, sizeof(void*)*3 + 1, v_noBuild_2006_);
v___x_2106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2102_);
lean_ctor_set(v___x_2106_, 1, v___x_2105_);
return v___x_2106_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___boxed(lean_object* v_inst_2109_, lean_object* v_depTrace_2110_, lean_object* v_traceFile_2111_, lean_object* v_build_2112_, lean_object* v_action_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
uint8_t v_action_boxed_2121_; lean_object* v_res_2122_; 
v_action_boxed_2121_ = lean_unbox(v_action_2113_);
v_res_2122_ = l_Lake_buildAction___redArg(v_inst_2109_, v_depTrace_2110_, v_traceFile_2111_, v_build_2112_, v_action_boxed_2121_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec(v_a_2117_);
lean_dec(v_a_2116_);
lean_dec(v_a_2115_);
lean_dec_ref(v_depTrace_2110_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction(lean_object* v_00_u03b1_2123_, lean_object* v_inst_2124_, lean_object* v_depTrace_2125_, lean_object* v_traceFile_2126_, lean_object* v_build_2127_, uint8_t v_action_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_){
_start:
{
lean_object* v___x_2136_; 
v___x_2136_ = l_Lake_buildAction___redArg(v_inst_2124_, v_depTrace_2125_, v_traceFile_2126_, v_build_2127_, v_action_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___boxed(lean_object* v_00_u03b1_2137_, lean_object* v_inst_2138_, lean_object* v_depTrace_2139_, lean_object* v_traceFile_2140_, lean_object* v_build_2141_, lean_object* v_action_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_){
_start:
{
uint8_t v_action_boxed_2150_; lean_object* v_res_2151_; 
v_action_boxed_2150_ = lean_unbox(v_action_2142_);
v_res_2151_ = l_Lake_buildAction(v_00_u03b1_2137_, v_inst_2138_, v_depTrace_2139_, v_traceFile_2140_, v_build_2141_, v_action_boxed_2150_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec(v_a_2146_);
lean_dec(v_a_2145_);
lean_dec(v_a_2144_);
lean_dec_ref(v_depTrace_2139_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg(lean_object* v_inst_2152_, lean_object* v_inst_2153_, lean_object* v_info_2154_, lean_object* v_depTrace_2155_, lean_object* v_traceFile_2156_, lean_object* v_build_2157_, uint8_t v_action_2158_, lean_object* v_oldTrace_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v_log_2167_; uint8_t v_action_2168_; uint8_t v_wantsRebuild_2169_; lean_object* v_trace_2170_; lean_object* v_buildTime_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2239_; 
v_log_2167_ = lean_ctor_get(v_a_2165_, 0);
v_action_2168_ = lean_ctor_get_uint8(v_a_2165_, sizeof(void*)*3);
v_wantsRebuild_2169_ = lean_ctor_get_uint8(v_a_2165_, sizeof(void*)*3 + 1);
v_trace_2170_ = lean_ctor_get(v_a_2165_, 1);
v_buildTime_2171_ = lean_ctor_get(v_a_2165_, 2);
v_isSharedCheck_2239_ = !lean_is_exclusive(v_a_2165_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2173_ = v_a_2165_;
v_isShared_2174_ = v_isSharedCheck_2239_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_buildTime_2171_);
lean_inc(v_trace_2170_);
lean_inc(v_log_2167_);
lean_dec(v_a_2165_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2239_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2175_; 
lean_inc_ref(v_traceFile_2156_);
v___x_2175_ = l_Lake_readTraceFile(v_traceFile_2156_, v_log_2167_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v_a_2177_; lean_object* v___x_2179_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
v_a_2177_ = lean_ctor_get(v___x_2175_, 1);
lean_inc(v_a_2177_);
lean_dec_ref(v___x_2175_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v_a_2177_);
v___x_2179_ = v___x_2173_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2177_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_trace_2170_);
lean_ctor_set(v_reuseFailAlloc_2226_, 2, v_buildTime_2171_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, sizeof(void*)*3, v_action_2168_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, sizeof(void*)*3 + 1, v_wantsRebuild_2169_);
v___x_2179_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2152_, v_inst_2153_, v_info_2154_, v_depTrace_2155_, v_a_2176_, v_oldTrace_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v___x_2179_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2216_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
v_a_2182_ = lean_ctor_get(v___x_2180_, 1);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2184_ = v___x_2180_;
v_isShared_2185_ = v_isSharedCheck_2216_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_inc(v_a_2181_);
lean_dec(v___x_2180_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2216_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
uint8_t v___x_2186_; uint8_t v___x_2187_; uint8_t v___x_2188_; 
v___x_2186_ = 0;
v___x_2187_ = lean_unbox(v_a_2181_);
lean_dec(v_a_2181_);
v___x_2188_ = l_Lake_instDecidableEqOutputStatus(v___x_2187_, v___x_2186_);
if (v___x_2188_ == 0)
{
uint8_t v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
lean_dec_ref(v_a_2160_);
lean_dec_ref(v_build_2157_);
lean_dec_ref(v_traceFile_2156_);
v___x_2189_ = 1;
v___x_2190_ = lean_box(v___x_2189_);
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 0, v___x_2190_);
v___x_2192_ = v___x_2184_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v_a_2182_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
else
{
lean_object* v___f_2194_; lean_object* v___x_2195_; 
lean_del_object(v___x_2184_);
v___f_2194_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2195_ = l_Lake_buildAction___redArg(v___f_2194_, v_depTrace_2155_, v_traceFile_2156_, v_build_2157_, v_action_2158_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2182_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2205_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 1);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2205_ == 0)
{
lean_object* v_unused_2206_; 
v_unused_2206_ = lean_ctor_get(v___x_2195_, 0);
lean_dec(v_unused_2206_);
v___x_2198_ = v___x_2195_;
v_isShared_2199_ = v_isSharedCheck_2205_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2195_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2205_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
uint8_t v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2203_; 
v___x_2200_ = 0;
v___x_2201_ = lean_box(v___x_2200_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 0, v___x_2201_);
v___x_2203_ = v___x_2198_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2201_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_a_2196_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
v_a_2207_ = lean_ctor_get(v___x_2195_, 0);
v_a_2208_ = lean_ctor_get(v___x_2195_, 1);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2195_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_inc(v_a_2207_);
lean_dec(v___x_2195_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2207_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec_ref(v_a_2160_);
lean_dec_ref(v_build_2157_);
lean_dec_ref(v_traceFile_2156_);
v_a_2217_ = lean_ctor_get(v___x_2180_, 0);
v_a_2218_ = lean_ctor_get(v___x_2180_, 1);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2180_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_inc(v_a_2217_);
lean_dec(v___x_2180_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2217_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
else
{
lean_object* v_a_2227_; lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2238_; 
lean_dec_ref(v_a_2160_);
lean_dec_ref(v_build_2157_);
lean_dec_ref(v_traceFile_2156_);
lean_dec(v_info_2154_);
lean_dec_ref(v_inst_2153_);
lean_dec_ref(v_inst_2152_);
v_a_2227_ = lean_ctor_get(v___x_2175_, 0);
v_a_2228_ = lean_ctor_get(v___x_2175_, 1);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2230_ = v___x_2175_;
v_isShared_2231_ = v_isSharedCheck_2238_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_inc(v_a_2227_);
lean_dec(v___x_2175_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2238_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v_a_2228_);
v___x_2233_ = v___x_2173_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2228_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_trace_2170_);
lean_ctor_set(v_reuseFailAlloc_2237_, 2, v_buildTime_2171_);
lean_ctor_set_uint8(v_reuseFailAlloc_2237_, sizeof(void*)*3, v_action_2168_);
lean_ctor_set_uint8(v_reuseFailAlloc_2237_, sizeof(void*)*3 + 1, v_wantsRebuild_2169_);
v___x_2233_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
lean_object* v___x_2235_; 
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 1, v___x_2233_);
v___x_2235_ = v___x_2230_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2227_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v___x_2233_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg___boxed(lean_object* v_inst_2240_, lean_object* v_inst_2241_, lean_object* v_info_2242_, lean_object* v_depTrace_2243_, lean_object* v_traceFile_2244_, lean_object* v_build_2245_, lean_object* v_action_2246_, lean_object* v_oldTrace_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_){
_start:
{
uint8_t v_action_boxed_2255_; lean_object* v_res_2256_; 
v_action_boxed_2255_ = lean_unbox(v_action_2246_);
v_res_2256_ = l_Lake_buildUnlessUpToDate_x3f___redArg(v_inst_2240_, v_inst_2241_, v_info_2242_, v_depTrace_2243_, v_traceFile_2244_, v_build_2245_, v_action_boxed_2255_, v_oldTrace_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_);
lean_dec_ref(v_a_2252_);
lean_dec(v_a_2251_);
lean_dec(v_a_2250_);
lean_dec(v_a_2249_);
lean_dec_ref(v_oldTrace_2247_);
lean_dec_ref(v_depTrace_2243_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f(lean_object* v_00_u03b9_2257_, lean_object* v_inst_2258_, lean_object* v_inst_2259_, lean_object* v_info_2260_, lean_object* v_depTrace_2261_, lean_object* v_traceFile_2262_, lean_object* v_build_2263_, uint8_t v_action_2264_, lean_object* v_oldTrace_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v_log_2273_; uint8_t v_action_2274_; uint8_t v_wantsRebuild_2275_; lean_object* v_trace_2276_; lean_object* v_buildTime_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2345_; 
v_log_2273_ = lean_ctor_get(v_a_2271_, 0);
v_action_2274_ = lean_ctor_get_uint8(v_a_2271_, sizeof(void*)*3);
v_wantsRebuild_2275_ = lean_ctor_get_uint8(v_a_2271_, sizeof(void*)*3 + 1);
v_trace_2276_ = lean_ctor_get(v_a_2271_, 1);
v_buildTime_2277_ = lean_ctor_get(v_a_2271_, 2);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_a_2271_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2279_ = v_a_2271_;
v_isShared_2280_ = v_isSharedCheck_2345_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_buildTime_2277_);
lean_inc(v_trace_2276_);
lean_inc(v_log_2273_);
lean_dec(v_a_2271_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2345_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2281_; 
lean_inc_ref(v_traceFile_2262_);
v___x_2281_ = l_Lake_readTraceFile(v_traceFile_2262_, v_log_2273_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v_a_2283_; lean_object* v___x_2285_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
v_a_2283_ = lean_ctor_get(v___x_2281_, 1);
lean_inc(v_a_2283_);
lean_dec_ref(v___x_2281_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v_a_2283_);
v___x_2285_ = v___x_2279_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2283_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_trace_2276_);
lean_ctor_set(v_reuseFailAlloc_2332_, 2, v_buildTime_2277_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*3, v_action_2274_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*3 + 1, v_wantsRebuild_2275_);
v___x_2285_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2258_, v_inst_2259_, v_info_2260_, v_depTrace_2261_, v_a_2282_, v_oldTrace_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v___x_2285_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2322_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
v_a_2288_ = lean_ctor_get(v___x_2286_, 1);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2290_ = v___x_2286_;
v_isShared_2291_ = v_isSharedCheck_2322_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_inc(v_a_2287_);
lean_dec(v___x_2286_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2322_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
uint8_t v___x_2292_; uint8_t v___x_2293_; uint8_t v___x_2294_; 
v___x_2292_ = 0;
v___x_2293_ = lean_unbox(v_a_2287_);
lean_dec(v_a_2287_);
v___x_2294_ = l_Lake_instDecidableEqOutputStatus(v___x_2293_, v___x_2292_);
if (v___x_2294_ == 0)
{
uint8_t v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2298_; 
lean_dec_ref(v_a_2266_);
lean_dec_ref(v_build_2263_);
lean_dec_ref(v_traceFile_2262_);
v___x_2295_ = 1;
v___x_2296_ = lean_box(v___x_2295_);
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v___x_2296_);
v___x_2298_ = v___x_2290_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2296_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v_a_2288_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
else
{
lean_object* v___f_2300_; lean_object* v___x_2301_; 
lean_del_object(v___x_2290_);
v___f_2300_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2301_ = l_Lake_buildAction___redArg(v___f_2300_, v_depTrace_2261_, v_traceFile_2262_, v_build_2263_, v_action_2264_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2288_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2311_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 1);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2311_ == 0)
{
lean_object* v_unused_2312_; 
v_unused_2312_ = lean_ctor_get(v___x_2301_, 0);
lean_dec(v_unused_2312_);
v___x_2304_ = v___x_2301_;
v_isShared_2305_ = v_isSharedCheck_2311_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2311_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
uint8_t v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2309_; 
v___x_2306_ = 0;
v___x_2307_ = lean_box(v___x_2306_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v___x_2307_);
v___x_2309_ = v___x_2304_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2307_);
lean_ctor_set(v_reuseFailAlloc_2310_, 1, v_a_2302_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
else
{
lean_object* v_a_2313_; lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
v_a_2313_ = lean_ctor_get(v___x_2301_, 0);
v_a_2314_ = lean_ctor_get(v___x_2301_, 1);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2301_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_inc(v_a_2313_);
lean_dec(v___x_2301_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2313_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
}
}
else
{
lean_object* v_a_2323_; lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec_ref(v_a_2266_);
lean_dec_ref(v_build_2263_);
lean_dec_ref(v_traceFile_2262_);
v_a_2323_ = lean_ctor_get(v___x_2286_, 0);
v_a_2324_ = lean_ctor_get(v___x_2286_, 1);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2286_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_inc(v_a_2323_);
lean_dec(v___x_2286_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2323_);
lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
}
else
{
lean_object* v_a_2333_; lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2344_; 
lean_dec_ref(v_a_2266_);
lean_dec_ref(v_build_2263_);
lean_dec_ref(v_traceFile_2262_);
lean_dec(v_info_2260_);
lean_dec_ref(v_inst_2259_);
lean_dec_ref(v_inst_2258_);
v_a_2333_ = lean_ctor_get(v___x_2281_, 0);
v_a_2334_ = lean_ctor_get(v___x_2281_, 1);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2336_ = v___x_2281_;
v_isShared_2337_ = v_isSharedCheck_2344_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_inc(v_a_2333_);
lean_dec(v___x_2281_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2344_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v_a_2334_);
v___x_2339_ = v___x_2279_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2334_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v_trace_2276_);
lean_ctor_set(v_reuseFailAlloc_2343_, 2, v_buildTime_2277_);
lean_ctor_set_uint8(v_reuseFailAlloc_2343_, sizeof(void*)*3, v_action_2274_);
lean_ctor_set_uint8(v_reuseFailAlloc_2343_, sizeof(void*)*3 + 1, v_wantsRebuild_2275_);
v___x_2339_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
lean_object* v___x_2341_; 
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 1, v___x_2339_);
v___x_2341_ = v___x_2336_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2333_);
lean_ctor_set(v_reuseFailAlloc_2342_, 1, v___x_2339_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___boxed(lean_object* v_00_u03b9_2346_, lean_object* v_inst_2347_, lean_object* v_inst_2348_, lean_object* v_info_2349_, lean_object* v_depTrace_2350_, lean_object* v_traceFile_2351_, lean_object* v_build_2352_, lean_object* v_action_2353_, lean_object* v_oldTrace_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_){
_start:
{
uint8_t v_action_boxed_2362_; lean_object* v_res_2363_; 
v_action_boxed_2362_ = lean_unbox(v_action_2353_);
v_res_2363_ = l_Lake_buildUnlessUpToDate_x3f(v_00_u03b9_2346_, v_inst_2347_, v_inst_2348_, v_info_2349_, v_depTrace_2350_, v_traceFile_2351_, v_build_2352_, v_action_boxed_2362_, v_oldTrace_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec(v_a_2357_);
lean_dec(v_a_2356_);
lean_dec_ref(v_oldTrace_2354_);
lean_dec_ref(v_depTrace_2350_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg(lean_object* v_inst_2364_, lean_object* v_inst_2365_, lean_object* v_info_2366_, lean_object* v_depTrace_2367_, lean_object* v_traceFile_2368_, lean_object* v_build_2369_, uint8_t v_action_2370_, lean_object* v_oldTrace_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v_a_2380_; lean_object* v_a_2381_; lean_object* v_log_2383_; uint8_t v_action_2384_; uint8_t v_wantsRebuild_2385_; lean_object* v_trace_2386_; lean_object* v_buildTime_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2425_; 
v_log_2383_ = lean_ctor_get(v_a_2377_, 0);
v_action_2384_ = lean_ctor_get_uint8(v_a_2377_, sizeof(void*)*3);
v_wantsRebuild_2385_ = lean_ctor_get_uint8(v_a_2377_, sizeof(void*)*3 + 1);
v_trace_2386_ = lean_ctor_get(v_a_2377_, 1);
v_buildTime_2387_ = lean_ctor_get(v_a_2377_, 2);
v_isSharedCheck_2425_ = !lean_is_exclusive(v_a_2377_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2389_ = v_a_2377_;
v_isShared_2390_ = v_isSharedCheck_2425_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_buildTime_2387_);
lean_inc(v_trace_2386_);
lean_inc(v_log_2383_);
lean_dec(v_a_2377_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2425_;
goto v_resetjp_2388_;
}
v___jp_2379_:
{
lean_object* v___x_2382_; 
v___x_2382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2382_, 0, v_a_2380_);
lean_ctor_set(v___x_2382_, 1, v_a_2381_);
return v___x_2382_;
}
v_resetjp_2388_:
{
lean_object* v___x_2391_; 
lean_inc_ref(v_traceFile_2368_);
v___x_2391_ = l_Lake_readTraceFile(v_traceFile_2368_, v_log_2383_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v_a_2393_; lean_object* v___x_2395_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
v_a_2393_ = lean_ctor_get(v___x_2391_, 1);
lean_inc(v_a_2393_);
lean_dec_ref(v___x_2391_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v_a_2393_);
v___x_2395_ = v___x_2389_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2393_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v_trace_2386_);
lean_ctor_set(v_reuseFailAlloc_2419_, 2, v_buildTime_2387_);
lean_ctor_set_uint8(v_reuseFailAlloc_2419_, sizeof(void*)*3, v_action_2384_);
lean_ctor_set_uint8(v_reuseFailAlloc_2419_, sizeof(void*)*3 + 1, v_wantsRebuild_2385_);
v___x_2395_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
lean_object* v___x_2396_; 
v___x_2396_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2364_, v_inst_2365_, v_info_2366_, v_depTrace_2367_, v_a_2392_, v_oldTrace_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v___x_2395_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2416_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
v_a_2398_ = lean_ctor_get(v___x_2396_, 1);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2400_ = v___x_2396_;
v_isShared_2401_ = v_isSharedCheck_2416_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_inc(v_a_2397_);
lean_dec(v___x_2396_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2416_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; lean_object* v_a_2404_; uint8_t v___x_2408_; uint8_t v___x_2409_; uint8_t v___x_2410_; 
v___x_2402_ = lean_box(0);
v___x_2408_ = 0;
v___x_2409_ = lean_unbox(v_a_2397_);
lean_dec(v_a_2397_);
v___x_2410_ = l_Lake_instDecidableEqOutputStatus(v___x_2409_, v___x_2408_);
if (v___x_2410_ == 0)
{
lean_dec_ref(v_a_2372_);
lean_dec_ref(v_build_2369_);
lean_dec_ref(v_traceFile_2368_);
v_a_2404_ = v_a_2398_;
goto v___jp_2403_;
}
else
{
lean_object* v___f_2411_; lean_object* v___x_2412_; 
v___f_2411_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2412_ = l_Lake_buildAction___redArg(v___f_2411_, v_depTrace_2367_, v_traceFile_2368_, v_build_2369_, v_action_2370_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2398_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 1);
lean_inc(v_a_2413_);
lean_dec_ref(v___x_2412_);
v_a_2404_ = v_a_2413_;
goto v___jp_2403_;
}
else
{
lean_object* v_a_2414_; lean_object* v_a_2415_; 
lean_del_object(v___x_2400_);
v_a_2414_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_a_2414_);
v_a_2415_ = lean_ctor_get(v___x_2412_, 1);
lean_inc(v_a_2415_);
lean_dec_ref(v___x_2412_);
v_a_2380_ = v_a_2414_;
v_a_2381_ = v_a_2415_;
goto v___jp_2379_;
}
}
v___jp_2403_:
{
lean_object* v___x_2406_; 
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 1, v_a_2404_);
lean_ctor_set(v___x_2400_, 0, v___x_2402_);
v___x_2406_ = v___x_2400_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2402_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v_a_2404_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
else
{
lean_object* v_a_2417_; lean_object* v_a_2418_; 
lean_dec_ref(v_a_2372_);
lean_dec_ref(v_build_2369_);
lean_dec_ref(v_traceFile_2368_);
v_a_2417_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2417_);
v_a_2418_ = lean_ctor_get(v___x_2396_, 1);
lean_inc(v_a_2418_);
lean_dec_ref(v___x_2396_);
v_a_2380_ = v_a_2417_;
v_a_2381_ = v_a_2418_;
goto v___jp_2379_;
}
}
}
else
{
lean_object* v_a_2420_; lean_object* v_a_2421_; lean_object* v___x_2423_; 
lean_dec_ref(v_a_2372_);
lean_dec_ref(v_build_2369_);
lean_dec_ref(v_traceFile_2368_);
lean_dec(v_info_2366_);
lean_dec_ref(v_inst_2365_);
lean_dec_ref(v_inst_2364_);
v_a_2420_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2420_);
v_a_2421_ = lean_ctor_get(v___x_2391_, 1);
lean_inc(v_a_2421_);
lean_dec_ref(v___x_2391_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v_a_2421_);
v___x_2423_ = v___x_2389_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2421_);
lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_trace_2386_);
lean_ctor_set(v_reuseFailAlloc_2424_, 2, v_buildTime_2387_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, sizeof(void*)*3, v_action_2384_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, sizeof(void*)*3 + 1, v_wantsRebuild_2385_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
v_a_2380_ = v_a_2420_;
v_a_2381_ = v___x_2423_;
goto v___jp_2379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg___boxed(lean_object* v_inst_2426_, lean_object* v_inst_2427_, lean_object* v_info_2428_, lean_object* v_depTrace_2429_, lean_object* v_traceFile_2430_, lean_object* v_build_2431_, lean_object* v_action_2432_, lean_object* v_oldTrace_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_){
_start:
{
uint8_t v_action_boxed_2441_; lean_object* v_res_2442_; 
v_action_boxed_2441_ = lean_unbox(v_action_2432_);
v_res_2442_ = l_Lake_buildUnlessUpToDate___redArg(v_inst_2426_, v_inst_2427_, v_info_2428_, v_depTrace_2429_, v_traceFile_2430_, v_build_2431_, v_action_boxed_2441_, v_oldTrace_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_);
lean_dec_ref(v_a_2438_);
lean_dec(v_a_2437_);
lean_dec(v_a_2436_);
lean_dec(v_a_2435_);
lean_dec_ref(v_oldTrace_2433_);
lean_dec_ref(v_depTrace_2429_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate(lean_object* v_00_u03b9_2443_, lean_object* v_inst_2444_, lean_object* v_inst_2445_, lean_object* v_info_2446_, lean_object* v_depTrace_2447_, lean_object* v_traceFile_2448_, lean_object* v_build_2449_, uint8_t v_action_2450_, lean_object* v_oldTrace_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v_a_2460_; lean_object* v_a_2461_; lean_object* v_log_2463_; uint8_t v_action_2464_; uint8_t v_wantsRebuild_2465_; lean_object* v_trace_2466_; lean_object* v_buildTime_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2505_; 
v_log_2463_ = lean_ctor_get(v_a_2457_, 0);
v_action_2464_ = lean_ctor_get_uint8(v_a_2457_, sizeof(void*)*3);
v_wantsRebuild_2465_ = lean_ctor_get_uint8(v_a_2457_, sizeof(void*)*3 + 1);
v_trace_2466_ = lean_ctor_get(v_a_2457_, 1);
v_buildTime_2467_ = lean_ctor_get(v_a_2457_, 2);
v_isSharedCheck_2505_ = !lean_is_exclusive(v_a_2457_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2469_ = v_a_2457_;
v_isShared_2470_ = v_isSharedCheck_2505_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_buildTime_2467_);
lean_inc(v_trace_2466_);
lean_inc(v_log_2463_);
lean_dec(v_a_2457_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2505_;
goto v_resetjp_2468_;
}
v___jp_2459_:
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2462_, 0, v_a_2460_);
lean_ctor_set(v___x_2462_, 1, v_a_2461_);
return v___x_2462_;
}
v_resetjp_2468_:
{
lean_object* v___x_2471_; 
lean_inc_ref(v_traceFile_2448_);
v___x_2471_ = l_Lake_readTraceFile(v_traceFile_2448_, v_log_2463_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; lean_object* v_a_2473_; lean_object* v___x_2475_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2472_);
v_a_2473_ = lean_ctor_get(v___x_2471_, 1);
lean_inc(v_a_2473_);
lean_dec_ref(v___x_2471_);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 0, v_a_2473_);
v___x_2475_ = v___x_2469_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2473_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v_trace_2466_);
lean_ctor_set(v_reuseFailAlloc_2499_, 2, v_buildTime_2467_);
lean_ctor_set_uint8(v_reuseFailAlloc_2499_, sizeof(void*)*3, v_action_2464_);
lean_ctor_set_uint8(v_reuseFailAlloc_2499_, sizeof(void*)*3 + 1, v_wantsRebuild_2465_);
v___x_2475_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2476_; 
v___x_2476_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2444_, v_inst_2445_, v_info_2446_, v_depTrace_2447_, v_a_2472_, v_oldTrace_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v___x_2475_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2496_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
v_a_2478_ = lean_ctor_get(v___x_2476_, 1);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2480_ = v___x_2476_;
v_isShared_2481_ = v_isSharedCheck_2496_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_inc(v_a_2477_);
lean_dec(v___x_2476_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2496_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2482_; lean_object* v_a_2484_; uint8_t v___x_2488_; uint8_t v___x_2489_; uint8_t v___x_2490_; 
v___x_2482_ = lean_box(0);
v___x_2488_ = 0;
v___x_2489_ = lean_unbox(v_a_2477_);
lean_dec(v_a_2477_);
v___x_2490_ = l_Lake_instDecidableEqOutputStatus(v___x_2489_, v___x_2488_);
if (v___x_2490_ == 0)
{
lean_dec_ref(v_a_2452_);
lean_dec_ref(v_build_2449_);
lean_dec_ref(v_traceFile_2448_);
v_a_2484_ = v_a_2478_;
goto v___jp_2483_;
}
else
{
lean_object* v___f_2491_; lean_object* v___x_2492_; 
v___f_2491_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2492_ = l_Lake_buildAction___redArg(v___f_2491_, v_depTrace_2447_, v_traceFile_2448_, v_build_2449_, v_action_2450_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2478_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_a_2493_; 
v_a_2493_ = lean_ctor_get(v___x_2492_, 1);
lean_inc(v_a_2493_);
lean_dec_ref(v___x_2492_);
v_a_2484_ = v_a_2493_;
goto v___jp_2483_;
}
else
{
lean_object* v_a_2494_; lean_object* v_a_2495_; 
lean_del_object(v___x_2480_);
v_a_2494_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_a_2494_);
v_a_2495_ = lean_ctor_get(v___x_2492_, 1);
lean_inc(v_a_2495_);
lean_dec_ref(v___x_2492_);
v_a_2460_ = v_a_2494_;
v_a_2461_ = v_a_2495_;
goto v___jp_2459_;
}
}
v___jp_2483_:
{
lean_object* v___x_2486_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 1, v_a_2484_);
lean_ctor_set(v___x_2480_, 0, v___x_2482_);
v___x_2486_ = v___x_2480_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v___x_2482_);
lean_ctor_set(v_reuseFailAlloc_2487_, 1, v_a_2484_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
else
{
lean_object* v_a_2497_; lean_object* v_a_2498_; 
lean_dec_ref(v_a_2452_);
lean_dec_ref(v_build_2449_);
lean_dec_ref(v_traceFile_2448_);
v_a_2497_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2497_);
v_a_2498_ = lean_ctor_get(v___x_2476_, 1);
lean_inc(v_a_2498_);
lean_dec_ref(v___x_2476_);
v_a_2460_ = v_a_2497_;
v_a_2461_ = v_a_2498_;
goto v___jp_2459_;
}
}
}
else
{
lean_object* v_a_2500_; lean_object* v_a_2501_; lean_object* v___x_2503_; 
lean_dec_ref(v_a_2452_);
lean_dec_ref(v_build_2449_);
lean_dec_ref(v_traceFile_2448_);
lean_dec(v_info_2446_);
lean_dec_ref(v_inst_2445_);
lean_dec_ref(v_inst_2444_);
v_a_2500_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2500_);
v_a_2501_ = lean_ctor_get(v___x_2471_, 1);
lean_inc(v_a_2501_);
lean_dec_ref(v___x_2471_);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 0, v_a_2501_);
v___x_2503_ = v___x_2469_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2501_);
lean_ctor_set(v_reuseFailAlloc_2504_, 1, v_trace_2466_);
lean_ctor_set(v_reuseFailAlloc_2504_, 2, v_buildTime_2467_);
lean_ctor_set_uint8(v_reuseFailAlloc_2504_, sizeof(void*)*3, v_action_2464_);
lean_ctor_set_uint8(v_reuseFailAlloc_2504_, sizeof(void*)*3 + 1, v_wantsRebuild_2465_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
v_a_2460_ = v_a_2500_;
v_a_2461_ = v___x_2503_;
goto v___jp_2459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___boxed(lean_object* v_00_u03b9_2506_, lean_object* v_inst_2507_, lean_object* v_inst_2508_, lean_object* v_info_2509_, lean_object* v_depTrace_2510_, lean_object* v_traceFile_2511_, lean_object* v_build_2512_, lean_object* v_action_2513_, lean_object* v_oldTrace_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_){
_start:
{
uint8_t v_action_boxed_2522_; lean_object* v_res_2523_; 
v_action_boxed_2522_ = lean_unbox(v_action_2513_);
v_res_2523_ = l_Lake_buildUnlessUpToDate(v_00_u03b9_2506_, v_inst_2507_, v_inst_2508_, v_info_2509_, v_depTrace_2510_, v_traceFile_2511_, v_build_2512_, v_action_boxed_2522_, v_oldTrace_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
lean_dec_ref(v_a_2519_);
lean_dec(v_a_2518_);
lean_dec(v_a_2517_);
lean_dec(v_a_2516_);
lean_dec_ref(v_oldTrace_2514_);
lean_dec_ref(v_depTrace_2510_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFileHash(lean_object* v_file_2525_, uint64_t v_hash_2526_){
_start:
{
lean_object* v___x_2528_; lean_object* v_hashFile_2529_; lean_object* v___x_2530_; 
v___x_2528_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
v_hashFile_2529_ = lean_string_append(v_file_2525_, v___x_2528_);
lean_inc_ref(v_hashFile_2529_);
v___x_2530_ = l_Lake_createParentDirs(v_hashFile_2529_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
lean_dec_ref(v___x_2530_);
v___x_2531_ = l_Lake_lowerHexUInt64(v_hash_2526_);
v___x_2532_ = l_IO_FS_writeFile(v_hashFile_2529_, v___x_2531_);
lean_dec_ref(v___x_2531_);
lean_dec_ref(v_hashFile_2529_);
return v___x_2532_;
}
else
{
lean_dec_ref(v_hashFile_2529_);
return v___x_2530_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_writeFileHash___boxed(lean_object* v_file_2533_, lean_object* v_hash_2534_, lean_object* v_a_2535_){
_start:
{
uint64_t v_hash_boxed_2536_; lean_object* v_res_2537_; 
v_hash_boxed_2536_ = lean_unbox_uint64(v_hash_2534_);
lean_dec_ref(v_hash_2534_);
v_res_2537_ = l_Lake_writeFileHash(v_file_2533_, v_hash_boxed_2536_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object* v_file_2538_, uint8_t v_text_2539_){
_start:
{
lean_object* v___y_2542_; 
if (v_text_2539_ == 0)
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Lake_computeBinFileHash(v_file_2538_);
v___y_2542_ = v___x_2554_;
goto v___jp_2541_;
}
else
{
lean_object* v___x_2555_; 
v___x_2555_ = l_Lake_computeTextFileHash(v_file_2538_);
v___y_2542_ = v___x_2555_;
goto v___jp_2541_;
}
v___jp_2541_:
{
if (lean_obj_tag(v___y_2542_) == 0)
{
lean_object* v_a_2543_; uint64_t v___x_2544_; lean_object* v___x_2545_; 
v_a_2543_ = lean_ctor_get(v___y_2542_, 0);
lean_inc(v_a_2543_);
lean_dec_ref(v___y_2542_);
v___x_2544_ = lean_unbox_uint64(v_a_2543_);
lean_dec(v_a_2543_);
v___x_2545_ = l_Lake_writeFileHash(v_file_2538_, v___x_2544_);
return v___x_2545_;
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
lean_dec_ref(v_file_2538_);
v_a_2546_ = lean_ctor_get(v___y_2542_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___y_2542_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v___y_2542_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___y_2542_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_a_2546_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash___boxed(lean_object* v_file_2556_, lean_object* v_text_2557_, lean_object* v_a_2558_){
_start:
{
uint8_t v_text_boxed_2559_; lean_object* v_res_2560_; 
v_text_boxed_2559_ = lean_unbox(v_text_2557_);
v_res_2560_ = l_Lake_cacheFileHash(v_file_2556_, v_text_boxed_2559_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lake_clearFileHash(lean_object* v_file_2561_){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2563_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
v___x_2564_ = lean_string_append(v_file_2561_, v___x_2563_);
v___x_2565_ = l_Lake_removeFileIfExists(v___x_2564_);
lean_dec_ref(v___x_2564_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l_Lake_clearFileHash___boxed(lean_object* v_file_2566_, lean_object* v_a_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l_Lake_clearFileHash(v_file_2566_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg(lean_object* v_file_2569_, uint8_t v_text_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v_toBuildConfig_2574_; uint8_t v_trustHash_2575_; lean_object* v___x_2576_; lean_object* v_hashFile_2577_; uint8_t v___y_2579_; lean_object* v___y_2580_; uint8_t v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2617_; 
v_toBuildConfig_2574_ = lean_ctor_get(v_a_2571_, 0);
v_trustHash_2575_ = lean_ctor_get_uint8(v_toBuildConfig_2574_, sizeof(void*)*2 + 1);
v___x_2576_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
lean_inc_ref(v_file_2569_);
v_hashFile_2577_ = lean_string_append(v_file_2569_, v___x_2576_);
if (v_trustHash_2575_ == 0)
{
v___y_2617_ = v_a_2572_;
goto v___jp_2616_;
}
else
{
lean_object* v___x_2630_; 
v___x_2630_ = l_Lake_Hash_load_x3f(v_hashFile_2577_);
if (lean_obj_tag(v___x_2630_) == 1)
{
lean_object* v_val_2631_; lean_object* v___x_2632_; 
lean_dec_ref(v_hashFile_2577_);
lean_dec_ref(v_file_2569_);
v_val_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_val_2631_);
lean_dec_ref(v___x_2630_);
v___x_2632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2632_, 0, v_val_2631_);
lean_ctor_set(v___x_2632_, 1, v_a_2572_);
return v___x_2632_;
}
else
{
lean_dec(v___x_2630_);
v___y_2617_ = v_a_2572_;
goto v___jp_2616_;
}
}
v___jp_2578_:
{
if (lean_obj_tag(v___y_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v___x_2586_; 
v_a_2585_ = lean_ctor_get(v___y_2584_, 0);
lean_inc(v_a_2585_);
lean_dec_ref(v___y_2584_);
lean_inc_ref(v_hashFile_2577_);
v___x_2586_ = l_Lake_createParentDirs(v_hashFile_2577_);
if (lean_obj_tag(v___x_2586_) == 0)
{
uint64_t v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
lean_dec_ref(v___x_2586_);
v___x_2587_ = lean_unbox_uint64(v_a_2585_);
v___x_2588_ = l_Lake_lowerHexUInt64(v___x_2587_);
v___x_2589_ = l_IO_FS_writeFile(v_hashFile_2577_, v___x_2588_);
lean_dec_ref(v___x_2588_);
lean_dec_ref(v_hashFile_2577_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
lean_dec_ref(v___x_2589_);
v___x_2590_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2590_, 0, v___y_2583_);
lean_ctor_set(v___x_2590_, 1, v___y_2582_);
lean_ctor_set(v___x_2590_, 2, v___y_2580_);
lean_ctor_set_uint8(v___x_2590_, sizeof(void*)*3, v___y_2579_);
lean_ctor_set_uint8(v___x_2590_, sizeof(void*)*3 + 1, v___y_2581_);
v___x_2591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2591_, 0, v_a_2585_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
return v___x_2591_;
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2593_; uint8_t v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
lean_dec(v_a_2585_);
v_a_2592_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2592_);
lean_dec_ref(v___x_2589_);
v___x_2593_ = lean_io_error_to_string(v_a_2592_);
v___x_2594_ = 3;
v___x_2595_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2595_, 0, v___x_2593_);
lean_ctor_set_uint8(v___x_2595_, sizeof(void*)*1, v___x_2594_);
v___x_2596_ = lean_array_get_size(v___y_2583_);
v___x_2597_ = lean_array_push(v___y_2583_, v___x_2595_);
v___x_2598_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2598_, 0, v___x_2597_);
lean_ctor_set(v___x_2598_, 1, v___y_2582_);
lean_ctor_set(v___x_2598_, 2, v___y_2580_);
lean_ctor_set_uint8(v___x_2598_, sizeof(void*)*3, v___y_2579_);
lean_ctor_set_uint8(v___x_2598_, sizeof(void*)*3 + 1, v___y_2581_);
v___x_2599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2596_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
return v___x_2599_;
}
}
else
{
lean_object* v_a_2600_; lean_object* v___x_2601_; uint8_t v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
lean_dec(v_a_2585_);
lean_dec_ref(v_hashFile_2577_);
v_a_2600_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2600_);
lean_dec_ref(v___x_2586_);
v___x_2601_ = lean_io_error_to_string(v_a_2600_);
v___x_2602_ = 3;
v___x_2603_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2603_, 0, v___x_2601_);
lean_ctor_set_uint8(v___x_2603_, sizeof(void*)*1, v___x_2602_);
v___x_2604_ = lean_array_get_size(v___y_2583_);
v___x_2605_ = lean_array_push(v___y_2583_, v___x_2603_);
v___x_2606_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
lean_ctor_set(v___x_2606_, 1, v___y_2582_);
lean_ctor_set(v___x_2606_, 2, v___y_2580_);
lean_ctor_set_uint8(v___x_2606_, sizeof(void*)*3, v___y_2579_);
lean_ctor_set_uint8(v___x_2606_, sizeof(void*)*3 + 1, v___y_2581_);
v___x_2607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2604_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
return v___x_2607_;
}
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2609_; uint8_t v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
lean_dec_ref(v_hashFile_2577_);
v_a_2608_ = lean_ctor_get(v___y_2584_, 0);
lean_inc(v_a_2608_);
lean_dec_ref(v___y_2584_);
v___x_2609_ = lean_io_error_to_string(v_a_2608_);
v___x_2610_ = 3;
v___x_2611_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2611_, 0, v___x_2609_);
lean_ctor_set_uint8(v___x_2611_, sizeof(void*)*1, v___x_2610_);
v___x_2612_ = lean_array_get_size(v___y_2583_);
v___x_2613_ = lean_array_push(v___y_2583_, v___x_2611_);
v___x_2614_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
lean_ctor_set(v___x_2614_, 1, v___y_2582_);
lean_ctor_set(v___x_2614_, 2, v___y_2580_);
lean_ctor_set_uint8(v___x_2614_, sizeof(void*)*3, v___y_2579_);
lean_ctor_set_uint8(v___x_2614_, sizeof(void*)*3 + 1, v___y_2581_);
v___x_2615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2612_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
return v___x_2615_;
}
}
v___jp_2616_:
{
if (v_text_2570_ == 0)
{
lean_object* v_log_2618_; uint8_t v_action_2619_; uint8_t v_wantsRebuild_2620_; lean_object* v_trace_2621_; lean_object* v_buildTime_2622_; lean_object* v___x_2623_; 
v_log_2618_ = lean_ctor_get(v___y_2617_, 0);
lean_inc_ref(v_log_2618_);
v_action_2619_ = lean_ctor_get_uint8(v___y_2617_, sizeof(void*)*3);
v_wantsRebuild_2620_ = lean_ctor_get_uint8(v___y_2617_, sizeof(void*)*3 + 1);
v_trace_2621_ = lean_ctor_get(v___y_2617_, 1);
lean_inc_ref(v_trace_2621_);
v_buildTime_2622_ = lean_ctor_get(v___y_2617_, 2);
lean_inc(v_buildTime_2622_);
lean_dec_ref(v___y_2617_);
v___x_2623_ = l_Lake_computeBinFileHash(v_file_2569_);
lean_dec_ref(v_file_2569_);
v___y_2579_ = v_action_2619_;
v___y_2580_ = v_buildTime_2622_;
v___y_2581_ = v_wantsRebuild_2620_;
v___y_2582_ = v_trace_2621_;
v___y_2583_ = v_log_2618_;
v___y_2584_ = v___x_2623_;
goto v___jp_2578_;
}
else
{
lean_object* v_log_2624_; uint8_t v_action_2625_; uint8_t v_wantsRebuild_2626_; lean_object* v_trace_2627_; lean_object* v_buildTime_2628_; lean_object* v___x_2629_; 
v_log_2624_ = lean_ctor_get(v___y_2617_, 0);
lean_inc_ref(v_log_2624_);
v_action_2625_ = lean_ctor_get_uint8(v___y_2617_, sizeof(void*)*3);
v_wantsRebuild_2626_ = lean_ctor_get_uint8(v___y_2617_, sizeof(void*)*3 + 1);
v_trace_2627_ = lean_ctor_get(v___y_2617_, 1);
lean_inc_ref(v_trace_2627_);
v_buildTime_2628_ = lean_ctor_get(v___y_2617_, 2);
lean_inc(v_buildTime_2628_);
lean_dec_ref(v___y_2617_);
v___x_2629_ = l_Lake_computeTextFileHash(v_file_2569_);
lean_dec_ref(v_file_2569_);
v___y_2579_ = v_action_2625_;
v___y_2580_ = v_buildTime_2628_;
v___y_2581_ = v_wantsRebuild_2626_;
v___y_2582_ = v_trace_2627_;
v___y_2583_ = v_log_2624_;
v___y_2584_ = v___x_2629_;
goto v___jp_2578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg___boxed(lean_object* v_file_2633_, lean_object* v_text_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
uint8_t v_text_boxed_2638_; lean_object* v_res_2639_; 
v_text_boxed_2638_ = lean_unbox(v_text_2634_);
v_res_2639_ = l_Lake_fetchFileHash___redArg(v_file_2633_, v_text_boxed_2638_, v_a_2635_, v_a_2636_);
lean_dec_ref(v_a_2635_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash(lean_object* v_file_2640_, uint8_t v_text_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Lake_fetchFileHash___redArg(v_file_2640_, v_text_2641_, v_a_2646_, v_a_2647_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___boxed(lean_object* v_file_2650_, lean_object* v_text_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
uint8_t v_text_boxed_2659_; lean_object* v_res_2660_; 
v_text_boxed_2659_ = lean_unbox(v_text_2651_);
v_res_2660_ = l_Lake_fetchFileHash(v_file_2650_, v_text_boxed_2659_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg(lean_object* v_file_2661_, uint8_t v_text_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_){
_start:
{
lean_object* v___x_2666_; 
lean_inc_ref(v_file_2661_);
v___x_2666_ = l_Lake_fetchFileHash___redArg(v_file_2661_, v_text_2662_, v_a_2663_, v_a_2664_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2705_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 1);
v_a_2668_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2670_ = v___x_2666_;
v_isShared_2671_ = v_isSharedCheck_2705_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2667_);
lean_inc(v_a_2668_);
lean_dec(v___x_2666_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2705_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v_log_2672_; uint8_t v_action_2673_; uint8_t v_wantsRebuild_2674_; lean_object* v_trace_2675_; lean_object* v_buildTime_2676_; lean_object* v___x_2677_; 
v_log_2672_ = lean_ctor_get(v_a_2667_, 0);
v_action_2673_ = lean_ctor_get_uint8(v_a_2667_, sizeof(void*)*3);
v_wantsRebuild_2674_ = lean_ctor_get_uint8(v_a_2667_, sizeof(void*)*3 + 1);
v_trace_2675_ = lean_ctor_get(v_a_2667_, 1);
v_buildTime_2676_ = lean_ctor_get(v_a_2667_, 2);
v___x_2677_ = lean_io_metadata(v_file_2661_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; lean_object* v_modified_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; uint64_t v___x_2682_; lean_object* v___x_2684_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2678_);
lean_dec_ref(v___x_2677_);
v_modified_2679_ = lean_ctor_get(v_a_2678_, 1);
lean_inc_ref(v_modified_2679_);
lean_dec(v_a_2678_);
v___x_2680_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_2681_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_2681_, 0, v_file_2661_);
lean_ctor_set(v___x_2681_, 1, v___x_2680_);
lean_ctor_set(v___x_2681_, 2, v_modified_2679_);
v___x_2682_ = lean_unbox_uint64(v_a_2668_);
lean_dec(v_a_2668_);
lean_ctor_set_uint64(v___x_2681_, sizeof(void*)*3, v___x_2682_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v___x_2681_);
v___x_2684_ = v___x_2670_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2681_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v_a_2667_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
else
{
lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2701_; 
lean_inc(v_buildTime_2676_);
lean_inc_ref(v_trace_2675_);
lean_inc_ref(v_log_2672_);
lean_dec(v_a_2668_);
lean_dec_ref(v_file_2661_);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_a_2667_);
if (v_isSharedCheck_2701_ == 0)
{
lean_object* v_unused_2702_; lean_object* v_unused_2703_; lean_object* v_unused_2704_; 
v_unused_2702_ = lean_ctor_get(v_a_2667_, 2);
lean_dec(v_unused_2702_);
v_unused_2703_ = lean_ctor_get(v_a_2667_, 1);
lean_dec(v_unused_2703_);
v_unused_2704_ = lean_ctor_get(v_a_2667_, 0);
lean_dec(v_unused_2704_);
v___x_2687_ = v_a_2667_;
v_isShared_2688_ = v_isSharedCheck_2701_;
goto v_resetjp_2686_;
}
else
{
lean_dec(v_a_2667_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2701_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v_a_2689_; lean_object* v___x_2690_; uint8_t v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2696_; 
v_a_2689_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2689_);
lean_dec_ref(v___x_2677_);
v___x_2690_ = lean_io_error_to_string(v_a_2689_);
v___x_2691_ = 3;
v___x_2692_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2692_, 0, v___x_2690_);
lean_ctor_set_uint8(v___x_2692_, sizeof(void*)*1, v___x_2691_);
v___x_2693_ = lean_array_get_size(v_log_2672_);
v___x_2694_ = lean_array_push(v_log_2672_, v___x_2692_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v___x_2694_);
v___x_2696_ = v___x_2687_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2694_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_trace_2675_);
lean_ctor_set(v_reuseFailAlloc_2700_, 2, v_buildTime_2676_);
lean_ctor_set_uint8(v_reuseFailAlloc_2700_, sizeof(void*)*3, v_action_2673_);
lean_ctor_set_uint8(v_reuseFailAlloc_2700_, sizeof(void*)*3 + 1, v_wantsRebuild_2674_);
v___x_2696_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
lean_object* v___x_2698_; 
if (v_isShared_2671_ == 0)
{
lean_ctor_set_tag(v___x_2670_, 1);
lean_ctor_set(v___x_2670_, 1, v___x_2696_);
lean_ctor_set(v___x_2670_, 0, v___x_2693_);
v___x_2698_ = v___x_2670_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2693_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v___x_2696_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
}
}
else
{
lean_object* v_a_2706_; lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
lean_dec_ref(v_file_2661_);
v_a_2706_ = lean_ctor_get(v___x_2666_, 0);
v_a_2707_ = lean_ctor_get(v___x_2666_, 1);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2666_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_inc(v_a_2706_);
lean_dec(v___x_2666_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2706_);
lean_ctor_set(v_reuseFailAlloc_2713_, 1, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg___boxed(lean_object* v_file_2715_, lean_object* v_text_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
uint8_t v_text_boxed_2720_; lean_object* v_res_2721_; 
v_text_boxed_2720_ = lean_unbox(v_text_2716_);
v_res_2721_ = l_Lake_fetchFileTrace___redArg(v_file_2715_, v_text_boxed_2720_, v_a_2717_, v_a_2718_);
lean_dec_ref(v_a_2717_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object* v_file_2722_, uint8_t v_text_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l_Lake_fetchFileTrace___redArg(v_file_2722_, v_text_2723_, v_a_2728_, v_a_2729_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object* v_file_2732_, lean_object* v_text_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_){
_start:
{
uint8_t v_text_boxed_2741_; lean_object* v_res_2742_; 
v_text_boxed_2741_ = lean_unbox(v_text_2733_);
v_res_2742_ = l_Lake_fetchFileTrace(v_file_2732_, v_text_boxed_2741_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_);
lean_dec_ref(v_a_2738_);
lean_dec(v_a_2737_);
lean_dec(v_a_2736_);
lean_dec(v_a_2735_);
lean_dec_ref(v_a_2734_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(lean_object* v_val_2743_, lean_object* v_a_x3f_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v___x_2747_; lean_object* v_log_2748_; uint8_t v_action_2749_; uint8_t v_wantsRebuild_2750_; lean_object* v_trace_2751_; lean_object* v_buildTime_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2763_; 
v___x_2747_ = lean_io_mono_ms_now();
v_log_2748_ = lean_ctor_get(v___y_2745_, 0);
v_action_2749_ = lean_ctor_get_uint8(v___y_2745_, sizeof(void*)*3);
v_wantsRebuild_2750_ = lean_ctor_get_uint8(v___y_2745_, sizeof(void*)*3 + 1);
v_trace_2751_ = lean_ctor_get(v___y_2745_, 1);
v_buildTime_2752_ = lean_ctor_get(v___y_2745_, 2);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___y_2745_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2754_ = v___y_2745_;
v_isShared_2755_ = v_isSharedCheck_2763_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_buildTime_2752_);
lean_inc(v_trace_2751_);
lean_inc(v_log_2748_);
lean_dec(v___y_2745_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2763_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2760_; 
v___x_2756_ = lean_nat_sub(v___x_2747_, v_val_2743_);
lean_dec(v___x_2747_);
v___x_2757_ = lean_box(0);
v___x_2758_ = lean_nat_add(v_buildTime_2752_, v___x_2756_);
lean_dec(v___x_2756_);
lean_dec(v_buildTime_2752_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 2, v___x_2758_);
v___x_2760_ = v___x_2754_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_log_2748_);
lean_ctor_set(v_reuseFailAlloc_2762_, 1, v_trace_2751_);
lean_ctor_set(v_reuseFailAlloc_2762_, 2, v___x_2758_);
lean_ctor_set_uint8(v_reuseFailAlloc_2762_, sizeof(void*)*3, v_action_2749_);
lean_ctor_set_uint8(v_reuseFailAlloc_2762_, sizeof(void*)*3 + 1, v_wantsRebuild_2750_);
v___x_2760_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
lean_object* v___x_2761_; 
v___x_2761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2757_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
return v___x_2761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0___boxed(lean_object* v_val_2764_, lean_object* v_a_x3f_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v_val_2764_, v_a_x3f_2765_, v___y_2766_);
lean_dec(v_a_x3f_2765_);
lean_dec(v_val_2764_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(lean_object* v_build_2769_, lean_object* v_file_2770_, lean_object* v_a_2771_, lean_object* v_depTrace_2772_, lean_object* v_traceFile_2773_, uint8_t v_action_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v_a_2782_; lean_object* v_a_2783_; lean_object* v_log_2786_; uint8_t v_action_2787_; uint8_t v_wantsRebuild_2788_; lean_object* v_trace_2789_; lean_object* v_buildTime_2790_; lean_object* v_toBuildConfig_2796_; lean_object* v_log_2797_; uint8_t v_action_2798_; uint8_t v_wantsRebuild_2799_; lean_object* v_trace_2800_; lean_object* v_buildTime_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2924_; 
v_toBuildConfig_2796_ = lean_ctor_get(v_a_2778_, 0);
v_log_2797_ = lean_ctor_get(v_a_2779_, 0);
v_action_2798_ = lean_ctor_get_uint8(v_a_2779_, sizeof(void*)*3);
v_wantsRebuild_2799_ = lean_ctor_get_uint8(v_a_2779_, sizeof(void*)*3 + 1);
v_trace_2800_ = lean_ctor_get(v_a_2779_, 1);
v_buildTime_2801_ = lean_ctor_get(v_a_2779_, 2);
v_isSharedCheck_2924_ = !lean_is_exclusive(v_a_2779_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2803_ = v_a_2779_;
v_isShared_2804_ = v_isSharedCheck_2924_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_buildTime_2801_);
lean_inc(v_trace_2800_);
lean_inc(v_log_2797_);
lean_dec(v_a_2779_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2924_;
goto v_resetjp_2802_;
}
v___jp_2781_:
{
lean_object* v___x_2784_; 
v___x_2784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2784_, 0, v_a_2782_);
lean_ctor_set(v___x_2784_, 1, v_a_2783_);
return v___x_2784_;
}
v___jp_2785_:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2791_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_2792_ = lean_array_get_size(v_log_2786_);
v___x_2793_ = lean_array_push(v_log_2786_, v___x_2791_);
v___x_2794_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
lean_ctor_set(v___x_2794_, 1, v_trace_2789_);
lean_ctor_set(v___x_2794_, 2, v_buildTime_2790_);
lean_ctor_set_uint8(v___x_2794_, sizeof(void*)*3, v_action_2787_);
lean_ctor_set_uint8(v___x_2794_, sizeof(void*)*3 + 1, v_wantsRebuild_2788_);
v___x_2795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2792_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
return v___x_2795_;
}
v_resetjp_2802_:
{
uint8_t v_noBuild_2805_; uint8_t v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v_noBuild_2805_ = lean_ctor_get_uint8(v_toBuildConfig_2796_, sizeof(void*)*2 + 2);
v___x_2806_ = l_Lake_JobAction_merge(v_action_2798_, v_action_2774_);
v___x_2807_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_2773_);
v___x_2808_ = l_System_FilePath_addExtension(v_traceFile_2773_, v___x_2807_);
if (v_noBuild_2805_ == 0)
{
lean_object* v___x_2809_; lean_object* v___x_2811_; 
v___x_2809_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_2797_);
if (v_isShared_2804_ == 0)
{
v___x_2811_ = v___x_2803_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_log_2797_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v_trace_2800_);
lean_ctor_set(v_reuseFailAlloc_2908_, 2, v_buildTime_2801_);
lean_ctor_set_uint8(v_reuseFailAlloc_2908_, sizeof(void*)*3 + 1, v_wantsRebuild_2799_);
v___x_2811_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
lean_object* v___x_2812_; lean_object* v_a_2814_; lean_object* v_a_2815_; 
lean_ctor_set_uint8(v___x_2811_, sizeof(void*)*3, v___x_2806_);
lean_inc_ref(v_a_2778_);
lean_inc(v_a_2777_);
lean_inc(v_a_2776_);
lean_inc(v_a_2775_);
v___x_2812_ = lean_apply_7(v_build_2769_, v_a_2771_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v___x_2811_, lean_box(0));
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2819_; lean_object* v_log_2820_; uint8_t v_action_2821_; uint8_t v_wantsRebuild_2822_; lean_object* v_trace_2823_; lean_object* v_buildTime_2824_; lean_object* v___x_2825_; 
v_a_2819_ = lean_ctor_get(v___x_2812_, 1);
lean_inc(v_a_2819_);
lean_dec_ref(v___x_2812_);
v_log_2820_ = lean_ctor_get(v_a_2819_, 0);
v_action_2821_ = lean_ctor_get_uint8(v_a_2819_, sizeof(void*)*3);
v_wantsRebuild_2822_ = lean_ctor_get_uint8(v_a_2819_, sizeof(void*)*3 + 1);
v_trace_2823_ = lean_ctor_get(v_a_2819_, 1);
v_buildTime_2824_ = lean_ctor_get(v_a_2819_, 2);
v___x_2825_ = l_Lake_clearFileHash(v_file_2770_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2826_);
lean_dec_ref(v___x_2825_);
v___x_2827_ = lean_array_get_size(v_log_2797_);
lean_dec_ref(v_log_2797_);
v___x_2828_ = lean_array_get_size(v_log_2820_);
v___x_2829_ = l_Array_extract___redArg(v_log_2820_, v___x_2827_, v___x_2828_);
v___x_2830_ = lean_box(0);
v___x_2831_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_2772_, v___x_2830_, v___x_2829_);
v___x_2832_ = l_Lake_BuildMetadata_writeFile(v_traceFile_2773_, v___x_2831_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2873_; 
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2873_ == 0)
{
lean_object* v_unused_2874_; 
v_unused_2874_ = lean_ctor_get(v___x_2832_, 0);
lean_dec(v_unused_2874_);
v___x_2834_ = v___x_2832_;
v_isShared_2835_ = v_isSharedCheck_2873_;
goto v_resetjp_2833_;
}
else
{
lean_dec(v___x_2832_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2873_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2836_; 
v___x_2836_ = l_Lake_removeFileIfExists(v___x_2808_);
lean_dec_ref(v___x_2808_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2856_; 
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2856_ == 0)
{
lean_object* v_unused_2857_; 
v_unused_2857_ = lean_ctor_get(v___x_2836_, 0);
lean_dec(v_unused_2857_);
v___x_2838_ = v___x_2836_;
v_isShared_2839_ = v_isSharedCheck_2856_;
goto v_resetjp_2837_;
}
else
{
lean_dec(v___x_2836_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2856_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
lean_inc(v_a_2826_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 0, v_a_2826_);
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2826_);
v___x_2841_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2843_; 
if (v_isShared_2835_ == 0)
{
lean_ctor_set_tag(v___x_2834_, 1);
lean_ctor_set(v___x_2834_, 0, v___x_2841_);
v___x_2843_ = v___x_2834_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2841_);
v___x_2843_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
lean_object* v___x_2844_; lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
v___x_2844_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v___x_2809_, v___x_2843_, v_a_2819_);
lean_dec_ref(v___x_2843_);
lean_dec(v___x_2809_);
v_a_2845_ = lean_ctor_get(v___x_2844_, 1);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2852_ == 0)
{
lean_object* v_unused_2853_; 
v_unused_2853_ = lean_ctor_get(v___x_2844_, 0);
lean_dec(v_unused_2853_);
v___x_2847_ = v___x_2844_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2844_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 0, v_a_2826_);
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2826_);
lean_ctor_set(v_reuseFailAlloc_2851_, 1, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
}
}
else
{
lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2869_; 
lean_inc(v_buildTime_2824_);
lean_inc_ref(v_trace_2823_);
lean_inc_ref(v_log_2820_);
lean_del_object(v___x_2834_);
lean_dec(v_a_2826_);
v_isSharedCheck_2869_ = !lean_is_exclusive(v_a_2819_);
if (v_isSharedCheck_2869_ == 0)
{
lean_object* v_unused_2870_; lean_object* v_unused_2871_; lean_object* v_unused_2872_; 
v_unused_2870_ = lean_ctor_get(v_a_2819_, 2);
lean_dec(v_unused_2870_);
v_unused_2871_ = lean_ctor_get(v_a_2819_, 1);
lean_dec(v_unused_2871_);
v_unused_2872_ = lean_ctor_get(v_a_2819_, 0);
lean_dec(v_unused_2872_);
v___x_2859_ = v_a_2819_;
v_isShared_2860_ = v_isSharedCheck_2869_;
goto v_resetjp_2858_;
}
else
{
lean_dec(v_a_2819_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2869_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v_a_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2867_; 
v_a_2861_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_a_2861_);
lean_dec_ref(v___x_2836_);
v___x_2862_ = lean_io_error_to_string(v_a_2861_);
v___x_2863_ = 3;
v___x_2864_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2864_, 0, v___x_2862_);
lean_ctor_set_uint8(v___x_2864_, sizeof(void*)*1, v___x_2863_);
v___x_2865_ = lean_array_push(v_log_2820_, v___x_2864_);
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
lean_ctor_set(v_reuseFailAlloc_2868_, 1, v_trace_2823_);
lean_ctor_set(v_reuseFailAlloc_2868_, 2, v_buildTime_2824_);
lean_ctor_set_uint8(v_reuseFailAlloc_2868_, sizeof(void*)*3, v_action_2821_);
lean_ctor_set_uint8(v_reuseFailAlloc_2868_, sizeof(void*)*3 + 1, v_wantsRebuild_2822_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
v_a_2814_ = v___x_2828_;
v_a_2815_ = v___x_2867_;
goto v___jp_2813_;
}
}
}
}
}
else
{
lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2886_; 
lean_inc(v_buildTime_2824_);
lean_inc_ref(v_trace_2823_);
lean_inc_ref(v_log_2820_);
lean_dec(v_a_2826_);
lean_dec_ref(v___x_2808_);
v_isSharedCheck_2886_ = !lean_is_exclusive(v_a_2819_);
if (v_isSharedCheck_2886_ == 0)
{
lean_object* v_unused_2887_; lean_object* v_unused_2888_; lean_object* v_unused_2889_; 
v_unused_2887_ = lean_ctor_get(v_a_2819_, 2);
lean_dec(v_unused_2887_);
v_unused_2888_ = lean_ctor_get(v_a_2819_, 1);
lean_dec(v_unused_2888_);
v_unused_2889_ = lean_ctor_get(v_a_2819_, 0);
lean_dec(v_unused_2889_);
v___x_2876_ = v_a_2819_;
v_isShared_2877_ = v_isSharedCheck_2886_;
goto v_resetjp_2875_;
}
else
{
lean_dec(v_a_2819_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2886_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v_a_2878_; lean_object* v___x_2879_; uint8_t v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2884_; 
v_a_2878_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_a_2878_);
lean_dec_ref(v___x_2832_);
v___x_2879_ = lean_io_error_to_string(v_a_2878_);
v___x_2880_ = 3;
v___x_2881_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2881_, 0, v___x_2879_);
lean_ctor_set_uint8(v___x_2881_, sizeof(void*)*1, v___x_2880_);
v___x_2882_ = lean_array_push(v_log_2820_, v___x_2881_);
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 0, v___x_2882_);
v___x_2884_ = v___x_2876_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2882_);
lean_ctor_set(v_reuseFailAlloc_2885_, 1, v_trace_2823_);
lean_ctor_set(v_reuseFailAlloc_2885_, 2, v_buildTime_2824_);
lean_ctor_set_uint8(v_reuseFailAlloc_2885_, sizeof(void*)*3, v_action_2821_);
lean_ctor_set_uint8(v_reuseFailAlloc_2885_, sizeof(void*)*3 + 1, v_wantsRebuild_2822_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
v_a_2814_ = v___x_2828_;
v_a_2815_ = v___x_2884_;
goto v___jp_2813_;
}
}
}
}
else
{
lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2902_; 
lean_inc(v_buildTime_2824_);
lean_inc_ref(v_trace_2823_);
lean_inc_ref(v_log_2820_);
lean_dec_ref(v___x_2808_);
lean_dec_ref(v_log_2797_);
lean_dec_ref(v_traceFile_2773_);
v_isSharedCheck_2902_ = !lean_is_exclusive(v_a_2819_);
if (v_isSharedCheck_2902_ == 0)
{
lean_object* v_unused_2903_; lean_object* v_unused_2904_; lean_object* v_unused_2905_; 
v_unused_2903_ = lean_ctor_get(v_a_2819_, 2);
lean_dec(v_unused_2903_);
v_unused_2904_ = lean_ctor_get(v_a_2819_, 1);
lean_dec(v_unused_2904_);
v_unused_2905_ = lean_ctor_get(v_a_2819_, 0);
lean_dec(v_unused_2905_);
v___x_2891_ = v_a_2819_;
v_isShared_2892_ = v_isSharedCheck_2902_;
goto v_resetjp_2890_;
}
else
{
lean_dec(v_a_2819_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2902_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v_a_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2900_; 
v_a_2893_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2893_);
lean_dec_ref(v___x_2825_);
v___x_2894_ = lean_io_error_to_string(v_a_2893_);
v___x_2895_ = 3;
v___x_2896_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2896_, 0, v___x_2894_);
lean_ctor_set_uint8(v___x_2896_, sizeof(void*)*1, v___x_2895_);
v___x_2897_ = lean_array_get_size(v_log_2820_);
v___x_2898_ = lean_array_push(v_log_2820_, v___x_2896_);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 0, v___x_2898_);
v___x_2900_ = v___x_2891_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2898_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v_trace_2823_);
lean_ctor_set(v_reuseFailAlloc_2901_, 2, v_buildTime_2824_);
lean_ctor_set_uint8(v_reuseFailAlloc_2901_, sizeof(void*)*3, v_action_2821_);
lean_ctor_set_uint8(v_reuseFailAlloc_2901_, sizeof(void*)*3 + 1, v_wantsRebuild_2822_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
v_a_2814_ = v___x_2897_;
v_a_2815_ = v___x_2900_;
goto v___jp_2813_;
}
}
}
}
else
{
lean_object* v_a_2906_; lean_object* v_a_2907_; 
lean_dec_ref(v___x_2808_);
lean_dec_ref(v_log_2797_);
lean_dec_ref(v_traceFile_2773_);
lean_dec_ref(v_file_2770_);
v_a_2906_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2906_);
v_a_2907_ = lean_ctor_get(v___x_2812_, 1);
lean_inc(v_a_2907_);
lean_dec_ref(v___x_2812_);
v_a_2814_ = v_a_2906_;
v_a_2815_ = v_a_2907_;
goto v___jp_2813_;
}
v___jp_2813_:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v_a_2818_; 
v___x_2816_ = lean_box(0);
v___x_2817_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v___x_2809_, v___x_2816_, v_a_2815_);
lean_dec(v___x_2809_);
v_a_2818_ = lean_ctor_get(v___x_2817_, 1);
lean_inc(v_a_2818_);
lean_dec_ref(v___x_2817_);
v_a_2782_ = v_a_2814_;
v_a_2783_ = v_a_2818_;
goto v___jp_2781_;
}
}
}
else
{
uint8_t v___x_2909_; 
lean_dec_ref(v_a_2771_);
lean_dec_ref(v_file_2770_);
lean_dec_ref(v_build_2769_);
v___x_2909_ = l_System_FilePath_pathExists(v_traceFile_2773_);
lean_dec_ref(v_traceFile_2773_);
if (v___x_2909_ == 0)
{
lean_dec_ref(v___x_2808_);
lean_del_object(v___x_2803_);
v_log_2786_ = v_log_2797_;
v_action_2787_ = v___x_2806_;
v_wantsRebuild_2788_ = v_noBuild_2805_;
v_trace_2789_ = v_trace_2800_;
v_buildTime_2790_ = v_buildTime_2801_;
goto v___jp_2785_;
}
else
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2910_ = lean_box(0);
v___x_2911_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_2912_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_2772_, v___x_2910_, v___x_2911_);
v___x_2913_ = l_Lake_BuildMetadata_writeFile(v___x_2808_, v___x_2912_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_dec_ref(v___x_2913_);
lean_del_object(v___x_2803_);
v_log_2786_ = v_log_2797_;
v_action_2787_ = v___x_2806_;
v_wantsRebuild_2788_ = v_noBuild_2805_;
v_trace_2789_ = v_trace_2800_;
v_buildTime_2790_ = v_buildTime_2801_;
goto v___jp_2785_;
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2915_; uint8_t v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2921_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_a_2914_);
lean_dec_ref(v___x_2913_);
v___x_2915_ = lean_io_error_to_string(v_a_2914_);
v___x_2916_ = 3;
v___x_2917_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2917_, 0, v___x_2915_);
lean_ctor_set_uint8(v___x_2917_, sizeof(void*)*1, v___x_2916_);
v___x_2918_ = lean_array_get_size(v_log_2797_);
v___x_2919_ = lean_array_push(v_log_2797_, v___x_2917_);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 0, v___x_2919_);
v___x_2921_ = v___x_2803_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v___x_2919_);
lean_ctor_set(v_reuseFailAlloc_2923_, 1, v_trace_2800_);
lean_ctor_set(v_reuseFailAlloc_2923_, 2, v_buildTime_2801_);
v___x_2921_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
lean_object* v___x_2922_; 
lean_ctor_set_uint8(v___x_2921_, sizeof(void*)*3, v___x_2806_);
lean_ctor_set_uint8(v___x_2921_, sizeof(void*)*3 + 1, v_noBuild_2805_);
v___x_2922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2918_);
lean_ctor_set(v___x_2922_, 1, v___x_2921_);
return v___x_2922_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___boxed(lean_object* v_build_2925_, lean_object* v_file_2926_, lean_object* v_a_2927_, lean_object* v_depTrace_2928_, lean_object* v_traceFile_2929_, lean_object* v_action_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_){
_start:
{
uint8_t v_action_boxed_2937_; lean_object* v_res_2938_; 
v_action_boxed_2937_ = lean_unbox(v_action_2930_);
v_res_2938_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(v_build_2925_, v_file_2926_, v_a_2927_, v_depTrace_2928_, v_traceFile_2929_, v_action_boxed_2937_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_);
lean_dec_ref(v_a_2934_);
lean_dec(v_a_2933_);
lean_dec(v_a_2932_);
lean_dec(v_a_2931_);
lean_dec_ref(v_depTrace_2928_);
return v_res_2938_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(lean_object* v_info_2939_, lean_object* v_self_2940_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_io_metadata(v_info_2939_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; lean_object* v_modified_2944_; uint8_t v___x_2945_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2943_);
lean_dec_ref(v___x_2942_);
v_modified_2944_ = lean_ctor_get(v_a_2943_, 1);
lean_inc_ref(v_modified_2944_);
lean_dec(v_a_2943_);
v___x_2945_ = l_IO_FS_instOrdSystemTime_ord(v_self_2940_, v_modified_2944_);
lean_dec_ref(v_modified_2944_);
if (v___x_2945_ == 0)
{
uint8_t v___x_2946_; 
v___x_2946_ = 1;
return v___x_2946_;
}
else
{
uint8_t v___x_2947_; 
v___x_2947_ = 0;
return v___x_2947_;
}
}
else
{
uint8_t v___x_2948_; 
lean_dec_ref(v___x_2942_);
v___x_2948_ = 0;
return v___x_2948_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___boxed(lean_object* v_info_2949_, lean_object* v_self_2950_, lean_object* v_a_2951_){
_start:
{
uint8_t v_res_2952_; lean_object* v_r_2953_; 
v_res_2952_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_2949_, v_self_2950_);
lean_dec_ref(v_self_2950_);
lean_dec_ref(v_info_2949_);
v_r_2953_ = lean_box(v_res_2952_);
return v_r_2953_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(lean_object* v_x_2954_, lean_object* v_x_2955_){
_start:
{
if (lean_obj_tag(v_x_2954_) == 0)
{
if (lean_obj_tag(v_x_2955_) == 0)
{
uint8_t v___x_2956_; 
v___x_2956_ = 1;
return v___x_2956_;
}
else
{
uint8_t v___x_2957_; 
v___x_2957_ = 0;
return v___x_2957_;
}
}
else
{
if (lean_obj_tag(v_x_2955_) == 0)
{
uint8_t v___x_2958_; 
v___x_2958_ = 0;
return v___x_2958_;
}
else
{
lean_object* v_val_2959_; lean_object* v_val_2960_; uint64_t v___x_2961_; uint64_t v___x_2962_; uint8_t v___x_2963_; 
v_val_2959_ = lean_ctor_get(v_x_2954_, 0);
v_val_2960_ = lean_ctor_get(v_x_2955_, 0);
v___x_2961_ = lean_unbox_uint64(v_val_2959_);
v___x_2962_ = lean_unbox_uint64(v_val_2960_);
v___x_2963_ = lean_uint64_dec_eq(v___x_2961_, v___x_2962_);
return v___x_2963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2964_, lean_object* v_x_2965_){
_start:
{
uint8_t v_res_2966_; lean_object* v_r_2967_; 
v_res_2966_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(v_x_2964_, v_x_2965_);
lean_dec(v_x_2965_);
lean_dec(v_x_2964_);
v_r_2967_ = lean_box(v_res_2966_);
return v_r_2967_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(lean_object* v_info_2968_, lean_object* v_depTrace_2969_, lean_object* v_depHash_2970_, lean_object* v_oldTrace_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_){
_start:
{
uint64_t v_hash_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; uint8_t v___x_2978_; 
v_hash_2975_ = lean_ctor_get_uint64(v_depTrace_2969_, sizeof(void*)*3);
v___x_2976_ = lean_box_uint64(v_hash_2975_);
v___x_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
v___x_2978_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(v___x_2977_, v_depHash_2970_);
lean_dec_ref(v___x_2977_);
if (v___x_2978_ == 0)
{
lean_object* v_toBuildConfig_2979_; uint8_t v_oldMode_2980_; 
v_toBuildConfig_2979_ = lean_ctor_get(v_a_2972_, 0);
v_oldMode_2980_ = lean_ctor_get_uint8(v_toBuildConfig_2979_, sizeof(void*)*2);
if (v_oldMode_2980_ == 0)
{
uint8_t v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2981_ = 0;
v___x_2982_ = lean_box(v___x_2981_);
v___x_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2982_);
lean_ctor_set(v___x_2983_, 1, v_a_2973_);
return v___x_2983_;
}
else
{
uint8_t v___x_2984_; 
v___x_2984_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_2968_, v_oldTrace_2971_);
if (v___x_2984_ == 0)
{
uint8_t v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2985_ = 0;
v___x_2986_ = lean_box(v___x_2985_);
v___x_2987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2986_);
lean_ctor_set(v___x_2987_, 1, v_a_2973_);
return v___x_2987_;
}
else
{
uint8_t v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2988_ = 1;
v___x_2989_ = lean_box(v___x_2988_);
v___x_2990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2989_);
lean_ctor_set(v___x_2990_, 1, v_a_2973_);
return v___x_2990_;
}
}
}
else
{
uint8_t v___x_2991_; 
v___x_2991_ = l_System_FilePath_pathExists(v_info_2968_);
if (v___x_2991_ == 0)
{
uint8_t v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2992_ = 0;
v___x_2993_ = lean_box(v___x_2992_);
v___x_2994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2993_);
lean_ctor_set(v___x_2994_, 1, v_a_2973_);
return v___x_2994_;
}
else
{
uint8_t v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2995_ = 2;
v___x_2996_ = lean_box(v___x_2995_);
v___x_2997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
lean_ctor_set(v___x_2997_, 1, v_a_2973_);
return v___x_2997_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg___boxed(lean_object* v_info_2998_, lean_object* v_depTrace_2999_, lean_object* v_depHash_3000_, lean_object* v_oldTrace_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_2998_, v_depTrace_2999_, v_depHash_3000_, v_oldTrace_3001_, v_a_3002_, v_a_3003_);
lean_dec_ref(v_a_3002_);
lean_dec_ref(v_oldTrace_3001_);
lean_dec(v_depHash_3000_);
lean_dec_ref(v_depTrace_2999_);
lean_dec_ref(v_info_2998_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(lean_object* v_a_3006_, lean_object* v_info_3007_, lean_object* v_depTrace_3008_, lean_object* v_savedTrace_3009_, lean_object* v_oldTrace_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_){
_start:
{
if (lean_obj_tag(v_savedTrace_3009_) == 2)
{
lean_object* v_data_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3067_; 
v_data_3017_ = lean_ctor_get(v_savedTrace_3009_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v_savedTrace_3009_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3019_ = v_savedTrace_3009_;
v_isShared_3020_ = v_isSharedCheck_3067_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_data_3017_);
lean_dec(v_savedTrace_3009_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3067_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
uint64_t v_depHash_3021_; lean_object* v_log_3022_; lean_object* v___x_3023_; lean_object* v___x_3025_; 
v_depHash_3021_ = lean_ctor_get_uint64(v_data_3017_, sizeof(void*)*3);
v_log_3022_ = lean_ctor_get(v_data_3017_, 2);
lean_inc_ref(v_log_3022_);
lean_dec_ref(v_data_3017_);
v___x_3023_ = lean_box_uint64(v_depHash_3021_);
if (v_isShared_3020_ == 0)
{
lean_ctor_set_tag(v___x_3019_, 1);
lean_ctor_set(v___x_3019_, 0, v___x_3023_);
v___x_3025_ = v___x_3019_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
lean_object* v___x_3026_; lean_object* v_a_3027_; lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3065_; 
v___x_3026_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_3007_, v_depTrace_3008_, v___x_3025_, v_oldTrace_3010_, v_a_3014_, v_a_3015_);
lean_dec_ref(v___x_3025_);
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
v_a_3028_ = lean_ctor_get(v___x_3026_, 1);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3030_ = v___x_3026_;
v_isShared_3031_ = v_isSharedCheck_3065_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_inc(v_a_3027_);
lean_dec(v___x_3026_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3065_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___y_3033_; uint8_t v___x_3037_; uint8_t v___x_3038_; uint8_t v___x_3039_; 
v___x_3037_ = 0;
v___x_3038_ = lean_unbox(v_a_3027_);
v___x_3039_ = l_Lake_instDecidableEqOutputStatus(v___x_3038_, v___x_3037_);
if (v___x_3039_ == 0)
{
lean_object* v_log_3040_; uint8_t v_action_3041_; uint8_t v_wantsRebuild_3042_; lean_object* v_trace_3043_; lean_object* v_buildTime_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3064_; 
v_log_3040_ = lean_ctor_get(v_a_3028_, 0);
v_action_3041_ = lean_ctor_get_uint8(v_a_3028_, sizeof(void*)*3);
v_wantsRebuild_3042_ = lean_ctor_get_uint8(v_a_3028_, sizeof(void*)*3 + 1);
v_trace_3043_ = lean_ctor_get(v_a_3028_, 1);
v_buildTime_3044_ = lean_ctor_get(v_a_3028_, 2);
v_isSharedCheck_3064_ = !lean_is_exclusive(v_a_3028_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3046_ = v_a_3028_;
v_isShared_3047_ = v_isSharedCheck_3064_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_buildTime_3044_);
lean_inc(v_trace_3043_);
lean_inc(v_log_3040_);
lean_dec(v_a_3028_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3064_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
uint8_t v___x_3048_; uint8_t v___x_3049_; lean_object* v___x_3051_; 
v___x_3048_ = 2;
v___x_3049_ = l_Lake_JobAction_merge(v_action_3041_, v___x_3048_);
if (v_isShared_3047_ == 0)
{
v___x_3051_ = v___x_3046_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_log_3040_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v_trace_3043_);
lean_ctor_set(v_reuseFailAlloc_3063_, 2, v_buildTime_3044_);
lean_ctor_set_uint8(v_reuseFailAlloc_3063_, sizeof(void*)*3 + 1, v_wantsRebuild_3042_);
v___x_3051_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3052_; 
lean_ctor_set_uint8(v___x_3051_, sizeof(void*)*3, v___x_3049_);
v___x_3052_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_3022_, v_a_3006_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v___x_3051_);
lean_dec_ref(v_log_3022_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 1);
lean_inc(v_a_3053_);
lean_dec_ref(v___x_3052_);
v___y_3033_ = v_a_3053_;
goto v___jp_3032_;
}
else
{
lean_object* v_a_3054_; lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_del_object(v___x_3030_);
lean_dec(v_a_3027_);
v_a_3054_ = lean_ctor_get(v___x_3052_, 0);
v_a_3055_ = lean_ctor_get(v___x_3052_, 1);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_3052_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_inc(v_a_3054_);
lean_dec(v___x_3052_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3054_);
lean_ctor_set(v_reuseFailAlloc_3061_, 1, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_log_3022_);
v___y_3033_ = v_a_3028_;
goto v___jp_3032_;
}
v___jp_3032_:
{
lean_object* v___x_3035_; 
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 1, v___y_3033_);
v___x_3035_ = v___x_3030_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3027_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v___y_3033_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
}
}
else
{
lean_object* v_toBuildConfig_3068_; uint8_t v_oldMode_3069_; 
lean_dec(v_savedTrace_3009_);
v_toBuildConfig_3068_ = lean_ctor_get(v_a_3014_, 0);
v_oldMode_3069_ = lean_ctor_get_uint8(v_toBuildConfig_3068_, sizeof(void*)*2);
if (v_oldMode_3069_ == 0)
{
uint8_t v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3070_ = 0;
v___x_3071_ = lean_box(v___x_3070_);
v___x_3072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
lean_ctor_set(v___x_3072_, 1, v_a_3015_);
return v___x_3072_;
}
else
{
uint8_t v___x_3073_; 
v___x_3073_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_3007_, v_oldTrace_3010_);
if (v___x_3073_ == 0)
{
uint8_t v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = 0;
v___x_3075_ = lean_box(v___x_3074_);
v___x_3076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
lean_ctor_set(v___x_3076_, 1, v_a_3015_);
return v___x_3076_;
}
else
{
uint8_t v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3077_ = 1;
v___x_3078_ = lean_box(v___x_3077_);
v___x_3079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
lean_ctor_set(v___x_3079_, 1, v_a_3015_);
return v___x_3079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0___boxed(lean_object* v_a_3080_, lean_object* v_info_3081_, lean_object* v_depTrace_3082_, lean_object* v_savedTrace_3083_, lean_object* v_oldTrace_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_3080_, v_info_3081_, v_depTrace_3082_, v_savedTrace_3083_, v_oldTrace_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_);
lean_dec_ref(v_a_3088_);
lean_dec(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec(v_a_3085_);
lean_dec_ref(v_oldTrace_3084_);
lean_dec_ref(v_depTrace_3082_);
lean_dec_ref(v_info_3081_);
lean_dec_ref(v_a_3080_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27(lean_object* v_file_3093_, lean_object* v_build_3094_, uint8_t v_text_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_){
_start:
{
lean_object* v_a_3104_; lean_object* v_a_3105_; lean_object* v_a_3108_; lean_object* v_log_3141_; uint8_t v_action_3142_; uint8_t v_wantsRebuild_3143_; lean_object* v_trace_3144_; lean_object* v_buildTime_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3176_; 
v_log_3141_ = lean_ctor_get(v_a_3101_, 0);
v_action_3142_ = lean_ctor_get_uint8(v_a_3101_, sizeof(void*)*3);
v_wantsRebuild_3143_ = lean_ctor_get_uint8(v_a_3101_, sizeof(void*)*3 + 1);
v_trace_3144_ = lean_ctor_get(v_a_3101_, 1);
v_buildTime_3145_ = lean_ctor_get(v_a_3101_, 2);
v_isSharedCheck_3176_ = !lean_is_exclusive(v_a_3101_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3147_ = v_a_3101_;
v_isShared_3148_ = v_isSharedCheck_3176_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_buildTime_3145_);
lean_inc(v_trace_3144_);
lean_inc(v_log_3141_);
lean_dec(v_a_3101_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3176_;
goto v_resetjp_3146_;
}
v___jp_3103_:
{
lean_object* v___x_3106_; 
v___x_3106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3106_, 0, v_a_3104_);
lean_ctor_set(v___x_3106_, 1, v_a_3105_);
return v___x_3106_;
}
v___jp_3107_:
{
lean_object* v___x_3109_; 
v___x_3109_ = l_Lake_fetchFileTrace___redArg(v_file_3093_, v_text_3095_, v_a_3100_, v_a_3108_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3131_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 1);
v_a_3111_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3113_ = v___x_3109_;
v_isShared_3114_ = v_isSharedCheck_3131_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3110_);
lean_inc(v_a_3111_);
lean_dec(v___x_3109_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3131_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v_log_3115_; uint8_t v_action_3116_; uint8_t v_wantsRebuild_3117_; lean_object* v_buildTime_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3129_; 
v_log_3115_ = lean_ctor_get(v_a_3110_, 0);
v_action_3116_ = lean_ctor_get_uint8(v_a_3110_, sizeof(void*)*3);
v_wantsRebuild_3117_ = lean_ctor_get_uint8(v_a_3110_, sizeof(void*)*3 + 1);
v_buildTime_3118_ = lean_ctor_get(v_a_3110_, 2);
v_isSharedCheck_3129_ = !lean_is_exclusive(v_a_3110_);
if (v_isSharedCheck_3129_ == 0)
{
lean_object* v_unused_3130_; 
v_unused_3130_ = lean_ctor_get(v_a_3110_, 1);
lean_dec(v_unused_3130_);
v___x_3120_ = v_a_3110_;
v_isShared_3121_ = v_isSharedCheck_3129_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_buildTime_3118_);
lean_inc(v_log_3115_);
lean_dec(v_a_3110_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3129_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3122_; lean_object* v___x_3124_; 
v___x_3122_ = lean_box(0);
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 1, v_a_3111_);
v___x_3124_ = v___x_3120_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_log_3115_);
lean_ctor_set(v_reuseFailAlloc_3128_, 1, v_a_3111_);
lean_ctor_set(v_reuseFailAlloc_3128_, 2, v_buildTime_3118_);
lean_ctor_set_uint8(v_reuseFailAlloc_3128_, sizeof(void*)*3, v_action_3116_);
lean_ctor_set_uint8(v_reuseFailAlloc_3128_, sizeof(void*)*3 + 1, v_wantsRebuild_3117_);
v___x_3124_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
lean_object* v___x_3126_; 
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 1, v___x_3124_);
lean_ctor_set(v___x_3113_, 0, v___x_3122_);
v___x_3126_ = v___x_3113_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3122_);
lean_ctor_set(v_reuseFailAlloc_3127_, 1, v___x_3124_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
}
else
{
lean_object* v_a_3132_; lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
v_a_3132_ = lean_ctor_get(v___x_3109_, 0);
v_a_3133_ = lean_ctor_get(v___x_3109_, 1);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v___x_3109_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_inc(v_a_3132_);
lean_dec(v___x_3109_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3132_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
v_resetjp_3146_:
{
lean_object* v___x_3149_; lean_object* v_traceFile_3150_; lean_object* v___x_3151_; 
v___x_3149_ = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(v_file_3093_);
v_traceFile_3150_ = lean_string_append(v_file_3093_, v___x_3149_);
lean_inc_ref(v_traceFile_3150_);
v___x_3151_ = l_Lake_readTraceFile(v_traceFile_3150_, v_log_3141_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v_a_3153_; lean_object* v_mtime_3154_; lean_object* v___x_3156_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3152_);
v_a_3153_ = lean_ctor_get(v___x_3151_, 1);
lean_inc(v_a_3153_);
lean_dec_ref(v___x_3151_);
v_mtime_3154_ = lean_ctor_get(v_trace_3144_, 2);
lean_inc_ref(v_trace_3144_);
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 0, v_a_3153_);
v___x_3156_ = v___x_3147_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3153_);
lean_ctor_set(v_reuseFailAlloc_3170_, 1, v_trace_3144_);
lean_ctor_set(v_reuseFailAlloc_3170_, 2, v_buildTime_3145_);
lean_ctor_set_uint8(v_reuseFailAlloc_3170_, sizeof(void*)*3, v_action_3142_);
lean_ctor_set_uint8(v_reuseFailAlloc_3170_, sizeof(void*)*3 + 1, v_wantsRebuild_3143_);
v___x_3156_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
lean_object* v___x_3157_; 
v___x_3157_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_3096_, v_file_3093_, v_trace_3144_, v_a_3152_, v_mtime_3154_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v___x_3156_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3158_; lean_object* v_a_3159_; uint8_t v___x_3160_; uint8_t v___x_3161_; uint8_t v___x_3162_; 
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_a_3158_);
v_a_3159_ = lean_ctor_get(v___x_3157_, 1);
lean_inc(v_a_3159_);
lean_dec_ref(v___x_3157_);
v___x_3160_ = 0;
v___x_3161_ = lean_unbox(v_a_3158_);
lean_dec(v_a_3158_);
v___x_3162_ = l_Lake_instDecidableEqOutputStatus(v___x_3161_, v___x_3160_);
if (v___x_3162_ == 0)
{
lean_dec_ref(v_traceFile_3150_);
lean_dec_ref(v_trace_3144_);
lean_dec_ref(v_a_3096_);
lean_dec_ref(v_build_3094_);
v_a_3108_ = v_a_3159_;
goto v___jp_3107_;
}
else
{
uint8_t v___x_3163_; lean_object* v___x_3164_; 
v___x_3163_ = 5;
lean_inc_ref(v_file_3093_);
v___x_3164_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(v_build_3094_, v_file_3093_, v_a_3096_, v_trace_3144_, v_traceFile_3150_, v___x_3163_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3159_);
lean_dec_ref(v_trace_3144_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 1);
lean_inc(v_a_3165_);
lean_dec_ref(v___x_3164_);
v_a_3108_ = v_a_3165_;
goto v___jp_3107_;
}
else
{
lean_object* v_a_3166_; lean_object* v_a_3167_; 
lean_dec_ref(v_file_3093_);
v_a_3166_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3166_);
v_a_3167_ = lean_ctor_get(v___x_3164_, 1);
lean_inc(v_a_3167_);
lean_dec_ref(v___x_3164_);
v_a_3104_ = v_a_3166_;
v_a_3105_ = v_a_3167_;
goto v___jp_3103_;
}
}
}
else
{
lean_object* v_a_3168_; lean_object* v_a_3169_; 
lean_dec_ref(v_traceFile_3150_);
lean_dec_ref(v_trace_3144_);
lean_dec_ref(v_a_3096_);
lean_dec_ref(v_build_3094_);
lean_dec_ref(v_file_3093_);
v_a_3168_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_a_3168_);
v_a_3169_ = lean_ctor_get(v___x_3157_, 1);
lean_inc(v_a_3169_);
lean_dec_ref(v___x_3157_);
v_a_3104_ = v_a_3168_;
v_a_3105_ = v_a_3169_;
goto v___jp_3103_;
}
}
}
else
{
lean_object* v_a_3171_; lean_object* v_a_3172_; lean_object* v___x_3174_; 
lean_dec_ref(v_traceFile_3150_);
lean_dec_ref(v_a_3096_);
lean_dec_ref(v_build_3094_);
lean_dec_ref(v_file_3093_);
v_a_3171_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3171_);
v_a_3172_ = lean_ctor_get(v___x_3151_, 1);
lean_inc(v_a_3172_);
lean_dec_ref(v___x_3151_);
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 0, v_a_3172_);
v___x_3174_ = v___x_3147_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3172_);
lean_ctor_set(v_reuseFailAlloc_3175_, 1, v_trace_3144_);
lean_ctor_set(v_reuseFailAlloc_3175_, 2, v_buildTime_3145_);
lean_ctor_set_uint8(v_reuseFailAlloc_3175_, sizeof(void*)*3, v_action_3142_);
lean_ctor_set_uint8(v_reuseFailAlloc_3175_, sizeof(void*)*3 + 1, v_wantsRebuild_3143_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
v_a_3104_ = v_a_3171_;
v_a_3105_ = v___x_3174_;
goto v___jp_3103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27___boxed(lean_object* v_file_3177_, lean_object* v_build_3178_, lean_object* v_text_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_){
_start:
{
uint8_t v_text_boxed_3187_; lean_object* v_res_3188_; 
v_text_boxed_3187_ = lean_unbox(v_text_3179_);
v_res_3188_ = l_Lake_buildFileUnlessUpToDate_x27(v_file_3177_, v_build_3178_, v_text_boxed_3187_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_);
lean_dec_ref(v_a_3184_);
lean_dec(v_a_3183_);
lean_dec(v_a_3182_);
lean_dec(v_a_3181_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(lean_object* v_a_3189_, lean_object* v_info_3190_, lean_object* v_depTrace_3191_, lean_object* v_depHash_3192_, lean_object* v_oldTrace_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_3190_, v_depTrace_3191_, v_depHash_3192_, v_oldTrace_3193_, v_a_3197_, v_a_3198_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___boxed(lean_object* v_a_3201_, lean_object* v_info_3202_, lean_object* v_depTrace_3203_, lean_object* v_depHash_3204_, lean_object* v_oldTrace_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(v_a_3201_, v_info_3202_, v_depTrace_3203_, v_depHash_3204_, v_oldTrace_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_);
lean_dec_ref(v_a_3209_);
lean_dec(v_a_3208_);
lean_dec(v_a_3207_);
lean_dec(v_a_3206_);
lean_dec_ref(v_oldTrace_3205_);
lean_dec(v_depHash_3204_);
lean_dec_ref(v_depTrace_3203_);
lean_dec_ref(v_info_3202_);
lean_dec_ref(v_a_3201_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0(lean_object* v___x_3213_, lean_object* v___x_3214_, lean_object* v_file_3215_, uint64_t v___x_3216_, lean_object* v___x_3217_, uint8_t v_useLocalFile_3218_, lean_object* v_____r_3219_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = l_IO_setAccessRights(v___x_3213_, v___x_3214_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v___x_3222_; 
lean_dec_ref(v___x_3221_);
lean_inc_ref(v_file_3215_);
v___x_3222_ = l_Lake_writeFileHash(v_file_3215_, v___x_3216_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v___x_3223_; 
lean_dec_ref(v___x_3222_);
v___x_3223_ = lean_io_metadata(v___x_3213_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3236_; 
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3226_ = v___x_3223_;
v_isShared_3227_ = v_isSharedCheck_3236_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3223_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3236_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v_modified_3228_; lean_object* v___y_3230_; 
v_modified_3228_ = lean_ctor_get(v_a_3224_, 1);
lean_inc_ref(v_modified_3228_);
lean_dec(v_a_3224_);
if (v_useLocalFile_3218_ == 0)
{
v___y_3230_ = v___x_3213_;
goto v___jp_3229_;
}
else
{
lean_dec_ref(v___x_3213_);
lean_inc_ref(v_file_3215_);
v___y_3230_ = v_file_3215_;
goto v___jp_3229_;
}
v___jp_3229_:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3234_; 
v___x_3231_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3217_);
lean_ctor_set(v___x_3231_, 1, v___y_3230_);
lean_ctor_set(v___x_3231_, 2, v_file_3215_);
lean_ctor_set(v___x_3231_, 3, v_modified_3228_);
v___x_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 0, v___x_3232_);
v___x_3234_ = v___x_3226_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3232_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
else
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3244_; 
lean_dec_ref(v___x_3217_);
lean_dec_ref(v_file_3215_);
lean_dec_ref(v___x_3213_);
v_a_3237_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3239_ = v___x_3223_;
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3223_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3242_; 
if (v_isShared_3240_ == 0)
{
v___x_3242_ = v___x_3239_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_a_3237_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
lean_dec_ref(v___x_3217_);
lean_dec_ref(v_file_3215_);
lean_dec_ref(v___x_3213_);
v_a_3245_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3222_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3222_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
lean_dec_ref(v___x_3217_);
lean_dec_ref(v_file_3215_);
lean_dec_ref(v___x_3213_);
v_a_3253_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_3221_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3221_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0___boxed(lean_object* v___x_3261_, lean_object* v___x_3262_, lean_object* v_file_3263_, lean_object* v___x_3264_, lean_object* v___x_3265_, lean_object* v_useLocalFile_3266_, lean_object* v_____r_3267_, lean_object* v___y_3268_){
_start:
{
uint64_t v___x_2969__boxed_3269_; uint8_t v_useLocalFile_boxed_3270_; lean_object* v_res_3271_; 
v___x_2969__boxed_3269_ = lean_unbox_uint64(v___x_3264_);
lean_dec_ref(v___x_3264_);
v_useLocalFile_boxed_3270_ = lean_unbox(v_useLocalFile_3266_);
v_res_3271_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3261_, v___x_3262_, v_file_3263_, v___x_2969__boxed_3269_, v___x_3265_, v_useLocalFile_boxed_3270_, v_____r_3267_);
lean_dec_ref(v___x_3262_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact(lean_object* v_cache_3279_, lean_object* v_file_3280_, lean_object* v_ext_3281_, uint8_t v_text_3282_, uint8_t v_exe_3283_, uint8_t v_useLocalFile_3284_){
_start:
{
lean_object* v_a_3287_; lean_object* v___y_3294_; uint8_t v___x_3305_; 
v___x_3305_ = 1;
if (v_text_3282_ == 0)
{
lean_object* v___x_3306_; 
v___x_3306_ = l_IO_FS_readBinFile(v_file_3280_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; uint64_t v___x_3308_; uint64_t v___x_3309_; uint64_t v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___y_3315_; lean_object* v___x_3336_; lean_object* v___x_3337_; uint8_t v___x_3338_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_a_3307_);
lean_dec_ref(v___x_3306_);
v___x_3308_ = l_Lake_Hash_nil;
v___x_3309_ = lean_byte_array_hash(v_a_3307_);
v___x_3310_ = lean_uint64_mix_hash(v___x_3308_, v___x_3309_);
lean_inc_ref(v_ext_3281_);
v___x_3311_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3311_, 0, v_ext_3281_);
lean_ctor_set_uint64(v___x_3311_, sizeof(void*)*1, v___x_3310_);
v___x_3312_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
v___x_3313_ = l_System_FilePath_join(v_cache_3279_, v___x_3312_);
v___x_3336_ = lean_string_utf8_byte_size(v_ext_3281_);
v___x_3337_ = lean_unsigned_to_nat(0u);
v___x_3338_ = lean_nat_dec_eq(v___x_3336_, v___x_3337_);
if (v___x_3338_ == 0)
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3339_ = l_Lake_lowerHexUInt64(v___x_3310_);
v___x_3340_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_3341_ = lean_string_append(v___x_3339_, v___x_3340_);
v___x_3342_ = lean_string_append(v___x_3341_, v_ext_3281_);
lean_dec_ref(v_ext_3281_);
v___y_3315_ = v___x_3342_;
goto v___jp_3314_;
}
else
{
lean_object* v___x_3343_; 
lean_dec_ref(v_ext_3281_);
v___x_3343_ = l_Lake_lowerHexUInt64(v___x_3310_);
v___y_3315_ = v___x_3343_;
goto v___jp_3314_;
}
v___jp_3314_:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3316_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_3316_, 0, v___x_3305_);
lean_ctor_set_uint8(v___x_3316_, 1, v_text_3282_);
lean_ctor_set_uint8(v___x_3316_, 2, v_exe_3283_);
lean_inc_ref_n(v___x_3316_, 2);
v___x_3317_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3316_);
lean_ctor_set(v___x_3317_, 1, v___x_3316_);
lean_ctor_set(v___x_3317_, 2, v___x_3316_);
v___x_3318_ = l_IO_setAccessRights(v_file_3280_, v___x_3317_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v___x_3319_; uint8_t v___x_3320_; 
lean_dec_ref(v___x_3318_);
v___x_3319_ = l_Lake_joinRelative(v___x_3313_, v___y_3315_);
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
v___x_3322_ = lean_io_hard_link(v_file_3280_, v___x_3319_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
lean_dec_ref(v___x_3322_);
lean_dec(v_a_3307_);
v___x_3323_ = lean_box(0);
v___x_3324_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3319_, v___x_3317_, v_file_3280_, v___x_3310_, v___x_3311_, v_useLocalFile_3284_, v___x_3323_);
lean_dec_ref(v___x_3317_);
v___y_3294_ = v___x_3324_;
goto v___jp_3293_;
}
else
{
lean_object* v_a_3325_; 
v_a_3325_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3325_);
lean_dec_ref(v___x_3322_);
if (lean_obj_tag(v_a_3325_) == 0)
{
lean_object* v___x_3326_; lean_object* v___x_3327_; 
lean_dec_ref(v_a_3325_);
lean_dec(v_a_3307_);
v___x_3326_ = lean_box(0);
v___x_3327_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3319_, v___x_3317_, v_file_3280_, v___x_3310_, v___x_3311_, v_useLocalFile_3284_, v___x_3326_);
lean_dec_ref(v___x_3317_);
v___y_3294_ = v___x_3327_;
goto v___jp_3293_;
}
else
{
lean_object* v___x_3328_; 
lean_dec(v_a_3325_);
v___x_3328_ = l_Lake_writeBinFileIfNew(v___x_3319_, v_a_3307_);
lean_dec(v_a_3307_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3329_; lean_object* v___x_3330_; 
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_a_3329_);
lean_dec_ref(v___x_3328_);
v___x_3330_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3319_, v___x_3317_, v_file_3280_, v___x_3310_, v___x_3311_, v_useLocalFile_3284_, v_a_3329_);
lean_dec_ref(v___x_3317_);
v___y_3294_ = v___x_3330_;
goto v___jp_3293_;
}
else
{
lean_object* v_a_3331_; 
lean_dec_ref(v___x_3319_);
lean_dec_ref(v___x_3317_);
lean_dec_ref(v___x_3311_);
lean_dec_ref(v_file_3280_);
v_a_3331_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_a_3331_);
lean_dec_ref(v___x_3328_);
v_a_3287_ = v_a_3331_;
goto v___jp_3286_;
}
}
}
}
else
{
lean_object* v_a_3332_; 
lean_dec_ref(v___x_3319_);
lean_dec_ref(v___x_3317_);
lean_dec_ref(v___x_3311_);
lean_dec(v_a_3307_);
lean_dec_ref(v_file_3280_);
v_a_3332_ = lean_ctor_get(v___x_3321_, 0);
lean_inc(v_a_3332_);
lean_dec_ref(v___x_3321_);
v_a_3287_ = v_a_3332_;
goto v___jp_3286_;
}
}
else
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
lean_dec(v_a_3307_);
v___x_3333_ = lean_box(0);
v___x_3334_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3319_, v___x_3317_, v_file_3280_, v___x_3310_, v___x_3311_, v_useLocalFile_3284_, v___x_3333_);
lean_dec_ref(v___x_3317_);
v___y_3294_ = v___x_3334_;
goto v___jp_3293_;
}
}
else
{
lean_object* v_a_3335_; 
lean_dec_ref(v___x_3317_);
lean_dec_ref(v___y_3315_);
lean_dec_ref(v___x_3313_);
lean_dec_ref(v___x_3311_);
lean_dec(v_a_3307_);
lean_dec_ref(v_file_3280_);
v_a_3335_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3335_);
lean_dec_ref(v___x_3318_);
v_a_3287_ = v_a_3335_;
goto v___jp_3286_;
}
}
}
else
{
lean_object* v_a_3344_; 
lean_dec_ref(v_ext_3281_);
lean_dec_ref(v_file_3280_);
lean_dec_ref(v_cache_3279_);
v_a_3344_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_a_3344_);
lean_dec_ref(v___x_3306_);
v_a_3287_ = v_a_3344_;
goto v___jp_3286_;
}
}
else
{
lean_object* v___x_3345_; 
v___x_3345_ = l_IO_FS_readFile(v_file_3280_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; lean_object* v___x_3347_; uint64_t v___x_3348_; uint64_t v___x_3349_; uint64_t v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___y_3355_; lean_object* v___x_3369_; lean_object* v___x_3370_; uint8_t v___x_3371_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_a_3346_);
lean_dec_ref(v___x_3345_);
v___x_3347_ = l_String_crlfToLf(v_a_3346_);
lean_dec(v_a_3346_);
v___x_3348_ = l_Lake_Hash_nil;
v___x_3349_ = lean_string_hash(v___x_3347_);
v___x_3350_ = lean_uint64_mix_hash(v___x_3348_, v___x_3349_);
lean_inc_ref(v_ext_3281_);
v___x_3351_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3351_, 0, v_ext_3281_);
lean_ctor_set_uint64(v___x_3351_, sizeof(void*)*1, v___x_3350_);
v___x_3352_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
v___x_3353_ = l_System_FilePath_join(v_cache_3279_, v___x_3352_);
v___x_3369_ = lean_string_utf8_byte_size(v_ext_3281_);
v___x_3370_ = lean_unsigned_to_nat(0u);
v___x_3371_ = lean_nat_dec_eq(v___x_3369_, v___x_3370_);
if (v___x_3371_ == 0)
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3372_ = l_Lake_lowerHexUInt64(v___x_3350_);
v___x_3373_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_3374_ = lean_string_append(v___x_3372_, v___x_3373_);
v___x_3375_ = lean_string_append(v___x_3374_, v_ext_3281_);
lean_dec_ref(v_ext_3281_);
v___y_3355_ = v___x_3375_;
goto v___jp_3354_;
}
else
{
lean_object* v___x_3376_; 
lean_dec_ref(v_ext_3281_);
v___x_3376_ = l_Lake_lowerHexUInt64(v___x_3350_);
v___y_3355_ = v___x_3376_;
goto v___jp_3354_;
}
v___jp_3354_:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3356_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__3));
v___x_3357_ = l_IO_setAccessRights(v_file_3280_, v___x_3356_);
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
v___x_3361_ = l_Lake_writeFileIfNew(v___x_3358_, v___x_3347_);
lean_dec_ref(v___x_3347_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3363_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3362_);
lean_dec_ref(v___x_3361_);
v___x_3363_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3358_, v___x_3356_, v_file_3280_, v___x_3350_, v___x_3351_, v_useLocalFile_3284_, v_a_3362_);
v___y_3294_ = v___x_3363_;
goto v___jp_3293_;
}
else
{
lean_object* v_a_3364_; 
lean_dec_ref(v___x_3358_);
lean_dec_ref(v___x_3351_);
lean_dec_ref(v_file_3280_);
v_a_3364_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3364_);
lean_dec_ref(v___x_3361_);
v_a_3287_ = v_a_3364_;
goto v___jp_3286_;
}
}
else
{
lean_object* v_a_3365_; 
lean_dec_ref(v___x_3358_);
lean_dec_ref(v___x_3351_);
lean_dec_ref(v___x_3347_);
lean_dec_ref(v_file_3280_);
v_a_3365_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3365_);
lean_dec_ref(v___x_3360_);
v_a_3287_ = v_a_3365_;
goto v___jp_3286_;
}
}
else
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
lean_dec_ref(v___x_3347_);
v___x_3366_ = lean_box(0);
v___x_3367_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3358_, v___x_3356_, v_file_3280_, v___x_3350_, v___x_3351_, v_useLocalFile_3284_, v___x_3366_);
v___y_3294_ = v___x_3367_;
goto v___jp_3293_;
}
}
else
{
lean_object* v_a_3368_; 
lean_dec_ref(v___y_3355_);
lean_dec_ref(v___x_3353_);
lean_dec_ref(v___x_3351_);
lean_dec_ref(v___x_3347_);
lean_dec_ref(v_file_3280_);
v_a_3368_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_a_3368_);
lean_dec_ref(v___x_3357_);
v_a_3287_ = v_a_3368_;
goto v___jp_3286_;
}
}
}
else
{
lean_object* v_a_3377_; 
lean_dec_ref(v_ext_3281_);
lean_dec_ref(v_file_3280_);
lean_dec_ref(v_cache_3279_);
v_a_3377_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_a_3377_);
lean_dec_ref(v___x_3345_);
v_a_3287_ = v_a_3377_;
goto v___jp_3286_;
}
}
v___jp_3286_:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3288_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__0));
v___x_3289_ = lean_io_error_to_string(v_a_3287_);
v___x_3290_ = lean_string_append(v___x_3288_, v___x_3289_);
lean_dec_ref(v___x_3289_);
v___x_3291_ = lean_mk_io_user_error(v___x_3290_);
v___x_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3291_);
return v___x_3292_;
}
v___jp_3293_:
{
if (lean_obj_tag(v___y_3294_) == 0)
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3303_; 
v_a_3295_ = lean_ctor_get(v___y_3294_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___y_3294_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3297_ = v___y_3294_;
v_isShared_3298_ = v_isSharedCheck_3303_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___y_3294_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3303_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v_a_3299_; lean_object* v___x_3301_; 
v_a_3299_ = lean_ctor_get(v_a_3295_, 0);
lean_inc(v_a_3299_);
lean_dec(v_a_3295_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 0, v_a_3299_);
v___x_3301_ = v___x_3297_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3299_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
else
{
lean_object* v_a_3304_; 
v_a_3304_ = lean_ctor_get(v___y_3294_, 0);
lean_inc(v_a_3304_);
lean_dec_ref(v___y_3294_);
v_a_3287_ = v_a_3304_;
goto v___jp_3286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___boxed(lean_object* v_cache_3378_, lean_object* v_file_3379_, lean_object* v_ext_3380_, lean_object* v_text_3381_, lean_object* v_exe_3382_, lean_object* v_useLocalFile_3383_, lean_object* v_a_3384_){
_start:
{
uint8_t v_text_boxed_3385_; uint8_t v_exe_boxed_3386_; uint8_t v_useLocalFile_boxed_3387_; lean_object* v_res_3388_; 
v_text_boxed_3385_ = lean_unbox(v_text_3381_);
v_exe_boxed_3386_ = lean_unbox(v_exe_3382_);
v_useLocalFile_boxed_3387_ = lean_unbox(v_useLocalFile_3383_);
v_res_3388_ = l_Lake_Cache_saveArtifact(v_cache_3378_, v_file_3379_, v_ext_3380_, v_text_boxed_3385_, v_exe_boxed_3386_, v_useLocalFile_boxed_3387_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0(lean_object* v_x_3389_){
_start:
{
lean_object* v_lakeCache_3390_; 
v_lakeCache_3390_ = lean_ctor_get(v_x_3389_, 2);
lean_inc_ref(v_lakeCache_3390_);
return v_lakeCache_3390_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0___boxed(lean_object* v_x_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l_Lake_cacheArtifact___redArg___lam__0(v_x_3391_);
lean_dec_ref(v_x_3391_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1(lean_object* v_file_3393_, lean_object* v_ext_3394_, uint8_t v_text_3395_, uint8_t v_exe_3396_, uint8_t v_useLocalFile_3397_, lean_object* v_inst_3398_, lean_object* v_____do__lift_3399_){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3400_ = lean_box(v_text_3395_);
v___x_3401_ = lean_box(v_exe_3396_);
v___x_3402_ = lean_box(v_useLocalFile_3397_);
v___x_3403_ = lean_alloc_closure((void*)(l_Lake_Cache_saveArtifact___boxed), 7, 6);
lean_closure_set(v___x_3403_, 0, v_____do__lift_3399_);
lean_closure_set(v___x_3403_, 1, v_file_3393_);
lean_closure_set(v___x_3403_, 2, v_ext_3394_);
lean_closure_set(v___x_3403_, 3, v___x_3400_);
lean_closure_set(v___x_3403_, 4, v___x_3401_);
lean_closure_set(v___x_3403_, 5, v___x_3402_);
v___x_3404_ = lean_apply_2(v_inst_3398_, lean_box(0), v___x_3403_);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1___boxed(lean_object* v_file_3405_, lean_object* v_ext_3406_, lean_object* v_text_3407_, lean_object* v_exe_3408_, lean_object* v_useLocalFile_3409_, lean_object* v_inst_3410_, lean_object* v_____do__lift_3411_){
_start:
{
uint8_t v_text_boxed_3412_; uint8_t v_exe_boxed_3413_; uint8_t v_useLocalFile_boxed_3414_; lean_object* v_res_3415_; 
v_text_boxed_3412_ = lean_unbox(v_text_3407_);
v_exe_boxed_3413_ = lean_unbox(v_exe_3408_);
v_useLocalFile_boxed_3414_ = lean_unbox(v_useLocalFile_3409_);
v_res_3415_ = l_Lake_cacheArtifact___redArg___lam__1(v_file_3405_, v_ext_3406_, v_text_boxed_3412_, v_exe_boxed_3413_, v_useLocalFile_boxed_3414_, v_inst_3410_, v_____do__lift_3411_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg(lean_object* v_inst_3417_, lean_object* v_inst_3418_, lean_object* v_inst_3419_, lean_object* v_file_3420_, lean_object* v_ext_3421_, uint8_t v_text_3422_, uint8_t v_exe_3423_, uint8_t v_useLocalFile_3424_){
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
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___boxed(lean_object* v_inst_3436_, lean_object* v_inst_3437_, lean_object* v_inst_3438_, lean_object* v_file_3439_, lean_object* v_ext_3440_, lean_object* v_text_3441_, lean_object* v_exe_3442_, lean_object* v_useLocalFile_3443_){
_start:
{
uint8_t v_text_boxed_3444_; uint8_t v_exe_boxed_3445_; uint8_t v_useLocalFile_boxed_3446_; lean_object* v_res_3447_; 
v_text_boxed_3444_ = lean_unbox(v_text_3441_);
v_exe_boxed_3445_ = lean_unbox(v_exe_3442_);
v_useLocalFile_boxed_3446_ = lean_unbox(v_useLocalFile_3443_);
v_res_3447_ = l_Lake_cacheArtifact___redArg(v_inst_3436_, v_inst_3437_, v_inst_3438_, v_file_3439_, v_ext_3440_, v_text_boxed_3444_, v_exe_boxed_3445_, v_useLocalFile_boxed_3446_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact(lean_object* v_m_3448_, lean_object* v_inst_3449_, lean_object* v_inst_3450_, lean_object* v_inst_3451_, lean_object* v_file_3452_, lean_object* v_ext_3453_, uint8_t v_text_3454_, uint8_t v_exe_3455_, uint8_t v_useLocalFile_3456_){
_start:
{
lean_object* v_toApplicative_3457_; lean_object* v_toFunctor_3458_; lean_object* v_toBind_3459_; lean_object* v_map_3460_; lean_object* v___f_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___f_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v_toApplicative_3457_ = lean_ctor_get(v_inst_3451_, 0);
v_toFunctor_3458_ = lean_ctor_get(v_toApplicative_3457_, 0);
lean_inc_ref(v_toFunctor_3458_);
v_toBind_3459_ = lean_ctor_get(v_inst_3451_, 1);
lean_inc(v_toBind_3459_);
lean_dec_ref(v_inst_3451_);
v_map_3460_ = lean_ctor_get(v_toFunctor_3458_, 0);
lean_inc(v_map_3460_);
lean_dec_ref(v_toFunctor_3458_);
v___f_3461_ = ((lean_object*)(l_Lake_cacheArtifact___redArg___closed__0));
v___x_3462_ = lean_box(v_text_3454_);
v___x_3463_ = lean_box(v_exe_3455_);
v___x_3464_ = lean_box(v_useLocalFile_3456_);
v___f_3465_ = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_3465_, 0, v_file_3452_);
lean_closure_set(v___f_3465_, 1, v_ext_3453_);
lean_closure_set(v___f_3465_, 2, v___x_3462_);
lean_closure_set(v___f_3465_, 3, v___x_3463_);
lean_closure_set(v___f_3465_, 4, v___x_3464_);
lean_closure_set(v___f_3465_, 5, v_inst_3450_);
v___x_3466_ = lean_apply_4(v_map_3460_, lean_box(0), lean_box(0), v___f_3461_, v_inst_3449_);
v___x_3467_ = lean_apply_4(v_toBind_3459_, lean_box(0), lean_box(0), v___x_3466_, v___f_3465_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___boxed(lean_object* v_m_3468_, lean_object* v_inst_3469_, lean_object* v_inst_3470_, lean_object* v_inst_3471_, lean_object* v_file_3472_, lean_object* v_ext_3473_, lean_object* v_text_3474_, lean_object* v_exe_3475_, lean_object* v_useLocalFile_3476_){
_start:
{
uint8_t v_text_boxed_3477_; uint8_t v_exe_boxed_3478_; uint8_t v_useLocalFile_boxed_3479_; lean_object* v_res_3480_; 
v_text_boxed_3477_ = lean_unbox(v_text_3474_);
v_exe_boxed_3478_ = lean_unbox(v_exe_3475_);
v_useLocalFile_boxed_3479_ = lean_unbox(v_useLocalFile_3476_);
v_res_3480_ = l_Lake_cacheArtifact(v_m_3468_, v_inst_3469_, v_inst_3470_, v_inst_3471_, v_file_3472_, v_ext_3473_, v_text_boxed_3477_, v_exe_boxed_3478_, v_useLocalFile_boxed_3479_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0(lean_object* v_x1_3482_, lean_object* v_x2_3483_){
_start:
{
lean_object* v_message_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v_message_3484_ = lean_ctor_get(v_x2_3483_, 0);
v___x_3485_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0));
v___x_3486_ = lean_string_append(v_x1_3482_, v___x_3485_);
v___x_3487_ = lean_string_append(v___x_3486_, v_message_3484_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___boxed(lean_object* v_x1_3488_, lean_object* v_x2_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0(v_x1_3488_, v_x2_3489_);
lean_dec_ref(v_x2_3489_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(lean_object* v_inst_3494_, uint64_t v_inputHash_3495_, lean_object* v_pkg_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_){
_start:
{
lean_object* v_toContext_3504_; lean_object* v_log_3505_; uint8_t v_action_3506_; uint8_t v_wantsRebuild_3507_; lean_object* v_trace_3508_; lean_object* v_buildTime_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3604_; 
v_toContext_3504_ = lean_ctor_get(v_a_3501_, 1);
v_log_3505_ = lean_ctor_get(v_a_3502_, 0);
v_action_3506_ = lean_ctor_get_uint8(v_a_3502_, sizeof(void*)*3);
v_wantsRebuild_3507_ = lean_ctor_get_uint8(v_a_3502_, sizeof(void*)*3 + 1);
v_trace_3508_ = lean_ctor_get(v_a_3502_, 1);
v_buildTime_3509_ = lean_ctor_get(v_a_3502_, 2);
v_isSharedCheck_3604_ = !lean_is_exclusive(v_a_3502_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3511_ = v_a_3502_;
v_isShared_3512_ = v_isSharedCheck_3604_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_buildTime_3509_);
lean_inc(v_trace_3508_);
lean_inc(v_log_3505_);
lean_dec(v_a_3502_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3604_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v_lakeCache_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v_lakeCache_3513_ = lean_ctor_get(v_toContext_3504_, 2);
v___x_3514_ = l_Lake_Package_cacheScope(v_pkg_3496_);
lean_inc_ref(v_lakeCache_3513_);
v___x_3515_ = l_Lake_Cache_readOutputs_x3f(v_lakeCache_3513_, v___x_3514_, v_inputHash_3495_, v_log_3505_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3591_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
v_a_3517_ = lean_ctor_get(v___x_3515_, 1);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3519_ = v___x_3515_;
v_isShared_3520_ = v_isSharedCheck_3591_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_inc(v_a_3516_);
lean_dec(v___x_3515_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3591_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 0, v_a_3517_);
v___x_3522_ = v___x_3511_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3517_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_trace_3508_);
lean_ctor_set(v_reuseFailAlloc_3590_, 2, v_buildTime_3509_);
lean_ctor_set_uint8(v_reuseFailAlloc_3590_, sizeof(void*)*3, v_action_3506_);
lean_ctor_set_uint8(v_reuseFailAlloc_3590_, sizeof(void*)*3 + 1, v_wantsRebuild_3507_);
v___x_3522_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
if (lean_obj_tag(v_a_3516_) == 1)
{
lean_object* v_val_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3585_; 
v_val_3523_ = lean_ctor_get(v_a_3516_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v_a_3516_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3525_ = v_a_3516_;
v_isShared_3526_ = v_isSharedCheck_3585_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_val_3523_);
lean_dec(v_a_3516_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3585_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3527_; lean_object* v_r_3529_; lean_object* v___y_3530_; 
lean_inc_ref(v_a_3501_);
lean_inc(v_a_3500_);
lean_inc(v_a_3499_);
lean_inc(v_a_3498_);
v___x_3527_ = lean_apply_8(v_inst_3494_, v_val_3523_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v___x_3522_, lean_box(0));
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v_a_3534_; lean_object* v_a_3535_; lean_object* v___x_3537_; 
v_a_3534_ = lean_ctor_get(v___x_3527_, 0);
lean_inc(v_a_3534_);
v_a_3535_ = lean_ctor_get(v___x_3527_, 1);
lean_inc(v_a_3535_);
lean_dec_ref(v___x_3527_);
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 0, v_a_3534_);
v___x_3537_ = v___x_3525_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3534_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
v_r_3529_ = v___x_3537_;
v___y_3530_ = v_a_3535_;
goto v___jp_3528_;
}
}
else
{
lean_object* v_a_3539_; lean_object* v_a_3540_; lean_object* v_log_3541_; uint8_t v_action_3542_; uint8_t v_wantsRebuild_3543_; lean_object* v_trace_3544_; lean_object* v_buildTime_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3584_; 
lean_del_object(v___x_3525_);
v_a_3539_ = lean_ctor_get(v___x_3527_, 1);
lean_inc(v_a_3539_);
v_a_3540_ = lean_ctor_get(v___x_3527_, 0);
lean_inc(v_a_3540_);
lean_dec_ref(v___x_3527_);
v_log_3541_ = lean_ctor_get(v_a_3539_, 0);
v_action_3542_ = lean_ctor_get_uint8(v_a_3539_, sizeof(void*)*3);
v_wantsRebuild_3543_ = lean_ctor_get_uint8(v_a_3539_, sizeof(void*)*3 + 1);
v_trace_3544_ = lean_ctor_get(v_a_3539_, 1);
v_buildTime_3545_ = lean_ctor_get(v_a_3539_, 2);
v_isSharedCheck_3584_ = !lean_is_exclusive(v_a_3539_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3547_ = v_a_3539_;
v_isShared_3548_ = v_isSharedCheck_3584_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_buildTime_3545_);
lean_inc(v_trace_3544_);
lean_inc(v_log_3541_);
lean_dec(v_a_3539_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3584_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___y_3553_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; uint8_t v___x_3575_; 
v___x_3549_ = lean_array_get_size(v_log_3541_);
lean_inc(v_a_3540_);
v___x_3550_ = l_Array_extract___redArg(v_log_3541_, v_a_3540_, v___x_3549_);
v___x_3551_ = l_Array_shrink___redArg(v_log_3541_, v_a_3540_);
lean_dec(v_a_3540_);
v___x_3561_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0));
v___x_3562_ = l_Lake_lowerHexUInt64(v_inputHash_3495_);
v___x_3563_ = lean_unsigned_to_nat(7u);
v___x_3564_ = lean_unsigned_to_nat(0u);
v___x_3565_ = lean_string_utf8_byte_size(v___x_3562_);
lean_inc_ref(v___x_3562_);
v___x_3566_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3562_);
lean_ctor_set(v___x_3566_, 1, v___x_3564_);
lean_ctor_set(v___x_3566_, 2, v___x_3565_);
v___x_3567_ = l_String_Slice_Pos_nextn(v___x_3566_, v___x_3564_, v___x_3563_);
lean_dec_ref(v___x_3566_);
v___x_3568_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3562_);
lean_ctor_set(v___x_3568_, 1, v___x_3564_);
lean_ctor_set(v___x_3568_, 2, v___x_3567_);
v___x_3569_ = l_String_Slice_toString(v___x_3568_);
lean_dec_ref(v___x_3568_);
v___x_3570_ = lean_string_append(v___x_3561_, v___x_3569_);
lean_dec_ref(v___x_3569_);
v___x_3571_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1));
v___x_3572_ = lean_string_append(v___x_3570_, v___x_3571_);
v___x_3573_ = lean_array_get_size(v___x_3550_);
v___x_3574_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__9));
v___x_3575_ = lean_nat_dec_lt(v___x_3564_, v___x_3573_);
if (v___x_3575_ == 0)
{
lean_dec_ref(v___x_3550_);
v___y_3553_ = v___x_3572_;
goto v___jp_3552_;
}
else
{
lean_object* v___f_3576_; uint8_t v___x_3577_; 
v___f_3576_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__2));
v___x_3577_ = lean_nat_dec_le(v___x_3573_, v___x_3573_);
if (v___x_3577_ == 0)
{
if (v___x_3575_ == 0)
{
lean_dec_ref(v___x_3550_);
v___y_3553_ = v___x_3572_;
goto v___jp_3552_;
}
else
{
size_t v___x_3578_; size_t v___x_3579_; lean_object* v___x_3580_; 
v___x_3578_ = ((size_t)0ULL);
v___x_3579_ = lean_usize_of_nat(v___x_3573_);
v___x_3580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3574_, v___f_3576_, v___x_3550_, v___x_3578_, v___x_3579_, v___x_3572_);
v___y_3553_ = v___x_3580_;
goto v___jp_3552_;
}
}
else
{
size_t v___x_3581_; size_t v___x_3582_; lean_object* v___x_3583_; 
v___x_3581_ = ((size_t)0ULL);
v___x_3582_ = lean_usize_of_nat(v___x_3573_);
v___x_3583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3574_, v___f_3576_, v___x_3550_, v___x_3581_, v___x_3582_, v___x_3572_);
v___y_3553_ = v___x_3583_;
goto v___jp_3552_;
}
}
v___jp_3552_:
{
uint8_t v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3558_; 
v___x_3554_ = 2;
v___x_3555_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3555_, 0, v___y_3553_);
lean_ctor_set_uint8(v___x_3555_, sizeof(void*)*1, v___x_3554_);
v___x_3556_ = lean_array_push(v___x_3551_, v___x_3555_);
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 0, v___x_3556_);
v___x_3558_ = v___x_3547_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3556_);
lean_ctor_set(v_reuseFailAlloc_3560_, 1, v_trace_3544_);
lean_ctor_set(v_reuseFailAlloc_3560_, 2, v_buildTime_3545_);
lean_ctor_set_uint8(v_reuseFailAlloc_3560_, sizeof(void*)*3, v_action_3542_);
lean_ctor_set_uint8(v_reuseFailAlloc_3560_, sizeof(void*)*3 + 1, v_wantsRebuild_3543_);
v___x_3558_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
lean_object* v___x_3559_; 
v___x_3559_ = lean_box(0);
v_r_3529_ = v___x_3559_;
v___y_3530_ = v___x_3558_;
goto v___jp_3528_;
}
}
}
}
v___jp_3528_:
{
lean_object* v___x_3532_; 
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 1, v___y_3530_);
lean_ctor_set(v___x_3519_, 0, v_r_3529_);
v___x_3532_ = v___x_3519_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_r_3529_);
lean_ctor_set(v_reuseFailAlloc_3533_, 1, v___y_3530_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
else
{
lean_object* v___x_3586_; lean_object* v___x_3588_; 
lean_dec(v_a_3516_);
lean_dec_ref(v_a_3497_);
lean_dec_ref(v_inst_3494_);
v___x_3586_ = lean_box(0);
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 1, v___x_3522_);
lean_ctor_set(v___x_3519_, 0, v___x_3586_);
v___x_3588_ = v___x_3519_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3586_);
lean_ctor_set(v_reuseFailAlloc_3589_, 1, v___x_3522_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
}
else
{
lean_object* v_a_3592_; lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3603_; 
lean_dec_ref(v_a_3497_);
lean_dec_ref(v_inst_3494_);
v_a_3592_ = lean_ctor_get(v___x_3515_, 0);
v_a_3593_ = lean_ctor_get(v___x_3515_, 1);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3595_ = v___x_3515_;
v_isShared_3596_ = v_isSharedCheck_3603_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_a_3593_);
lean_inc(v_a_3592_);
lean_dec(v___x_3515_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3603_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3598_; 
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 0, v_a_3593_);
v___x_3598_ = v___x_3511_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3593_);
lean_ctor_set(v_reuseFailAlloc_3602_, 1, v_trace_3508_);
lean_ctor_set(v_reuseFailAlloc_3602_, 2, v_buildTime_3509_);
lean_ctor_set_uint8(v_reuseFailAlloc_3602_, sizeof(void*)*3, v_action_3506_);
lean_ctor_set_uint8(v_reuseFailAlloc_3602_, sizeof(void*)*3 + 1, v_wantsRebuild_3507_);
v___x_3598_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
lean_object* v___x_3600_; 
if (v_isShared_3596_ == 0)
{
lean_ctor_set(v___x_3595_, 1, v___x_3598_);
v___x_3600_ = v___x_3595_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3592_);
lean_ctor_set(v_reuseFailAlloc_3601_, 1, v___x_3598_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___boxed(lean_object* v_inst_3605_, lean_object* v_inputHash_3606_, lean_object* v_pkg_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_){
_start:
{
uint64_t v_inputHash_boxed_3615_; lean_object* v_res_3616_; 
v_inputHash_boxed_3615_ = lean_unbox_uint64(v_inputHash_3606_);
lean_dec_ref(v_inputHash_3606_);
v_res_3616_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3605_, v_inputHash_boxed_3615_, v_pkg_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_);
lean_dec_ref(v_a_3612_);
lean_dec(v_a_3611_);
lean_dec(v_a_3610_);
lean_dec(v_a_3609_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f(lean_object* v_00_u03b1_3617_, lean_object* v_inst_3618_, uint64_t v_inputHash_3619_, lean_object* v_pkg_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_){
_start:
{
lean_object* v___x_3628_; 
v___x_3628_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3618_, v_inputHash_3619_, v_pkg_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___boxed(lean_object* v_00_u03b1_3629_, lean_object* v_inst_3630_, lean_object* v_inputHash_3631_, lean_object* v_pkg_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_){
_start:
{
uint64_t v_inputHash_boxed_3640_; lean_object* v_res_3641_; 
v_inputHash_boxed_3640_ = lean_unbox_uint64(v_inputHash_3631_);
lean_dec_ref(v_inputHash_3631_);
v_res_3641_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f(v_00_u03b1_3629_, v_inst_3630_, v_inputHash_boxed_3640_, v_pkg_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_);
lean_dec_ref(v_a_3637_);
lean_dec(v_a_3636_);
lean_dec(v_a_3635_);
lean_dec(v_a_3634_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(lean_object* v_a_3642_, lean_object* v_____r_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3651_, 0, v_a_3642_);
v___x_3652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3651_);
v___x_3653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3652_);
lean_ctor_set(v___x_3653_, 1, v___y_3649_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0___boxed(lean_object* v_a_3654_, lean_object* v_____r_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
lean_object* v_res_3663_; 
v_res_3663_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3654_, v_____r_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
lean_dec_ref(v___y_3660_);
lean_dec(v___y_3659_);
lean_dec(v___y_3658_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
return v_res_3663_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg(lean_object* v_inst_3665_, uint64_t v_inputHash_3666_, lean_object* v_savedTrace_3667_, lean_object* v_pkg_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_){
_start:
{
lean_object* v___y_3677_; lean_object* v_a_3681_; lean_object* v_a_3682_; lean_object* v___y_3697_; 
if (lean_obj_tag(v_savedTrace_3667_) == 2)
{
lean_object* v_data_3712_; uint64_t v_depHash_3713_; lean_object* v_outputs_x3f_3714_; uint8_t v___x_3715_; 
v_data_3712_ = lean_ctor_get(v_savedTrace_3667_, 0);
lean_inc_ref(v_data_3712_);
lean_dec_ref(v_savedTrace_3667_);
v_depHash_3713_ = lean_ctor_get_uint64(v_data_3712_, sizeof(void*)*3);
v_outputs_x3f_3714_ = lean_ctor_get(v_data_3712_, 1);
lean_inc(v_outputs_x3f_3714_);
lean_dec_ref(v_data_3712_);
v___x_3715_ = lean_uint64_dec_eq(v_depHash_3713_, v_inputHash_3666_);
if (v___x_3715_ == 0)
{
lean_dec(v_outputs_x3f_3714_);
lean_dec_ref(v_a_3669_);
lean_dec_ref(v_pkg_3668_);
lean_dec_ref(v_inst_3665_);
v___y_3677_ = v_a_3674_;
goto v___jp_3676_;
}
else
{
if (lean_obj_tag(v_outputs_x3f_3714_) == 1)
{
lean_object* v_val_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v_val_3716_ = lean_ctor_get(v_outputs_x3f_3714_, 0);
lean_inc_n(v_val_3716_, 2);
lean_dec_ref(v_outputs_x3f_3714_);
v___x_3717_ = lean_box(0);
v___x_3718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3718_, 0, v_val_3716_);
lean_ctor_set(v___x_3718_, 1, v___x_3717_);
lean_ctor_set(v___x_3718_, 2, v___x_3717_);
lean_inc_ref(v_a_3673_);
lean_inc(v_a_3672_);
lean_inc(v_a_3671_);
lean_inc(v_a_3670_);
lean_inc_ref(v_a_3669_);
v___x_3719_ = lean_apply_8(v_inst_3665_, v___x_3718_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, lean_box(0));
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v_config_3720_; lean_object* v_a_3721_; lean_object* v_a_3722_; lean_object* v_enableArtifactCache_x3f_3723_; lean_object* v_a_3725_; uint8_t v_a_3729_; lean_object* v_a_3730_; 
v_config_3720_ = lean_ctor_get(v_pkg_3668_, 6);
v_a_3721_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_a_3721_);
v_a_3722_ = lean_ctor_get(v___x_3719_, 1);
lean_inc(v_a_3722_);
lean_dec_ref(v___x_3719_);
v_enableArtifactCache_x3f_3723_ = lean_ctor_get(v_config_3720_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_3723_) == 0)
{
lean_object* v_toContext_3761_; lean_object* v_lakeEnv_3762_; lean_object* v_enableArtifactCache_x3f_3763_; 
v_toContext_3761_ = lean_ctor_get(v_a_3673_, 1);
v_lakeEnv_3762_ = lean_ctor_get(v_toContext_3761_, 0);
v_enableArtifactCache_x3f_3763_ = lean_ctor_get(v_lakeEnv_3762_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_3763_) == 0)
{
lean_object* v_packages_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v_config_3767_; lean_object* v_enableArtifactCache_x3f_3768_; 
v_packages_3764_ = lean_ctor_get(v_toContext_3761_, 4);
v___x_3765_ = lean_unsigned_to_nat(0u);
v___x_3766_ = lean_array_fget_borrowed(v_packages_3764_, v___x_3765_);
v_config_3767_ = lean_ctor_get(v___x_3766_, 6);
v_enableArtifactCache_x3f_3768_ = lean_ctor_get(v_config_3767_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_3768_) == 0)
{
lean_dec(v_val_3716_);
lean_dec_ref(v_pkg_3668_);
v_a_3725_ = v_a_3722_;
goto v___jp_3724_;
}
else
{
lean_object* v_val_3769_; uint8_t v___x_3770_; 
v_val_3769_ = lean_ctor_get(v_enableArtifactCache_x3f_3768_, 0);
v___x_3770_ = lean_unbox(v_val_3769_);
v_a_3729_ = v___x_3770_;
v_a_3730_ = v_a_3722_;
goto v___jp_3728_;
}
}
else
{
lean_object* v_val_3771_; uint8_t v___x_3772_; 
v_val_3771_ = lean_ctor_get(v_enableArtifactCache_x3f_3763_, 0);
v___x_3772_ = lean_unbox(v_val_3771_);
v_a_3729_ = v___x_3772_;
v_a_3730_ = v_a_3722_;
goto v___jp_3728_;
}
}
else
{
lean_object* v_val_3773_; uint8_t v___x_3774_; 
v_val_3773_ = lean_ctor_get(v_enableArtifactCache_x3f_3723_, 0);
v___x_3774_ = lean_unbox(v_val_3773_);
v_a_3729_ = v___x_3774_;
v_a_3730_ = v_a_3722_;
goto v___jp_3728_;
}
v___jp_3724_:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3726_ = lean_box(0);
v___x_3727_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3721_, v___x_3726_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3725_);
lean_dec_ref(v_a_3669_);
v___y_3697_ = v___x_3727_;
goto v___jp_3696_;
}
v___jp_3728_:
{
if (v_a_3729_ == 0)
{
lean_dec(v_val_3716_);
lean_dec_ref(v_pkg_3668_);
v_a_3725_ = v_a_3730_;
goto v___jp_3724_;
}
else
{
lean_object* v_toContext_3731_; lean_object* v_log_3732_; uint8_t v_action_3733_; uint8_t v_wantsRebuild_3734_; lean_object* v_trace_3735_; lean_object* v_buildTime_3736_; lean_object* v_lakeCache_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
v_toContext_3731_ = lean_ctor_get(v_a_3673_, 1);
v_log_3732_ = lean_ctor_get(v_a_3730_, 0);
v_action_3733_ = lean_ctor_get_uint8(v_a_3730_, sizeof(void*)*3);
v_wantsRebuild_3734_ = lean_ctor_get_uint8(v_a_3730_, sizeof(void*)*3 + 1);
v_trace_3735_ = lean_ctor_get(v_a_3730_, 1);
v_buildTime_3736_ = lean_ctor_get(v_a_3730_, 2);
v_lakeCache_3737_ = lean_ctor_get(v_toContext_3731_, 2);
v___x_3738_ = l_Lake_Package_cacheScope(v_pkg_3668_);
lean_inc_ref(v_lakeCache_3737_);
v___x_3739_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_3737_, v___x_3738_, v_inputHash_3666_, v_val_3716_, v___x_3717_, v___x_3717_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v___x_3740_; lean_object* v___x_3741_; 
lean_dec_ref(v___x_3739_);
v___x_3740_ = lean_box(0);
v___x_3741_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3721_, v___x_3740_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3730_);
lean_dec_ref(v_a_3669_);
v___y_3697_ = v___x_3741_;
goto v___jp_3696_;
}
else
{
lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3757_; 
lean_inc(v_buildTime_3736_);
lean_inc_ref(v_trace_3735_);
lean_inc_ref(v_log_3732_);
v_isSharedCheck_3757_ = !lean_is_exclusive(v_a_3730_);
if (v_isSharedCheck_3757_ == 0)
{
lean_object* v_unused_3758_; lean_object* v_unused_3759_; lean_object* v_unused_3760_; 
v_unused_3758_ = lean_ctor_get(v_a_3730_, 2);
lean_dec(v_unused_3758_);
v_unused_3759_ = lean_ctor_get(v_a_3730_, 1);
lean_dec(v_unused_3759_);
v_unused_3760_ = lean_ctor_get(v_a_3730_, 0);
lean_dec(v_unused_3760_);
v___x_3743_ = v_a_3730_;
v_isShared_3744_ = v_isSharedCheck_3757_;
goto v_resetjp_3742_;
}
else
{
lean_dec(v_a_3730_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3757_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v_a_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; uint8_t v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3754_; 
v_a_3745_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_a_3745_);
lean_dec_ref(v___x_3739_);
v___x_3746_ = ((lean_object*)(l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0));
v___x_3747_ = lean_io_error_to_string(v_a_3745_);
v___x_3748_ = lean_string_append(v___x_3746_, v___x_3747_);
lean_dec_ref(v___x_3747_);
v___x_3749_ = 2;
v___x_3750_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3750_, 0, v___x_3748_);
lean_ctor_set_uint8(v___x_3750_, sizeof(void*)*1, v___x_3749_);
v___x_3751_ = lean_box(0);
v___x_3752_ = lean_array_push(v_log_3732_, v___x_3750_);
if (v_isShared_3744_ == 0)
{
lean_ctor_set(v___x_3743_, 0, v___x_3752_);
v___x_3754_ = v___x_3743_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3752_);
lean_ctor_set(v_reuseFailAlloc_3756_, 1, v_trace_3735_);
lean_ctor_set(v_reuseFailAlloc_3756_, 2, v_buildTime_3736_);
lean_ctor_set_uint8(v_reuseFailAlloc_3756_, sizeof(void*)*3, v_action_3733_);
lean_ctor_set_uint8(v_reuseFailAlloc_3756_, sizeof(void*)*3 + 1, v_wantsRebuild_3734_);
v___x_3754_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
lean_object* v___x_3755_; 
v___x_3755_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3721_, v___x_3751_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v___x_3754_);
lean_dec_ref(v_a_3669_);
v___y_3697_ = v___x_3755_;
goto v___jp_3696_;
}
}
}
}
}
}
else
{
lean_object* v_a_3775_; lean_object* v_a_3776_; 
lean_dec(v_val_3716_);
lean_dec_ref(v_a_3669_);
lean_dec_ref(v_pkg_3668_);
v_a_3775_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_a_3775_);
v_a_3776_ = lean_ctor_get(v___x_3719_, 1);
lean_inc(v_a_3776_);
lean_dec_ref(v___x_3719_);
v_a_3681_ = v_a_3775_;
v_a_3682_ = v_a_3776_;
goto v___jp_3680_;
}
}
else
{
lean_dec(v_outputs_x3f_3714_);
lean_dec_ref(v_a_3669_);
lean_dec_ref(v_pkg_3668_);
lean_dec_ref(v_inst_3665_);
v___y_3677_ = v_a_3674_;
goto v___jp_3676_;
}
}
}
else
{
lean_dec_ref(v_a_3669_);
lean_dec_ref(v_pkg_3668_);
lean_dec(v_savedTrace_3667_);
lean_dec_ref(v_inst_3665_);
v___y_3677_ = v_a_3674_;
goto v___jp_3676_;
}
v___jp_3676_:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3678_ = lean_box(0);
v___x_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3678_);
lean_ctor_set(v___x_3679_, 1, v___y_3677_);
return v___x_3679_;
}
v___jp_3680_:
{
lean_object* v_log_3683_; uint8_t v_action_3684_; uint8_t v_wantsRebuild_3685_; lean_object* v_trace_3686_; lean_object* v_buildTime_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3695_; 
v_log_3683_ = lean_ctor_get(v_a_3682_, 0);
v_action_3684_ = lean_ctor_get_uint8(v_a_3682_, sizeof(void*)*3);
v_wantsRebuild_3685_ = lean_ctor_get_uint8(v_a_3682_, sizeof(void*)*3 + 1);
v_trace_3686_ = lean_ctor_get(v_a_3682_, 1);
v_buildTime_3687_ = lean_ctor_get(v_a_3682_, 2);
v_isSharedCheck_3695_ = !lean_is_exclusive(v_a_3682_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3689_ = v_a_3682_;
v_isShared_3690_ = v_isSharedCheck_3695_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_buildTime_3687_);
lean_inc(v_trace_3686_);
lean_inc(v_log_3683_);
lean_dec(v_a_3682_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3695_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3691_; lean_object* v___x_3693_; 
v___x_3691_ = l_Array_shrink___redArg(v_log_3683_, v_a_3681_);
lean_dec(v_a_3681_);
if (v_isShared_3690_ == 0)
{
lean_ctor_set(v___x_3689_, 0, v___x_3691_);
v___x_3693_ = v___x_3689_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3691_);
lean_ctor_set(v_reuseFailAlloc_3694_, 1, v_trace_3686_);
lean_ctor_set(v_reuseFailAlloc_3694_, 2, v_buildTime_3687_);
lean_ctor_set_uint8(v_reuseFailAlloc_3694_, sizeof(void*)*3, v_action_3684_);
lean_ctor_set_uint8(v_reuseFailAlloc_3694_, sizeof(void*)*3 + 1, v_wantsRebuild_3685_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
v___y_3677_ = v___x_3693_;
goto v___jp_3676_;
}
}
}
v___jp_3696_:
{
if (lean_obj_tag(v___y_3697_) == 0)
{
lean_object* v_a_3698_; 
v_a_3698_ = lean_ctor_get(v___y_3697_, 0);
if (lean_obj_tag(v_a_3698_) == 0)
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3707_; 
lean_inc_ref(v_a_3698_);
v_a_3699_ = lean_ctor_get(v___y_3697_, 1);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___y_3697_);
if (v_isSharedCheck_3707_ == 0)
{
lean_object* v_unused_3708_; 
v_unused_3708_ = lean_ctor_get(v___y_3697_, 0);
lean_dec(v_unused_3708_);
v___x_3701_ = v___y_3697_;
v_isShared_3702_ = v_isSharedCheck_3707_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___y_3697_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3707_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v_a_3703_; lean_object* v___x_3705_; 
v_a_3703_ = lean_ctor_get(v_a_3698_, 0);
lean_inc(v_a_3703_);
lean_dec_ref(v_a_3698_);
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 0, v_a_3703_);
v___x_3705_ = v___x_3701_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3703_);
lean_ctor_set(v_reuseFailAlloc_3706_, 1, v_a_3699_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
else
{
lean_object* v_a_3709_; 
v_a_3709_ = lean_ctor_get(v___y_3697_, 1);
lean_inc(v_a_3709_);
lean_dec_ref(v___y_3697_);
v___y_3677_ = v_a_3709_;
goto v___jp_3676_;
}
}
else
{
lean_object* v_a_3710_; lean_object* v_a_3711_; 
v_a_3710_ = lean_ctor_get(v___y_3697_, 0);
lean_inc(v_a_3710_);
v_a_3711_ = lean_ctor_get(v___y_3697_, 1);
lean_inc(v_a_3711_);
lean_dec_ref(v___y_3697_);
v_a_3681_ = v_a_3710_;
v_a_3682_ = v_a_3711_;
goto v___jp_3680_;
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
lean_dec_ref(v_a_3785_);
lean_dec(v_a_3784_);
lean_dec(v_a_3783_);
lean_dec(v_a_3782_);
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
lean_dec_ref(v_a_3812_);
lean_dec(v_a_3811_);
lean_dec(v_a_3810_);
lean_dec(v_a_3809_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg(lean_object* v_inst_3817_, uint64_t v_inputHash_3818_, lean_object* v_savedTrace_3819_, lean_object* v_pkg_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_){
_start:
{
lean_object* v___x_3828_; 
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
lean_dec_ref(v_a_3851_);
lean_dec(v_a_3850_);
lean_dec(v_a_3849_);
lean_dec(v_a_3848_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f(lean_object* v_00_u03b1_3856_, lean_object* v_inst_3857_, uint64_t v_inputHash_3858_, lean_object* v_savedTrace_3859_, lean_object* v_pkg_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_){
_start:
{
lean_object* v___x_3868_; 
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
lean_dec_ref(v_a_3892_);
lean_dec(v_a_3891_);
lean_dec(v_a_3890_);
lean_dec(v_a_3889_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__0(lean_object* v_descr_3897_, lean_object* v___x_3898_, lean_object* v_mtime_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; 
lean_inc_ref(v___x_3898_);
v___x_3907_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3907_, 0, v_descr_3897_);
lean_ctor_set(v___x_3907_, 1, v___x_3898_);
lean_ctor_set(v___x_3907_, 2, v___x_3898_);
lean_ctor_set(v___x_3907_, 3, v_mtime_3899_);
v___x_3908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3907_);
lean_ctor_set(v___x_3908_, 1, v___y_3905_);
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__0___boxed(lean_object* v_descr_3909_, lean_object* v___x_3910_, lean_object* v_mtime_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_){
_start:
{
lean_object* v_res_3919_; 
v_res_3919_ = l_Lake_resolveArtifact___lam__0(v_descr_3909_, v___x_3910_, v_mtime_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
lean_dec_ref(v___y_3916_);
lean_dec(v___y_3915_);
lean_dec(v___y_3914_);
lean_dec(v___y_3913_);
lean_dec_ref(v___y_3912_);
return v_res_3919_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__1(lean_object* v___x_3921_, lean_object* v___f_3922_, lean_object* v_____r_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_){
_start:
{
lean_object* v_log_3931_; uint8_t v_action_3932_; uint8_t v_wantsRebuild_3933_; lean_object* v_trace_3934_; lean_object* v_buildTime_3935_; lean_object* v___x_3936_; 
v_log_3931_ = lean_ctor_get(v___y_3929_, 0);
v_action_3932_ = lean_ctor_get_uint8(v___y_3929_, sizeof(void*)*3);
v_wantsRebuild_3933_ = lean_ctor_get_uint8(v___y_3929_, sizeof(void*)*3 + 1);
v_trace_3934_ = lean_ctor_get(v___y_3929_, 1);
v_buildTime_3935_ = lean_ctor_get(v___y_3929_, 2);
v___x_3936_ = lean_io_metadata(v___x_3921_);
if (lean_obj_tag(v___x_3936_) == 0)
{
lean_object* v_a_3937_; lean_object* v_modified_3938_; lean_object* v___x_3939_; 
v_a_3937_ = lean_ctor_get(v___x_3936_, 0);
lean_inc(v_a_3937_);
lean_dec_ref(v___x_3936_);
v_modified_3938_ = lean_ctor_get(v_a_3937_, 1);
lean_inc_ref(v_modified_3938_);
lean_dec(v_a_3937_);
lean_inc_ref(v___y_3928_);
lean_inc(v___y_3927_);
lean_inc(v___y_3926_);
lean_inc(v___y_3925_);
v___x_3939_ = lean_apply_8(v___f_3922_, v_modified_3938_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, lean_box(0));
return v___x_3939_;
}
else
{
lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3955_; 
lean_inc(v_buildTime_3935_);
lean_inc_ref(v_trace_3934_);
lean_inc_ref(v_log_3931_);
lean_dec_ref(v___y_3924_);
lean_dec_ref(v___f_3922_);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___y_3929_);
if (v_isSharedCheck_3955_ == 0)
{
lean_object* v_unused_3956_; lean_object* v_unused_3957_; lean_object* v_unused_3958_; 
v_unused_3956_ = lean_ctor_get(v___y_3929_, 2);
lean_dec(v_unused_3956_);
v_unused_3957_ = lean_ctor_get(v___y_3929_, 1);
lean_dec(v_unused_3957_);
v_unused_3958_ = lean_ctor_get(v___y_3929_, 0);
lean_dec(v_unused_3958_);
v___x_3941_ = v___y_3929_;
v_isShared_3942_ = v_isSharedCheck_3955_;
goto v_resetjp_3940_;
}
else
{
lean_dec(v___y_3929_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3955_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v_a_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; uint8_t v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3952_; 
v_a_3943_ = lean_ctor_get(v___x_3936_, 0);
lean_inc(v_a_3943_);
lean_dec_ref(v___x_3936_);
v___x_3944_ = ((lean_object*)(l_Lake_resolveArtifact___lam__1___closed__0));
v___x_3945_ = lean_io_error_to_string(v_a_3943_);
v___x_3946_ = lean_string_append(v___x_3944_, v___x_3945_);
lean_dec_ref(v___x_3945_);
v___x_3947_ = 3;
v___x_3948_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3948_, 0, v___x_3946_);
lean_ctor_set_uint8(v___x_3948_, sizeof(void*)*1, v___x_3947_);
v___x_3949_ = lean_array_get_size(v_log_3931_);
v___x_3950_ = lean_array_push(v_log_3931_, v___x_3948_);
if (v_isShared_3942_ == 0)
{
lean_ctor_set(v___x_3941_, 0, v___x_3950_);
v___x_3952_ = v___x_3941_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v___x_3950_);
lean_ctor_set(v_reuseFailAlloc_3954_, 1, v_trace_3934_);
lean_ctor_set(v_reuseFailAlloc_3954_, 2, v_buildTime_3935_);
lean_ctor_set_uint8(v_reuseFailAlloc_3954_, sizeof(void*)*3, v_action_3932_);
lean_ctor_set_uint8(v_reuseFailAlloc_3954_, sizeof(void*)*3 + 1, v_wantsRebuild_3933_);
v___x_3952_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
lean_object* v___x_3953_; 
v___x_3953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3949_);
lean_ctor_set(v___x_3953_, 1, v___x_3952_);
return v___x_3953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__1___boxed(lean_object* v___x_3959_, lean_object* v___f_3960_, lean_object* v_____r_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v_res_3969_; 
v_res_3969_ = l_Lake_resolveArtifact___lam__1(v___x_3959_, v___f_3960_, v_____r_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
lean_dec_ref(v___y_3966_);
lean_dec(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec(v___y_3963_);
lean_dec_ref(v___x_3959_);
return v_res_3969_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact(lean_object* v_descr_3981_, lean_object* v_service_x3f_3982_, lean_object* v_scope_x3f_3983_, uint8_t v_exe_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_){
_start:
{
lean_object* v___y_3993_; lean_object* v_a_3994_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v_toContext_4000_; lean_object* v_log_4001_; uint8_t v_action_4002_; uint8_t v_wantsRebuild_4003_; lean_object* v_trace_4004_; lean_object* v_buildTime_4005_; lean_object* v_lakeConfig_4006_; lean_object* v_lakeCache_4007_; uint64_t v_hash_4008_; lean_object* v_ext_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___y_4013_; lean_object* v___x_4111_; lean_object* v___x_4112_; uint8_t v___x_4113_; 
v_toContext_4000_ = lean_ctor_get(v_a_3989_, 1);
v_log_4001_ = lean_ctor_get(v_a_3990_, 0);
v_action_4002_ = lean_ctor_get_uint8(v_a_3990_, sizeof(void*)*3);
v_wantsRebuild_4003_ = lean_ctor_get_uint8(v_a_3990_, sizeof(void*)*3 + 1);
v_trace_4004_ = lean_ctor_get(v_a_3990_, 1);
v_buildTime_4005_ = lean_ctor_get(v_a_3990_, 2);
v_lakeConfig_4006_ = lean_ctor_get(v_toContext_4000_, 1);
v_lakeCache_4007_ = lean_ctor_get(v_toContext_4000_, 2);
v_hash_4008_ = lean_ctor_get_uint64(v_descr_3981_, sizeof(void*)*1);
v_ext_4009_ = lean_ctor_get(v_descr_3981_, 0);
v___x_4010_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
lean_inc_ref(v_lakeCache_4007_);
v___x_4011_ = l_System_FilePath_join(v_lakeCache_4007_, v___x_4010_);
v___x_4111_ = lean_string_utf8_byte_size(v_ext_4009_);
v___x_4112_ = lean_unsigned_to_nat(0u);
v___x_4113_ = lean_nat_dec_eq(v___x_4111_, v___x_4112_);
if (v___x_4113_ == 0)
{
lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4114_ = l_Lake_lowerHexUInt64(v_hash_4008_);
v___x_4115_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_4116_ = lean_string_append(v___x_4114_, v___x_4115_);
v___x_4117_ = lean_string_append(v___x_4116_, v_ext_4009_);
v___y_4013_ = v___x_4117_;
goto v___jp_4012_;
}
else
{
lean_object* v___x_4118_; 
v___x_4118_ = l_Lake_lowerHexUInt64(v_hash_4008_);
v___y_4013_ = v___x_4118_;
goto v___jp_4012_;
}
v___jp_3992_:
{
lean_object* v___x_3995_; 
v___x_3995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3995_, 0, v___y_3993_);
lean_ctor_set(v___x_3995_, 1, v_a_3994_);
return v___x_3995_;
}
v___jp_3996_:
{
if (lean_obj_tag(v___y_3998_) == 0)
{
lean_dec(v___y_3997_);
return v___y_3998_;
}
else
{
lean_object* v_a_3999_; 
v_a_3999_ = lean_ctor_get(v___y_3998_, 1);
lean_inc(v_a_3999_);
lean_dec_ref(v___y_3998_);
v___y_3993_ = v___y_3997_;
v_a_3994_ = v_a_3999_;
goto v___jp_3992_;
}
}
v___jp_4012_:
{
lean_object* v___x_4014_; lean_object* v___f_4015_; lean_object* v___x_4016_; 
v___x_4014_ = l_Lake_joinRelative(v___x_4011_, v___y_4013_);
lean_inc_ref(v___x_4014_);
lean_inc_ref(v_descr_3981_);
v___f_4015_ = lean_alloc_closure((void*)(l_Lake_resolveArtifact___lam__0___boxed), 10, 2);
lean_closure_set(v___f_4015_, 0, v_descr_3981_);
lean_closure_set(v___f_4015_, 1, v___x_4014_);
v___x_4016_ = lean_io_metadata(v___x_4014_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_object* v_a_4017_; lean_object* v_modified_4018_; lean_object* v___x_4019_; 
lean_dec_ref(v___f_4015_);
lean_dec(v_scope_x3f_3983_);
lean_dec(v_service_x3f_3982_);
v_a_4017_ = lean_ctor_get(v___x_4016_, 0);
lean_inc(v_a_4017_);
lean_dec_ref(v___x_4016_);
v_modified_4018_ = lean_ctor_get(v_a_4017_, 1);
lean_inc_ref(v_modified_4018_);
lean_dec(v_a_4017_);
v___x_4019_ = l_Lake_resolveArtifact___lam__0(v_descr_3981_, v___x_4014_, v_modified_4018_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_);
lean_dec_ref(v_a_3985_);
return v___x_4019_;
}
else
{
lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4107_; 
lean_inc(v_buildTime_4005_);
lean_inc_ref(v_trace_4004_);
lean_inc_ref(v_log_4001_);
lean_dec_ref(v_descr_3981_);
v_isSharedCheck_4107_ = !lean_is_exclusive(v_a_3990_);
if (v_isSharedCheck_4107_ == 0)
{
lean_object* v_unused_4108_; lean_object* v_unused_4109_; lean_object* v_unused_4110_; 
v_unused_4108_ = lean_ctor_get(v_a_3990_, 2);
lean_dec(v_unused_4108_);
v_unused_4109_ = lean_ctor_get(v_a_3990_, 1);
lean_dec(v_unused_4109_);
v_unused_4110_ = lean_ctor_get(v_a_3990_, 0);
lean_dec(v_unused_4110_);
v___x_4021_ = v_a_3990_;
v_isShared_4022_ = v_isSharedCheck_4107_;
goto v_resetjp_4020_;
}
else
{
lean_dec(v_a_3990_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4107_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v_a_4023_; 
v_a_4023_ = lean_ctor_get(v___x_4016_, 0);
lean_inc(v_a_4023_);
lean_dec_ref(v___x_4016_);
if (lean_obj_tag(v_a_4023_) == 11)
{
lean_object* v___x_4024_; 
lean_dec_ref(v_a_4023_);
v___x_4024_ = lean_array_get_size(v_log_4001_);
if (lean_obj_tag(v_service_x3f_3982_) == 1)
{
lean_object* v_val_4025_; lean_object* v_cacheServices_4026_; uint8_t v___x_4027_; uint8_t v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
v_val_4025_ = lean_ctor_get(v_service_x3f_3982_, 0);
lean_inc_n(v_val_4025_, 2);
lean_dec_ref(v_service_x3f_3982_);
v_cacheServices_4026_ = lean_ctor_get(v_lakeConfig_4006_, 3);
v___x_4027_ = 4;
v___x_4028_ = l_Lake_JobAction_merge(v_action_4002_, v___x_4027_);
v___x_4029_ = lean_box(0);
v___x_4030_ = l_Lean_Name_str___override(v___x_4029_, v_val_4025_);
v___x_4031_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_cacheServices_4026_, v___x_4030_);
lean_dec(v___x_4030_);
if (lean_obj_tag(v___x_4031_) == 1)
{
lean_dec(v_val_4025_);
if (lean_obj_tag(v_scope_x3f_3983_) == 1)
{
lean_object* v_val_4032_; lean_object* v_val_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; uint8_t v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; 
v_val_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_val_4032_);
lean_dec_ref(v___x_4031_);
v_val_4033_ = lean_ctor_get(v_scope_x3f_3983_, 0);
lean_inc(v_val_4033_);
lean_dec_ref(v_scope_x3f_3983_);
v___x_4034_ = l_Lake_CacheService_artifactUrl(v_hash_4008_, v_val_4032_, v_val_4033_);
v___x_4035_ = ((lean_object*)(l_Lake_resolveArtifact___closed__0));
v___x_4036_ = l_Lake_lowerHexUInt64(v_hash_4008_);
v___x_4037_ = lean_string_append(v___x_4035_, v___x_4036_);
lean_dec_ref(v___x_4036_);
v___x_4038_ = ((lean_object*)(l_Lake_resolveArtifact___closed__1));
v___x_4039_ = lean_string_append(v___x_4037_, v___x_4038_);
v___x_4040_ = lean_string_append(v___x_4039_, v___x_4014_);
v___x_4041_ = ((lean_object*)(l_Lake_resolveArtifact___closed__2));
v___x_4042_ = lean_string_append(v___x_4040_, v___x_4041_);
v___x_4043_ = lean_string_append(v___x_4042_, v___x_4034_);
v___x_4044_ = 0;
v___x_4045_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4045_, 0, v___x_4043_);
lean_ctor_set_uint8(v___x_4045_, sizeof(void*)*1, v___x_4044_);
v___x_4046_ = lean_array_push(v_log_4001_, v___x_4045_);
lean_inc_ref(v___x_4014_);
v___x_4047_ = l_Lake_downloadArtifactCore(v_hash_4008_, v___x_4034_, v___x_4014_, v___x_4046_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v_a_4048_; uint8_t v___x_4049_; uint8_t v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
v_a_4048_ = lean_ctor_get(v___x_4047_, 1);
lean_inc(v_a_4048_);
lean_dec_ref(v___x_4047_);
v___x_4049_ = 1;
v___x_4050_ = 0;
v___x_4051_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4051_, 0, v___x_4049_);
lean_ctor_set_uint8(v___x_4051_, 1, v___x_4050_);
lean_ctor_set_uint8(v___x_4051_, 2, v_exe_3984_);
lean_inc_ref_n(v___x_4051_, 2);
v___x_4052_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4051_);
lean_ctor_set(v___x_4052_, 1, v___x_4051_);
lean_ctor_set(v___x_4052_, 2, v___x_4051_);
v___x_4053_ = l_IO_setAccessRights(v___x_4014_, v___x_4052_);
lean_dec_ref(v___x_4052_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v___x_4055_; 
lean_dec_ref(v___x_4053_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v_a_4048_);
v___x_4055_ = v___x_4021_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_a_4048_);
lean_ctor_set(v_reuseFailAlloc_4058_, 1, v_trace_4004_);
lean_ctor_set(v_reuseFailAlloc_4058_, 2, v_buildTime_4005_);
lean_ctor_set_uint8(v_reuseFailAlloc_4058_, sizeof(void*)*3 + 1, v_wantsRebuild_4003_);
v___x_4055_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
lean_object* v___x_4056_; lean_object* v___x_4057_; 
lean_ctor_set_uint8(v___x_4055_, sizeof(void*)*3, v___x_4028_);
v___x_4056_ = lean_box(0);
v___x_4057_ = l_Lake_resolveArtifact___lam__1(v___x_4014_, v___f_4015_, v___x_4056_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_, v___x_4055_);
lean_dec_ref(v___x_4014_);
v___y_3997_ = v___x_4024_;
v___y_3998_ = v___x_4057_;
goto v___jp_3996_;
}
}
else
{
lean_object* v_a_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; uint8_t v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4068_; 
v_a_4059_ = lean_ctor_get(v___x_4053_, 0);
lean_inc(v_a_4059_);
lean_dec_ref(v___x_4053_);
v___x_4060_ = ((lean_object*)(l_Lake_resolveArtifact___closed__3));
v___x_4061_ = lean_io_error_to_string(v_a_4059_);
v___x_4062_ = lean_string_append(v___x_4060_, v___x_4061_);
lean_dec_ref(v___x_4061_);
v___x_4063_ = 2;
v___x_4064_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4064_, 0, v___x_4062_);
lean_ctor_set_uint8(v___x_4064_, sizeof(void*)*1, v___x_4063_);
v___x_4065_ = lean_box(0);
v___x_4066_ = lean_array_push(v_a_4048_, v___x_4064_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v___x_4066_);
v___x_4068_ = v___x_4021_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v___x_4066_);
lean_ctor_set(v_reuseFailAlloc_4070_, 1, v_trace_4004_);
lean_ctor_set(v_reuseFailAlloc_4070_, 2, v_buildTime_4005_);
lean_ctor_set_uint8(v_reuseFailAlloc_4070_, sizeof(void*)*3 + 1, v_wantsRebuild_4003_);
v___x_4068_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
lean_object* v___x_4069_; 
lean_ctor_set_uint8(v___x_4068_, sizeof(void*)*3, v___x_4028_);
v___x_4069_ = l_Lake_resolveArtifact___lam__1(v___x_4014_, v___f_4015_, v___x_4065_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_, v___x_4068_);
lean_dec_ref(v___x_4014_);
v___y_3997_ = v___x_4024_;
v___y_3998_ = v___x_4069_;
goto v___jp_3996_;
}
}
}
else
{
lean_object* v_a_4071_; lean_object* v___x_4073_; 
lean_dec_ref(v___f_4015_);
lean_dec_ref(v___x_4014_);
lean_dec_ref(v_a_3985_);
v_a_4071_ = lean_ctor_get(v___x_4047_, 1);
lean_inc(v_a_4071_);
lean_dec_ref(v___x_4047_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v_a_4071_);
v___x_4073_ = v___x_4021_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_a_4071_);
lean_ctor_set(v_reuseFailAlloc_4074_, 1, v_trace_4004_);
lean_ctor_set(v_reuseFailAlloc_4074_, 2, v_buildTime_4005_);
lean_ctor_set_uint8(v_reuseFailAlloc_4074_, sizeof(void*)*3 + 1, v_wantsRebuild_4003_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
lean_ctor_set_uint8(v___x_4073_, sizeof(void*)*3, v___x_4028_);
v___y_3993_ = v___x_4024_;
v_a_3994_ = v___x_4073_;
goto v___jp_3992_;
}
}
}
else
{
lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4078_; 
lean_dec_ref(v___x_4031_);
lean_dec_ref(v___f_4015_);
lean_dec_ref(v___x_4014_);
lean_dec_ref(v_a_3985_);
lean_dec(v_scope_x3f_3983_);
v___x_4075_ = ((lean_object*)(l_Lake_resolveArtifact___closed__5));
v___x_4076_ = lean_array_push(v_log_4001_, v___x_4075_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v___x_4076_);
v___x_4078_ = v___x_4021_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v___x_4076_);
lean_ctor_set(v_reuseFailAlloc_4079_, 1, v_trace_4004_);
lean_ctor_set(v_reuseFailAlloc_4079_, 2, v_buildTime_4005_);
lean_ctor_set_uint8(v_reuseFailAlloc_4079_, sizeof(void*)*3 + 1, v_wantsRebuild_4003_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
lean_ctor_set_uint8(v___x_4078_, sizeof(void*)*3, v___x_4028_);
v___y_3993_ = v___x_4024_;
v_a_3994_ = v___x_4078_;
goto v___jp_3992_;
}
}
}
else
{
lean_object* v___x_4080_; lean_object* v___x_4081_; uint8_t v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4086_; 
lean_dec(v___x_4031_);
lean_dec_ref(v___f_4015_);
lean_dec_ref(v___x_4014_);
lean_dec_ref(v_a_3985_);
lean_dec(v_scope_x3f_3983_);
v___x_4080_ = ((lean_object*)(l_Lake_resolveArtifact___closed__6));
v___x_4081_ = lean_string_append(v___x_4080_, v_val_4025_);
lean_dec(v_val_4025_);
v___x_4082_ = 3;
v___x_4083_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4083_, 0, v___x_4081_);
lean_ctor_set_uint8(v___x_4083_, sizeof(void*)*1, v___x_4082_);
v___x_4084_ = lean_array_push(v_log_4001_, v___x_4083_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v___x_4084_);
v___x_4086_ = v___x_4021_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v___x_4084_);
lean_ctor_set(v_reuseFailAlloc_4087_, 1, v_trace_4004_);
lean_ctor_set(v_reuseFailAlloc_4087_, 2, v_buildTime_4005_);
lean_ctor_set_uint8(v_reuseFailAlloc_4087_, sizeof(void*)*3 + 1, v_wantsRebuild_4003_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
lean_ctor_set_uint8(v___x_4086_, sizeof(void*)*3, v___x_4028_);
v___y_3993_ = v___x_4024_;
v_a_3994_ = v___x_4086_;
goto v___jp_3992_;
}
}
}
else
{
lean_object* v___x_4088_; lean_object* v___x_4089_; uint8_t v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4094_; 
lean_dec_ref(v___f_4015_);
lean_dec_ref(v_a_3985_);
lean_dec(v_scope_x3f_3983_);
lean_dec(v_service_x3f_3982_);
v___x_4088_ = ((lean_object*)(l_Lake_resolveArtifact___closed__7));
v___x_4089_ = lean_string_append(v___x_4088_, v___x_4014_);
lean_dec_ref(v___x_4014_);
v___x_4090_ = 3;
v___x_4091_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4091_, 0, v___x_4089_);
lean_ctor_set_uint8(v___x_4091_, sizeof(void*)*1, v___x_4090_);
v___x_4092_ = lean_array_push(v_log_4001_, v___x_4091_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v___x_4092_);
v___x_4094_ = v___x_4021_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v___x_4092_);
lean_ctor_set(v_reuseFailAlloc_4095_, 1, v_trace_4004_);
lean_ctor_set(v_reuseFailAlloc_4095_, 2, v_buildTime_4005_);
lean_ctor_set_uint8(v_reuseFailAlloc_4095_, sizeof(void*)*3, v_action_4002_);
lean_ctor_set_uint8(v_reuseFailAlloc_4095_, sizeof(void*)*3 + 1, v_wantsRebuild_4003_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
v___y_3993_ = v___x_4024_;
v_a_3994_ = v___x_4094_;
goto v___jp_3992_;
}
}
}
else
{
lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; uint8_t v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4104_; 
lean_dec_ref(v___f_4015_);
lean_dec_ref(v___x_4014_);
lean_dec_ref(v_a_3985_);
lean_dec(v_scope_x3f_3983_);
lean_dec(v_service_x3f_3982_);
v___x_4096_ = ((lean_object*)(l_Lake_resolveArtifact___closed__8));
v___x_4097_ = lean_io_error_to_string(v_a_4023_);
v___x_4098_ = lean_string_append(v___x_4096_, v___x_4097_);
lean_dec_ref(v___x_4097_);
v___x_4099_ = 3;
v___x_4100_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4100_, 0, v___x_4098_);
lean_ctor_set_uint8(v___x_4100_, sizeof(void*)*1, v___x_4099_);
v___x_4101_ = lean_array_get_size(v_log_4001_);
v___x_4102_ = lean_array_push(v_log_4001_, v___x_4100_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v___x_4102_);
v___x_4104_ = v___x_4021_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v___x_4102_);
lean_ctor_set(v_reuseFailAlloc_4106_, 1, v_trace_4004_);
lean_ctor_set(v_reuseFailAlloc_4106_, 2, v_buildTime_4005_);
lean_ctor_set_uint8(v_reuseFailAlloc_4106_, sizeof(void*)*3, v_action_4002_);
lean_ctor_set_uint8(v_reuseFailAlloc_4106_, sizeof(void*)*3 + 1, v_wantsRebuild_4003_);
v___x_4104_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
lean_object* v___x_4105_; 
v___x_4105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4105_, 0, v___x_4101_);
lean_ctor_set(v___x_4105_, 1, v___x_4104_);
return v___x_4105_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___boxed(lean_object* v_descr_4119_, lean_object* v_service_x3f_4120_, lean_object* v_scope_x3f_4121_, lean_object* v_exe_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_){
_start:
{
uint8_t v_exe_boxed_4130_; lean_object* v_res_4131_; 
v_exe_boxed_4130_ = lean_unbox(v_exe_4122_);
v_res_4131_ = l_Lake_resolveArtifact(v_descr_4119_, v_service_x3f_4120_, v_scope_x3f_4121_, v_exe_boxed_4130_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_);
lean_dec_ref(v_a_4127_);
lean_dec(v_a_4126_);
lean_dec(v_a_4125_);
lean_dec(v_a_4124_);
return v_res_4131_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput(lean_object* v_out_4134_, uint8_t v_exe_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_){
_start:
{
lean_object* v_data_4143_; lean_object* v_service_x3f_4144_; lean_object* v_scope_x3f_4145_; lean_object* v___x_4146_; 
v_data_4143_ = lean_ctor_get(v_out_4134_, 0);
lean_inc_n(v_data_4143_, 2);
v_service_x3f_4144_ = lean_ctor_get(v_out_4134_, 1);
lean_inc(v_service_x3f_4144_);
v_scope_x3f_4145_ = lean_ctor_get(v_out_4134_, 2);
lean_inc(v_scope_x3f_4145_);
lean_dec_ref(v_out_4134_);
v___x_4146_ = l_Lake_ArtifactDescr_fromJson_x3f(v_data_4143_);
if (lean_obj_tag(v___x_4146_) == 0)
{
lean_object* v_a_4147_; lean_object* v_log_4148_; uint8_t v_action_4149_; uint8_t v_wantsRebuild_4150_; lean_object* v_trace_4151_; lean_object* v_buildTime_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4174_; 
lean_dec(v_scope_x3f_4145_);
lean_dec(v_service_x3f_4144_);
lean_dec_ref(v_a_4136_);
v_a_4147_ = lean_ctor_get(v___x_4146_, 0);
lean_inc(v_a_4147_);
lean_dec_ref(v___x_4146_);
v_log_4148_ = lean_ctor_get(v_a_4141_, 0);
v_action_4149_ = lean_ctor_get_uint8(v_a_4141_, sizeof(void*)*3);
v_wantsRebuild_4150_ = lean_ctor_get_uint8(v_a_4141_, sizeof(void*)*3 + 1);
v_trace_4151_ = lean_ctor_get(v_a_4141_, 1);
v_buildTime_4152_ = lean_ctor_get(v_a_4141_, 2);
v_isSharedCheck_4174_ = !lean_is_exclusive(v_a_4141_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4154_ = v_a_4141_;
v_isShared_4155_ = v_isSharedCheck_4174_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_buildTime_4152_);
lean_inc(v_trace_4151_);
lean_inc(v_log_4148_);
lean_dec(v_a_4141_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4174_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; uint8_t v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4171_; 
v___x_4156_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__0));
v___x_4157_ = l_Lean_Json_render(v_data_4143_);
v___x_4158_ = lean_unsigned_to_nat(80u);
v___x_4159_ = lean_unsigned_to_nat(2u);
v___x_4160_ = lean_unsigned_to_nat(0u);
v___x_4161_ = l_Std_Format_pretty(v___x_4157_, v___x_4158_, v___x_4159_, v___x_4160_);
v___x_4162_ = lean_string_append(v___x_4156_, v___x_4161_);
lean_dec_ref(v___x_4161_);
v___x_4163_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__1));
v___x_4164_ = lean_string_append(v___x_4162_, v___x_4163_);
v___x_4165_ = lean_string_append(v___x_4164_, v_a_4147_);
lean_dec(v_a_4147_);
v___x_4166_ = 3;
v___x_4167_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4167_, 0, v___x_4165_);
lean_ctor_set_uint8(v___x_4167_, sizeof(void*)*1, v___x_4166_);
v___x_4168_ = lean_array_get_size(v_log_4148_);
v___x_4169_ = lean_array_push(v_log_4148_, v___x_4167_);
if (v_isShared_4155_ == 0)
{
lean_ctor_set(v___x_4154_, 0, v___x_4169_);
v___x_4171_ = v___x_4154_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v___x_4169_);
lean_ctor_set(v_reuseFailAlloc_4173_, 1, v_trace_4151_);
lean_ctor_set(v_reuseFailAlloc_4173_, 2, v_buildTime_4152_);
lean_ctor_set_uint8(v_reuseFailAlloc_4173_, sizeof(void*)*3, v_action_4149_);
lean_ctor_set_uint8(v_reuseFailAlloc_4173_, sizeof(void*)*3 + 1, v_wantsRebuild_4150_);
v___x_4171_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
lean_object* v___x_4172_; 
v___x_4172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4168_);
lean_ctor_set(v___x_4172_, 1, v___x_4171_);
return v___x_4172_;
}
}
}
else
{
lean_object* v_a_4175_; lean_object* v___x_4176_; 
lean_dec(v_data_4143_);
v_a_4175_ = lean_ctor_get(v___x_4146_, 0);
lean_inc(v_a_4175_);
lean_dec_ref(v___x_4146_);
v___x_4176_ = l_Lake_resolveArtifact(v_a_4175_, v_service_x3f_4144_, v_scope_x3f_4145_, v_exe_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_);
return v___x_4176_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput___boxed(lean_object* v_out_4177_, lean_object* v_exe_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_){
_start:
{
uint8_t v_exe_boxed_4186_; lean_object* v_res_4187_; 
v_exe_boxed_4186_ = lean_unbox(v_exe_4178_);
v_res_4187_ = l_Lake_resolveArtifactOutput(v_out_4177_, v_exe_boxed_4186_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_);
lean_dec_ref(v_a_4183_);
lean_dec(v_a_4182_);
lean_dec(v_a_4181_);
lean_dec(v_a_4180_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(uint8_t v_exe_4188_, lean_object* v_out_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_){
_start:
{
lean_object* v___x_4197_; 
v___x_4197_ = l_Lake_resolveArtifactOutput(v_out_4189_, v_exe_4188_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed(lean_object* v_exe_4198_, lean_object* v_out_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
uint8_t v_exe_boxed_4207_; lean_object* v_res_4208_; 
v_exe_boxed_4207_ = lean_unbox(v_exe_4198_);
v_res_4208_ = l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(v_exe_boxed_4207_, v_out_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec(v___y_4203_);
lean_dec(v___y_4202_);
lean_dec(v___y_4201_);
return v_res_4208_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(uint8_t v_exe_4209_){
_start:
{
lean_object* v___x_4210_; lean_object* v___f_4211_; 
v___x_4210_ = lean_box(v_exe_4209_);
v___f_4211_ = lean_alloc_closure((void*)(l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4211_, 0, v___x_4210_);
return v___f_4211_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___boxed(lean_object* v_exe_4212_){
_start:
{
uint8_t v_exe_boxed_4213_; lean_object* v_res_4214_; 
v_exe_boxed_4213_ = lean_unbox(v_exe_4212_);
v_res_4214_ = l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(v_exe_boxed_4213_);
return v_res_4214_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg(lean_object* v_path_4215_, lean_object* v_ext_4216_, uint8_t v_text_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_){
_start:
{
lean_object* v___x_4221_; 
lean_inc_ref(v_path_4215_);
v___x_4221_ = l_Lake_fetchFileHash___redArg(v_path_4215_, v_text_4217_, v_a_4218_, v_a_4219_);
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_object* v_a_4222_; lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4240_; 
v_a_4222_ = lean_ctor_get(v___x_4221_, 0);
v_a_4223_ = lean_ctor_get(v___x_4221_, 1);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4225_ = v___x_4221_;
v_isShared_4226_ = v_isSharedCheck_4240_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_inc(v_a_4222_);
lean_dec(v___x_4221_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4240_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___x_4236_; 
v___x_4236_ = lean_io_metadata(v_path_4215_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v_a_4237_; lean_object* v_modified_4238_; 
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_a_4237_);
lean_dec_ref(v___x_4236_);
v_modified_4238_ = lean_ctor_get(v_a_4237_, 1);
lean_inc_ref(v_modified_4238_);
lean_dec(v_a_4237_);
v___y_4228_ = v_a_4223_;
v___y_4229_ = v_modified_4238_;
goto v___jp_4227_;
}
else
{
lean_object* v___x_4239_; 
lean_dec_ref(v___x_4236_);
v___x_4239_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___y_4228_ = v_a_4223_;
v___y_4229_ = v___x_4239_;
goto v___jp_4227_;
}
v___jp_4227_:
{
lean_object* v___x_4230_; uint64_t v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4234_; 
v___x_4230_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4230_, 0, v_ext_4216_);
v___x_4231_ = lean_unbox_uint64(v_a_4222_);
lean_dec(v_a_4222_);
lean_ctor_set_uint64(v___x_4230_, sizeof(void*)*1, v___x_4231_);
lean_inc_ref(v_path_4215_);
v___x_4232_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4230_);
lean_ctor_set(v___x_4232_, 1, v_path_4215_);
lean_ctor_set(v___x_4232_, 2, v_path_4215_);
lean_ctor_set(v___x_4232_, 3, v___y_4229_);
if (v_isShared_4226_ == 0)
{
lean_ctor_set(v___x_4225_, 1, v___y_4228_);
lean_ctor_set(v___x_4225_, 0, v___x_4232_);
v___x_4234_ = v___x_4225_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v___x_4232_);
lean_ctor_set(v_reuseFailAlloc_4235_, 1, v___y_4228_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
else
{
lean_object* v_a_4241_; lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4249_; 
lean_dec_ref(v_ext_4216_);
lean_dec_ref(v_path_4215_);
v_a_4241_ = lean_ctor_get(v___x_4221_, 0);
v_a_4242_ = lean_ctor_get(v___x_4221_, 1);
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4244_ = v___x_4221_;
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_inc(v_a_4241_);
lean_dec(v___x_4221_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4247_; 
if (v_isShared_4245_ == 0)
{
v___x_4247_ = v___x_4244_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_a_4241_);
lean_ctor_set(v_reuseFailAlloc_4248_, 1, v_a_4242_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg___boxed(lean_object* v_path_4250_, lean_object* v_ext_4251_, lean_object* v_text_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_){
_start:
{
uint8_t v_text_boxed_4256_; lean_object* v_res_4257_; 
v_text_boxed_4256_ = lean_unbox(v_text_4252_);
v_res_4257_ = l_Lake_computeArtifact___redArg(v_path_4250_, v_ext_4251_, v_text_boxed_4256_, v_a_4253_, v_a_4254_);
lean_dec_ref(v_a_4253_);
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact(lean_object* v_path_4258_, lean_object* v_ext_4259_, uint8_t v_text_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_){
_start:
{
lean_object* v___x_4268_; 
v___x_4268_ = l_Lake_computeArtifact___redArg(v_path_4258_, v_ext_4259_, v_text_4260_, v_a_4265_, v_a_4266_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___boxed(lean_object* v_path_4269_, lean_object* v_ext_4270_, lean_object* v_text_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_){
_start:
{
uint8_t v_text_boxed_4279_; lean_object* v_res_4280_; 
v_text_boxed_4279_ = lean_unbox(v_text_4271_);
v_res_4280_ = l_Lake_computeArtifact(v_path_4269_, v_ext_4270_, v_text_boxed_4279_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_, v_a_4277_);
lean_dec_ref(v_a_4276_);
lean_dec(v_a_4275_);
lean_dec(v_a_4274_);
lean_dec(v_a_4273_);
lean_dec_ref(v_a_4272_);
return v_res_4280_;
}
}
LEAN_EXPORT lean_object* l_Lake_restoreArtifact(lean_object* v_file_4284_, lean_object* v_art_4285_, uint8_t v_exe_4286_, lean_object* v_a_4287_){
_start:
{
lean_object* v___y_4290_; uint8_t v___x_4303_; 
v___x_4303_ = l_System_FilePath_pathExists(v_file_4284_);
if (v___x_4303_ == 0)
{
lean_object* v_descr_4304_; lean_object* v_path_4305_; lean_object* v___y_4307_; lean_object* v___x_4322_; lean_object* v___x_4323_; uint8_t v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; 
v_descr_4304_ = lean_ctor_get(v_art_4285_, 0);
v_path_4305_ = lean_ctor_get(v_art_4285_, 1);
v___x_4322_ = ((lean_object*)(l_Lake_restoreArtifact___closed__1));
v___x_4323_ = lean_string_append(v___x_4322_, v_path_4305_);
v___x_4324_ = 0;
v___x_4325_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4325_, 0, v___x_4323_);
lean_ctor_set_uint8(v___x_4325_, sizeof(void*)*1, v___x_4324_);
v___x_4326_ = lean_array_push(v_a_4287_, v___x_4325_);
lean_inc_ref(v_file_4284_);
v___x_4327_ = l_Lake_createParentDirs(v_file_4284_);
if (lean_obj_tag(v___x_4327_) == 0)
{
lean_object* v___x_4328_; 
lean_dec_ref(v___x_4327_);
v___x_4328_ = lean_io_hard_link(v_path_4305_, v_file_4284_);
if (lean_obj_tag(v___x_4328_) == 0)
{
lean_dec_ref(v___x_4328_);
v___y_4307_ = v___x_4326_;
goto v___jp_4306_;
}
else
{
lean_object* v_a_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; 
v_a_4329_ = lean_ctor_get(v___x_4328_, 0);
lean_inc(v_a_4329_);
lean_dec_ref(v___x_4328_);
v___x_4330_ = ((lean_object*)(l_Lake_restoreArtifact___closed__2));
v___x_4331_ = lean_io_error_to_string(v_a_4329_);
v___x_4332_ = lean_string_append(v___x_4330_, v___x_4331_);
lean_dec_ref(v___x_4331_);
v___x_4333_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4333_, 0, v___x_4332_);
lean_ctor_set_uint8(v___x_4333_, sizeof(void*)*1, v___x_4324_);
v___x_4334_ = lean_array_push(v___x_4326_, v___x_4333_);
v___x_4335_ = l_Lake_copyFile(v_path_4305_, v_file_4284_);
if (lean_obj_tag(v___x_4335_) == 0)
{
uint8_t v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; 
lean_dec_ref(v___x_4335_);
v___x_4336_ = 1;
v___x_4337_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4337_, 0, v___x_4336_);
lean_ctor_set_uint8(v___x_4337_, 1, v___x_4303_);
lean_ctor_set_uint8(v___x_4337_, 2, v_exe_4286_);
lean_inc_ref_n(v___x_4337_, 2);
v___x_4338_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4337_);
lean_ctor_set(v___x_4338_, 1, v___x_4337_);
lean_ctor_set(v___x_4338_, 2, v___x_4337_);
v___x_4339_ = l_IO_setAccessRights(v_file_4284_, v___x_4338_);
lean_dec_ref(v___x_4338_);
if (lean_obj_tag(v___x_4339_) == 0)
{
lean_dec_ref(v___x_4339_);
v___y_4307_ = v___x_4334_;
goto v___jp_4306_;
}
else
{
lean_object* v_a_4340_; lean_object* v___x_4341_; uint8_t v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
lean_dec_ref(v_art_4285_);
lean_dec_ref(v_file_4284_);
v_a_4340_ = lean_ctor_get(v___x_4339_, 0);
lean_inc(v_a_4340_);
lean_dec_ref(v___x_4339_);
v___x_4341_ = lean_io_error_to_string(v_a_4340_);
v___x_4342_ = 3;
v___x_4343_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4343_, 0, v___x_4341_);
lean_ctor_set_uint8(v___x_4343_, sizeof(void*)*1, v___x_4342_);
v___x_4344_ = lean_array_get_size(v___x_4334_);
v___x_4345_ = lean_array_push(v___x_4334_, v___x_4343_);
v___x_4346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4346_, 0, v___x_4344_);
lean_ctor_set(v___x_4346_, 1, v___x_4345_);
return v___x_4346_;
}
}
else
{
lean_object* v_a_4347_; lean_object* v___x_4348_; uint8_t v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; 
lean_dec_ref(v_art_4285_);
lean_dec_ref(v_file_4284_);
v_a_4347_ = lean_ctor_get(v___x_4335_, 0);
lean_inc(v_a_4347_);
lean_dec_ref(v___x_4335_);
v___x_4348_ = lean_io_error_to_string(v_a_4347_);
v___x_4349_ = 3;
v___x_4350_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4350_, 0, v___x_4348_);
lean_ctor_set_uint8(v___x_4350_, sizeof(void*)*1, v___x_4349_);
v___x_4351_ = lean_array_get_size(v___x_4334_);
v___x_4352_ = lean_array_push(v___x_4334_, v___x_4350_);
v___x_4353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4353_, 0, v___x_4351_);
lean_ctor_set(v___x_4353_, 1, v___x_4352_);
return v___x_4353_;
}
}
}
else
{
lean_object* v_a_4354_; lean_object* v___x_4355_; uint8_t v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
lean_dec_ref(v_art_4285_);
lean_dec_ref(v_file_4284_);
v_a_4354_ = lean_ctor_get(v___x_4327_, 0);
lean_inc(v_a_4354_);
lean_dec_ref(v___x_4327_);
v___x_4355_ = lean_io_error_to_string(v_a_4354_);
v___x_4356_ = 3;
v___x_4357_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4357_, 0, v___x_4355_);
lean_ctor_set_uint8(v___x_4357_, sizeof(void*)*1, v___x_4356_);
v___x_4358_ = lean_array_get_size(v___x_4326_);
v___x_4359_ = lean_array_push(v___x_4326_, v___x_4357_);
v___x_4360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4360_, 0, v___x_4358_);
lean_ctor_set(v___x_4360_, 1, v___x_4359_);
return v___x_4360_;
}
v___jp_4306_:
{
uint64_t v_hash_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; uint8_t v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
v_hash_4308_ = lean_ctor_get_uint64(v_descr_4304_, sizeof(void*)*1);
v___x_4309_ = ((lean_object*)(l_Lake_restoreArtifact___closed__0));
v___x_4310_ = lean_string_append(v___x_4309_, v_file_4284_);
v___x_4311_ = 0;
v___x_4312_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4312_, 0, v___x_4310_);
lean_ctor_set_uint8(v___x_4312_, sizeof(void*)*1, v___x_4311_);
v___x_4313_ = lean_array_push(v___y_4307_, v___x_4312_);
lean_inc_ref(v_file_4284_);
v___x_4314_ = l_Lake_writeFileHash(v_file_4284_, v_hash_4308_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_dec_ref(v___x_4314_);
v___y_4290_ = v___x_4313_;
goto v___jp_4289_;
}
else
{
lean_object* v_a_4315_; lean_object* v___x_4316_; uint8_t v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; 
lean_dec_ref(v_art_4285_);
lean_dec_ref(v_file_4284_);
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
lean_inc(v_a_4315_);
lean_dec_ref(v___x_4314_);
v___x_4316_ = lean_io_error_to_string(v_a_4315_);
v___x_4317_ = 3;
v___x_4318_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4318_, 0, v___x_4316_);
lean_ctor_set_uint8(v___x_4318_, sizeof(void*)*1, v___x_4317_);
v___x_4319_ = lean_array_get_size(v___x_4313_);
v___x_4320_ = lean_array_push(v___x_4313_, v___x_4318_);
v___x_4321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4321_, 0, v___x_4319_);
lean_ctor_set(v___x_4321_, 1, v___x_4320_);
return v___x_4321_;
}
}
}
else
{
v___y_4290_ = v_a_4287_;
goto v___jp_4289_;
}
v___jp_4289_:
{
lean_object* v_descr_4291_; lean_object* v_mtime_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4300_; 
v_descr_4291_ = lean_ctor_get(v_art_4285_, 0);
v_mtime_4292_ = lean_ctor_get(v_art_4285_, 3);
v_isSharedCheck_4300_ = !lean_is_exclusive(v_art_4285_);
if (v_isSharedCheck_4300_ == 0)
{
lean_object* v_unused_4301_; lean_object* v_unused_4302_; 
v_unused_4301_ = lean_ctor_get(v_art_4285_, 2);
lean_dec(v_unused_4301_);
v_unused_4302_ = lean_ctor_get(v_art_4285_, 1);
lean_dec(v_unused_4302_);
v___x_4294_ = v_art_4285_;
v_isShared_4295_ = v_isSharedCheck_4300_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_mtime_4292_);
lean_inc(v_descr_4291_);
lean_dec(v_art_4285_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4300_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4297_; 
lean_inc_ref(v_file_4284_);
if (v_isShared_4295_ == 0)
{
lean_ctor_set(v___x_4294_, 2, v_file_4284_);
lean_ctor_set(v___x_4294_, 1, v_file_4284_);
v___x_4297_ = v___x_4294_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_descr_4291_);
lean_ctor_set(v_reuseFailAlloc_4299_, 1, v_file_4284_);
lean_ctor_set(v_reuseFailAlloc_4299_, 2, v_file_4284_);
lean_ctor_set(v_reuseFailAlloc_4299_, 3, v_mtime_4292_);
v___x_4297_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
lean_object* v___x_4298_; 
v___x_4298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4297_);
lean_ctor_set(v___x_4298_, 1, v___y_4290_);
return v___x_4298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_restoreArtifact___boxed(lean_object* v_file_4361_, lean_object* v_art_4362_, lean_object* v_exe_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_){
_start:
{
uint8_t v_exe_boxed_4366_; lean_object* v_res_4367_; 
v_exe_boxed_4366_ = lean_unbox(v_exe_4363_);
v_res_4367_ = l_Lake_restoreArtifact(v_file_4361_, v_art_4362_, v_exe_boxed_4366_, v_a_4364_);
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(lean_object* v_val_4368_, lean_object* v_a_x3f_4369_, lean_object* v___y_4370_){
_start:
{
lean_object* v___x_4372_; lean_object* v_log_4373_; uint8_t v_action_4374_; uint8_t v_wantsRebuild_4375_; lean_object* v_trace_4376_; lean_object* v_buildTime_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4388_; 
v___x_4372_ = lean_io_mono_ms_now();
v_log_4373_ = lean_ctor_get(v___y_4370_, 0);
v_action_4374_ = lean_ctor_get_uint8(v___y_4370_, sizeof(void*)*3);
v_wantsRebuild_4375_ = lean_ctor_get_uint8(v___y_4370_, sizeof(void*)*3 + 1);
v_trace_4376_ = lean_ctor_get(v___y_4370_, 1);
v_buildTime_4377_ = lean_ctor_get(v___y_4370_, 2);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___y_4370_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4379_ = v___y_4370_;
v_isShared_4380_ = v_isSharedCheck_4388_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_buildTime_4377_);
lean_inc(v_trace_4376_);
lean_inc(v_log_4373_);
lean_dec(v___y_4370_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4388_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4385_; 
v___x_4381_ = lean_nat_sub(v___x_4372_, v_val_4368_);
lean_dec(v___x_4372_);
v___x_4382_ = lean_box(0);
v___x_4383_ = lean_nat_add(v_buildTime_4377_, v___x_4381_);
lean_dec(v___x_4381_);
lean_dec(v_buildTime_4377_);
if (v_isShared_4380_ == 0)
{
lean_ctor_set(v___x_4379_, 2, v___x_4383_);
v___x_4385_ = v___x_4379_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_log_4373_);
lean_ctor_set(v_reuseFailAlloc_4387_, 1, v_trace_4376_);
lean_ctor_set(v_reuseFailAlloc_4387_, 2, v___x_4383_);
lean_ctor_set_uint8(v_reuseFailAlloc_4387_, sizeof(void*)*3, v_action_4374_);
lean_ctor_set_uint8(v_reuseFailAlloc_4387_, sizeof(void*)*3 + 1, v_wantsRebuild_4375_);
v___x_4385_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
lean_object* v___x_4386_; 
v___x_4386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4386_, 0, v___x_4382_);
lean_ctor_set(v___x_4386_, 1, v___x_4385_);
return v___x_4386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0___boxed(lean_object* v_val_4389_, lean_object* v_a_x3f_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_){
_start:
{
lean_object* v_res_4393_; 
v_res_4393_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v_val_4389_, v_a_x3f_4390_, v___y_4391_);
lean_dec(v_a_x3f_4390_);
lean_dec(v_val_4389_);
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(lean_object* v_file_4394_, lean_object* v_build_4395_, lean_object* v_traceFile_4396_, lean_object* v_ext_4397_, uint8_t v_text_4398_, lean_object* v_a_4399_, lean_object* v_depTrace_4400_, lean_object* v_traceFile_4401_, uint8_t v_action_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_){
_start:
{
lean_object* v_a_4410_; lean_object* v_a_4411_; lean_object* v_log_4414_; uint8_t v_action_4415_; uint8_t v_wantsRebuild_4416_; lean_object* v_trace_4417_; lean_object* v_buildTime_4418_; lean_object* v_toBuildConfig_4424_; lean_object* v_log_4425_; uint8_t v_action_4426_; uint8_t v_wantsRebuild_4427_; lean_object* v_trace_4428_; lean_object* v_buildTime_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4608_; 
v_toBuildConfig_4424_ = lean_ctor_get(v_a_4406_, 0);
v_log_4425_ = lean_ctor_get(v_a_4407_, 0);
v_action_4426_ = lean_ctor_get_uint8(v_a_4407_, sizeof(void*)*3);
v_wantsRebuild_4427_ = lean_ctor_get_uint8(v_a_4407_, sizeof(void*)*3 + 1);
v_trace_4428_ = lean_ctor_get(v_a_4407_, 1);
v_buildTime_4429_ = lean_ctor_get(v_a_4407_, 2);
v_isSharedCheck_4608_ = !lean_is_exclusive(v_a_4407_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4431_ = v_a_4407_;
v_isShared_4432_ = v_isSharedCheck_4608_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_buildTime_4429_);
lean_inc(v_trace_4428_);
lean_inc(v_log_4425_);
lean_dec(v_a_4407_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4608_;
goto v_resetjp_4430_;
}
v___jp_4409_:
{
lean_object* v___x_4412_; 
v___x_4412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4412_, 0, v_a_4410_);
lean_ctor_set(v___x_4412_, 1, v_a_4411_);
return v___x_4412_;
}
v___jp_4413_:
{
lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
v___x_4419_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_4420_ = lean_array_get_size(v_log_4414_);
v___x_4421_ = lean_array_push(v_log_4414_, v___x_4419_);
v___x_4422_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4422_, 0, v___x_4421_);
lean_ctor_set(v___x_4422_, 1, v_trace_4417_);
lean_ctor_set(v___x_4422_, 2, v_buildTime_4418_);
lean_ctor_set_uint8(v___x_4422_, sizeof(void*)*3, v_action_4415_);
lean_ctor_set_uint8(v___x_4422_, sizeof(void*)*3 + 1, v_wantsRebuild_4416_);
v___x_4423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4423_, 0, v___x_4420_);
lean_ctor_set(v___x_4423_, 1, v___x_4422_);
return v___x_4423_;
}
v_resetjp_4430_:
{
uint8_t v_noBuild_4433_; uint8_t v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v_noBuild_4433_ = lean_ctor_get_uint8(v_toBuildConfig_4424_, sizeof(void*)*2 + 2);
v___x_4434_ = l_Lake_JobAction_merge(v_action_4426_, v_action_4402_);
v___x_4435_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_4401_);
v___x_4436_ = l_System_FilePath_addExtension(v_traceFile_4401_, v___x_4435_);
if (v_noBuild_4433_ == 0)
{
lean_object* v___x_4437_; lean_object* v_a_4439_; lean_object* v_a_4440_; lean_object* v___x_4444_; 
v___x_4437_ = lean_io_mono_ms_now();
v___x_4444_ = l_Lake_removeFileIfExists(v_file_4394_);
if (lean_obj_tag(v___x_4444_) == 0)
{
lean_object* v___x_4446_; 
lean_dec_ref(v___x_4444_);
lean_inc_ref(v_log_4425_);
if (v_isShared_4432_ == 0)
{
v___x_4446_ = v___x_4431_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_log_4425_);
lean_ctor_set(v_reuseFailAlloc_4583_, 1, v_trace_4428_);
lean_ctor_set(v_reuseFailAlloc_4583_, 2, v_buildTime_4429_);
lean_ctor_set_uint8(v_reuseFailAlloc_4583_, sizeof(void*)*3 + 1, v_wantsRebuild_4427_);
v___x_4446_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
lean_object* v___x_4447_; 
lean_ctor_set_uint8(v___x_4446_, sizeof(void*)*3, v___x_4434_);
lean_inc_ref(v_a_4406_);
lean_inc(v_a_4405_);
lean_inc(v_a_4404_);
lean_inc(v_a_4403_);
v___x_4447_ = lean_apply_7(v_build_4395_, v_a_4399_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_, v___x_4446_, lean_box(0));
if (lean_obj_tag(v___x_4447_) == 0)
{
lean_object* v_a_4448_; lean_object* v_log_4449_; uint8_t v_action_4450_; uint8_t v_wantsRebuild_4451_; lean_object* v_trace_4452_; lean_object* v_buildTime_4453_; lean_object* v___x_4454_; 
v_a_4448_ = lean_ctor_get(v___x_4447_, 1);
lean_inc(v_a_4448_);
lean_dec_ref(v___x_4447_);
v_log_4449_ = lean_ctor_get(v_a_4448_, 0);
v_action_4450_ = lean_ctor_get_uint8(v_a_4448_, sizeof(void*)*3);
v_wantsRebuild_4451_ = lean_ctor_get_uint8(v_a_4448_, sizeof(void*)*3 + 1);
v_trace_4452_ = lean_ctor_get(v_a_4448_, 1);
v_buildTime_4453_ = lean_ctor_get(v_a_4448_, 2);
lean_inc_ref(v_file_4394_);
v___x_4454_ = l_Lake_clearFileHash(v_file_4394_);
if (lean_obj_tag(v___x_4454_) == 0)
{
lean_object* v___x_4455_; 
lean_dec_ref(v___x_4454_);
v___x_4455_ = l_Lake_removeFileIfExists(v_traceFile_4396_);
if (lean_obj_tag(v___x_4455_) == 0)
{
lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4547_; 
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4547_ == 0)
{
lean_object* v_unused_4548_; 
v_unused_4548_ = lean_ctor_get(v___x_4455_, 0);
lean_dec(v_unused_4548_);
v___x_4457_ = v___x_4455_;
v_isShared_4458_ = v_isSharedCheck_4547_;
goto v_resetjp_4456_;
}
else
{
lean_dec(v___x_4455_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4547_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v___x_4459_; 
v___x_4459_ = l_Lake_computeArtifact___redArg(v_file_4394_, v_ext_4397_, v_text_4398_, v_a_4406_, v_a_4448_);
if (lean_obj_tag(v___x_4459_) == 0)
{
lean_object* v_a_4460_; lean_object* v_a_4461_; lean_object* v_descr_4462_; lean_object* v_log_4463_; uint8_t v_action_4464_; uint8_t v_wantsRebuild_4465_; lean_object* v_trace_4466_; lean_object* v_buildTime_4467_; uint64_t v_hash_4468_; lean_object* v_ext_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___y_4474_; lean_object* v___x_4537_; lean_object* v___x_4538_; uint8_t v___x_4539_; 
v_a_4460_ = lean_ctor_get(v___x_4459_, 1);
lean_inc(v_a_4460_);
v_a_4461_ = lean_ctor_get(v___x_4459_, 0);
lean_inc(v_a_4461_);
lean_dec_ref(v___x_4459_);
v_descr_4462_ = lean_ctor_get(v_a_4461_, 0);
v_log_4463_ = lean_ctor_get(v_a_4460_, 0);
v_action_4464_ = lean_ctor_get_uint8(v_a_4460_, sizeof(void*)*3);
v_wantsRebuild_4465_ = lean_ctor_get_uint8(v_a_4460_, sizeof(void*)*3 + 1);
v_trace_4466_ = lean_ctor_get(v_a_4460_, 1);
v_buildTime_4467_ = lean_ctor_get(v_a_4460_, 2);
v_hash_4468_ = lean_ctor_get_uint64(v_descr_4462_, sizeof(void*)*1);
v_ext_4469_ = lean_ctor_get(v_descr_4462_, 0);
v___x_4470_ = lean_array_get_size(v_log_4425_);
lean_dec_ref(v_log_4425_);
v___x_4471_ = lean_array_get_size(v_log_4463_);
v___x_4472_ = l_Array_extract___redArg(v_log_4463_, v___x_4470_, v___x_4471_);
v___x_4537_ = lean_string_utf8_byte_size(v_ext_4469_);
v___x_4538_ = lean_unsigned_to_nat(0u);
v___x_4539_ = lean_nat_dec_eq(v___x_4537_, v___x_4538_);
if (v___x_4539_ == 0)
{
lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
v___x_4540_ = l_Lake_lowerHexUInt64(v_hash_4468_);
v___x_4541_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_4542_ = lean_string_append(v___x_4540_, v___x_4541_);
v___x_4543_ = lean_string_append(v___x_4542_, v_ext_4469_);
v___y_4474_ = v___x_4543_;
goto v___jp_4473_;
}
else
{
lean_object* v___x_4544_; 
v___x_4544_ = l_Lake_lowerHexUInt64(v_hash_4468_);
v___y_4474_ = v___x_4544_;
goto v___jp_4473_;
}
v___jp_4473_:
{
lean_object* v___x_4476_; 
if (v_isShared_4458_ == 0)
{
lean_ctor_set_tag(v___x_4457_, 3);
lean_ctor_set(v___x_4457_, 0, v___y_4474_);
v___x_4476_ = v___x_4457_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v___y_4474_);
v___x_4476_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
lean_object* v___x_4477_; lean_object* v___x_4478_; 
v___x_4477_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_4400_, v___x_4476_, v___x_4472_);
v___x_4478_ = l_Lake_BuildMetadata_writeFile(v_traceFile_4401_, v___x_4477_);
if (lean_obj_tag(v___x_4478_) == 0)
{
lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4519_; 
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4478_);
if (v_isSharedCheck_4519_ == 0)
{
lean_object* v_unused_4520_; 
v_unused_4520_ = lean_ctor_get(v___x_4478_, 0);
lean_dec(v_unused_4520_);
v___x_4480_ = v___x_4478_;
v_isShared_4481_ = v_isSharedCheck_4519_;
goto v_resetjp_4479_;
}
else
{
lean_dec(v___x_4478_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4519_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4482_; 
v___x_4482_ = l_Lake_removeFileIfExists(v___x_4436_);
lean_dec_ref(v___x_4436_);
if (lean_obj_tag(v___x_4482_) == 0)
{
lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4502_; 
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4482_);
if (v_isSharedCheck_4502_ == 0)
{
lean_object* v_unused_4503_; 
v_unused_4503_ = lean_ctor_get(v___x_4482_, 0);
lean_dec(v_unused_4503_);
v___x_4484_ = v___x_4482_;
v_isShared_4485_ = v_isSharedCheck_4502_;
goto v_resetjp_4483_;
}
else
{
lean_dec(v___x_4482_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4502_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v___x_4487_; 
lean_inc(v_a_4461_);
if (v_isShared_4485_ == 0)
{
lean_ctor_set(v___x_4484_, 0, v_a_4461_);
v___x_4487_ = v___x_4484_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_a_4461_);
v___x_4487_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
lean_object* v___x_4489_; 
if (v_isShared_4481_ == 0)
{
lean_ctor_set_tag(v___x_4480_, 1);
lean_ctor_set(v___x_4480_, 0, v___x_4487_);
v___x_4489_ = v___x_4480_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v___x_4487_);
v___x_4489_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
lean_object* v___x_4490_; lean_object* v_a_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4498_; 
v___x_4490_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v___x_4437_, v___x_4489_, v_a_4460_);
lean_dec_ref(v___x_4489_);
lean_dec(v___x_4437_);
v_a_4491_ = lean_ctor_get(v___x_4490_, 1);
v_isSharedCheck_4498_ = !lean_is_exclusive(v___x_4490_);
if (v_isSharedCheck_4498_ == 0)
{
lean_object* v_unused_4499_; 
v_unused_4499_ = lean_ctor_get(v___x_4490_, 0);
lean_dec(v_unused_4499_);
v___x_4493_ = v___x_4490_;
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_a_4491_);
lean_dec(v___x_4490_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4496_; 
if (v_isShared_4494_ == 0)
{
lean_ctor_set(v___x_4493_, 0, v_a_4461_);
v___x_4496_ = v___x_4493_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_a_4461_);
lean_ctor_set(v_reuseFailAlloc_4497_, 1, v_a_4491_);
v___x_4496_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
return v___x_4496_;
}
}
}
}
}
}
else
{
lean_object* v___x_4505_; uint8_t v_isShared_4506_; uint8_t v_isSharedCheck_4515_; 
lean_inc(v_buildTime_4467_);
lean_inc_ref(v_trace_4466_);
lean_inc_ref(v_log_4463_);
lean_del_object(v___x_4480_);
lean_dec(v_a_4461_);
v_isSharedCheck_4515_ = !lean_is_exclusive(v_a_4460_);
if (v_isSharedCheck_4515_ == 0)
{
lean_object* v_unused_4516_; lean_object* v_unused_4517_; lean_object* v_unused_4518_; 
v_unused_4516_ = lean_ctor_get(v_a_4460_, 2);
lean_dec(v_unused_4516_);
v_unused_4517_ = lean_ctor_get(v_a_4460_, 1);
lean_dec(v_unused_4517_);
v_unused_4518_ = lean_ctor_get(v_a_4460_, 0);
lean_dec(v_unused_4518_);
v___x_4505_ = v_a_4460_;
v_isShared_4506_ = v_isSharedCheck_4515_;
goto v_resetjp_4504_;
}
else
{
lean_dec(v_a_4460_);
v___x_4505_ = lean_box(0);
v_isShared_4506_ = v_isSharedCheck_4515_;
goto v_resetjp_4504_;
}
v_resetjp_4504_:
{
lean_object* v_a_4507_; lean_object* v___x_4508_; uint8_t v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4513_; 
v_a_4507_ = lean_ctor_get(v___x_4482_, 0);
lean_inc(v_a_4507_);
lean_dec_ref(v___x_4482_);
v___x_4508_ = lean_io_error_to_string(v_a_4507_);
v___x_4509_ = 3;
v___x_4510_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4510_, 0, v___x_4508_);
lean_ctor_set_uint8(v___x_4510_, sizeof(void*)*1, v___x_4509_);
v___x_4511_ = lean_array_push(v_log_4463_, v___x_4510_);
if (v_isShared_4506_ == 0)
{
lean_ctor_set(v___x_4505_, 0, v___x_4511_);
v___x_4513_ = v___x_4505_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v___x_4511_);
lean_ctor_set(v_reuseFailAlloc_4514_, 1, v_trace_4466_);
lean_ctor_set(v_reuseFailAlloc_4514_, 2, v_buildTime_4467_);
lean_ctor_set_uint8(v_reuseFailAlloc_4514_, sizeof(void*)*3, v_action_4464_);
lean_ctor_set_uint8(v_reuseFailAlloc_4514_, sizeof(void*)*3 + 1, v_wantsRebuild_4465_);
v___x_4513_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
v_a_4439_ = v___x_4471_;
v_a_4440_ = v___x_4513_;
goto v___jp_4438_;
}
}
}
}
}
else
{
lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4532_; 
lean_inc(v_buildTime_4467_);
lean_inc_ref(v_trace_4466_);
lean_inc_ref(v_log_4463_);
lean_dec(v_a_4461_);
lean_dec_ref(v___x_4436_);
v_isSharedCheck_4532_ = !lean_is_exclusive(v_a_4460_);
if (v_isSharedCheck_4532_ == 0)
{
lean_object* v_unused_4533_; lean_object* v_unused_4534_; lean_object* v_unused_4535_; 
v_unused_4533_ = lean_ctor_get(v_a_4460_, 2);
lean_dec(v_unused_4533_);
v_unused_4534_ = lean_ctor_get(v_a_4460_, 1);
lean_dec(v_unused_4534_);
v_unused_4535_ = lean_ctor_get(v_a_4460_, 0);
lean_dec(v_unused_4535_);
v___x_4522_ = v_a_4460_;
v_isShared_4523_ = v_isSharedCheck_4532_;
goto v_resetjp_4521_;
}
else
{
lean_dec(v_a_4460_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4532_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v_a_4524_; lean_object* v___x_4525_; uint8_t v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4530_; 
v_a_4524_ = lean_ctor_get(v___x_4478_, 0);
lean_inc(v_a_4524_);
lean_dec_ref(v___x_4478_);
v___x_4525_ = lean_io_error_to_string(v_a_4524_);
v___x_4526_ = 3;
v___x_4527_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4527_, 0, v___x_4525_);
lean_ctor_set_uint8(v___x_4527_, sizeof(void*)*1, v___x_4526_);
v___x_4528_ = lean_array_push(v_log_4463_, v___x_4527_);
if (v_isShared_4523_ == 0)
{
lean_ctor_set(v___x_4522_, 0, v___x_4528_);
v___x_4530_ = v___x_4522_;
goto v_reusejp_4529_;
}
else
{
lean_object* v_reuseFailAlloc_4531_; 
v_reuseFailAlloc_4531_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4531_, 0, v___x_4528_);
lean_ctor_set(v_reuseFailAlloc_4531_, 1, v_trace_4466_);
lean_ctor_set(v_reuseFailAlloc_4531_, 2, v_buildTime_4467_);
lean_ctor_set_uint8(v_reuseFailAlloc_4531_, sizeof(void*)*3, v_action_4464_);
lean_ctor_set_uint8(v_reuseFailAlloc_4531_, sizeof(void*)*3 + 1, v_wantsRebuild_4465_);
v___x_4530_ = v_reuseFailAlloc_4531_;
goto v_reusejp_4529_;
}
v_reusejp_4529_:
{
v_a_4439_ = v___x_4471_;
v_a_4440_ = v___x_4530_;
goto v___jp_4438_;
}
}
}
}
}
}
else
{
lean_object* v_a_4545_; lean_object* v_a_4546_; 
lean_del_object(v___x_4457_);
lean_dec_ref(v___x_4436_);
lean_dec_ref(v_log_4425_);
lean_dec_ref(v_traceFile_4401_);
v_a_4545_ = lean_ctor_get(v___x_4459_, 0);
lean_inc(v_a_4545_);
v_a_4546_ = lean_ctor_get(v___x_4459_, 1);
lean_inc(v_a_4546_);
lean_dec_ref(v___x_4459_);
v_a_4439_ = v_a_4545_;
v_a_4440_ = v_a_4546_;
goto v___jp_4438_;
}
}
}
else
{
lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4561_; 
lean_inc(v_buildTime_4453_);
lean_inc_ref(v_trace_4452_);
lean_inc_ref(v_log_4449_);
lean_dec_ref(v___x_4436_);
lean_dec_ref(v_log_4425_);
lean_dec_ref(v_traceFile_4401_);
lean_dec_ref(v_ext_4397_);
lean_dec_ref(v_file_4394_);
v_isSharedCheck_4561_ = !lean_is_exclusive(v_a_4448_);
if (v_isSharedCheck_4561_ == 0)
{
lean_object* v_unused_4562_; lean_object* v_unused_4563_; lean_object* v_unused_4564_; 
v_unused_4562_ = lean_ctor_get(v_a_4448_, 2);
lean_dec(v_unused_4562_);
v_unused_4563_ = lean_ctor_get(v_a_4448_, 1);
lean_dec(v_unused_4563_);
v_unused_4564_ = lean_ctor_get(v_a_4448_, 0);
lean_dec(v_unused_4564_);
v___x_4550_ = v_a_4448_;
v_isShared_4551_ = v_isSharedCheck_4561_;
goto v_resetjp_4549_;
}
else
{
lean_dec(v_a_4448_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4561_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
lean_object* v_a_4552_; lean_object* v___x_4553_; uint8_t v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4559_; 
v_a_4552_ = lean_ctor_get(v___x_4455_, 0);
lean_inc(v_a_4552_);
lean_dec_ref(v___x_4455_);
v___x_4553_ = lean_io_error_to_string(v_a_4552_);
v___x_4554_ = 3;
v___x_4555_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4555_, 0, v___x_4553_);
lean_ctor_set_uint8(v___x_4555_, sizeof(void*)*1, v___x_4554_);
v___x_4556_ = lean_array_get_size(v_log_4449_);
v___x_4557_ = lean_array_push(v_log_4449_, v___x_4555_);
if (v_isShared_4551_ == 0)
{
lean_ctor_set(v___x_4550_, 0, v___x_4557_);
v___x_4559_ = v___x_4550_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v___x_4557_);
lean_ctor_set(v_reuseFailAlloc_4560_, 1, v_trace_4452_);
lean_ctor_set(v_reuseFailAlloc_4560_, 2, v_buildTime_4453_);
lean_ctor_set_uint8(v_reuseFailAlloc_4560_, sizeof(void*)*3, v_action_4450_);
lean_ctor_set_uint8(v_reuseFailAlloc_4560_, sizeof(void*)*3 + 1, v_wantsRebuild_4451_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
v_a_4439_ = v___x_4556_;
v_a_4440_ = v___x_4559_;
goto v___jp_4438_;
}
}
}
}
else
{
lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4577_; 
lean_inc(v_buildTime_4453_);
lean_inc_ref(v_trace_4452_);
lean_inc_ref(v_log_4449_);
lean_dec_ref(v___x_4436_);
lean_dec_ref(v_log_4425_);
lean_dec_ref(v_traceFile_4401_);
lean_dec_ref(v_ext_4397_);
lean_dec_ref(v_file_4394_);
v_isSharedCheck_4577_ = !lean_is_exclusive(v_a_4448_);
if (v_isSharedCheck_4577_ == 0)
{
lean_object* v_unused_4578_; lean_object* v_unused_4579_; lean_object* v_unused_4580_; 
v_unused_4578_ = lean_ctor_get(v_a_4448_, 2);
lean_dec(v_unused_4578_);
v_unused_4579_ = lean_ctor_get(v_a_4448_, 1);
lean_dec(v_unused_4579_);
v_unused_4580_ = lean_ctor_get(v_a_4448_, 0);
lean_dec(v_unused_4580_);
v___x_4566_ = v_a_4448_;
v_isShared_4567_ = v_isSharedCheck_4577_;
goto v_resetjp_4565_;
}
else
{
lean_dec(v_a_4448_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4577_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
lean_object* v_a_4568_; lean_object* v___x_4569_; uint8_t v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4575_; 
v_a_4568_ = lean_ctor_get(v___x_4454_, 0);
lean_inc(v_a_4568_);
lean_dec_ref(v___x_4454_);
v___x_4569_ = lean_io_error_to_string(v_a_4568_);
v___x_4570_ = 3;
v___x_4571_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4571_, 0, v___x_4569_);
lean_ctor_set_uint8(v___x_4571_, sizeof(void*)*1, v___x_4570_);
v___x_4572_ = lean_array_get_size(v_log_4449_);
v___x_4573_ = lean_array_push(v_log_4449_, v___x_4571_);
if (v_isShared_4567_ == 0)
{
lean_ctor_set(v___x_4566_, 0, v___x_4573_);
v___x_4575_ = v___x_4566_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v___x_4573_);
lean_ctor_set(v_reuseFailAlloc_4576_, 1, v_trace_4452_);
lean_ctor_set(v_reuseFailAlloc_4576_, 2, v_buildTime_4453_);
lean_ctor_set_uint8(v_reuseFailAlloc_4576_, sizeof(void*)*3, v_action_4450_);
lean_ctor_set_uint8(v_reuseFailAlloc_4576_, sizeof(void*)*3 + 1, v_wantsRebuild_4451_);
v___x_4575_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
v_a_4439_ = v___x_4572_;
v_a_4440_ = v___x_4575_;
goto v___jp_4438_;
}
}
}
}
else
{
lean_object* v_a_4581_; lean_object* v_a_4582_; 
lean_dec_ref(v___x_4436_);
lean_dec_ref(v_log_4425_);
lean_dec_ref(v_traceFile_4401_);
lean_dec_ref(v_ext_4397_);
lean_dec_ref(v_file_4394_);
v_a_4581_ = lean_ctor_get(v___x_4447_, 0);
lean_inc(v_a_4581_);
v_a_4582_ = lean_ctor_get(v___x_4447_, 1);
lean_inc(v_a_4582_);
lean_dec_ref(v___x_4447_);
v_a_4439_ = v_a_4581_;
v_a_4440_ = v_a_4582_;
goto v___jp_4438_;
}
}
}
else
{
lean_object* v_a_4584_; lean_object* v___x_4585_; uint8_t v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4591_; 
lean_dec_ref(v___x_4436_);
lean_dec_ref(v_traceFile_4401_);
lean_dec_ref(v_a_4399_);
lean_dec_ref(v_ext_4397_);
lean_dec_ref(v_build_4395_);
lean_dec_ref(v_file_4394_);
v_a_4584_ = lean_ctor_get(v___x_4444_, 0);
lean_inc(v_a_4584_);
lean_dec_ref(v___x_4444_);
v___x_4585_ = lean_io_error_to_string(v_a_4584_);
v___x_4586_ = 3;
v___x_4587_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4587_, 0, v___x_4585_);
lean_ctor_set_uint8(v___x_4587_, sizeof(void*)*1, v___x_4586_);
v___x_4588_ = lean_array_get_size(v_log_4425_);
v___x_4589_ = lean_array_push(v_log_4425_, v___x_4587_);
if (v_isShared_4432_ == 0)
{
lean_ctor_set(v___x_4431_, 0, v___x_4589_);
v___x_4591_ = v___x_4431_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v___x_4589_);
lean_ctor_set(v_reuseFailAlloc_4592_, 1, v_trace_4428_);
lean_ctor_set(v_reuseFailAlloc_4592_, 2, v_buildTime_4429_);
lean_ctor_set_uint8(v_reuseFailAlloc_4592_, sizeof(void*)*3 + 1, v_wantsRebuild_4427_);
v___x_4591_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
lean_ctor_set_uint8(v___x_4591_, sizeof(void*)*3, v___x_4434_);
v_a_4439_ = v___x_4588_;
v_a_4440_ = v___x_4591_;
goto v___jp_4438_;
}
}
v___jp_4438_:
{
lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v_a_4443_; 
v___x_4441_ = lean_box(0);
v___x_4442_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v___x_4437_, v___x_4441_, v_a_4440_);
lean_dec(v___x_4437_);
v_a_4443_ = lean_ctor_get(v___x_4442_, 1);
lean_inc(v_a_4443_);
lean_dec_ref(v___x_4442_);
v_a_4410_ = v_a_4439_;
v_a_4411_ = v_a_4443_;
goto v___jp_4409_;
}
}
else
{
uint8_t v___x_4593_; 
lean_dec_ref(v_a_4399_);
lean_dec_ref(v_ext_4397_);
lean_dec_ref(v_build_4395_);
lean_dec_ref(v_file_4394_);
v___x_4593_ = l_System_FilePath_pathExists(v_traceFile_4401_);
lean_dec_ref(v_traceFile_4401_);
if (v___x_4593_ == 0)
{
lean_dec_ref(v___x_4436_);
lean_del_object(v___x_4431_);
v_log_4414_ = v_log_4425_;
v_action_4415_ = v___x_4434_;
v_wantsRebuild_4416_ = v_noBuild_4433_;
v_trace_4417_ = v_trace_4428_;
v_buildTime_4418_ = v_buildTime_4429_;
goto v___jp_4413_;
}
else
{
lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; 
v___x_4594_ = lean_box(0);
v___x_4595_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_4596_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_4400_, v___x_4594_, v___x_4595_);
v___x_4597_ = l_Lake_BuildMetadata_writeFile(v___x_4436_, v___x_4596_);
if (lean_obj_tag(v___x_4597_) == 0)
{
lean_dec_ref(v___x_4597_);
lean_del_object(v___x_4431_);
v_log_4414_ = v_log_4425_;
v_action_4415_ = v___x_4434_;
v_wantsRebuild_4416_ = v_noBuild_4433_;
v_trace_4417_ = v_trace_4428_;
v_buildTime_4418_ = v_buildTime_4429_;
goto v___jp_4413_;
}
else
{
lean_object* v_a_4598_; lean_object* v___x_4599_; uint8_t v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4605_; 
v_a_4598_ = lean_ctor_get(v___x_4597_, 0);
lean_inc(v_a_4598_);
lean_dec_ref(v___x_4597_);
v___x_4599_ = lean_io_error_to_string(v_a_4598_);
v___x_4600_ = 3;
v___x_4601_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4601_, 0, v___x_4599_);
lean_ctor_set_uint8(v___x_4601_, sizeof(void*)*1, v___x_4600_);
v___x_4602_ = lean_array_get_size(v_log_4425_);
v___x_4603_ = lean_array_push(v_log_4425_, v___x_4601_);
if (v_isShared_4432_ == 0)
{
lean_ctor_set(v___x_4431_, 0, v___x_4603_);
v___x_4605_ = v___x_4431_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v___x_4603_);
lean_ctor_set(v_reuseFailAlloc_4607_, 1, v_trace_4428_);
lean_ctor_set(v_reuseFailAlloc_4607_, 2, v_buildTime_4429_);
v___x_4605_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
lean_object* v___x_4606_; 
lean_ctor_set_uint8(v___x_4605_, sizeof(void*)*3, v___x_4434_);
lean_ctor_set_uint8(v___x_4605_, sizeof(void*)*3 + 1, v_noBuild_4433_);
v___x_4606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4606_, 0, v___x_4602_);
lean_ctor_set(v___x_4606_, 1, v___x_4605_);
return v___x_4606_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___boxed(lean_object* v_file_4609_, lean_object* v_build_4610_, lean_object* v_traceFile_4611_, lean_object* v_ext_4612_, lean_object* v_text_4613_, lean_object* v_a_4614_, lean_object* v_depTrace_4615_, lean_object* v_traceFile_4616_, lean_object* v_action_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_){
_start:
{
uint8_t v_text_boxed_4624_; uint8_t v_action_boxed_4625_; lean_object* v_res_4626_; 
v_text_boxed_4624_ = lean_unbox(v_text_4613_);
v_action_boxed_4625_ = lean_unbox(v_action_4617_);
v_res_4626_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(v_file_4609_, v_build_4610_, v_traceFile_4611_, v_ext_4612_, v_text_boxed_4624_, v_a_4614_, v_depTrace_4615_, v_traceFile_4616_, v_action_boxed_4625_, v_a_4618_, v_a_4619_, v_a_4620_, v_a_4621_, v_a_4622_);
lean_dec_ref(v_a_4621_);
lean_dec(v_a_4620_);
lean_dec(v_a_4619_);
lean_dec(v_a_4618_);
lean_dec_ref(v_depTrace_4615_);
lean_dec_ref(v_traceFile_4611_);
return v_res_4626_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(lean_object* v_file_4627_, lean_object* v_build_4628_, uint8_t v_text_4629_, lean_object* v_ext_4630_, lean_object* v_depTrace_4631_, lean_object* v_traceFile_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_){
_start:
{
uint8_t v___x_4640_; lean_object* v___x_4641_; 
v___x_4640_ = 5;
lean_inc_ref(v_traceFile_4632_);
v___x_4641_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(v_file_4627_, v_build_4628_, v_traceFile_4632_, v_ext_4630_, v_text_4629_, v_a_4633_, v_depTrace_4631_, v_traceFile_4632_, v___x_4640_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_);
lean_dec_ref(v_traceFile_4632_);
return v___x_4641_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild___boxed(lean_object* v_file_4642_, lean_object* v_build_4643_, lean_object* v_text_4644_, lean_object* v_ext_4645_, lean_object* v_depTrace_4646_, lean_object* v_traceFile_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_){
_start:
{
uint8_t v_text_boxed_4655_; lean_object* v_res_4656_; 
v_text_boxed_4655_ = lean_unbox(v_text_4644_);
v_res_4656_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_4642_, v_build_4643_, v_text_boxed_4655_, v_ext_4645_, v_depTrace_4646_, v_traceFile_4647_, v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_);
lean_dec_ref(v_a_4652_);
lean_dec(v_a_4651_);
lean_dec(v_a_4650_);
lean_dec(v_a_4649_);
lean_dec_ref(v_depTrace_4646_);
return v_res_4656_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(lean_object* v_art_4658_, lean_object* v_traceFile_4659_, lean_object* v_a_4660_){
_start:
{
lean_object* v_log_4662_; uint8_t v_action_4663_; uint8_t v_wantsRebuild_4664_; lean_object* v_trace_4665_; lean_object* v_buildTime_4666_; lean_object* v___x_4667_; 
v_log_4662_ = lean_ctor_get(v_a_4660_, 0);
v_action_4663_ = lean_ctor_get_uint8(v_a_4660_, sizeof(void*)*3);
v_wantsRebuild_4664_ = lean_ctor_get_uint8(v_a_4660_, sizeof(void*)*3 + 1);
v_trace_4665_ = lean_ctor_get(v_a_4660_, 1);
v_buildTime_4666_ = lean_ctor_get(v_a_4660_, 2);
v___x_4667_ = lean_io_metadata(v_traceFile_4659_);
if (lean_obj_tag(v___x_4667_) == 0)
{
lean_object* v_a_4668_; lean_object* v_modified_4669_; lean_object* v_descr_4670_; lean_object* v_path_4671_; lean_object* v_name_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4680_; 
v_a_4668_ = lean_ctor_get(v___x_4667_, 0);
lean_inc(v_a_4668_);
lean_dec_ref(v___x_4667_);
v_modified_4669_ = lean_ctor_get(v_a_4668_, 1);
lean_inc_ref(v_modified_4669_);
lean_dec(v_a_4668_);
v_descr_4670_ = lean_ctor_get(v_art_4658_, 0);
v_path_4671_ = lean_ctor_get(v_art_4658_, 1);
v_name_4672_ = lean_ctor_get(v_art_4658_, 2);
v_isSharedCheck_4680_ = !lean_is_exclusive(v_art_4658_);
if (v_isSharedCheck_4680_ == 0)
{
lean_object* v_unused_4681_; 
v_unused_4681_ = lean_ctor_get(v_art_4658_, 3);
lean_dec(v_unused_4681_);
v___x_4674_ = v_art_4658_;
v_isShared_4675_ = v_isSharedCheck_4680_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_name_4672_);
lean_inc(v_path_4671_);
lean_inc(v_descr_4670_);
lean_dec(v_art_4658_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4680_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___x_4677_; 
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 3, v_modified_4669_);
v___x_4677_ = v___x_4674_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v_descr_4670_);
lean_ctor_set(v_reuseFailAlloc_4679_, 1, v_path_4671_);
lean_ctor_set(v_reuseFailAlloc_4679_, 2, v_name_4672_);
lean_ctor_set(v_reuseFailAlloc_4679_, 3, v_modified_4669_);
v___x_4677_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
lean_object* v___x_4678_; 
v___x_4678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4678_, 0, v___x_4677_);
lean_ctor_set(v___x_4678_, 1, v_a_4660_);
return v___x_4678_;
}
}
}
else
{
lean_object* v_a_4682_; 
v_a_4682_ = lean_ctor_get(v___x_4667_, 0);
lean_inc(v_a_4682_);
lean_dec_ref(v___x_4667_);
if (lean_obj_tag(v_a_4682_) == 11)
{
lean_object* v___x_4683_; 
lean_dec_ref(v_a_4682_);
v___x_4683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4683_, 0, v_art_4658_);
lean_ctor_set(v___x_4683_, 1, v_a_4660_);
return v___x_4683_;
}
else
{
lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4698_; 
lean_inc(v_buildTime_4666_);
lean_inc_ref(v_trace_4665_);
lean_inc_ref(v_log_4662_);
lean_dec_ref(v_art_4658_);
v_isSharedCheck_4698_ = !lean_is_exclusive(v_a_4660_);
if (v_isSharedCheck_4698_ == 0)
{
lean_object* v_unused_4699_; lean_object* v_unused_4700_; lean_object* v_unused_4701_; 
v_unused_4699_ = lean_ctor_get(v_a_4660_, 2);
lean_dec(v_unused_4699_);
v_unused_4700_ = lean_ctor_get(v_a_4660_, 1);
lean_dec(v_unused_4700_);
v_unused_4701_ = lean_ctor_get(v_a_4660_, 0);
lean_dec(v_unused_4701_);
v___x_4685_ = v_a_4660_;
v_isShared_4686_ = v_isSharedCheck_4698_;
goto v_resetjp_4684_;
}
else
{
lean_dec(v_a_4660_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4698_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; uint8_t v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4695_; 
v___x_4687_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___closed__0));
v___x_4688_ = lean_io_error_to_string(v_a_4682_);
v___x_4689_ = lean_string_append(v___x_4687_, v___x_4688_);
lean_dec_ref(v___x_4688_);
v___x_4690_ = 3;
v___x_4691_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4691_, 0, v___x_4689_);
lean_ctor_set_uint8(v___x_4691_, sizeof(void*)*1, v___x_4690_);
v___x_4692_ = lean_array_get_size(v_log_4662_);
v___x_4693_ = lean_array_push(v_log_4662_, v___x_4691_);
if (v_isShared_4686_ == 0)
{
lean_ctor_set(v___x_4685_, 0, v___x_4693_);
v___x_4695_ = v___x_4685_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v___x_4693_);
lean_ctor_set(v_reuseFailAlloc_4697_, 1, v_trace_4665_);
lean_ctor_set(v_reuseFailAlloc_4697_, 2, v_buildTime_4666_);
lean_ctor_set_uint8(v_reuseFailAlloc_4697_, sizeof(void*)*3, v_action_4663_);
lean_ctor_set_uint8(v_reuseFailAlloc_4697_, sizeof(void*)*3 + 1, v_wantsRebuild_4664_);
v___x_4695_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
lean_object* v___x_4696_; 
v___x_4696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4696_, 0, v___x_4692_);
lean_ctor_set(v___x_4696_, 1, v___x_4695_);
return v___x_4696_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___boxed(lean_object* v_art_4702_, lean_object* v_traceFile_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_){
_start:
{
lean_object* v_res_4706_; 
v_res_4706_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_4702_, v_traceFile_4703_, v_a_4704_);
lean_dec_ref(v_traceFile_4703_);
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(lean_object* v_art_4707_, lean_object* v_traceFile_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_){
_start:
{
lean_object* v___x_4716_; 
v___x_4716_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_4707_, v_traceFile_4708_, v_a_4714_);
return v___x_4716_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___boxed(lean_object* v_art_4717_, lean_object* v_traceFile_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_){
_start:
{
lean_object* v_res_4726_; 
v_res_4726_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(v_art_4717_, v_traceFile_4718_, v_a_4719_, v_a_4720_, v_a_4721_, v_a_4722_, v_a_4723_, v_a_4724_);
lean_dec_ref(v_a_4723_);
lean_dec(v_a_4722_);
lean_dec(v_a_4721_);
lean_dec(v_a_4720_);
lean_dec_ref(v_a_4719_);
lean_dec_ref(v_traceFile_4718_);
return v_res_4726_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0(lean_object* v_a_4727_, lean_object* v_____r_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_){
_start:
{
lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; 
v___x_4736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4736_, 0, v_a_4727_);
v___x_4737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4737_, 0, v___x_4736_);
v___x_4738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4738_, 0, v___x_4737_);
lean_ctor_set(v___x_4738_, 1, v___y_4734_);
return v___x_4738_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0___boxed(lean_object* v_a_4739_, lean_object* v_____r_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_){
_start:
{
lean_object* v_res_4748_; 
v_res_4748_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0(v_a_4739_, v_____r_4740_, v___y_4741_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_);
lean_dec_ref(v___y_4745_);
lean_dec(v___y_4744_);
lean_dec(v___y_4743_);
lean_dec(v___y_4742_);
lean_dec_ref(v___y_4741_);
return v_res_4748_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(uint8_t v_exe_4749_, lean_object* v___y_4750_, uint64_t v_inputHash_4751_, lean_object* v_savedTrace_4752_, lean_object* v_pkg_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_){
_start:
{
lean_object* v___y_4761_; lean_object* v_a_4765_; lean_object* v_a_4766_; lean_object* v___y_4781_; 
if (lean_obj_tag(v_savedTrace_4752_) == 2)
{
lean_object* v_data_4796_; uint64_t v_depHash_4797_; lean_object* v_outputs_x3f_4798_; uint8_t v___x_4799_; 
v_data_4796_ = lean_ctor_get(v_savedTrace_4752_, 0);
lean_inc_ref(v_data_4796_);
lean_dec_ref(v_savedTrace_4752_);
v_depHash_4797_ = lean_ctor_get_uint64(v_data_4796_, sizeof(void*)*3);
v_outputs_x3f_4798_ = lean_ctor_get(v_data_4796_, 1);
lean_inc(v_outputs_x3f_4798_);
lean_dec_ref(v_data_4796_);
v___x_4799_ = lean_uint64_dec_eq(v_depHash_4797_, v_inputHash_4751_);
if (v___x_4799_ == 0)
{
lean_dec(v_outputs_x3f_4798_);
lean_dec_ref(v_pkg_4753_);
lean_dec_ref(v___y_4750_);
v___y_4761_ = v_a_4758_;
goto v___jp_4760_;
}
else
{
if (lean_obj_tag(v_outputs_x3f_4798_) == 1)
{
lean_object* v_val_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; 
v_val_4800_ = lean_ctor_get(v_outputs_x3f_4798_, 0);
lean_inc_n(v_val_4800_, 2);
lean_dec_ref(v_outputs_x3f_4798_);
v___x_4801_ = lean_box(0);
v___x_4802_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4802_, 0, v_val_4800_);
lean_ctor_set(v___x_4802_, 1, v___x_4801_);
lean_ctor_set(v___x_4802_, 2, v___x_4801_);
lean_inc_ref(v___y_4750_);
v___x_4803_ = l_Lake_resolveArtifactOutput(v___x_4802_, v_exe_4749_, v___y_4750_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_);
if (lean_obj_tag(v___x_4803_) == 0)
{
lean_object* v_config_4804_; lean_object* v_a_4805_; lean_object* v_a_4806_; lean_object* v_enableArtifactCache_x3f_4807_; lean_object* v_a_4809_; uint8_t v_a_4813_; lean_object* v_a_4814_; 
v_config_4804_ = lean_ctor_get(v_pkg_4753_, 6);
v_a_4805_ = lean_ctor_get(v___x_4803_, 0);
lean_inc(v_a_4805_);
v_a_4806_ = lean_ctor_get(v___x_4803_, 1);
lean_inc(v_a_4806_);
lean_dec_ref(v___x_4803_);
v_enableArtifactCache_x3f_4807_ = lean_ctor_get(v_config_4804_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_4807_) == 0)
{
lean_object* v_toContext_4845_; lean_object* v_lakeEnv_4846_; lean_object* v_enableArtifactCache_x3f_4847_; 
v_toContext_4845_ = lean_ctor_get(v_a_4757_, 1);
v_lakeEnv_4846_ = lean_ctor_get(v_toContext_4845_, 0);
v_enableArtifactCache_x3f_4847_ = lean_ctor_get(v_lakeEnv_4846_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_4847_) == 0)
{
lean_object* v_packages_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v_config_4851_; lean_object* v_enableArtifactCache_x3f_4852_; 
v_packages_4848_ = lean_ctor_get(v_toContext_4845_, 4);
v___x_4849_ = lean_unsigned_to_nat(0u);
v___x_4850_ = lean_array_fget_borrowed(v_packages_4848_, v___x_4849_);
v_config_4851_ = lean_ctor_get(v___x_4850_, 6);
v_enableArtifactCache_x3f_4852_ = lean_ctor_get(v_config_4851_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_4852_) == 0)
{
lean_dec(v_val_4800_);
lean_dec_ref(v_pkg_4753_);
v_a_4809_ = v_a_4806_;
goto v___jp_4808_;
}
else
{
lean_object* v_val_4853_; uint8_t v___x_4854_; 
v_val_4853_ = lean_ctor_get(v_enableArtifactCache_x3f_4852_, 0);
v___x_4854_ = lean_unbox(v_val_4853_);
v_a_4813_ = v___x_4854_;
v_a_4814_ = v_a_4806_;
goto v___jp_4812_;
}
}
else
{
lean_object* v_val_4855_; uint8_t v___x_4856_; 
v_val_4855_ = lean_ctor_get(v_enableArtifactCache_x3f_4847_, 0);
v___x_4856_ = lean_unbox(v_val_4855_);
v_a_4813_ = v___x_4856_;
v_a_4814_ = v_a_4806_;
goto v___jp_4812_;
}
}
else
{
lean_object* v_val_4857_; uint8_t v___x_4858_; 
v_val_4857_ = lean_ctor_get(v_enableArtifactCache_x3f_4807_, 0);
v___x_4858_ = lean_unbox(v_val_4857_);
v_a_4813_ = v___x_4858_;
v_a_4814_ = v_a_4806_;
goto v___jp_4812_;
}
v___jp_4808_:
{
lean_object* v___x_4810_; lean_object* v___x_4811_; 
v___x_4810_ = lean_box(0);
v___x_4811_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0(v_a_4805_, v___x_4810_, v___y_4750_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4809_);
lean_dec_ref(v___y_4750_);
v___y_4781_ = v___x_4811_;
goto v___jp_4780_;
}
v___jp_4812_:
{
if (v_a_4813_ == 0)
{
lean_dec(v_val_4800_);
lean_dec_ref(v_pkg_4753_);
v_a_4809_ = v_a_4814_;
goto v___jp_4808_;
}
else
{
lean_object* v_toContext_4815_; lean_object* v_log_4816_; uint8_t v_action_4817_; uint8_t v_wantsRebuild_4818_; lean_object* v_trace_4819_; lean_object* v_buildTime_4820_; lean_object* v_lakeCache_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; 
v_toContext_4815_ = lean_ctor_get(v_a_4757_, 1);
v_log_4816_ = lean_ctor_get(v_a_4814_, 0);
v_action_4817_ = lean_ctor_get_uint8(v_a_4814_, sizeof(void*)*3);
v_wantsRebuild_4818_ = lean_ctor_get_uint8(v_a_4814_, sizeof(void*)*3 + 1);
v_trace_4819_ = lean_ctor_get(v_a_4814_, 1);
v_buildTime_4820_ = lean_ctor_get(v_a_4814_, 2);
v_lakeCache_4821_ = lean_ctor_get(v_toContext_4815_, 2);
v___x_4822_ = l_Lake_Package_cacheScope(v_pkg_4753_);
lean_inc_ref(v_lakeCache_4821_);
v___x_4823_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_4821_, v___x_4822_, v_inputHash_4751_, v_val_4800_, v___x_4801_, v___x_4801_);
if (lean_obj_tag(v___x_4823_) == 0)
{
lean_object* v___x_4824_; lean_object* v___x_4825_; 
lean_dec_ref(v___x_4823_);
v___x_4824_ = lean_box(0);
v___x_4825_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0(v_a_4805_, v___x_4824_, v___y_4750_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4814_);
lean_dec_ref(v___y_4750_);
v___y_4781_ = v___x_4825_;
goto v___jp_4780_;
}
else
{
lean_object* v___x_4827_; uint8_t v_isShared_4828_; uint8_t v_isSharedCheck_4841_; 
lean_inc(v_buildTime_4820_);
lean_inc_ref(v_trace_4819_);
lean_inc_ref(v_log_4816_);
v_isSharedCheck_4841_ = !lean_is_exclusive(v_a_4814_);
if (v_isSharedCheck_4841_ == 0)
{
lean_object* v_unused_4842_; lean_object* v_unused_4843_; lean_object* v_unused_4844_; 
v_unused_4842_ = lean_ctor_get(v_a_4814_, 2);
lean_dec(v_unused_4842_);
v_unused_4843_ = lean_ctor_get(v_a_4814_, 1);
lean_dec(v_unused_4843_);
v_unused_4844_ = lean_ctor_get(v_a_4814_, 0);
lean_dec(v_unused_4844_);
v___x_4827_ = v_a_4814_;
v_isShared_4828_ = v_isSharedCheck_4841_;
goto v_resetjp_4826_;
}
else
{
lean_dec(v_a_4814_);
v___x_4827_ = lean_box(0);
v_isShared_4828_ = v_isSharedCheck_4841_;
goto v_resetjp_4826_;
}
v_resetjp_4826_:
{
lean_object* v_a_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; uint8_t v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4838_; 
v_a_4829_ = lean_ctor_get(v___x_4823_, 0);
lean_inc(v_a_4829_);
lean_dec_ref(v___x_4823_);
v___x_4830_ = ((lean_object*)(l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0));
v___x_4831_ = lean_io_error_to_string(v_a_4829_);
v___x_4832_ = lean_string_append(v___x_4830_, v___x_4831_);
lean_dec_ref(v___x_4831_);
v___x_4833_ = 2;
v___x_4834_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4834_, 0, v___x_4832_);
lean_ctor_set_uint8(v___x_4834_, sizeof(void*)*1, v___x_4833_);
v___x_4835_ = lean_box(0);
v___x_4836_ = lean_array_push(v_log_4816_, v___x_4834_);
if (v_isShared_4828_ == 0)
{
lean_ctor_set(v___x_4827_, 0, v___x_4836_);
v___x_4838_ = v___x_4827_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4840_; 
v_reuseFailAlloc_4840_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4840_, 0, v___x_4836_);
lean_ctor_set(v_reuseFailAlloc_4840_, 1, v_trace_4819_);
lean_ctor_set(v_reuseFailAlloc_4840_, 2, v_buildTime_4820_);
lean_ctor_set_uint8(v_reuseFailAlloc_4840_, sizeof(void*)*3, v_action_4817_);
lean_ctor_set_uint8(v_reuseFailAlloc_4840_, sizeof(void*)*3 + 1, v_wantsRebuild_4818_);
v___x_4838_ = v_reuseFailAlloc_4840_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
lean_object* v___x_4839_; 
v___x_4839_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___lam__0(v_a_4805_, v___x_4835_, v___y_4750_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v___x_4838_);
lean_dec_ref(v___y_4750_);
v___y_4781_ = v___x_4839_;
goto v___jp_4780_;
}
}
}
}
}
}
else
{
lean_object* v_a_4859_; lean_object* v_a_4860_; 
lean_dec(v_val_4800_);
lean_dec_ref(v_pkg_4753_);
lean_dec_ref(v___y_4750_);
v_a_4859_ = lean_ctor_get(v___x_4803_, 0);
lean_inc(v_a_4859_);
v_a_4860_ = lean_ctor_get(v___x_4803_, 1);
lean_inc(v_a_4860_);
lean_dec_ref(v___x_4803_);
v_a_4765_ = v_a_4859_;
v_a_4766_ = v_a_4860_;
goto v___jp_4764_;
}
}
else
{
lean_dec(v_outputs_x3f_4798_);
lean_dec_ref(v_pkg_4753_);
lean_dec_ref(v___y_4750_);
v___y_4761_ = v_a_4758_;
goto v___jp_4760_;
}
}
}
else
{
lean_dec_ref(v_pkg_4753_);
lean_dec(v_savedTrace_4752_);
lean_dec_ref(v___y_4750_);
v___y_4761_ = v_a_4758_;
goto v___jp_4760_;
}
v___jp_4760_:
{
lean_object* v___x_4762_; lean_object* v___x_4763_; 
v___x_4762_ = lean_box(0);
v___x_4763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4763_, 0, v___x_4762_);
lean_ctor_set(v___x_4763_, 1, v___y_4761_);
return v___x_4763_;
}
v___jp_4764_:
{
lean_object* v_log_4767_; uint8_t v_action_4768_; uint8_t v_wantsRebuild_4769_; lean_object* v_trace_4770_; lean_object* v_buildTime_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4779_; 
v_log_4767_ = lean_ctor_get(v_a_4766_, 0);
v_action_4768_ = lean_ctor_get_uint8(v_a_4766_, sizeof(void*)*3);
v_wantsRebuild_4769_ = lean_ctor_get_uint8(v_a_4766_, sizeof(void*)*3 + 1);
v_trace_4770_ = lean_ctor_get(v_a_4766_, 1);
v_buildTime_4771_ = lean_ctor_get(v_a_4766_, 2);
v_isSharedCheck_4779_ = !lean_is_exclusive(v_a_4766_);
if (v_isSharedCheck_4779_ == 0)
{
v___x_4773_ = v_a_4766_;
v_isShared_4774_ = v_isSharedCheck_4779_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_buildTime_4771_);
lean_inc(v_trace_4770_);
lean_inc(v_log_4767_);
lean_dec(v_a_4766_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4779_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
lean_object* v___x_4775_; lean_object* v___x_4777_; 
v___x_4775_ = l_Array_shrink___redArg(v_log_4767_, v_a_4765_);
lean_dec(v_a_4765_);
if (v_isShared_4774_ == 0)
{
lean_ctor_set(v___x_4773_, 0, v___x_4775_);
v___x_4777_ = v___x_4773_;
goto v_reusejp_4776_;
}
else
{
lean_object* v_reuseFailAlloc_4778_; 
v_reuseFailAlloc_4778_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4778_, 0, v___x_4775_);
lean_ctor_set(v_reuseFailAlloc_4778_, 1, v_trace_4770_);
lean_ctor_set(v_reuseFailAlloc_4778_, 2, v_buildTime_4771_);
lean_ctor_set_uint8(v_reuseFailAlloc_4778_, sizeof(void*)*3, v_action_4768_);
lean_ctor_set_uint8(v_reuseFailAlloc_4778_, sizeof(void*)*3 + 1, v_wantsRebuild_4769_);
v___x_4777_ = v_reuseFailAlloc_4778_;
goto v_reusejp_4776_;
}
v_reusejp_4776_:
{
v___y_4761_ = v___x_4777_;
goto v___jp_4760_;
}
}
}
v___jp_4780_:
{
if (lean_obj_tag(v___y_4781_) == 0)
{
lean_object* v_a_4782_; 
v_a_4782_ = lean_ctor_get(v___y_4781_, 0);
if (lean_obj_tag(v_a_4782_) == 0)
{
lean_object* v_a_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4791_; 
lean_inc_ref(v_a_4782_);
v_a_4783_ = lean_ctor_get(v___y_4781_, 1);
v_isSharedCheck_4791_ = !lean_is_exclusive(v___y_4781_);
if (v_isSharedCheck_4791_ == 0)
{
lean_object* v_unused_4792_; 
v_unused_4792_ = lean_ctor_get(v___y_4781_, 0);
lean_dec(v_unused_4792_);
v___x_4785_ = v___y_4781_;
v_isShared_4786_ = v_isSharedCheck_4791_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_a_4783_);
lean_dec(v___y_4781_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4791_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v_a_4787_; lean_object* v___x_4789_; 
v_a_4787_ = lean_ctor_get(v_a_4782_, 0);
lean_inc(v_a_4787_);
lean_dec_ref(v_a_4782_);
if (v_isShared_4786_ == 0)
{
lean_ctor_set(v___x_4785_, 0, v_a_4787_);
v___x_4789_ = v___x_4785_;
goto v_reusejp_4788_;
}
else
{
lean_object* v_reuseFailAlloc_4790_; 
v_reuseFailAlloc_4790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4790_, 0, v_a_4787_);
lean_ctor_set(v_reuseFailAlloc_4790_, 1, v_a_4783_);
v___x_4789_ = v_reuseFailAlloc_4790_;
goto v_reusejp_4788_;
}
v_reusejp_4788_:
{
return v___x_4789_;
}
}
}
else
{
lean_object* v_a_4793_; 
v_a_4793_ = lean_ctor_get(v___y_4781_, 1);
lean_inc(v_a_4793_);
lean_dec_ref(v___y_4781_);
v___y_4761_ = v_a_4793_;
goto v___jp_4760_;
}
}
else
{
lean_object* v_a_4794_; lean_object* v_a_4795_; 
v_a_4794_ = lean_ctor_get(v___y_4781_, 0);
lean_inc(v_a_4794_);
v_a_4795_ = lean_ctor_get(v___y_4781_, 1);
lean_inc(v_a_4795_);
lean_dec_ref(v___y_4781_);
v_a_4765_ = v_a_4794_;
v_a_4766_ = v_a_4795_;
goto v___jp_4764_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___boxed(lean_object* v_exe_4861_, lean_object* v___y_4862_, lean_object* v_inputHash_4863_, lean_object* v_savedTrace_4864_, lean_object* v_pkg_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_){
_start:
{
uint8_t v_exe_boxed_4872_; uint64_t v_inputHash_boxed_4873_; lean_object* v_res_4874_; 
v_exe_boxed_4872_ = lean_unbox(v_exe_4861_);
v_inputHash_boxed_4873_ = lean_unbox_uint64(v_inputHash_4863_);
lean_dec_ref(v_inputHash_4863_);
v_res_4874_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(v_exe_boxed_4872_, v___y_4862_, v_inputHash_boxed_4873_, v_savedTrace_4864_, v_pkg_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_);
lean_dec_ref(v_a_4869_);
lean_dec(v_a_4868_);
lean_dec(v_a_4867_);
lean_dec(v_a_4866_);
return v_res_4874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(lean_object* v_as_4875_, size_t v_i_4876_, size_t v_stop_4877_, lean_object* v_b_4878_){
_start:
{
uint8_t v___x_4879_; 
v___x_4879_ = lean_usize_dec_eq(v_i_4876_, v_stop_4877_);
if (v___x_4879_ == 0)
{
lean_object* v___x_4880_; lean_object* v_message_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; size_t v___x_4885_; size_t v___x_4886_; 
v___x_4880_ = lean_array_uget_borrowed(v_as_4875_, v_i_4876_);
v_message_4881_ = lean_ctor_get(v___x_4880_, 0);
v___x_4882_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0));
v___x_4883_ = lean_string_append(v_b_4878_, v___x_4882_);
v___x_4884_ = lean_string_append(v___x_4883_, v_message_4881_);
v___x_4885_ = ((size_t)1ULL);
v___x_4886_ = lean_usize_add(v_i_4876_, v___x_4885_);
v_i_4876_ = v___x_4886_;
v_b_4878_ = v___x_4884_;
goto _start;
}
else
{
return v_b_4878_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0___boxed(lean_object* v_as_4888_, lean_object* v_i_4889_, lean_object* v_stop_4890_, lean_object* v_b_4891_){
_start:
{
size_t v_i_boxed_4892_; size_t v_stop_boxed_4893_; lean_object* v_res_4894_; 
v_i_boxed_4892_ = lean_unbox_usize(v_i_4889_);
lean_dec(v_i_4889_);
v_stop_boxed_4893_ = lean_unbox_usize(v_stop_4890_);
lean_dec(v_stop_4890_);
v_res_4894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(v_as_4888_, v_i_boxed_4892_, v_stop_boxed_4893_, v_b_4891_);
lean_dec_ref(v_as_4888_);
return v_res_4894_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(uint8_t v_exe_4895_, lean_object* v___y_4896_, uint64_t v_inputHash_4897_, lean_object* v_pkg_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_){
_start:
{
lean_object* v_toContext_4905_; lean_object* v_log_4906_; uint8_t v_action_4907_; uint8_t v_wantsRebuild_4908_; lean_object* v_trace_4909_; lean_object* v_buildTime_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_5003_; 
v_toContext_4905_ = lean_ctor_get(v_a_4902_, 1);
v_log_4906_ = lean_ctor_get(v_a_4903_, 0);
v_action_4907_ = lean_ctor_get_uint8(v_a_4903_, sizeof(void*)*3);
v_wantsRebuild_4908_ = lean_ctor_get_uint8(v_a_4903_, sizeof(void*)*3 + 1);
v_trace_4909_ = lean_ctor_get(v_a_4903_, 1);
v_buildTime_4910_ = lean_ctor_get(v_a_4903_, 2);
v_isSharedCheck_5003_ = !lean_is_exclusive(v_a_4903_);
if (v_isSharedCheck_5003_ == 0)
{
v___x_4912_ = v_a_4903_;
v_isShared_4913_ = v_isSharedCheck_5003_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_buildTime_4910_);
lean_inc(v_trace_4909_);
lean_inc(v_log_4906_);
lean_dec(v_a_4903_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_5003_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v_lakeCache_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; 
v_lakeCache_4914_ = lean_ctor_get(v_toContext_4905_, 2);
v___x_4915_ = l_Lake_Package_cacheScope(v_pkg_4898_);
lean_inc_ref(v_lakeCache_4914_);
v___x_4916_ = l_Lake_Cache_readOutputs_x3f(v_lakeCache_4914_, v___x_4915_, v_inputHash_4897_, v_log_4906_);
if (lean_obj_tag(v___x_4916_) == 0)
{
lean_object* v_a_4917_; lean_object* v_a_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4990_; 
v_a_4917_ = lean_ctor_get(v___x_4916_, 0);
v_a_4918_ = lean_ctor_get(v___x_4916_, 1);
v_isSharedCheck_4990_ = !lean_is_exclusive(v___x_4916_);
if (v_isSharedCheck_4990_ == 0)
{
v___x_4920_ = v___x_4916_;
v_isShared_4921_ = v_isSharedCheck_4990_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_a_4918_);
lean_inc(v_a_4917_);
lean_dec(v___x_4916_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4990_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v___x_4923_; 
if (v_isShared_4913_ == 0)
{
lean_ctor_set(v___x_4912_, 0, v_a_4918_);
v___x_4923_ = v___x_4912_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4989_; 
v_reuseFailAlloc_4989_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4989_, 0, v_a_4918_);
lean_ctor_set(v_reuseFailAlloc_4989_, 1, v_trace_4909_);
lean_ctor_set(v_reuseFailAlloc_4989_, 2, v_buildTime_4910_);
lean_ctor_set_uint8(v_reuseFailAlloc_4989_, sizeof(void*)*3, v_action_4907_);
lean_ctor_set_uint8(v_reuseFailAlloc_4989_, sizeof(void*)*3 + 1, v_wantsRebuild_4908_);
v___x_4923_ = v_reuseFailAlloc_4989_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
if (lean_obj_tag(v_a_4917_) == 1)
{
lean_object* v_val_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4984_; 
v_val_4924_ = lean_ctor_get(v_a_4917_, 0);
v_isSharedCheck_4984_ = !lean_is_exclusive(v_a_4917_);
if (v_isSharedCheck_4984_ == 0)
{
v___x_4926_ = v_a_4917_;
v_isShared_4927_ = v_isSharedCheck_4984_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_val_4924_);
lean_dec(v_a_4917_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4984_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v___x_4928_; lean_object* v_r_4930_; lean_object* v___y_4931_; 
v___x_4928_ = l_Lake_resolveArtifactOutput(v_val_4924_, v_exe_4895_, v___y_4896_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v___x_4923_);
if (lean_obj_tag(v___x_4928_) == 0)
{
lean_object* v_a_4935_; lean_object* v_a_4936_; lean_object* v___x_4938_; 
v_a_4935_ = lean_ctor_get(v___x_4928_, 0);
lean_inc(v_a_4935_);
v_a_4936_ = lean_ctor_get(v___x_4928_, 1);
lean_inc(v_a_4936_);
lean_dec_ref(v___x_4928_);
if (v_isShared_4927_ == 0)
{
lean_ctor_set(v___x_4926_, 0, v_a_4935_);
v___x_4938_ = v___x_4926_;
goto v_reusejp_4937_;
}
else
{
lean_object* v_reuseFailAlloc_4939_; 
v_reuseFailAlloc_4939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4939_, 0, v_a_4935_);
v___x_4938_ = v_reuseFailAlloc_4939_;
goto v_reusejp_4937_;
}
v_reusejp_4937_:
{
v_r_4930_ = v___x_4938_;
v___y_4931_ = v_a_4936_;
goto v___jp_4929_;
}
}
else
{
lean_object* v_a_4940_; lean_object* v_a_4941_; lean_object* v_log_4942_; uint8_t v_action_4943_; uint8_t v_wantsRebuild_4944_; lean_object* v_trace_4945_; lean_object* v_buildTime_4946_; lean_object* v___x_4948_; uint8_t v_isShared_4949_; uint8_t v_isSharedCheck_4983_; 
lean_del_object(v___x_4926_);
v_a_4940_ = lean_ctor_get(v___x_4928_, 1);
lean_inc(v_a_4940_);
v_a_4941_ = lean_ctor_get(v___x_4928_, 0);
lean_inc(v_a_4941_);
lean_dec_ref(v___x_4928_);
v_log_4942_ = lean_ctor_get(v_a_4940_, 0);
v_action_4943_ = lean_ctor_get_uint8(v_a_4940_, sizeof(void*)*3);
v_wantsRebuild_4944_ = lean_ctor_get_uint8(v_a_4940_, sizeof(void*)*3 + 1);
v_trace_4945_ = lean_ctor_get(v_a_4940_, 1);
v_buildTime_4946_ = lean_ctor_get(v_a_4940_, 2);
v_isSharedCheck_4983_ = !lean_is_exclusive(v_a_4940_);
if (v_isSharedCheck_4983_ == 0)
{
v___x_4948_ = v_a_4940_;
v_isShared_4949_ = v_isSharedCheck_4983_;
goto v_resetjp_4947_;
}
else
{
lean_inc(v_buildTime_4946_);
lean_inc(v_trace_4945_);
lean_inc(v_log_4942_);
lean_dec(v_a_4940_);
v___x_4948_ = lean_box(0);
v_isShared_4949_ = v_isSharedCheck_4983_;
goto v_resetjp_4947_;
}
v_resetjp_4947_:
{
lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___y_4954_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; uint8_t v___x_4975_; 
v___x_4950_ = lean_array_get_size(v_log_4942_);
lean_inc(v_a_4941_);
v___x_4951_ = l_Array_extract___redArg(v_log_4942_, v_a_4941_, v___x_4950_);
v___x_4952_ = l_Array_shrink___redArg(v_log_4942_, v_a_4941_);
lean_dec(v_a_4941_);
v___x_4962_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0));
v___x_4963_ = l_Lake_lowerHexUInt64(v_inputHash_4897_);
v___x_4964_ = lean_unsigned_to_nat(7u);
v___x_4965_ = lean_unsigned_to_nat(0u);
v___x_4966_ = lean_string_utf8_byte_size(v___x_4963_);
lean_inc_ref(v___x_4963_);
v___x_4967_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4967_, 0, v___x_4963_);
lean_ctor_set(v___x_4967_, 1, v___x_4965_);
lean_ctor_set(v___x_4967_, 2, v___x_4966_);
v___x_4968_ = l_String_Slice_Pos_nextn(v___x_4967_, v___x_4965_, v___x_4964_);
lean_dec_ref(v___x_4967_);
v___x_4969_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4969_, 0, v___x_4963_);
lean_ctor_set(v___x_4969_, 1, v___x_4965_);
lean_ctor_set(v___x_4969_, 2, v___x_4968_);
v___x_4970_ = l_String_Slice_toString(v___x_4969_);
lean_dec_ref(v___x_4969_);
v___x_4971_ = lean_string_append(v___x_4962_, v___x_4970_);
lean_dec_ref(v___x_4970_);
v___x_4972_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1));
v___x_4973_ = lean_string_append(v___x_4971_, v___x_4972_);
v___x_4974_ = lean_array_get_size(v___x_4951_);
v___x_4975_ = lean_nat_dec_lt(v___x_4965_, v___x_4974_);
if (v___x_4975_ == 0)
{
lean_dec_ref(v___x_4951_);
v___y_4954_ = v___x_4973_;
goto v___jp_4953_;
}
else
{
uint8_t v___x_4976_; 
v___x_4976_ = lean_nat_dec_le(v___x_4974_, v___x_4974_);
if (v___x_4976_ == 0)
{
if (v___x_4975_ == 0)
{
lean_dec_ref(v___x_4951_);
v___y_4954_ = v___x_4973_;
goto v___jp_4953_;
}
else
{
size_t v___x_4977_; size_t v___x_4978_; lean_object* v___x_4979_; 
v___x_4977_ = ((size_t)0ULL);
v___x_4978_ = lean_usize_of_nat(v___x_4974_);
v___x_4979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(v___x_4951_, v___x_4977_, v___x_4978_, v___x_4973_);
lean_dec_ref(v___x_4951_);
v___y_4954_ = v___x_4979_;
goto v___jp_4953_;
}
}
else
{
size_t v___x_4980_; size_t v___x_4981_; lean_object* v___x_4982_; 
v___x_4980_ = ((size_t)0ULL);
v___x_4981_ = lean_usize_of_nat(v___x_4974_);
v___x_4982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0_spec__0(v___x_4951_, v___x_4980_, v___x_4981_, v___x_4973_);
lean_dec_ref(v___x_4951_);
v___y_4954_ = v___x_4982_;
goto v___jp_4953_;
}
}
v___jp_4953_:
{
uint8_t v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4959_; 
v___x_4955_ = 2;
v___x_4956_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4956_, 0, v___y_4954_);
lean_ctor_set_uint8(v___x_4956_, sizeof(void*)*1, v___x_4955_);
v___x_4957_ = lean_array_push(v___x_4952_, v___x_4956_);
if (v_isShared_4949_ == 0)
{
lean_ctor_set(v___x_4948_, 0, v___x_4957_);
v___x_4959_ = v___x_4948_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4961_; 
v_reuseFailAlloc_4961_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4961_, 0, v___x_4957_);
lean_ctor_set(v_reuseFailAlloc_4961_, 1, v_trace_4945_);
lean_ctor_set(v_reuseFailAlloc_4961_, 2, v_buildTime_4946_);
lean_ctor_set_uint8(v_reuseFailAlloc_4961_, sizeof(void*)*3, v_action_4943_);
lean_ctor_set_uint8(v_reuseFailAlloc_4961_, sizeof(void*)*3 + 1, v_wantsRebuild_4944_);
v___x_4959_ = v_reuseFailAlloc_4961_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
lean_object* v___x_4960_; 
v___x_4960_ = lean_box(0);
v_r_4930_ = v___x_4960_;
v___y_4931_ = v___x_4959_;
goto v___jp_4929_;
}
}
}
}
v___jp_4929_:
{
lean_object* v___x_4933_; 
if (v_isShared_4921_ == 0)
{
lean_ctor_set(v___x_4920_, 1, v___y_4931_);
lean_ctor_set(v___x_4920_, 0, v_r_4930_);
v___x_4933_ = v___x_4920_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v_r_4930_);
lean_ctor_set(v_reuseFailAlloc_4934_, 1, v___y_4931_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
return v___x_4933_;
}
}
}
}
else
{
lean_object* v___x_4985_; lean_object* v___x_4987_; 
lean_dec(v_a_4917_);
lean_dec_ref(v___y_4896_);
v___x_4985_ = lean_box(0);
if (v_isShared_4921_ == 0)
{
lean_ctor_set(v___x_4920_, 1, v___x_4923_);
lean_ctor_set(v___x_4920_, 0, v___x_4985_);
v___x_4987_ = v___x_4920_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4988_; 
v_reuseFailAlloc_4988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4988_, 0, v___x_4985_);
lean_ctor_set(v_reuseFailAlloc_4988_, 1, v___x_4923_);
v___x_4987_ = v_reuseFailAlloc_4988_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
return v___x_4987_;
}
}
}
}
}
else
{
lean_object* v_a_4991_; lean_object* v_a_4992_; lean_object* v___x_4994_; uint8_t v_isShared_4995_; uint8_t v_isSharedCheck_5002_; 
lean_dec_ref(v___y_4896_);
v_a_4991_ = lean_ctor_get(v___x_4916_, 0);
v_a_4992_ = lean_ctor_get(v___x_4916_, 1);
v_isSharedCheck_5002_ = !lean_is_exclusive(v___x_4916_);
if (v_isSharedCheck_5002_ == 0)
{
v___x_4994_ = v___x_4916_;
v_isShared_4995_ = v_isSharedCheck_5002_;
goto v_resetjp_4993_;
}
else
{
lean_inc(v_a_4992_);
lean_inc(v_a_4991_);
lean_dec(v___x_4916_);
v___x_4994_ = lean_box(0);
v_isShared_4995_ = v_isSharedCheck_5002_;
goto v_resetjp_4993_;
}
v_resetjp_4993_:
{
lean_object* v___x_4997_; 
if (v_isShared_4913_ == 0)
{
lean_ctor_set(v___x_4912_, 0, v_a_4992_);
v___x_4997_ = v___x_4912_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v_a_4992_);
lean_ctor_set(v_reuseFailAlloc_5001_, 1, v_trace_4909_);
lean_ctor_set(v_reuseFailAlloc_5001_, 2, v_buildTime_4910_);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, sizeof(void*)*3, v_action_4907_);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, sizeof(void*)*3 + 1, v_wantsRebuild_4908_);
v___x_4997_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
lean_object* v___x_4999_; 
if (v_isShared_4995_ == 0)
{
lean_ctor_set(v___x_4994_, 1, v___x_4997_);
v___x_4999_ = v___x_4994_;
goto v_reusejp_4998_;
}
else
{
lean_object* v_reuseFailAlloc_5000_; 
v_reuseFailAlloc_5000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5000_, 0, v_a_4991_);
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
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object* v_exe_5004_, lean_object* v___y_5005_, lean_object* v_inputHash_5006_, lean_object* v_pkg_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_){
_start:
{
uint8_t v_exe_boxed_5014_; uint64_t v_inputHash_boxed_5015_; lean_object* v_res_5016_; 
v_exe_boxed_5014_ = lean_unbox(v_exe_5004_);
v_inputHash_boxed_5015_ = lean_unbox_uint64(v_inputHash_5006_);
lean_dec_ref(v_inputHash_5006_);
v_res_5016_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(v_exe_boxed_5014_, v___y_5005_, v_inputHash_boxed_5015_, v_pkg_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
lean_dec_ref(v_a_5011_);
lean_dec(v_a_5010_);
lean_dec(v_a_5009_);
lean_dec(v_a_5008_);
return v_res_5016_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(uint8_t v_exe_5017_, uint64_t v_hash_5018_, lean_object* v_val_5019_, lean_object* v_file_5020_, lean_object* v___x_5021_, lean_object* v_a_5022_, uint8_t v_restore_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_){
_start:
{
lean_object* v_a_5032_; lean_object* v___y_5036_; lean_object* v___y_5037_; lean_object* v___y_5038_; uint8_t v___y_5076_; uint8_t v___y_5077_; lean_object* v___y_5078_; lean_object* v___y_5079_; lean_object* v___y_5080_; lean_object* v___y_5081_; lean_object* v___y_5082_; lean_object* v___y_5083_; lean_object* v___y_5097_; lean_object* v___x_5154_; 
lean_inc_ref(v_val_5019_);
lean_inc_ref(v___y_5024_);
v___x_5154_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(v_exe_5017_, v___y_5024_, v_hash_5018_, v_val_5019_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
if (lean_obj_tag(v___x_5154_) == 0)
{
lean_object* v_a_5155_; 
v_a_5155_ = lean_ctor_get(v___x_5154_, 0);
lean_inc(v_a_5155_);
if (lean_obj_tag(v_a_5155_) == 1)
{
lean_dec_ref(v_a_5155_);
lean_dec_ref(v___y_5024_);
lean_dec_ref(v_val_5019_);
v___y_5097_ = v___x_5154_;
goto v___jp_5096_;
}
else
{
lean_object* v_a_5156_; lean_object* v___x_5157_; lean_object* v_a_5158_; 
lean_dec(v_a_5155_);
v_a_5156_ = lean_ctor_get(v___x_5154_, 1);
lean_inc(v_a_5156_);
lean_dec_ref(v___x_5154_);
lean_inc(v_a_5022_);
v___x_5157_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(v_exe_5017_, v___y_5024_, v_hash_5018_, v_a_5022_, v_val_5019_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v_a_5156_);
v_a_5158_ = lean_ctor_get(v___x_5157_, 0);
lean_inc(v_a_5158_);
if (lean_obj_tag(v_a_5158_) == 1)
{
lean_dec_ref(v_a_5158_);
v___y_5097_ = v___x_5157_;
goto v___jp_5096_;
}
else
{
lean_object* v_a_5159_; 
lean_dec(v_a_5158_);
lean_dec(v_a_5022_);
lean_dec_ref(v___x_5021_);
lean_dec_ref(v_file_5020_);
v_a_5159_ = lean_ctor_get(v___x_5157_, 1);
lean_inc(v_a_5159_);
lean_dec_ref(v___x_5157_);
v_a_5032_ = v_a_5159_;
goto v___jp_5031_;
}
}
}
else
{
lean_dec_ref(v___y_5024_);
lean_dec_ref(v_val_5019_);
v___y_5097_ = v___x_5154_;
goto v___jp_5096_;
}
v___jp_5031_:
{
lean_object* v___x_5033_; lean_object* v___x_5034_; 
v___x_5033_ = lean_box(0);
v___x_5034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5034_, 0, v___x_5033_);
lean_ctor_set(v___x_5034_, 1, v_a_5032_);
return v___x_5034_;
}
v___jp_5035_:
{
if (v_restore_5023_ == 0)
{
lean_object* v___x_5039_; 
lean_dec_ref(v___y_5037_);
lean_dec_ref(v_file_5020_);
v___x_5039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5039_, 0, v___y_5036_);
lean_ctor_set(v___x_5039_, 1, v___y_5038_);
return v___x_5039_;
}
else
{
lean_object* v_log_5040_; uint8_t v_action_5041_; uint8_t v_wantsRebuild_5042_; lean_object* v_trace_5043_; lean_object* v_buildTime_5044_; lean_object* v___x_5046_; uint8_t v_isShared_5047_; uint8_t v_isSharedCheck_5074_; 
lean_dec(v___y_5036_);
v_log_5040_ = lean_ctor_get(v___y_5038_, 0);
v_action_5041_ = lean_ctor_get_uint8(v___y_5038_, sizeof(void*)*3);
v_wantsRebuild_5042_ = lean_ctor_get_uint8(v___y_5038_, sizeof(void*)*3 + 1);
v_trace_5043_ = lean_ctor_get(v___y_5038_, 1);
v_buildTime_5044_ = lean_ctor_get(v___y_5038_, 2);
v_isSharedCheck_5074_ = !lean_is_exclusive(v___y_5038_);
if (v_isSharedCheck_5074_ == 0)
{
v___x_5046_ = v___y_5038_;
v_isShared_5047_ = v_isSharedCheck_5074_;
goto v_resetjp_5045_;
}
else
{
lean_inc(v_buildTime_5044_);
lean_inc(v_trace_5043_);
lean_inc(v_log_5040_);
lean_dec(v___y_5038_);
v___x_5046_ = lean_box(0);
v_isShared_5047_ = v_isSharedCheck_5074_;
goto v_resetjp_5045_;
}
v_resetjp_5045_:
{
lean_object* v___x_5048_; 
v___x_5048_ = l_Lake_restoreArtifact(v_file_5020_, v___y_5037_, v_exe_5017_, v_log_5040_);
if (lean_obj_tag(v___x_5048_) == 0)
{
lean_object* v_a_5049_; lean_object* v_a_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5061_; 
v_a_5049_ = lean_ctor_get(v___x_5048_, 0);
v_a_5050_ = lean_ctor_get(v___x_5048_, 1);
v_isSharedCheck_5061_ = !lean_is_exclusive(v___x_5048_);
if (v_isSharedCheck_5061_ == 0)
{
v___x_5052_ = v___x_5048_;
v_isShared_5053_ = v_isSharedCheck_5061_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_a_5050_);
lean_inc(v_a_5049_);
lean_dec(v___x_5048_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5061_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
lean_object* v___x_5055_; 
if (v_isShared_5047_ == 0)
{
lean_ctor_set(v___x_5046_, 0, v_a_5050_);
v___x_5055_ = v___x_5046_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5060_; 
v_reuseFailAlloc_5060_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5060_, 0, v_a_5050_);
lean_ctor_set(v_reuseFailAlloc_5060_, 1, v_trace_5043_);
lean_ctor_set(v_reuseFailAlloc_5060_, 2, v_buildTime_5044_);
lean_ctor_set_uint8(v_reuseFailAlloc_5060_, sizeof(void*)*3, v_action_5041_);
lean_ctor_set_uint8(v_reuseFailAlloc_5060_, sizeof(void*)*3 + 1, v_wantsRebuild_5042_);
v___x_5055_ = v_reuseFailAlloc_5060_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
lean_object* v___x_5056_; lean_object* v___x_5058_; 
v___x_5056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5056_, 0, v_a_5049_);
if (v_isShared_5053_ == 0)
{
lean_ctor_set(v___x_5052_, 1, v___x_5055_);
lean_ctor_set(v___x_5052_, 0, v___x_5056_);
v___x_5058_ = v___x_5052_;
goto v_reusejp_5057_;
}
else
{
lean_object* v_reuseFailAlloc_5059_; 
v_reuseFailAlloc_5059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5059_, 0, v___x_5056_);
lean_ctor_set(v_reuseFailAlloc_5059_, 1, v___x_5055_);
v___x_5058_ = v_reuseFailAlloc_5059_;
goto v_reusejp_5057_;
}
v_reusejp_5057_:
{
return v___x_5058_;
}
}
}
}
else
{
lean_object* v_a_5062_; lean_object* v_a_5063_; lean_object* v___x_5065_; uint8_t v_isShared_5066_; uint8_t v_isSharedCheck_5073_; 
v_a_5062_ = lean_ctor_get(v___x_5048_, 0);
v_a_5063_ = lean_ctor_get(v___x_5048_, 1);
v_isSharedCheck_5073_ = !lean_is_exclusive(v___x_5048_);
if (v_isSharedCheck_5073_ == 0)
{
v___x_5065_ = v___x_5048_;
v_isShared_5066_ = v_isSharedCheck_5073_;
goto v_resetjp_5064_;
}
else
{
lean_inc(v_a_5063_);
lean_inc(v_a_5062_);
lean_dec(v___x_5048_);
v___x_5065_ = lean_box(0);
v_isShared_5066_ = v_isSharedCheck_5073_;
goto v_resetjp_5064_;
}
v_resetjp_5064_:
{
lean_object* v___x_5068_; 
if (v_isShared_5047_ == 0)
{
lean_ctor_set(v___x_5046_, 0, v_a_5063_);
v___x_5068_ = v___x_5046_;
goto v_reusejp_5067_;
}
else
{
lean_object* v_reuseFailAlloc_5072_; 
v_reuseFailAlloc_5072_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5072_, 0, v_a_5063_);
lean_ctor_set(v_reuseFailAlloc_5072_, 1, v_trace_5043_);
lean_ctor_set(v_reuseFailAlloc_5072_, 2, v_buildTime_5044_);
lean_ctor_set_uint8(v_reuseFailAlloc_5072_, sizeof(void*)*3, v_action_5041_);
lean_ctor_set_uint8(v_reuseFailAlloc_5072_, sizeof(void*)*3 + 1, v_wantsRebuild_5042_);
v___x_5068_ = v_reuseFailAlloc_5072_;
goto v_reusejp_5067_;
}
v_reusejp_5067_:
{
lean_object* v___x_5070_; 
if (v_isShared_5066_ == 0)
{
lean_ctor_set(v___x_5065_, 1, v___x_5068_);
v___x_5070_ = v___x_5065_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_a_5062_);
lean_ctor_set(v_reuseFailAlloc_5071_, 1, v___x_5068_);
v___x_5070_ = v_reuseFailAlloc_5071_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
return v___x_5070_;
}
}
}
}
}
}
}
v___jp_5075_:
{
lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; 
v___x_5084_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5084_, 0, v___y_5083_);
v___x_5085_ = l_Lake_BuildMetadata_ofFetch(v_hash_5018_, v___x_5084_);
v___x_5086_ = l_Lake_BuildMetadata_writeFile(v___x_5021_, v___x_5085_);
if (lean_obj_tag(v___x_5086_) == 0)
{
lean_object* v___x_5087_; 
lean_dec_ref(v___x_5086_);
v___x_5087_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5087_, 0, v___y_5078_);
lean_ctor_set(v___x_5087_, 1, v___y_5080_);
lean_ctor_set(v___x_5087_, 2, v___y_5082_);
lean_ctor_set_uint8(v___x_5087_, sizeof(void*)*3, v___y_5077_);
lean_ctor_set_uint8(v___x_5087_, sizeof(void*)*3 + 1, v___y_5076_);
v___y_5036_ = v___y_5079_;
v___y_5037_ = v___y_5081_;
v___y_5038_ = v___x_5087_;
goto v___jp_5035_;
}
else
{
lean_object* v_a_5088_; lean_object* v___x_5089_; uint8_t v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; 
lean_dec_ref(v___y_5081_);
lean_dec(v___y_5079_);
lean_dec_ref(v_file_5020_);
v_a_5088_ = lean_ctor_get(v___x_5086_, 0);
lean_inc(v_a_5088_);
lean_dec_ref(v___x_5086_);
v___x_5089_ = lean_io_error_to_string(v_a_5088_);
v___x_5090_ = 3;
v___x_5091_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5091_, 0, v___x_5089_);
lean_ctor_set_uint8(v___x_5091_, sizeof(void*)*1, v___x_5090_);
v___x_5092_ = lean_array_get_size(v___y_5078_);
v___x_5093_ = lean_array_push(v___y_5078_, v___x_5091_);
v___x_5094_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5094_, 0, v___x_5093_);
lean_ctor_set(v___x_5094_, 1, v___y_5080_);
lean_ctor_set(v___x_5094_, 2, v___y_5082_);
lean_ctor_set_uint8(v___x_5094_, sizeof(void*)*3, v___y_5077_);
lean_ctor_set_uint8(v___x_5094_, sizeof(void*)*3 + 1, v___y_5076_);
v___x_5095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5095_, 0, v___x_5092_);
lean_ctor_set(v___x_5095_, 1, v___x_5094_);
return v___x_5095_;
}
}
v___jp_5096_:
{
if (lean_obj_tag(v___y_5097_) == 0)
{
lean_object* v_a_5098_; 
v_a_5098_ = lean_ctor_get(v___y_5097_, 0);
if (lean_obj_tag(v_a_5098_) == 1)
{
lean_object* v_a_5099_; lean_object* v_val_5100_; lean_object* v___x_5101_; 
lean_inc_ref(v_a_5098_);
v_a_5099_ = lean_ctor_get(v___y_5097_, 1);
lean_inc(v_a_5099_);
lean_dec_ref(v___y_5097_);
v_val_5100_ = lean_ctor_get(v_a_5098_, 0);
lean_inc(v_val_5100_);
v___x_5101_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_hash_5018_, v_a_5022_, v_a_5099_);
lean_dec(v_a_5022_);
if (lean_obj_tag(v___x_5101_) == 0)
{
lean_object* v_a_5102_; uint8_t v___x_5103_; 
v_a_5102_ = lean_ctor_get(v___x_5101_, 0);
lean_inc(v_a_5102_);
v___x_5103_ = lean_unbox(v_a_5102_);
lean_dec(v_a_5102_);
if (v___x_5103_ == 0)
{
lean_object* v_a_5104_; lean_object* v___x_5106_; uint8_t v_isShared_5107_; uint8_t v_isSharedCheck_5141_; 
v_a_5104_ = lean_ctor_get(v___x_5101_, 1);
v_isSharedCheck_5141_ = !lean_is_exclusive(v___x_5101_);
if (v_isSharedCheck_5141_ == 0)
{
lean_object* v_unused_5142_; 
v_unused_5142_ = lean_ctor_get(v___x_5101_, 0);
lean_dec(v_unused_5142_);
v___x_5106_ = v___x_5101_;
v_isShared_5107_ = v_isSharedCheck_5141_;
goto v_resetjp_5105_;
}
else
{
lean_inc(v_a_5104_);
lean_dec(v___x_5101_);
v___x_5106_ = lean_box(0);
v_isShared_5107_ = v_isSharedCheck_5141_;
goto v_resetjp_5105_;
}
v_resetjp_5105_:
{
lean_object* v_log_5108_; uint8_t v_action_5109_; uint8_t v_wantsRebuild_5110_; lean_object* v_trace_5111_; lean_object* v_buildTime_5112_; lean_object* v___x_5114_; uint8_t v_isShared_5115_; uint8_t v_isSharedCheck_5140_; 
v_log_5108_ = lean_ctor_get(v_a_5104_, 0);
v_action_5109_ = lean_ctor_get_uint8(v_a_5104_, sizeof(void*)*3);
v_wantsRebuild_5110_ = lean_ctor_get_uint8(v_a_5104_, sizeof(void*)*3 + 1);
v_trace_5111_ = lean_ctor_get(v_a_5104_, 1);
v_buildTime_5112_ = lean_ctor_get(v_a_5104_, 2);
v_isSharedCheck_5140_ = !lean_is_exclusive(v_a_5104_);
if (v_isSharedCheck_5140_ == 0)
{
v___x_5114_ = v_a_5104_;
v_isShared_5115_ = v_isSharedCheck_5140_;
goto v_resetjp_5113_;
}
else
{
lean_inc(v_buildTime_5112_);
lean_inc(v_trace_5111_);
lean_inc(v_log_5108_);
lean_dec(v_a_5104_);
v___x_5114_ = lean_box(0);
v_isShared_5115_ = v_isSharedCheck_5140_;
goto v_resetjp_5113_;
}
v_resetjp_5113_:
{
lean_object* v___x_5116_; 
v___x_5116_ = l_Lake_removeFileIfExists(v_file_5020_);
if (lean_obj_tag(v___x_5116_) == 0)
{
lean_object* v_descr_5117_; uint64_t v_hash_5118_; lean_object* v_ext_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; uint8_t v___x_5122_; 
lean_dec_ref(v___x_5116_);
lean_del_object(v___x_5114_);
lean_del_object(v___x_5106_);
v_descr_5117_ = lean_ctor_get(v_val_5100_, 0);
v_hash_5118_ = lean_ctor_get_uint64(v_descr_5117_, sizeof(void*)*1);
v_ext_5119_ = lean_ctor_get(v_descr_5117_, 0);
v___x_5120_ = lean_string_utf8_byte_size(v_ext_5119_);
v___x_5121_ = lean_unsigned_to_nat(0u);
v___x_5122_ = lean_nat_dec_eq(v___x_5120_, v___x_5121_);
if (v___x_5122_ == 0)
{
lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; 
v___x_5123_ = l_Lake_lowerHexUInt64(v_hash_5118_);
v___x_5124_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5125_ = lean_string_append(v___x_5123_, v___x_5124_);
v___x_5126_ = lean_string_append(v___x_5125_, v_ext_5119_);
v___y_5076_ = v_wantsRebuild_5110_;
v___y_5077_ = v_action_5109_;
v___y_5078_ = v_log_5108_;
v___y_5079_ = v_a_5098_;
v___y_5080_ = v_trace_5111_;
v___y_5081_ = v_val_5100_;
v___y_5082_ = v_buildTime_5112_;
v___y_5083_ = v___x_5126_;
goto v___jp_5075_;
}
else
{
lean_object* v___x_5127_; 
v___x_5127_ = l_Lake_lowerHexUInt64(v_hash_5118_);
v___y_5076_ = v_wantsRebuild_5110_;
v___y_5077_ = v_action_5109_;
v___y_5078_ = v_log_5108_;
v___y_5079_ = v_a_5098_;
v___y_5080_ = v_trace_5111_;
v___y_5081_ = v_val_5100_;
v___y_5082_ = v_buildTime_5112_;
v___y_5083_ = v___x_5127_;
goto v___jp_5075_;
}
}
else
{
lean_object* v_a_5128_; lean_object* v___x_5129_; uint8_t v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5135_; 
lean_dec(v_val_5100_);
lean_dec_ref(v_a_5098_);
lean_dec_ref(v___x_5021_);
lean_dec_ref(v_file_5020_);
v_a_5128_ = lean_ctor_get(v___x_5116_, 0);
lean_inc(v_a_5128_);
lean_dec_ref(v___x_5116_);
v___x_5129_ = lean_io_error_to_string(v_a_5128_);
v___x_5130_ = 3;
v___x_5131_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5131_, 0, v___x_5129_);
lean_ctor_set_uint8(v___x_5131_, sizeof(void*)*1, v___x_5130_);
v___x_5132_ = lean_array_get_size(v_log_5108_);
v___x_5133_ = lean_array_push(v_log_5108_, v___x_5131_);
if (v_isShared_5115_ == 0)
{
lean_ctor_set(v___x_5114_, 0, v___x_5133_);
v___x_5135_ = v___x_5114_;
goto v_reusejp_5134_;
}
else
{
lean_object* v_reuseFailAlloc_5139_; 
v_reuseFailAlloc_5139_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5139_, 0, v___x_5133_);
lean_ctor_set(v_reuseFailAlloc_5139_, 1, v_trace_5111_);
lean_ctor_set(v_reuseFailAlloc_5139_, 2, v_buildTime_5112_);
lean_ctor_set_uint8(v_reuseFailAlloc_5139_, sizeof(void*)*3, v_action_5109_);
lean_ctor_set_uint8(v_reuseFailAlloc_5139_, sizeof(void*)*3 + 1, v_wantsRebuild_5110_);
v___x_5135_ = v_reuseFailAlloc_5139_;
goto v_reusejp_5134_;
}
v_reusejp_5134_:
{
lean_object* v___x_5137_; 
if (v_isShared_5107_ == 0)
{
lean_ctor_set_tag(v___x_5106_, 1);
lean_ctor_set(v___x_5106_, 1, v___x_5135_);
lean_ctor_set(v___x_5106_, 0, v___x_5132_);
v___x_5137_ = v___x_5106_;
goto v_reusejp_5136_;
}
else
{
lean_object* v_reuseFailAlloc_5138_; 
v_reuseFailAlloc_5138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5138_, 0, v___x_5132_);
lean_ctor_set(v_reuseFailAlloc_5138_, 1, v___x_5135_);
v___x_5137_ = v_reuseFailAlloc_5138_;
goto v_reusejp_5136_;
}
v_reusejp_5136_:
{
return v___x_5137_;
}
}
}
}
}
}
else
{
lean_object* v_a_5143_; 
lean_dec_ref(v___x_5021_);
v_a_5143_ = lean_ctor_get(v___x_5101_, 1);
lean_inc(v_a_5143_);
lean_dec_ref(v___x_5101_);
v___y_5036_ = v_a_5098_;
v___y_5037_ = v_val_5100_;
v___y_5038_ = v_a_5143_;
goto v___jp_5035_;
}
}
else
{
lean_object* v_a_5144_; lean_object* v_a_5145_; lean_object* v___x_5147_; uint8_t v_isShared_5148_; uint8_t v_isSharedCheck_5152_; 
lean_dec(v_val_5100_);
lean_dec_ref(v_a_5098_);
lean_dec_ref(v___x_5021_);
lean_dec_ref(v_file_5020_);
v_a_5144_ = lean_ctor_get(v___x_5101_, 0);
v_a_5145_ = lean_ctor_get(v___x_5101_, 1);
v_isSharedCheck_5152_ = !lean_is_exclusive(v___x_5101_);
if (v_isSharedCheck_5152_ == 0)
{
v___x_5147_ = v___x_5101_;
v_isShared_5148_ = v_isSharedCheck_5152_;
goto v_resetjp_5146_;
}
else
{
lean_inc(v_a_5145_);
lean_inc(v_a_5144_);
lean_dec(v___x_5101_);
v___x_5147_ = lean_box(0);
v_isShared_5148_ = v_isSharedCheck_5152_;
goto v_resetjp_5146_;
}
v_resetjp_5146_:
{
lean_object* v___x_5150_; 
if (v_isShared_5148_ == 0)
{
v___x_5150_ = v___x_5147_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5151_; 
v_reuseFailAlloc_5151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5151_, 0, v_a_5144_);
lean_ctor_set(v_reuseFailAlloc_5151_, 1, v_a_5145_);
v___x_5150_ = v_reuseFailAlloc_5151_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
return v___x_5150_;
}
}
}
}
else
{
lean_object* v_a_5153_; 
lean_dec(v_a_5022_);
lean_dec_ref(v___x_5021_);
lean_dec_ref(v_file_5020_);
v_a_5153_ = lean_ctor_get(v___y_5097_, 1);
lean_inc(v_a_5153_);
lean_dec_ref(v___y_5097_);
v_a_5032_ = v_a_5153_;
goto v___jp_5031_;
}
}
else
{
lean_dec(v_a_5022_);
lean_dec_ref(v___x_5021_);
lean_dec_ref(v_file_5020_);
return v___y_5097_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object* v_exe_5160_, lean_object* v_hash_5161_, lean_object* v_val_5162_, lean_object* v_file_5163_, lean_object* v___x_5164_, lean_object* v_a_5165_, lean_object* v_restore_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_){
_start:
{
uint8_t v_exe_boxed_5174_; uint64_t v_hash_boxed_5175_; uint8_t v_restore_boxed_5176_; lean_object* v_res_5177_; 
v_exe_boxed_5174_ = lean_unbox(v_exe_5160_);
v_hash_boxed_5175_ = lean_unbox_uint64(v_hash_5161_);
lean_dec_ref(v_hash_5161_);
v_restore_boxed_5176_ = lean_unbox(v_restore_5166_);
v_res_5177_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_boxed_5174_, v_hash_boxed_5175_, v_val_5162_, v_file_5163_, v___x_5164_, v_a_5165_, v_restore_boxed_5176_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_);
lean_dec_ref(v___y_5171_);
lean_dec(v___y_5170_);
lean_dec(v___y_5169_);
lean_dec(v___y_5168_);
return v_res_5177_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1(uint8_t v_a_5178_, lean_object* v_file_5179_, lean_object* v_ext_5180_, uint8_t v_text_5181_, uint8_t v_exe_5182_, uint8_t v___y_5183_, lean_object* v_val_5184_, uint64_t v_hash_5185_, lean_object* v_____r_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_){
_start:
{
uint8_t v___x_5194_; uint8_t v___x_5195_; 
v___x_5194_ = 1;
v___x_5195_ = l_Lake_instDecidableEqOutputStatus(v_a_5178_, v___x_5194_);
if (v___x_5195_ == 0)
{
lean_object* v_toContext_5196_; lean_object* v_log_5197_; uint8_t v_action_5198_; uint8_t v_wantsRebuild_5199_; lean_object* v_trace_5200_; lean_object* v_buildTime_5201_; lean_object* v_lakeCache_5202_; lean_object* v___x_5203_; 
v_toContext_5196_ = lean_ctor_get(v___y_5191_, 1);
v_log_5197_ = lean_ctor_get(v___y_5192_, 0);
v_action_5198_ = lean_ctor_get_uint8(v___y_5192_, sizeof(void*)*3);
v_wantsRebuild_5199_ = lean_ctor_get_uint8(v___y_5192_, sizeof(void*)*3 + 1);
v_trace_5200_ = lean_ctor_get(v___y_5192_, 1);
v_buildTime_5201_ = lean_ctor_get(v___y_5192_, 2);
v_lakeCache_5202_ = lean_ctor_get(v_toContext_5196_, 2);
lean_inc_ref(v_lakeCache_5202_);
v___x_5203_ = l_Lake_Cache_saveArtifact(v_lakeCache_5202_, v_file_5179_, v_ext_5180_, v_text_5181_, v_exe_5182_, v___y_5183_);
if (lean_obj_tag(v___x_5203_) == 0)
{
lean_object* v_a_5204_; lean_object* v___x_5206_; uint8_t v_isShared_5207_; uint8_t v_isSharedCheck_5245_; 
v_a_5204_ = lean_ctor_get(v___x_5203_, 0);
v_isSharedCheck_5245_ = !lean_is_exclusive(v___x_5203_);
if (v_isSharedCheck_5245_ == 0)
{
v___x_5206_ = v___x_5203_;
v_isShared_5207_ = v_isSharedCheck_5245_;
goto v_resetjp_5205_;
}
else
{
lean_inc(v_a_5204_);
lean_dec(v___x_5203_);
v___x_5206_ = lean_box(0);
v_isShared_5207_ = v_isSharedCheck_5245_;
goto v_resetjp_5205_;
}
v_resetjp_5205_:
{
lean_object* v_descr_5208_; uint64_t v_hash_5209_; lean_object* v_ext_5210_; lean_object* v___x_5211_; lean_object* v___y_5213_; lean_object* v___x_5237_; lean_object* v___x_5238_; uint8_t v___x_5239_; 
v_descr_5208_ = lean_ctor_get(v_a_5204_, 0);
v_hash_5209_ = lean_ctor_get_uint64(v_descr_5208_, sizeof(void*)*1);
v_ext_5210_ = lean_ctor_get(v_descr_5208_, 0);
v___x_5211_ = l_Lake_Package_cacheScope(v_val_5184_);
v___x_5237_ = lean_string_utf8_byte_size(v_ext_5210_);
v___x_5238_ = lean_unsigned_to_nat(0u);
v___x_5239_ = lean_nat_dec_eq(v___x_5237_, v___x_5238_);
if (v___x_5239_ == 0)
{
lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; 
v___x_5240_ = l_Lake_lowerHexUInt64(v_hash_5209_);
v___x_5241_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5242_ = lean_string_append(v___x_5240_, v___x_5241_);
v___x_5243_ = lean_string_append(v___x_5242_, v_ext_5210_);
v___y_5213_ = v___x_5243_;
goto v___jp_5212_;
}
else
{
lean_object* v___x_5244_; 
v___x_5244_ = l_Lake_lowerHexUInt64(v_hash_5209_);
v___y_5213_ = v___x_5244_;
goto v___jp_5212_;
}
v___jp_5212_:
{
lean_object* v___x_5215_; 
if (v_isShared_5207_ == 0)
{
lean_ctor_set_tag(v___x_5206_, 3);
lean_ctor_set(v___x_5206_, 0, v___y_5213_);
v___x_5215_ = v___x_5206_;
goto v_reusejp_5214_;
}
else
{
lean_object* v_reuseFailAlloc_5236_; 
v_reuseFailAlloc_5236_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5236_, 0, v___y_5213_);
v___x_5215_ = v_reuseFailAlloc_5236_;
goto v_reusejp_5214_;
}
v_reusejp_5214_:
{
lean_object* v___x_5216_; lean_object* v___x_5217_; 
v___x_5216_ = lean_box(0);
lean_inc_ref(v_lakeCache_5202_);
v___x_5217_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_5202_, v___x_5211_, v_hash_5185_, v___x_5215_, v___x_5216_, v___x_5216_);
if (lean_obj_tag(v___x_5217_) == 0)
{
lean_object* v___x_5218_; 
lean_dec_ref(v___x_5217_);
v___x_5218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5218_, 0, v_a_5204_);
lean_ctor_set(v___x_5218_, 1, v___y_5192_);
return v___x_5218_;
}
else
{
lean_object* v___x_5220_; uint8_t v_isShared_5221_; uint8_t v_isSharedCheck_5232_; 
lean_inc(v_buildTime_5201_);
lean_inc_ref(v_trace_5200_);
lean_inc_ref(v_log_5197_);
lean_dec(v_a_5204_);
v_isSharedCheck_5232_ = !lean_is_exclusive(v___y_5192_);
if (v_isSharedCheck_5232_ == 0)
{
lean_object* v_unused_5233_; lean_object* v_unused_5234_; lean_object* v_unused_5235_; 
v_unused_5233_ = lean_ctor_get(v___y_5192_, 2);
lean_dec(v_unused_5233_);
v_unused_5234_ = lean_ctor_get(v___y_5192_, 1);
lean_dec(v_unused_5234_);
v_unused_5235_ = lean_ctor_get(v___y_5192_, 0);
lean_dec(v_unused_5235_);
v___x_5220_ = v___y_5192_;
v_isShared_5221_ = v_isSharedCheck_5232_;
goto v_resetjp_5219_;
}
else
{
lean_dec(v___y_5192_);
v___x_5220_ = lean_box(0);
v_isShared_5221_ = v_isSharedCheck_5232_;
goto v_resetjp_5219_;
}
v_resetjp_5219_:
{
lean_object* v_a_5222_; lean_object* v___x_5223_; uint8_t v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5229_; 
v_a_5222_ = lean_ctor_get(v___x_5217_, 0);
lean_inc(v_a_5222_);
lean_dec_ref(v___x_5217_);
v___x_5223_ = lean_io_error_to_string(v_a_5222_);
v___x_5224_ = 3;
v___x_5225_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5225_, 0, v___x_5223_);
lean_ctor_set_uint8(v___x_5225_, sizeof(void*)*1, v___x_5224_);
v___x_5226_ = lean_array_get_size(v_log_5197_);
v___x_5227_ = lean_array_push(v_log_5197_, v___x_5225_);
if (v_isShared_5221_ == 0)
{
lean_ctor_set(v___x_5220_, 0, v___x_5227_);
v___x_5229_ = v___x_5220_;
goto v_reusejp_5228_;
}
else
{
lean_object* v_reuseFailAlloc_5231_; 
v_reuseFailAlloc_5231_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5231_, 0, v___x_5227_);
lean_ctor_set(v_reuseFailAlloc_5231_, 1, v_trace_5200_);
lean_ctor_set(v_reuseFailAlloc_5231_, 2, v_buildTime_5201_);
lean_ctor_set_uint8(v_reuseFailAlloc_5231_, sizeof(void*)*3, v_action_5198_);
lean_ctor_set_uint8(v_reuseFailAlloc_5231_, sizeof(void*)*3 + 1, v_wantsRebuild_5199_);
v___x_5229_ = v_reuseFailAlloc_5231_;
goto v_reusejp_5228_;
}
v_reusejp_5228_:
{
lean_object* v___x_5230_; 
v___x_5230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5230_, 0, v___x_5226_);
lean_ctor_set(v___x_5230_, 1, v___x_5229_);
return v___x_5230_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5247_; uint8_t v_isShared_5248_; uint8_t v_isSharedCheck_5259_; 
lean_inc(v_buildTime_5201_);
lean_inc_ref(v_trace_5200_);
lean_inc_ref(v_log_5197_);
lean_dec_ref(v_val_5184_);
v_isSharedCheck_5259_ = !lean_is_exclusive(v___y_5192_);
if (v_isSharedCheck_5259_ == 0)
{
lean_object* v_unused_5260_; lean_object* v_unused_5261_; lean_object* v_unused_5262_; 
v_unused_5260_ = lean_ctor_get(v___y_5192_, 2);
lean_dec(v_unused_5260_);
v_unused_5261_ = lean_ctor_get(v___y_5192_, 1);
lean_dec(v_unused_5261_);
v_unused_5262_ = lean_ctor_get(v___y_5192_, 0);
lean_dec(v_unused_5262_);
v___x_5247_ = v___y_5192_;
v_isShared_5248_ = v_isSharedCheck_5259_;
goto v_resetjp_5246_;
}
else
{
lean_dec(v___y_5192_);
v___x_5247_ = lean_box(0);
v_isShared_5248_ = v_isSharedCheck_5259_;
goto v_resetjp_5246_;
}
v_resetjp_5246_:
{
lean_object* v_a_5249_; lean_object* v___x_5250_; uint8_t v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5256_; 
v_a_5249_ = lean_ctor_get(v___x_5203_, 0);
lean_inc(v_a_5249_);
lean_dec_ref(v___x_5203_);
v___x_5250_ = lean_io_error_to_string(v_a_5249_);
v___x_5251_ = 3;
v___x_5252_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5252_, 0, v___x_5250_);
lean_ctor_set_uint8(v___x_5252_, sizeof(void*)*1, v___x_5251_);
v___x_5253_ = lean_array_get_size(v_log_5197_);
v___x_5254_ = lean_array_push(v_log_5197_, v___x_5252_);
if (v_isShared_5248_ == 0)
{
lean_ctor_set(v___x_5247_, 0, v___x_5254_);
v___x_5256_ = v___x_5247_;
goto v_reusejp_5255_;
}
else
{
lean_object* v_reuseFailAlloc_5258_; 
v_reuseFailAlloc_5258_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5258_, 0, v___x_5254_);
lean_ctor_set(v_reuseFailAlloc_5258_, 1, v_trace_5200_);
lean_ctor_set(v_reuseFailAlloc_5258_, 2, v_buildTime_5201_);
lean_ctor_set_uint8(v_reuseFailAlloc_5258_, sizeof(void*)*3, v_action_5198_);
lean_ctor_set_uint8(v_reuseFailAlloc_5258_, sizeof(void*)*3 + 1, v_wantsRebuild_5199_);
v___x_5256_ = v_reuseFailAlloc_5258_;
goto v_reusejp_5255_;
}
v_reusejp_5255_:
{
lean_object* v___x_5257_; 
v___x_5257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5257_, 0, v___x_5253_);
lean_ctor_set(v___x_5257_, 1, v___x_5256_);
return v___x_5257_;
}
}
}
}
else
{
lean_object* v___x_5263_; 
lean_dec_ref(v_val_5184_);
v___x_5263_ = l_Lake_computeArtifact___redArg(v_file_5179_, v_ext_5180_, v_text_5181_, v___y_5191_, v___y_5192_);
return v___x_5263_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___boxed(lean_object* v_a_5264_, lean_object* v_file_5265_, lean_object* v_ext_5266_, lean_object* v_text_5267_, lean_object* v_exe_5268_, lean_object* v___y_5269_, lean_object* v_val_5270_, lean_object* v_hash_5271_, lean_object* v_____r_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_){
_start:
{
uint8_t v_a_297811__boxed_5280_; uint8_t v_text_boxed_5281_; uint8_t v_exe_boxed_5282_; uint8_t v___y_297812__boxed_5283_; uint64_t v_hash_boxed_5284_; lean_object* v_res_5285_; 
v_a_297811__boxed_5280_ = lean_unbox(v_a_5264_);
v_text_boxed_5281_ = lean_unbox(v_text_5267_);
v_exe_boxed_5282_ = lean_unbox(v_exe_5268_);
v___y_297812__boxed_5283_ = lean_unbox(v___y_5269_);
v_hash_boxed_5284_ = lean_unbox_uint64(v_hash_5271_);
lean_dec_ref(v_hash_5271_);
v_res_5285_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v_a_297811__boxed_5280_, v_file_5265_, v_ext_5266_, v_text_boxed_5281_, v_exe_boxed_5282_, v___y_297812__boxed_5283_, v_val_5270_, v_hash_boxed_5284_, v_____r_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_);
lean_dec_ref(v___y_5277_);
lean_dec(v___y_5276_);
lean_dec(v___y_5275_);
lean_dec(v___y_5274_);
lean_dec_ref(v___y_5273_);
return v_res_5285_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object* v_file_5286_, lean_object* v_build_5287_, uint8_t v_text_5288_, lean_object* v_ext_5289_, uint8_t v_restore_5290_, uint8_t v_exe_5291_, uint8_t v_platformIndependent_5292_, lean_object* v_a_5293_, lean_object* v_a_5294_, lean_object* v_a_5295_, lean_object* v_a_5296_, lean_object* v_a_5297_, lean_object* v_a_5298_){
_start:
{
lean_object* v_log_5300_; uint8_t v_action_5301_; uint8_t v_wantsRebuild_5302_; lean_object* v_trace_5303_; lean_object* v_buildTime_5304_; lean_object* v___x_5306_; uint8_t v_isShared_5307_; uint8_t v_isSharedCheck_5559_; 
v_log_5300_ = lean_ctor_get(v_a_5298_, 0);
v_action_5301_ = lean_ctor_get_uint8(v_a_5298_, sizeof(void*)*3);
v_wantsRebuild_5302_ = lean_ctor_get_uint8(v_a_5298_, sizeof(void*)*3 + 1);
v_trace_5303_ = lean_ctor_get(v_a_5298_, 1);
v_buildTime_5304_ = lean_ctor_get(v_a_5298_, 2);
v_isSharedCheck_5559_ = !lean_is_exclusive(v_a_5298_);
if (v_isSharedCheck_5559_ == 0)
{
v___x_5306_ = v_a_5298_;
v_isShared_5307_ = v_isSharedCheck_5559_;
goto v_resetjp_5305_;
}
else
{
lean_inc(v_buildTime_5304_);
lean_inc(v_trace_5303_);
lean_inc(v_log_5300_);
lean_dec(v_a_5298_);
v___x_5306_ = lean_box(0);
v_isShared_5307_ = v_isSharedCheck_5559_;
goto v_resetjp_5305_;
}
v_resetjp_5305_:
{
lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v_art_5311_; lean_object* v___y_5312_; lean_object* v___y_5328_; lean_object* v_log_5329_; uint8_t v_action_5330_; uint8_t v_wantsRebuild_5331_; lean_object* v_buildTime_5332_; lean_object* v___x_5338_; 
v___x_5308_ = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(v_file_5286_);
v___x_5309_ = lean_string_append(v_file_5286_, v___x_5308_);
lean_inc_ref(v___x_5309_);
v___x_5338_ = l_Lake_readTraceFile(v___x_5309_, v_log_5300_);
if (lean_obj_tag(v___x_5338_) == 0)
{
if (lean_obj_tag(v_a_5294_) == 1)
{
lean_object* v_a_5339_; lean_object* v_a_5340_; lean_object* v_val_5341_; uint64_t v_hash_5342_; lean_object* v_mtime_5343_; lean_object* v___y_5345_; lean_object* v___y_5346_; lean_object* v___y_5347_; lean_object* v___y_5348_; lean_object* v___y_5349_; uint8_t v___y_5350_; lean_object* v___y_5351_; uint8_t v___y_5352_; lean_object* v___y_5353_; lean_object* v_wsIdx_5357_; lean_object* v_config_5358_; lean_object* v_a_5360_; lean_object* v_a_5361_; lean_object* v___y_5391_; lean_object* v_enableArtifactCache_x3f_5394_; lean_object* v_restoreAllArtifacts_x3f_5395_; uint8_t v___y_5397_; lean_object* v_a_5398_; uint8_t v___y_5415_; uint8_t v_a_5416_; lean_object* v_a_5417_; lean_object* v_a_5420_; lean_object* v___y_5452_; uint8_t v___y_5453_; uint8_t v___y_5492_; uint8_t v_a_5493_; lean_object* v_a_5494_; uint8_t v_a_5496_; lean_object* v_a_5497_; lean_object* v___x_5509_; 
v_a_5339_ = lean_ctor_get(v___x_5338_, 0);
lean_inc(v_a_5339_);
v_a_5340_ = lean_ctor_get(v___x_5338_, 1);
lean_inc(v_a_5340_);
lean_dec_ref(v___x_5338_);
v_val_5341_ = lean_ctor_get(v_a_5294_, 0);
v_hash_5342_ = lean_ctor_get_uint64(v_trace_5303_, sizeof(void*)*3);
v_mtime_5343_ = lean_ctor_get(v_trace_5303_, 2);
v_wsIdx_5357_ = lean_ctor_get(v_val_5341_, 0);
v_config_5358_ = lean_ctor_get(v_val_5341_, 6);
v_enableArtifactCache_x3f_5394_ = lean_ctor_get(v_config_5358_, 24);
v_restoreAllArtifacts_x3f_5395_ = lean_ctor_get(v_config_5358_, 25);
lean_inc_ref(v_trace_5303_);
v___x_5509_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5509_, 0, v_a_5340_);
lean_ctor_set(v___x_5509_, 1, v_trace_5303_);
lean_ctor_set(v___x_5509_, 2, v_buildTime_5304_);
lean_ctor_set_uint8(v___x_5509_, sizeof(void*)*3, v_action_5301_);
lean_ctor_set_uint8(v___x_5509_, sizeof(void*)*3 + 1, v_wantsRebuild_5302_);
if (lean_obj_tag(v_enableArtifactCache_x3f_5394_) == 0)
{
lean_object* v_toContext_5510_; lean_object* v_lakeEnv_5511_; lean_object* v_enableArtifactCache_x3f_5512_; 
v_toContext_5510_ = lean_ctor_get(v_a_5297_, 1);
v_lakeEnv_5511_ = lean_ctor_get(v_toContext_5510_, 0);
v_enableArtifactCache_x3f_5512_ = lean_ctor_get(v_lakeEnv_5511_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_5512_) == 0)
{
lean_object* v_packages_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; lean_object* v_config_5516_; lean_object* v_enableArtifactCache_x3f_5517_; 
v_packages_5513_ = lean_ctor_get(v_toContext_5510_, 4);
v___x_5514_ = lean_unsigned_to_nat(0u);
v___x_5515_ = lean_array_fget_borrowed(v_packages_5513_, v___x_5514_);
v_config_5516_ = lean_ctor_get(v___x_5515_, 6);
v_enableArtifactCache_x3f_5517_ = lean_ctor_get(v_config_5516_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_5517_) == 0)
{
v_a_5420_ = v___x_5509_;
goto v___jp_5419_;
}
else
{
lean_object* v_val_5518_; uint8_t v___x_5519_; 
v_val_5518_ = lean_ctor_get(v_enableArtifactCache_x3f_5517_, 0);
v___x_5519_ = lean_unbox(v_val_5518_);
v_a_5496_ = v___x_5519_;
v_a_5497_ = v___x_5509_;
goto v___jp_5495_;
}
}
else
{
lean_object* v_val_5520_; uint8_t v___x_5521_; 
v_val_5520_ = lean_ctor_get(v_enableArtifactCache_x3f_5512_, 0);
v___x_5521_ = lean_unbox(v_val_5520_);
v_a_5496_ = v___x_5521_;
v_a_5497_ = v___x_5509_;
goto v___jp_5495_;
}
}
else
{
lean_object* v_val_5522_; uint8_t v___x_5523_; 
v_val_5522_ = lean_ctor_get(v_enableArtifactCache_x3f_5394_, 0);
v___x_5523_ = lean_unbox(v_val_5522_);
v_a_5496_ = v___x_5523_;
v_a_5497_ = v___x_5509_;
goto v___jp_5495_;
}
v___jp_5344_:
{
lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; 
lean_dec_ref(v___y_5346_);
v___x_5354_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5354_, 0, v___y_5353_);
v___x_5355_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_hash_5342_, v___x_5354_, v___y_5347_, v_platformIndependent_5292_);
v___x_5356_ = lean_st_ref_set(v___y_5351_, v___x_5355_);
v___y_5328_ = v___y_5349_;
v_log_5329_ = v___y_5348_;
v_action_5330_ = v___y_5352_;
v_wantsRebuild_5331_ = v___y_5350_;
v_buildTime_5332_ = v___y_5345_;
goto v___jp_5327_;
}
v___jp_5359_:
{
lean_object* v___x_5362_; uint8_t v___x_5363_; 
v___x_5362_ = lean_unsigned_to_nat(0u);
v___x_5363_ = lean_nat_dec_eq(v_wsIdx_5357_, v___x_5362_);
if (v___x_5363_ == 0)
{
lean_object* v_log_5364_; uint8_t v_action_5365_; uint8_t v_wantsRebuild_5366_; lean_object* v_buildTime_5367_; 
v_log_5364_ = lean_ctor_get(v_a_5361_, 0);
lean_inc_ref(v_log_5364_);
v_action_5365_ = lean_ctor_get_uint8(v_a_5361_, sizeof(void*)*3);
v_wantsRebuild_5366_ = lean_ctor_get_uint8(v_a_5361_, sizeof(void*)*3 + 1);
v_buildTime_5367_ = lean_ctor_get(v_a_5361_, 2);
lean_inc(v_buildTime_5367_);
lean_dec_ref(v_a_5361_);
v___y_5328_ = v_a_5360_;
v_log_5329_ = v_log_5364_;
v_action_5330_ = v_action_5365_;
v_wantsRebuild_5331_ = v_wantsRebuild_5366_;
v_buildTime_5332_ = v_buildTime_5367_;
goto v___jp_5327_;
}
else
{
lean_object* v_outputsRef_x3f_5368_; 
v_outputsRef_x3f_5368_ = lean_ctor_get(v_a_5297_, 4);
if (lean_obj_tag(v_outputsRef_x3f_5368_) == 1)
{
lean_object* v_log_5369_; uint8_t v_action_5370_; uint8_t v_wantsRebuild_5371_; lean_object* v_trace_5372_; lean_object* v_buildTime_5373_; lean_object* v_val_5374_; lean_object* v___x_5375_; lean_object* v_descr_5376_; uint64_t v_hash_5377_; lean_object* v_ext_5378_; lean_object* v___x_5379_; uint8_t v___x_5380_; 
v_log_5369_ = lean_ctor_get(v_a_5361_, 0);
lean_inc_ref(v_log_5369_);
v_action_5370_ = lean_ctor_get_uint8(v_a_5361_, sizeof(void*)*3);
v_wantsRebuild_5371_ = lean_ctor_get_uint8(v_a_5361_, sizeof(void*)*3 + 1);
v_trace_5372_ = lean_ctor_get(v_a_5361_, 1);
lean_inc_ref(v_trace_5372_);
v_buildTime_5373_ = lean_ctor_get(v_a_5361_, 2);
lean_inc(v_buildTime_5373_);
lean_dec_ref(v_a_5361_);
v_val_5374_ = lean_ctor_get(v_outputsRef_x3f_5368_, 0);
v___x_5375_ = lean_st_ref_take(v_val_5374_);
v_descr_5376_ = lean_ctor_get(v_a_5360_, 0);
v_hash_5377_ = lean_ctor_get_uint64(v_descr_5376_, sizeof(void*)*1);
v_ext_5378_ = lean_ctor_get(v_descr_5376_, 0);
v___x_5379_ = lean_string_utf8_byte_size(v_ext_5378_);
v___x_5380_ = lean_nat_dec_eq(v___x_5379_, v___x_5362_);
if (v___x_5380_ == 0)
{
lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; 
v___x_5381_ = l_Lake_lowerHexUInt64(v_hash_5377_);
v___x_5382_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5383_ = lean_string_append(v___x_5381_, v___x_5382_);
v___x_5384_ = lean_string_append(v___x_5383_, v_ext_5378_);
v___y_5345_ = v_buildTime_5373_;
v___y_5346_ = v_trace_5372_;
v___y_5347_ = v___x_5375_;
v___y_5348_ = v_log_5369_;
v___y_5349_ = v_a_5360_;
v___y_5350_ = v_wantsRebuild_5371_;
v___y_5351_ = v_val_5374_;
v___y_5352_ = v_action_5370_;
v___y_5353_ = v___x_5384_;
goto v___jp_5344_;
}
else
{
lean_object* v___x_5385_; 
v___x_5385_ = l_Lake_lowerHexUInt64(v_hash_5377_);
v___y_5345_ = v_buildTime_5373_;
v___y_5346_ = v_trace_5372_;
v___y_5347_ = v___x_5375_;
v___y_5348_ = v_log_5369_;
v___y_5349_ = v_a_5360_;
v___y_5350_ = v_wantsRebuild_5371_;
v___y_5351_ = v_val_5374_;
v___y_5352_ = v_action_5370_;
v___y_5353_ = v___x_5385_;
goto v___jp_5344_;
}
}
else
{
lean_object* v_log_5386_; uint8_t v_action_5387_; uint8_t v_wantsRebuild_5388_; lean_object* v_buildTime_5389_; 
v_log_5386_ = lean_ctor_get(v_a_5361_, 0);
lean_inc_ref(v_log_5386_);
v_action_5387_ = lean_ctor_get_uint8(v_a_5361_, sizeof(void*)*3);
v_wantsRebuild_5388_ = lean_ctor_get_uint8(v_a_5361_, sizeof(void*)*3 + 1);
v_buildTime_5389_ = lean_ctor_get(v_a_5361_, 2);
lean_inc(v_buildTime_5389_);
lean_dec_ref(v_a_5361_);
v___y_5328_ = v_a_5360_;
v_log_5329_ = v_log_5386_;
v_action_5330_ = v_action_5387_;
v_wantsRebuild_5331_ = v_wantsRebuild_5388_;
v_buildTime_5332_ = v_buildTime_5389_;
goto v___jp_5327_;
}
}
}
v___jp_5390_:
{
if (lean_obj_tag(v___y_5391_) == 0)
{
lean_object* v_a_5392_; lean_object* v_a_5393_; 
v_a_5392_ = lean_ctor_get(v___y_5391_, 0);
lean_inc(v_a_5392_);
v_a_5393_ = lean_ctor_get(v___y_5391_, 1);
lean_inc(v_a_5393_);
lean_dec_ref(v___y_5391_);
v_a_5360_ = v_a_5392_;
v_a_5361_ = v_a_5393_;
goto v___jp_5359_;
}
else
{
lean_dec_ref(v___x_5309_);
lean_del_object(v___x_5306_);
return v___y_5391_;
}
}
v___jp_5396_:
{
lean_object* v___x_5399_; 
lean_inc_ref(v_a_5293_);
lean_inc_ref(v___x_5309_);
lean_inc_ref(v_file_5286_);
lean_inc(v_val_5341_);
v___x_5399_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_5291_, v_hash_5342_, v_val_5341_, v_file_5286_, v___x_5309_, v_a_5339_, v___y_5397_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5398_);
if (lean_obj_tag(v___x_5399_) == 0)
{
lean_object* v_a_5400_; 
v_a_5400_ = lean_ctor_get(v___x_5399_, 0);
lean_inc(v_a_5400_);
if (lean_obj_tag(v_a_5400_) == 1)
{
lean_object* v_a_5401_; lean_object* v_val_5402_; 
lean_dec_ref(v_trace_5303_);
lean_dec_ref(v_a_5293_);
lean_dec_ref(v_ext_5289_);
lean_dec_ref(v_build_5287_);
lean_dec_ref(v_file_5286_);
v_a_5401_ = lean_ctor_get(v___x_5399_, 1);
lean_inc(v_a_5401_);
lean_dec_ref(v___x_5399_);
v_val_5402_ = lean_ctor_get(v_a_5400_, 0);
lean_inc(v_val_5402_);
lean_dec_ref(v_a_5400_);
v_a_5360_ = v_val_5402_;
v_a_5361_ = v_a_5401_;
goto v___jp_5359_;
}
else
{
lean_object* v_a_5403_; lean_object* v___x_5404_; 
lean_dec(v_a_5400_);
v_a_5403_ = lean_ctor_get(v___x_5399_, 1);
lean_inc(v_a_5403_);
lean_dec_ref(v___x_5399_);
lean_inc_ref(v___x_5309_);
v___x_5404_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5286_, v_build_5287_, v_text_5288_, v_ext_5289_, v_trace_5303_, v___x_5309_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5403_);
lean_dec_ref(v_trace_5303_);
v___y_5391_ = v___x_5404_;
goto v___jp_5390_;
}
}
else
{
lean_object* v_a_5405_; lean_object* v_a_5406_; lean_object* v___x_5408_; uint8_t v_isShared_5409_; uint8_t v_isSharedCheck_5413_; 
lean_dec_ref(v___x_5309_);
lean_del_object(v___x_5306_);
lean_dec_ref(v_trace_5303_);
lean_dec_ref(v_a_5293_);
lean_dec_ref(v_ext_5289_);
lean_dec_ref(v_build_5287_);
lean_dec_ref(v_file_5286_);
v_a_5405_ = lean_ctor_get(v___x_5399_, 0);
v_a_5406_ = lean_ctor_get(v___x_5399_, 1);
v_isSharedCheck_5413_ = !lean_is_exclusive(v___x_5399_);
if (v_isSharedCheck_5413_ == 0)
{
v___x_5408_ = v___x_5399_;
v_isShared_5409_ = v_isSharedCheck_5413_;
goto v_resetjp_5407_;
}
else
{
lean_inc(v_a_5406_);
lean_inc(v_a_5405_);
lean_dec(v___x_5399_);
v___x_5408_ = lean_box(0);
v_isShared_5409_ = v_isSharedCheck_5413_;
goto v_resetjp_5407_;
}
v_resetjp_5407_:
{
lean_object* v___x_5411_; 
if (v_isShared_5409_ == 0)
{
v___x_5411_ = v___x_5408_;
goto v_reusejp_5410_;
}
else
{
lean_object* v_reuseFailAlloc_5412_; 
v_reuseFailAlloc_5412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5412_, 0, v_a_5405_);
lean_ctor_set(v_reuseFailAlloc_5412_, 1, v_a_5406_);
v___x_5411_ = v_reuseFailAlloc_5412_;
goto v_reusejp_5410_;
}
v_reusejp_5410_:
{
return v___x_5411_;
}
}
}
}
v___jp_5414_:
{
if (v_a_5416_ == 0)
{
lean_object* v___x_5418_; 
lean_dec(v_a_5339_);
lean_inc_ref(v___x_5309_);
v___x_5418_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5286_, v_build_5287_, v_text_5288_, v_ext_5289_, v_trace_5303_, v___x_5309_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5417_);
lean_dec_ref(v_trace_5303_);
v___y_5391_ = v___x_5418_;
goto v___jp_5390_;
}
else
{
v___y_5397_ = v___y_5415_;
v_a_5398_ = v_a_5417_;
goto v___jp_5396_;
}
}
v___jp_5419_:
{
lean_object* v___x_5421_; 
lean_inc(v_a_5339_);
v___x_5421_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5293_, v_file_5286_, v_trace_5303_, v_a_5339_, v_mtime_5343_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5420_);
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
lean_dec(v_a_5422_);
v___x_5426_ = l_Lake_instDecidableEqOutputStatus(v___x_5425_, v___x_5424_);
if (v___x_5426_ == 0)
{
lean_object* v___x_5427_; 
lean_dec(v_a_5339_);
lean_dec_ref(v_trace_5303_);
lean_dec_ref(v_a_5293_);
lean_dec_ref(v_build_5287_);
v___x_5427_ = l_Lake_computeArtifact___redArg(v_file_5286_, v_ext_5289_, v_text_5288_, v_a_5297_, v_a_5423_);
v___y_5391_ = v___x_5427_;
goto v___jp_5390_;
}
else
{
if (lean_obj_tag(v_enableArtifactCache_x3f_5394_) == 0)
{
lean_object* v_toContext_5428_; lean_object* v_lakeEnv_5429_; lean_object* v_enableArtifactCache_x3f_5430_; 
v_toContext_5428_ = lean_ctor_get(v_a_5297_, 1);
v_lakeEnv_5429_ = lean_ctor_get(v_toContext_5428_, 0);
v_enableArtifactCache_x3f_5430_ = lean_ctor_get(v_lakeEnv_5429_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_5430_) == 0)
{
lean_object* v_packages_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v_config_5434_; lean_object* v_enableArtifactCache_x3f_5435_; 
v_packages_5431_ = lean_ctor_get(v_toContext_5428_, 4);
v___x_5432_ = lean_unsigned_to_nat(0u);
v___x_5433_ = lean_array_fget_borrowed(v_packages_5431_, v___x_5432_);
v_config_5434_ = lean_ctor_get(v___x_5433_, 6);
v_enableArtifactCache_x3f_5435_ = lean_ctor_get(v_config_5434_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_5435_) == 0)
{
v___y_5397_ = v___x_5426_;
v_a_5398_ = v_a_5423_;
goto v___jp_5396_;
}
else
{
lean_object* v_val_5436_; uint8_t v___x_5437_; 
v_val_5436_ = lean_ctor_get(v_enableArtifactCache_x3f_5435_, 0);
v___x_5437_ = lean_unbox(v_val_5436_);
v___y_5415_ = v___x_5426_;
v_a_5416_ = v___x_5437_;
v_a_5417_ = v_a_5423_;
goto v___jp_5414_;
}
}
else
{
lean_object* v_val_5438_; uint8_t v___x_5439_; 
v_val_5438_ = lean_ctor_get(v_enableArtifactCache_x3f_5430_, 0);
v___x_5439_ = lean_unbox(v_val_5438_);
v___y_5415_ = v___x_5426_;
v_a_5416_ = v___x_5439_;
v_a_5417_ = v_a_5423_;
goto v___jp_5414_;
}
}
else
{
lean_object* v_val_5440_; uint8_t v___x_5441_; 
v_val_5440_ = lean_ctor_get(v_enableArtifactCache_x3f_5394_, 0);
v___x_5441_ = lean_unbox(v_val_5440_);
v___y_5415_ = v___x_5426_;
v_a_5416_ = v___x_5441_;
v_a_5417_ = v_a_5423_;
goto v___jp_5414_;
}
}
}
else
{
lean_object* v_a_5442_; lean_object* v_a_5443_; lean_object* v___x_5445_; uint8_t v_isShared_5446_; uint8_t v_isSharedCheck_5450_; 
lean_dec(v_a_5339_);
lean_dec_ref(v___x_5309_);
lean_del_object(v___x_5306_);
lean_dec_ref(v_trace_5303_);
lean_dec_ref(v_a_5293_);
lean_dec_ref(v_ext_5289_);
lean_dec_ref(v_build_5287_);
lean_dec_ref(v_file_5286_);
v_a_5442_ = lean_ctor_get(v___x_5421_, 0);
v_a_5443_ = lean_ctor_get(v___x_5421_, 1);
v_isSharedCheck_5450_ = !lean_is_exclusive(v___x_5421_);
if (v_isSharedCheck_5450_ == 0)
{
v___x_5445_ = v___x_5421_;
v_isShared_5446_ = v_isSharedCheck_5450_;
goto v_resetjp_5444_;
}
else
{
lean_inc(v_a_5443_);
lean_inc(v_a_5442_);
lean_dec(v___x_5421_);
v___x_5445_ = lean_box(0);
v_isShared_5446_ = v_isSharedCheck_5450_;
goto v_resetjp_5444_;
}
v_resetjp_5444_:
{
lean_object* v___x_5448_; 
if (v_isShared_5446_ == 0)
{
v___x_5448_ = v___x_5445_;
goto v_reusejp_5447_;
}
else
{
lean_object* v_reuseFailAlloc_5449_; 
v_reuseFailAlloc_5449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5449_, 0, v_a_5442_);
lean_ctor_set(v_reuseFailAlloc_5449_, 1, v_a_5443_);
v___x_5448_ = v_reuseFailAlloc_5449_;
goto v_reusejp_5447_;
}
v_reusejp_5447_:
{
return v___x_5448_;
}
}
}
}
v___jp_5451_:
{
lean_object* v___x_5454_; 
lean_inc_ref(v_a_5293_);
lean_inc(v_a_5339_);
lean_inc_ref(v___x_5309_);
lean_inc_ref(v_file_5286_);
lean_inc(v_val_5341_);
v___x_5454_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_5291_, v_hash_5342_, v_val_5341_, v_file_5286_, v___x_5309_, v_a_5339_, v___y_5453_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v___y_5452_);
if (lean_obj_tag(v___x_5454_) == 0)
{
lean_object* v_a_5455_; 
v_a_5455_ = lean_ctor_get(v___x_5454_, 0);
lean_inc(v_a_5455_);
if (lean_obj_tag(v_a_5455_) == 1)
{
lean_object* v_a_5456_; lean_object* v_val_5457_; 
lean_dec(v_a_5339_);
lean_dec_ref(v_trace_5303_);
lean_dec_ref(v_a_5293_);
lean_dec_ref(v_ext_5289_);
lean_dec_ref(v_build_5287_);
lean_dec_ref(v_file_5286_);
v_a_5456_ = lean_ctor_get(v___x_5454_, 1);
lean_inc(v_a_5456_);
lean_dec_ref(v___x_5454_);
v_val_5457_ = lean_ctor_get(v_a_5455_, 0);
lean_inc(v_val_5457_);
lean_dec_ref(v_a_5455_);
v_a_5360_ = v_val_5457_;
v_a_5361_ = v_a_5456_;
goto v___jp_5359_;
}
else
{
lean_object* v_a_5458_; lean_object* v___x_5459_; 
lean_dec(v_a_5455_);
v_a_5458_ = lean_ctor_get(v___x_5454_, 1);
lean_inc(v_a_5458_);
lean_dec_ref(v___x_5454_);
v___x_5459_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5293_, v_file_5286_, v_trace_5303_, v_a_5339_, v_mtime_5343_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5458_);
if (lean_obj_tag(v___x_5459_) == 0)
{
lean_object* v_a_5460_; lean_object* v_a_5461_; uint8_t v___x_5462_; uint8_t v___x_5463_; uint8_t v___x_5464_; 
v_a_5460_ = lean_ctor_get(v___x_5459_, 0);
lean_inc(v_a_5460_);
v_a_5461_ = lean_ctor_get(v___x_5459_, 1);
lean_inc(v_a_5461_);
lean_dec_ref(v___x_5459_);
v___x_5462_ = 0;
v___x_5463_ = lean_unbox(v_a_5460_);
v___x_5464_ = l_Lake_instDecidableEqOutputStatus(v___x_5463_, v___x_5462_);
if (v___x_5464_ == 0)
{
lean_object* v___x_5465_; uint8_t v___x_5466_; lean_object* v___x_5467_; 
lean_dec_ref(v_trace_5303_);
lean_dec_ref(v_build_5287_);
v___x_5465_ = lean_box(0);
v___x_5466_ = lean_unbox(v_a_5460_);
lean_dec(v_a_5460_);
lean_inc(v_val_5341_);
v___x_5467_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v___x_5466_, v_file_5286_, v_ext_5289_, v_text_5288_, v_exe_5291_, v___y_5453_, v_val_5341_, v_hash_5342_, v___x_5465_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5461_);
lean_dec_ref(v_a_5293_);
v___y_5391_ = v___x_5467_;
goto v___jp_5390_;
}
else
{
lean_object* v___x_5468_; 
lean_inc_ref(v_a_5293_);
lean_inc_ref(v___x_5309_);
lean_inc_ref(v_ext_5289_);
lean_inc_ref(v_file_5286_);
v___x_5468_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5286_, v_build_5287_, v_text_5288_, v_ext_5289_, v_trace_5303_, v___x_5309_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5461_);
lean_dec_ref(v_trace_5303_);
if (lean_obj_tag(v___x_5468_) == 0)
{
lean_object* v_a_5469_; lean_object* v___x_5470_; uint8_t v___x_5471_; lean_object* v___x_5472_; 
v_a_5469_ = lean_ctor_get(v___x_5468_, 1);
lean_inc(v_a_5469_);
lean_dec_ref(v___x_5468_);
v___x_5470_ = lean_box(0);
v___x_5471_ = lean_unbox(v_a_5460_);
lean_dec(v_a_5460_);
lean_inc(v_val_5341_);
v___x_5472_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v___x_5471_, v_file_5286_, v_ext_5289_, v_text_5288_, v_exe_5291_, v___y_5453_, v_val_5341_, v_hash_5342_, v___x_5470_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5469_);
lean_dec_ref(v_a_5293_);
v___y_5391_ = v___x_5472_;
goto v___jp_5390_;
}
else
{
lean_dec(v_a_5460_);
lean_dec_ref(v___x_5309_);
lean_del_object(v___x_5306_);
lean_dec_ref(v_a_5293_);
lean_dec_ref(v_ext_5289_);
lean_dec_ref(v_file_5286_);
return v___x_5468_;
}
}
}
else
{
lean_object* v_a_5473_; lean_object* v_a_5474_; lean_object* v___x_5476_; uint8_t v_isShared_5477_; uint8_t v_isSharedCheck_5481_; 
lean_dec_ref(v___x_5309_);
lean_del_object(v___x_5306_);
lean_dec_ref(v_trace_5303_);
lean_dec_ref(v_a_5293_);
lean_dec_ref(v_ext_5289_);
lean_dec_ref(v_build_5287_);
lean_dec_ref(v_file_5286_);
v_a_5473_ = lean_ctor_get(v___x_5459_, 0);
v_a_5474_ = lean_ctor_get(v___x_5459_, 1);
v_isSharedCheck_5481_ = !lean_is_exclusive(v___x_5459_);
if (v_isSharedCheck_5481_ == 0)
{
v___x_5476_ = v___x_5459_;
v_isShared_5477_ = v_isSharedCheck_5481_;
goto v_resetjp_5475_;
}
else
{
lean_inc(v_a_5474_);
lean_inc(v_a_5473_);
lean_dec(v___x_5459_);
v___x_5476_ = lean_box(0);
v_isShared_5477_ = v_isSharedCheck_5481_;
goto v_resetjp_5475_;
}
v_resetjp_5475_:
{
lean_object* v___x_5479_; 
if (v_isShared_5477_ == 0)
{
v___x_5479_ = v___x_5476_;
goto v_reusejp_5478_;
}
else
{
lean_object* v_reuseFailAlloc_5480_; 
v_reuseFailAlloc_5480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5480_, 0, v_a_5473_);
lean_ctor_set(v_reuseFailAlloc_5480_, 1, v_a_5474_);
v___x_5479_ = v_reuseFailAlloc_5480_;
goto v_reusejp_5478_;
}
v_reusejp_5478_:
{
return v___x_5479_;
}
}
}
}
}
else
{
lean_object* v_a_5482_; lean_object* v_a_5483_; lean_object* v___x_5485_; uint8_t v_isShared_5486_; uint8_t v_isSharedCheck_5490_; 
lean_dec(v_a_5339_);
lean_dec_ref(v___x_5309_);
lean_del_object(v___x_5306_);
lean_dec_ref(v_trace_5303_);
lean_dec_ref(v_a_5293_);
lean_dec_ref(v_ext_5289_);
lean_dec_ref(v_build_5287_);
lean_dec_ref(v_file_5286_);
v_a_5482_ = lean_ctor_get(v___x_5454_, 0);
v_a_5483_ = lean_ctor_get(v___x_5454_, 1);
v_isSharedCheck_5490_ = !lean_is_exclusive(v___x_5454_);
if (v_isSharedCheck_5490_ == 0)
{
v___x_5485_ = v___x_5454_;
v_isShared_5486_ = v_isSharedCheck_5490_;
goto v_resetjp_5484_;
}
else
{
lean_inc(v_a_5483_);
lean_inc(v_a_5482_);
lean_dec(v___x_5454_);
v___x_5485_ = lean_box(0);
v_isShared_5486_ = v_isSharedCheck_5490_;
goto v_resetjp_5484_;
}
v_resetjp_5484_:
{
lean_object* v___x_5488_; 
if (v_isShared_5486_ == 0)
{
v___x_5488_ = v___x_5485_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5489_; 
v_reuseFailAlloc_5489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5489_, 0, v_a_5482_);
lean_ctor_set(v_reuseFailAlloc_5489_, 1, v_a_5483_);
v___x_5488_ = v_reuseFailAlloc_5489_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
return v___x_5488_;
}
}
}
}
v___jp_5491_:
{
if (v_restore_5290_ == 0)
{
v___y_5452_ = v_a_5494_;
v___y_5453_ = v_a_5493_;
goto v___jp_5451_;
}
else
{
v___y_5452_ = v_a_5494_;
v___y_5453_ = v___y_5492_;
goto v___jp_5451_;
}
}
v___jp_5495_:
{
if (v_a_5496_ == 0)
{
v_a_5420_ = v_a_5497_;
goto v___jp_5419_;
}
else
{
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5395_) == 0)
{
lean_object* v_toContext_5498_; lean_object* v_packages_5499_; lean_object* v___x_5500_; lean_object* v___x_5501_; lean_object* v_config_5502_; lean_object* v_restoreAllArtifacts_x3f_5503_; 
v_toContext_5498_ = lean_ctor_get(v_a_5297_, 1);
v_packages_5499_ = lean_ctor_get(v_toContext_5498_, 4);
v___x_5500_ = lean_unsigned_to_nat(0u);
v___x_5501_ = lean_array_fget_borrowed(v_packages_5499_, v___x_5500_);
v_config_5502_ = lean_ctor_get(v___x_5501_, 6);
v_restoreAllArtifacts_x3f_5503_ = lean_ctor_get(v_config_5502_, 25);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5503_) == 0)
{
uint8_t v___x_5504_; 
v___x_5504_ = 0;
v___y_5492_ = v_a_5496_;
v_a_5493_ = v___x_5504_;
v_a_5494_ = v_a_5497_;
goto v___jp_5491_;
}
else
{
lean_object* v_val_5505_; uint8_t v___x_5506_; 
v_val_5505_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5503_, 0);
v___x_5506_ = lean_unbox(v_val_5505_);
v___y_5492_ = v_a_5496_;
v_a_5493_ = v___x_5506_;
v_a_5494_ = v_a_5497_;
goto v___jp_5491_;
}
}
else
{
lean_object* v_val_5507_; uint8_t v___x_5508_; 
v_val_5507_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5395_, 0);
v___x_5508_ = lean_unbox(v_val_5507_);
v___y_5492_ = v_a_5496_;
v_a_5493_ = v___x_5508_;
v_a_5494_ = v_a_5497_;
goto v___jp_5491_;
}
}
}
}
else
{
lean_object* v_a_5524_; lean_object* v_a_5525_; lean_object* v_mtime_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; 
lean_del_object(v___x_5306_);
v_a_5524_ = lean_ctor_get(v___x_5338_, 0);
lean_inc(v_a_5524_);
v_a_5525_ = lean_ctor_get(v___x_5338_, 1);
lean_inc(v_a_5525_);
lean_dec_ref(v___x_5338_);
v_mtime_5526_ = lean_ctor_get(v_trace_5303_, 2);
lean_inc_ref(v_trace_5303_);
v___x_5527_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5527_, 0, v_a_5525_);
lean_ctor_set(v___x_5527_, 1, v_trace_5303_);
lean_ctor_set(v___x_5527_, 2, v_buildTime_5304_);
lean_ctor_set_uint8(v___x_5527_, sizeof(void*)*3, v_action_5301_);
lean_ctor_set_uint8(v___x_5527_, sizeof(void*)*3 + 1, v_wantsRebuild_5302_);
v___x_5528_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5293_, v_file_5286_, v_trace_5303_, v_a_5524_, v_mtime_5526_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v___x_5527_);
if (lean_obj_tag(v___x_5528_) == 0)
{
lean_object* v_a_5529_; lean_object* v_a_5530_; uint8_t v___x_5531_; uint8_t v___x_5532_; uint8_t v___x_5533_; 
v_a_5529_ = lean_ctor_get(v___x_5528_, 0);
lean_inc(v_a_5529_);
v_a_5530_ = lean_ctor_get(v___x_5528_, 1);
lean_inc(v_a_5530_);
lean_dec_ref(v___x_5528_);
v___x_5531_ = 0;
v___x_5532_ = lean_unbox(v_a_5529_);
lean_dec(v_a_5529_);
v___x_5533_ = l_Lake_instDecidableEqOutputStatus(v___x_5532_, v___x_5531_);
if (v___x_5533_ == 0)
{
lean_object* v___x_5534_; 
lean_dec_ref(v_trace_5303_);
lean_dec_ref(v_a_5293_);
lean_dec_ref(v_build_5287_);
v___x_5534_ = l_Lake_computeArtifact___redArg(v_file_5286_, v_ext_5289_, v_text_5288_, v_a_5297_, v_a_5530_);
if (lean_obj_tag(v___x_5534_) == 0)
{
lean_object* v_a_5535_; lean_object* v_a_5536_; 
v_a_5535_ = lean_ctor_get(v___x_5534_, 0);
lean_inc(v_a_5535_);
v_a_5536_ = lean_ctor_get(v___x_5534_, 1);
lean_inc(v_a_5536_);
lean_dec_ref(v___x_5534_);
v_art_5311_ = v_a_5535_;
v___y_5312_ = v_a_5536_;
goto v___jp_5310_;
}
else
{
lean_dec_ref(v___x_5309_);
return v___x_5534_;
}
}
else
{
lean_object* v___x_5537_; 
lean_inc_ref(v___x_5309_);
v___x_5537_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5286_, v_build_5287_, v_text_5288_, v_ext_5289_, v_trace_5303_, v___x_5309_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5530_);
lean_dec_ref(v_trace_5303_);
if (lean_obj_tag(v___x_5537_) == 0)
{
lean_object* v_a_5538_; lean_object* v_a_5539_; 
v_a_5538_ = lean_ctor_get(v___x_5537_, 0);
lean_inc(v_a_5538_);
v_a_5539_ = lean_ctor_get(v___x_5537_, 1);
lean_inc(v_a_5539_);
lean_dec_ref(v___x_5537_);
v_art_5311_ = v_a_5538_;
v___y_5312_ = v_a_5539_;
goto v___jp_5310_;
}
else
{
lean_dec_ref(v___x_5309_);
return v___x_5537_;
}
}
}
else
{
lean_object* v_a_5540_; lean_object* v_a_5541_; lean_object* v___x_5543_; uint8_t v_isShared_5544_; uint8_t v_isSharedCheck_5548_; 
lean_dec_ref(v___x_5309_);
lean_dec_ref(v_trace_5303_);
lean_dec_ref(v_a_5293_);
lean_dec_ref(v_ext_5289_);
lean_dec_ref(v_build_5287_);
lean_dec_ref(v_file_5286_);
v_a_5540_ = lean_ctor_get(v___x_5528_, 0);
v_a_5541_ = lean_ctor_get(v___x_5528_, 1);
v_isSharedCheck_5548_ = !lean_is_exclusive(v___x_5528_);
if (v_isSharedCheck_5548_ == 0)
{
v___x_5543_ = v___x_5528_;
v_isShared_5544_ = v_isSharedCheck_5548_;
goto v_resetjp_5542_;
}
else
{
lean_inc(v_a_5541_);
lean_inc(v_a_5540_);
lean_dec(v___x_5528_);
v___x_5543_ = lean_box(0);
v_isShared_5544_ = v_isSharedCheck_5548_;
goto v_resetjp_5542_;
}
v_resetjp_5542_:
{
lean_object* v___x_5546_; 
if (v_isShared_5544_ == 0)
{
v___x_5546_ = v___x_5543_;
goto v_reusejp_5545_;
}
else
{
lean_object* v_reuseFailAlloc_5547_; 
v_reuseFailAlloc_5547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5547_, 0, v_a_5540_);
lean_ctor_set(v_reuseFailAlloc_5547_, 1, v_a_5541_);
v___x_5546_ = v_reuseFailAlloc_5547_;
goto v_reusejp_5545_;
}
v_reusejp_5545_:
{
return v___x_5546_;
}
}
}
}
}
else
{
lean_object* v_a_5549_; lean_object* v_a_5550_; lean_object* v___x_5552_; uint8_t v_isShared_5553_; uint8_t v_isSharedCheck_5558_; 
lean_dec_ref(v___x_5309_);
lean_del_object(v___x_5306_);
lean_dec_ref(v_a_5293_);
lean_dec_ref(v_ext_5289_);
lean_dec_ref(v_build_5287_);
lean_dec_ref(v_file_5286_);
v_a_5549_ = lean_ctor_get(v___x_5338_, 0);
v_a_5550_ = lean_ctor_get(v___x_5338_, 1);
v_isSharedCheck_5558_ = !lean_is_exclusive(v___x_5338_);
if (v_isSharedCheck_5558_ == 0)
{
v___x_5552_ = v___x_5338_;
v_isShared_5553_ = v_isSharedCheck_5558_;
goto v_resetjp_5551_;
}
else
{
lean_inc(v_a_5550_);
lean_inc(v_a_5549_);
lean_dec(v___x_5338_);
v___x_5552_ = lean_box(0);
v_isShared_5553_ = v_isSharedCheck_5558_;
goto v_resetjp_5551_;
}
v_resetjp_5551_:
{
lean_object* v___x_5554_; lean_object* v___x_5556_; 
v___x_5554_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5554_, 0, v_a_5550_);
lean_ctor_set(v___x_5554_, 1, v_trace_5303_);
lean_ctor_set(v___x_5554_, 2, v_buildTime_5304_);
lean_ctor_set_uint8(v___x_5554_, sizeof(void*)*3, v_action_5301_);
lean_ctor_set_uint8(v___x_5554_, sizeof(void*)*3 + 1, v_wantsRebuild_5302_);
if (v_isShared_5553_ == 0)
{
lean_ctor_set(v___x_5552_, 1, v___x_5554_);
v___x_5556_ = v___x_5552_;
goto v_reusejp_5555_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v_a_5549_);
lean_ctor_set(v_reuseFailAlloc_5557_, 1, v___x_5554_);
v___x_5556_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5555_;
}
v_reusejp_5555_:
{
return v___x_5556_;
}
}
}
v___jp_5310_:
{
lean_object* v_log_5313_; uint8_t v_action_5314_; uint8_t v_wantsRebuild_5315_; lean_object* v_buildTime_5316_; lean_object* v___x_5318_; uint8_t v_isShared_5319_; uint8_t v_isSharedCheck_5325_; 
v_log_5313_ = lean_ctor_get(v___y_5312_, 0);
v_action_5314_ = lean_ctor_get_uint8(v___y_5312_, sizeof(void*)*3);
v_wantsRebuild_5315_ = lean_ctor_get_uint8(v___y_5312_, sizeof(void*)*3 + 1);
v_buildTime_5316_ = lean_ctor_get(v___y_5312_, 2);
v_isSharedCheck_5325_ = !lean_is_exclusive(v___y_5312_);
if (v_isSharedCheck_5325_ == 0)
{
lean_object* v_unused_5326_; 
v_unused_5326_ = lean_ctor_get(v___y_5312_, 1);
lean_dec(v_unused_5326_);
v___x_5318_ = v___y_5312_;
v_isShared_5319_ = v_isSharedCheck_5325_;
goto v_resetjp_5317_;
}
else
{
lean_inc(v_buildTime_5316_);
lean_inc(v_log_5313_);
lean_dec(v___y_5312_);
v___x_5318_ = lean_box(0);
v_isShared_5319_ = v_isSharedCheck_5325_;
goto v_resetjp_5317_;
}
v_resetjp_5317_:
{
lean_object* v___x_5320_; lean_object* v___x_5322_; 
v___x_5320_ = l_Lake_Artifact_trace(v_art_5311_);
if (v_isShared_5319_ == 0)
{
lean_ctor_set(v___x_5318_, 1, v___x_5320_);
v___x_5322_ = v___x_5318_;
goto v_reusejp_5321_;
}
else
{
lean_object* v_reuseFailAlloc_5324_; 
v_reuseFailAlloc_5324_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5324_, 0, v_log_5313_);
lean_ctor_set(v_reuseFailAlloc_5324_, 1, v___x_5320_);
lean_ctor_set(v_reuseFailAlloc_5324_, 2, v_buildTime_5316_);
lean_ctor_set_uint8(v_reuseFailAlloc_5324_, sizeof(void*)*3, v_action_5314_);
lean_ctor_set_uint8(v_reuseFailAlloc_5324_, sizeof(void*)*3 + 1, v_wantsRebuild_5315_);
v___x_5322_ = v_reuseFailAlloc_5324_;
goto v_reusejp_5321_;
}
v_reusejp_5321_:
{
lean_object* v___x_5323_; 
v___x_5323_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_5311_, v___x_5309_, v___x_5322_);
lean_dec_ref(v___x_5309_);
return v___x_5323_;
}
}
}
v___jp_5327_:
{
lean_object* v___x_5333_; lean_object* v___x_5335_; 
v___x_5333_ = l_Lake_Artifact_trace(v___y_5328_);
if (v_isShared_5307_ == 0)
{
lean_ctor_set(v___x_5306_, 2, v_buildTime_5332_);
lean_ctor_set(v___x_5306_, 1, v___x_5333_);
lean_ctor_set(v___x_5306_, 0, v_log_5329_);
v___x_5335_ = v___x_5306_;
goto v_reusejp_5334_;
}
else
{
lean_object* v_reuseFailAlloc_5337_; 
v_reuseFailAlloc_5337_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5337_, 0, v_log_5329_);
lean_ctor_set(v_reuseFailAlloc_5337_, 1, v___x_5333_);
lean_ctor_set(v_reuseFailAlloc_5337_, 2, v_buildTime_5332_);
v___x_5335_ = v_reuseFailAlloc_5337_;
goto v_reusejp_5334_;
}
v_reusejp_5334_:
{
lean_object* v___x_5336_; 
lean_ctor_set_uint8(v___x_5335_, sizeof(void*)*3, v_action_5330_);
lean_ctor_set_uint8(v___x_5335_, sizeof(void*)*3 + 1, v_wantsRebuild_5331_);
v___x_5336_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v___y_5328_, v___x_5309_, v___x_5335_);
lean_dec_ref(v___x_5309_);
return v___x_5336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___boxed(lean_object* v_file_5560_, lean_object* v_build_5561_, lean_object* v_text_5562_, lean_object* v_ext_5563_, lean_object* v_restore_5564_, lean_object* v_exe_5565_, lean_object* v_platformIndependent_5566_, lean_object* v_a_5567_, lean_object* v_a_5568_, lean_object* v_a_5569_, lean_object* v_a_5570_, lean_object* v_a_5571_, lean_object* v_a_5572_, lean_object* v_a_5573_){
_start:
{
uint8_t v_text_boxed_5574_; uint8_t v_restore_boxed_5575_; uint8_t v_exe_boxed_5576_; uint8_t v_platformIndependent_boxed_5577_; lean_object* v_res_5578_; 
v_text_boxed_5574_ = lean_unbox(v_text_5562_);
v_restore_boxed_5575_ = lean_unbox(v_restore_5564_);
v_exe_boxed_5576_ = lean_unbox(v_exe_5565_);
v_platformIndependent_boxed_5577_ = lean_unbox(v_platformIndependent_5566_);
v_res_5578_ = l_Lake_buildArtifactUnlessUpToDate(v_file_5560_, v_build_5561_, v_text_boxed_5574_, v_ext_5563_, v_restore_boxed_5575_, v_exe_boxed_5576_, v_platformIndependent_boxed_5577_, v_a_5567_, v_a_5568_, v_a_5569_, v_a_5570_, v_a_5571_, v_a_5572_);
lean_dec_ref(v_a_5571_);
lean_dec(v_a_5570_);
lean_dec(v_a_5569_);
lean_dec(v_a_5568_);
return v_res_5578_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0(lean_object* v_extraDepTrace_5580_, lean_object* v_build_5581_, lean_object* v_file_5582_, uint8_t v_text_5583_, lean_object* v_depInfo_5584_, lean_object* v___y_5585_, lean_object* v___y_5586_, lean_object* v___y_5587_, lean_object* v___y_5588_, lean_object* v___y_5589_, lean_object* v___y_5590_){
_start:
{
lean_object* v___x_5592_; 
lean_inc_ref(v___y_5589_);
lean_inc(v___y_5588_);
lean_inc(v___y_5587_);
lean_inc(v___y_5586_);
lean_inc_ref(v___y_5585_);
v___x_5592_ = lean_apply_7(v_extraDepTrace_5580_, v___y_5585_, v___y_5586_, v___y_5587_, v___y_5588_, v___y_5589_, v___y_5590_, lean_box(0));
if (lean_obj_tag(v___x_5592_) == 0)
{
lean_object* v_a_5593_; lean_object* v_a_5594_; lean_object* v_log_5595_; uint8_t v_action_5596_; uint8_t v_wantsRebuild_5597_; lean_object* v_trace_5598_; lean_object* v_buildTime_5599_; lean_object* v___x_5601_; uint8_t v_isShared_5602_; uint8_t v_isSharedCheck_5630_; 
v_a_5593_ = lean_ctor_get(v___x_5592_, 1);
lean_inc(v_a_5593_);
v_a_5594_ = lean_ctor_get(v___x_5592_, 0);
lean_inc(v_a_5594_);
lean_dec_ref(v___x_5592_);
v_log_5595_ = lean_ctor_get(v_a_5593_, 0);
v_action_5596_ = lean_ctor_get_uint8(v_a_5593_, sizeof(void*)*3);
v_wantsRebuild_5597_ = lean_ctor_get_uint8(v_a_5593_, sizeof(void*)*3 + 1);
v_trace_5598_ = lean_ctor_get(v_a_5593_, 1);
v_buildTime_5599_ = lean_ctor_get(v_a_5593_, 2);
v_isSharedCheck_5630_ = !lean_is_exclusive(v_a_5593_);
if (v_isSharedCheck_5630_ == 0)
{
v___x_5601_ = v_a_5593_;
v_isShared_5602_ = v_isSharedCheck_5630_;
goto v_resetjp_5600_;
}
else
{
lean_inc(v_buildTime_5599_);
lean_inc(v_trace_5598_);
lean_inc(v_log_5595_);
lean_dec(v_a_5593_);
v___x_5601_ = lean_box(0);
v_isShared_5602_ = v_isSharedCheck_5630_;
goto v_resetjp_5600_;
}
v_resetjp_5600_:
{
lean_object* v___x_5603_; lean_object* v___x_5605_; 
v___x_5603_ = l_Lake_BuildTrace_mix(v_trace_5598_, v_a_5594_);
if (v_isShared_5602_ == 0)
{
lean_ctor_set(v___x_5601_, 1, v___x_5603_);
v___x_5605_ = v___x_5601_;
goto v_reusejp_5604_;
}
else
{
lean_object* v_reuseFailAlloc_5629_; 
v_reuseFailAlloc_5629_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5629_, 0, v_log_5595_);
lean_ctor_set(v_reuseFailAlloc_5629_, 1, v___x_5603_);
lean_ctor_set(v_reuseFailAlloc_5629_, 2, v_buildTime_5599_);
lean_ctor_set_uint8(v_reuseFailAlloc_5629_, sizeof(void*)*3, v_action_5596_);
lean_ctor_set_uint8(v_reuseFailAlloc_5629_, sizeof(void*)*3 + 1, v_wantsRebuild_5597_);
v___x_5605_ = v_reuseFailAlloc_5629_;
goto v_reusejp_5604_;
}
v_reusejp_5604_:
{
lean_object* v___x_5606_; lean_object* v___x_5607_; uint8_t v___x_5608_; lean_object* v___x_5609_; 
v___x_5606_ = lean_apply_1(v_build_5581_, v_depInfo_5584_);
v___x_5607_ = ((lean_object*)(l_Lake_buildFileAfterDep___redArg___lam__0___closed__0));
v___x_5608_ = 0;
v___x_5609_ = l_Lake_buildArtifactUnlessUpToDate(v_file_5582_, v___x_5606_, v_text_5583_, v___x_5607_, v___x_5608_, v___x_5608_, v___x_5608_, v___y_5585_, v___y_5586_, v___y_5587_, v___y_5588_, v___y_5589_, v___x_5605_);
if (lean_obj_tag(v___x_5609_) == 0)
{
lean_object* v_a_5610_; lean_object* v_a_5611_; lean_object* v___x_5613_; uint8_t v_isShared_5614_; uint8_t v_isSharedCheck_5619_; 
v_a_5610_ = lean_ctor_get(v___x_5609_, 0);
v_a_5611_ = lean_ctor_get(v___x_5609_, 1);
v_isSharedCheck_5619_ = !lean_is_exclusive(v___x_5609_);
if (v_isSharedCheck_5619_ == 0)
{
v___x_5613_ = v___x_5609_;
v_isShared_5614_ = v_isSharedCheck_5619_;
goto v_resetjp_5612_;
}
else
{
lean_inc(v_a_5611_);
lean_inc(v_a_5610_);
lean_dec(v___x_5609_);
v___x_5613_ = lean_box(0);
v_isShared_5614_ = v_isSharedCheck_5619_;
goto v_resetjp_5612_;
}
v_resetjp_5612_:
{
lean_object* v_path_5615_; lean_object* v___x_5617_; 
v_path_5615_ = lean_ctor_get(v_a_5610_, 1);
lean_inc_ref(v_path_5615_);
lean_dec(v_a_5610_);
if (v_isShared_5614_ == 0)
{
lean_ctor_set(v___x_5613_, 0, v_path_5615_);
v___x_5617_ = v___x_5613_;
goto v_reusejp_5616_;
}
else
{
lean_object* v_reuseFailAlloc_5618_; 
v_reuseFailAlloc_5618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5618_, 0, v_path_5615_);
lean_ctor_set(v_reuseFailAlloc_5618_, 1, v_a_5611_);
v___x_5617_ = v_reuseFailAlloc_5618_;
goto v_reusejp_5616_;
}
v_reusejp_5616_:
{
return v___x_5617_;
}
}
}
else
{
lean_object* v_a_5620_; lean_object* v_a_5621_; lean_object* v___x_5623_; uint8_t v_isShared_5624_; uint8_t v_isSharedCheck_5628_; 
v_a_5620_ = lean_ctor_get(v___x_5609_, 0);
v_a_5621_ = lean_ctor_get(v___x_5609_, 1);
v_isSharedCheck_5628_ = !lean_is_exclusive(v___x_5609_);
if (v_isSharedCheck_5628_ == 0)
{
v___x_5623_ = v___x_5609_;
v_isShared_5624_ = v_isSharedCheck_5628_;
goto v_resetjp_5622_;
}
else
{
lean_inc(v_a_5621_);
lean_inc(v_a_5620_);
lean_dec(v___x_5609_);
v___x_5623_ = lean_box(0);
v_isShared_5624_ = v_isSharedCheck_5628_;
goto v_resetjp_5622_;
}
v_resetjp_5622_:
{
lean_object* v___x_5626_; 
if (v_isShared_5624_ == 0)
{
v___x_5626_ = v___x_5623_;
goto v_reusejp_5625_;
}
else
{
lean_object* v_reuseFailAlloc_5627_; 
v_reuseFailAlloc_5627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5627_, 0, v_a_5620_);
lean_ctor_set(v_reuseFailAlloc_5627_, 1, v_a_5621_);
v___x_5626_ = v_reuseFailAlloc_5627_;
goto v_reusejp_5625_;
}
v_reusejp_5625_:
{
return v___x_5626_;
}
}
}
}
}
}
else
{
lean_object* v_a_5631_; lean_object* v_a_5632_; lean_object* v___x_5634_; uint8_t v_isShared_5635_; uint8_t v_isSharedCheck_5639_; 
lean_dec_ref(v___y_5585_);
lean_dec(v_depInfo_5584_);
lean_dec_ref(v_file_5582_);
lean_dec_ref(v_build_5581_);
v_a_5631_ = lean_ctor_get(v___x_5592_, 0);
v_a_5632_ = lean_ctor_get(v___x_5592_, 1);
v_isSharedCheck_5639_ = !lean_is_exclusive(v___x_5592_);
if (v_isSharedCheck_5639_ == 0)
{
v___x_5634_ = v___x_5592_;
v_isShared_5635_ = v_isSharedCheck_5639_;
goto v_resetjp_5633_;
}
else
{
lean_inc(v_a_5632_);
lean_inc(v_a_5631_);
lean_dec(v___x_5592_);
v___x_5634_ = lean_box(0);
v_isShared_5635_ = v_isSharedCheck_5639_;
goto v_resetjp_5633_;
}
v_resetjp_5633_:
{
lean_object* v___x_5637_; 
if (v_isShared_5635_ == 0)
{
v___x_5637_ = v___x_5634_;
goto v_reusejp_5636_;
}
else
{
lean_object* v_reuseFailAlloc_5638_; 
v_reuseFailAlloc_5638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5638_, 0, v_a_5631_);
lean_ctor_set(v_reuseFailAlloc_5638_, 1, v_a_5632_);
v___x_5637_ = v_reuseFailAlloc_5638_;
goto v_reusejp_5636_;
}
v_reusejp_5636_:
{
return v___x_5637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___boxed(lean_object* v_extraDepTrace_5640_, lean_object* v_build_5641_, lean_object* v_file_5642_, lean_object* v_text_5643_, lean_object* v_depInfo_5644_, lean_object* v___y_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_, lean_object* v___y_5648_, lean_object* v___y_5649_, lean_object* v___y_5650_, lean_object* v___y_5651_){
_start:
{
uint8_t v_text_boxed_5652_; lean_object* v_res_5653_; 
v_text_boxed_5652_ = lean_unbox(v_text_5643_);
v_res_5653_ = l_Lake_buildFileAfterDep___redArg___lam__0(v_extraDepTrace_5640_, v_build_5641_, v_file_5642_, v_text_boxed_5652_, v_depInfo_5644_, v___y_5645_, v___y_5646_, v___y_5647_, v___y_5648_, v___y_5649_, v___y_5650_);
lean_dec_ref(v___y_5649_);
lean_dec(v___y_5648_);
lean_dec(v___y_5647_);
lean_dec(v___y_5646_);
return v_res_5653_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg(lean_object* v_file_5654_, lean_object* v_dep_5655_, lean_object* v_build_5656_, lean_object* v_extraDepTrace_5657_, uint8_t v_text_5658_, lean_object* v_a_5659_, lean_object* v_a_5660_, lean_object* v_a_5661_, lean_object* v_a_5662_, lean_object* v_a_5663_, lean_object* v_a_5664_){
_start:
{
lean_object* v___x_5666_; lean_object* v___f_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; uint8_t v___x_5670_; lean_object* v___x_5671_; 
v___x_5666_ = lean_box(v_text_5658_);
v___f_5667_ = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_5667_, 0, v_extraDepTrace_5657_);
lean_closure_set(v___f_5667_, 1, v_build_5656_);
lean_closure_set(v___f_5667_, 2, v_file_5654_);
lean_closure_set(v___f_5667_, 3, v___x_5666_);
v___x_5668_ = l_Lake_instDataKindFilePath;
v___x_5669_ = lean_unsigned_to_nat(0u);
v___x_5670_ = 0;
v___x_5671_ = l_Lake_Job_mapM___redArg(v___x_5668_, v_dep_5655_, v___f_5667_, v___x_5669_, v___x_5670_, v_a_5659_, v_a_5660_, v_a_5661_, v_a_5662_, v_a_5663_, v_a_5664_);
return v___x_5671_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___boxed(lean_object* v_file_5672_, lean_object* v_dep_5673_, lean_object* v_build_5674_, lean_object* v_extraDepTrace_5675_, lean_object* v_text_5676_, lean_object* v_a_5677_, lean_object* v_a_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_, lean_object* v_a_5681_, lean_object* v_a_5682_, lean_object* v_a_5683_){
_start:
{
uint8_t v_text_boxed_5684_; lean_object* v_res_5685_; 
v_text_boxed_5684_ = lean_unbox(v_text_5676_);
v_res_5685_ = l_Lake_buildFileAfterDep___redArg(v_file_5672_, v_dep_5673_, v_build_5674_, v_extraDepTrace_5675_, v_text_boxed_5684_, v_a_5677_, v_a_5678_, v_a_5679_, v_a_5680_, v_a_5681_, v_a_5682_);
lean_dec_ref(v_a_5682_);
lean_dec_ref(v_a_5681_);
lean_dec(v_a_5680_);
lean_dec(v_a_5679_);
lean_dec(v_a_5678_);
return v_res_5685_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object* v_00_u03b1_5686_, lean_object* v_file_5687_, lean_object* v_dep_5688_, lean_object* v_build_5689_, lean_object* v_extraDepTrace_5690_, uint8_t v_text_5691_, lean_object* v_a_5692_, lean_object* v_a_5693_, lean_object* v_a_5694_, lean_object* v_a_5695_, lean_object* v_a_5696_, lean_object* v_a_5697_){
_start:
{
lean_object* v___x_5699_; lean_object* v___f_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; uint8_t v___x_5703_; lean_object* v___x_5704_; 
v___x_5699_ = lean_box(v_text_5691_);
v___f_5700_ = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_5700_, 0, v_extraDepTrace_5690_);
lean_closure_set(v___f_5700_, 1, v_build_5689_);
lean_closure_set(v___f_5700_, 2, v_file_5687_);
lean_closure_set(v___f_5700_, 3, v___x_5699_);
v___x_5701_ = l_Lake_instDataKindFilePath;
v___x_5702_ = lean_unsigned_to_nat(0u);
v___x_5703_ = 0;
v___x_5704_ = l_Lake_Job_mapM___redArg(v___x_5701_, v_dep_5688_, v___f_5700_, v___x_5702_, v___x_5703_, v_a_5692_, v_a_5693_, v_a_5694_, v_a_5695_, v_a_5696_, v_a_5697_);
return v___x_5704_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___boxed(lean_object* v_00_u03b1_5705_, lean_object* v_file_5706_, lean_object* v_dep_5707_, lean_object* v_build_5708_, lean_object* v_extraDepTrace_5709_, lean_object* v_text_5710_, lean_object* v_a_5711_, lean_object* v_a_5712_, lean_object* v_a_5713_, lean_object* v_a_5714_, lean_object* v_a_5715_, lean_object* v_a_5716_, lean_object* v_a_5717_){
_start:
{
uint8_t v_text_boxed_5718_; lean_object* v_res_5719_; 
v_text_boxed_5718_ = lean_unbox(v_text_5710_);
v_res_5719_ = l_Lake_buildFileAfterDep(v_00_u03b1_5705_, v_file_5706_, v_dep_5707_, v_build_5708_, v_extraDepTrace_5709_, v_text_boxed_5718_, v_a_5711_, v_a_5712_, v_a_5713_, v_a_5714_, v_a_5715_, v_a_5716_);
lean_dec_ref(v_a_5716_);
lean_dec_ref(v_a_5715_);
lean_dec(v_a_5714_);
lean_dec(v_a_5713_);
lean_dec(v_a_5712_);
return v_res_5719_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(lean_object* v_info_5720_){
_start:
{
lean_object* v___x_5722_; 
v___x_5722_ = l_Lake_computeBinFileHash(v_info_5720_);
if (lean_obj_tag(v___x_5722_) == 0)
{
lean_object* v_a_5723_; lean_object* v___x_5724_; 
v_a_5723_ = lean_ctor_get(v___x_5722_, 0);
lean_inc(v_a_5723_);
lean_dec_ref(v___x_5722_);
v___x_5724_ = lean_io_metadata(v_info_5720_);
if (lean_obj_tag(v___x_5724_) == 0)
{
lean_object* v_a_5725_; lean_object* v___x_5727_; uint8_t v_isShared_5728_; uint8_t v_isSharedCheck_5736_; 
v_a_5725_ = lean_ctor_get(v___x_5724_, 0);
v_isSharedCheck_5736_ = !lean_is_exclusive(v___x_5724_);
if (v_isSharedCheck_5736_ == 0)
{
v___x_5727_ = v___x_5724_;
v_isShared_5728_ = v_isSharedCheck_5736_;
goto v_resetjp_5726_;
}
else
{
lean_inc(v_a_5725_);
lean_dec(v___x_5724_);
v___x_5727_ = lean_box(0);
v_isShared_5728_ = v_isSharedCheck_5736_;
goto v_resetjp_5726_;
}
v_resetjp_5726_:
{
lean_object* v_modified_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; uint64_t v___x_5732_; lean_object* v___x_5734_; 
v_modified_5729_ = lean_ctor_get(v_a_5725_, 1);
lean_inc_ref(v_modified_5729_);
lean_dec(v_a_5725_);
v___x_5730_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_5731_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_5731_, 0, v_info_5720_);
lean_ctor_set(v___x_5731_, 1, v___x_5730_);
lean_ctor_set(v___x_5731_, 2, v_modified_5729_);
v___x_5732_ = lean_unbox_uint64(v_a_5723_);
lean_dec(v_a_5723_);
lean_ctor_set_uint64(v___x_5731_, sizeof(void*)*3, v___x_5732_);
if (v_isShared_5728_ == 0)
{
lean_ctor_set(v___x_5727_, 0, v___x_5731_);
v___x_5734_ = v___x_5727_;
goto v_reusejp_5733_;
}
else
{
lean_object* v_reuseFailAlloc_5735_; 
v_reuseFailAlloc_5735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5735_, 0, v___x_5731_);
v___x_5734_ = v_reuseFailAlloc_5735_;
goto v_reusejp_5733_;
}
v_reusejp_5733_:
{
return v___x_5734_;
}
}
}
else
{
lean_object* v_a_5737_; lean_object* v___x_5739_; uint8_t v_isShared_5740_; uint8_t v_isSharedCheck_5744_; 
lean_dec(v_a_5723_);
lean_dec_ref(v_info_5720_);
v_a_5737_ = lean_ctor_get(v___x_5724_, 0);
v_isSharedCheck_5744_ = !lean_is_exclusive(v___x_5724_);
if (v_isSharedCheck_5744_ == 0)
{
v___x_5739_ = v___x_5724_;
v_isShared_5740_ = v_isSharedCheck_5744_;
goto v_resetjp_5738_;
}
else
{
lean_inc(v_a_5737_);
lean_dec(v___x_5724_);
v___x_5739_ = lean_box(0);
v_isShared_5740_ = v_isSharedCheck_5744_;
goto v_resetjp_5738_;
}
v_resetjp_5738_:
{
lean_object* v___x_5742_; 
if (v_isShared_5740_ == 0)
{
v___x_5742_ = v___x_5739_;
goto v_reusejp_5741_;
}
else
{
lean_object* v_reuseFailAlloc_5743_; 
v_reuseFailAlloc_5743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5743_, 0, v_a_5737_);
v___x_5742_ = v_reuseFailAlloc_5743_;
goto v_reusejp_5741_;
}
v_reusejp_5741_:
{
return v___x_5742_;
}
}
}
}
else
{
lean_object* v_a_5745_; lean_object* v___x_5747_; uint8_t v_isShared_5748_; uint8_t v_isSharedCheck_5752_; 
lean_dec_ref(v_info_5720_);
v_a_5745_ = lean_ctor_get(v___x_5722_, 0);
v_isSharedCheck_5752_ = !lean_is_exclusive(v___x_5722_);
if (v_isSharedCheck_5752_ == 0)
{
v___x_5747_ = v___x_5722_;
v_isShared_5748_ = v_isSharedCheck_5752_;
goto v_resetjp_5746_;
}
else
{
lean_inc(v_a_5745_);
lean_dec(v___x_5722_);
v___x_5747_ = lean_box(0);
v_isShared_5748_ = v_isSharedCheck_5752_;
goto v_resetjp_5746_;
}
v_resetjp_5746_:
{
lean_object* v___x_5750_; 
if (v_isShared_5748_ == 0)
{
v___x_5750_ = v___x_5747_;
goto v_reusejp_5749_;
}
else
{
lean_object* v_reuseFailAlloc_5751_; 
v_reuseFailAlloc_5751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5751_, 0, v_a_5745_);
v___x_5750_ = v_reuseFailAlloc_5751_;
goto v_reusejp_5749_;
}
v_reusejp_5749_:
{
return v___x_5750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0___boxed(lean_object* v_info_5753_, lean_object* v_a_5754_){
_start:
{
lean_object* v_res_5755_; 
v_res_5755_ = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(v_info_5753_);
return v_res_5755_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0(lean_object* v_path_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_, lean_object* v___y_5761_, lean_object* v___y_5762_){
_start:
{
lean_object* v_log_5764_; uint8_t v_action_5765_; uint8_t v_wantsRebuild_5766_; lean_object* v_trace_5767_; lean_object* v_buildTime_5768_; lean_object* v___x_5770_; uint8_t v_isShared_5771_; uint8_t v_isSharedCheck_5788_; 
v_log_5764_ = lean_ctor_get(v___y_5762_, 0);
v_action_5765_ = lean_ctor_get_uint8(v___y_5762_, sizeof(void*)*3);
v_wantsRebuild_5766_ = lean_ctor_get_uint8(v___y_5762_, sizeof(void*)*3 + 1);
v_trace_5767_ = lean_ctor_get(v___y_5762_, 1);
v_buildTime_5768_ = lean_ctor_get(v___y_5762_, 2);
v_isSharedCheck_5788_ = !lean_is_exclusive(v___y_5762_);
if (v_isSharedCheck_5788_ == 0)
{
v___x_5770_ = v___y_5762_;
v_isShared_5771_ = v_isSharedCheck_5788_;
goto v_resetjp_5769_;
}
else
{
lean_inc(v_buildTime_5768_);
lean_inc(v_trace_5767_);
lean_inc(v_log_5764_);
lean_dec(v___y_5762_);
v___x_5770_ = lean_box(0);
v_isShared_5771_ = v_isSharedCheck_5788_;
goto v_resetjp_5769_;
}
v_resetjp_5769_:
{
lean_object* v___x_5772_; 
lean_inc_ref(v_path_5756_);
v___x_5772_ = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(v_path_5756_);
if (lean_obj_tag(v___x_5772_) == 0)
{
lean_object* v_a_5773_; lean_object* v___x_5775_; 
lean_dec_ref(v_trace_5767_);
v_a_5773_ = lean_ctor_get(v___x_5772_, 0);
lean_inc(v_a_5773_);
lean_dec_ref(v___x_5772_);
if (v_isShared_5771_ == 0)
{
lean_ctor_set(v___x_5770_, 1, v_a_5773_);
v___x_5775_ = v___x_5770_;
goto v_reusejp_5774_;
}
else
{
lean_object* v_reuseFailAlloc_5777_; 
v_reuseFailAlloc_5777_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5777_, 0, v_log_5764_);
lean_ctor_set(v_reuseFailAlloc_5777_, 1, v_a_5773_);
lean_ctor_set(v_reuseFailAlloc_5777_, 2, v_buildTime_5768_);
lean_ctor_set_uint8(v_reuseFailAlloc_5777_, sizeof(void*)*3, v_action_5765_);
lean_ctor_set_uint8(v_reuseFailAlloc_5777_, sizeof(void*)*3 + 1, v_wantsRebuild_5766_);
v___x_5775_ = v_reuseFailAlloc_5777_;
goto v_reusejp_5774_;
}
v_reusejp_5774_:
{
lean_object* v___x_5776_; 
v___x_5776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5776_, 0, v_path_5756_);
lean_ctor_set(v___x_5776_, 1, v___x_5775_);
return v___x_5776_;
}
}
else
{
lean_object* v_a_5778_; lean_object* v___x_5779_; uint8_t v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5783_; lean_object* v___x_5785_; 
lean_dec_ref(v_path_5756_);
v_a_5778_ = lean_ctor_get(v___x_5772_, 0);
lean_inc(v_a_5778_);
lean_dec_ref(v___x_5772_);
v___x_5779_ = lean_io_error_to_string(v_a_5778_);
v___x_5780_ = 3;
v___x_5781_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5781_, 0, v___x_5779_);
lean_ctor_set_uint8(v___x_5781_, sizeof(void*)*1, v___x_5780_);
v___x_5782_ = lean_array_get_size(v_log_5764_);
v___x_5783_ = lean_array_push(v_log_5764_, v___x_5781_);
if (v_isShared_5771_ == 0)
{
lean_ctor_set(v___x_5770_, 0, v___x_5783_);
v___x_5785_ = v___x_5770_;
goto v_reusejp_5784_;
}
else
{
lean_object* v_reuseFailAlloc_5787_; 
v_reuseFailAlloc_5787_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5787_, 0, v___x_5783_);
lean_ctor_set(v_reuseFailAlloc_5787_, 1, v_trace_5767_);
lean_ctor_set(v_reuseFailAlloc_5787_, 2, v_buildTime_5768_);
lean_ctor_set_uint8(v_reuseFailAlloc_5787_, sizeof(void*)*3, v_action_5765_);
lean_ctor_set_uint8(v_reuseFailAlloc_5787_, sizeof(void*)*3 + 1, v_wantsRebuild_5766_);
v___x_5785_ = v_reuseFailAlloc_5787_;
goto v_reusejp_5784_;
}
v_reusejp_5784_:
{
lean_object* v___x_5786_; 
v___x_5786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5786_, 0, v___x_5782_);
lean_ctor_set(v___x_5786_, 1, v___x_5785_);
return v___x_5786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0___boxed(lean_object* v_path_5789_, lean_object* v___y_5790_, lean_object* v___y_5791_, lean_object* v___y_5792_, lean_object* v___y_5793_, lean_object* v___y_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_){
_start:
{
lean_object* v_res_5797_; 
v_res_5797_ = l_Lake_inputBinFile___redArg___lam__0(v_path_5789_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_, v___y_5794_, v___y_5795_);
lean_dec_ref(v___y_5794_);
lean_dec(v___y_5793_);
lean_dec(v___y_5792_);
lean_dec(v___y_5791_);
lean_dec_ref(v___y_5790_);
return v_res_5797_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg(lean_object* v_path_5799_, lean_object* v_a_5800_, lean_object* v_a_5801_, lean_object* v_a_5802_, lean_object* v_a_5803_, lean_object* v_a_5804_){
_start:
{
lean_object* v___f_5806_; lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; 
v___f_5806_ = lean_alloc_closure((void*)(l_Lake_inputBinFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5806_, 0, v_path_5799_);
v___x_5807_ = l_Lake_instDataKindFilePath;
v___x_5808_ = lean_unsigned_to_nat(0u);
v___x_5809_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
v___x_5810_ = l_Lake_Job_async___redArg(v___x_5807_, v___f_5806_, v___x_5808_, v___x_5809_, v_a_5800_, v_a_5801_, v_a_5802_, v_a_5803_, v_a_5804_);
return v___x_5810_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___boxed(lean_object* v_path_5811_, lean_object* v_a_5812_, lean_object* v_a_5813_, lean_object* v_a_5814_, lean_object* v_a_5815_, lean_object* v_a_5816_, lean_object* v_a_5817_){
_start:
{
lean_object* v_res_5818_; 
v_res_5818_ = l_Lake_inputBinFile___redArg(v_path_5811_, v_a_5812_, v_a_5813_, v_a_5814_, v_a_5815_, v_a_5816_);
lean_dec_ref(v_a_5816_);
lean_dec(v_a_5815_);
lean_dec(v_a_5814_);
lean_dec(v_a_5813_);
return v_res_5818_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object* v_path_5819_, lean_object* v_a_5820_, lean_object* v_a_5821_, lean_object* v_a_5822_, lean_object* v_a_5823_, lean_object* v_a_5824_, lean_object* v_a_5825_){
_start:
{
lean_object* v___x_5827_; 
v___x_5827_ = l_Lake_inputBinFile___redArg(v_path_5819_, v_a_5820_, v_a_5821_, v_a_5822_, v_a_5823_, v_a_5824_);
return v___x_5827_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___boxed(lean_object* v_path_5828_, lean_object* v_a_5829_, lean_object* v_a_5830_, lean_object* v_a_5831_, lean_object* v_a_5832_, lean_object* v_a_5833_, lean_object* v_a_5834_, lean_object* v_a_5835_){
_start:
{
lean_object* v_res_5836_; 
v_res_5836_ = l_Lake_inputBinFile(v_path_5828_, v_a_5829_, v_a_5830_, v_a_5831_, v_a_5832_, v_a_5833_, v_a_5834_);
lean_dec_ref(v_a_5834_);
lean_dec_ref(v_a_5833_);
lean_dec(v_a_5832_);
lean_dec(v_a_5831_);
lean_dec(v_a_5830_);
return v_res_5836_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(lean_object* v_info_5837_){
_start:
{
lean_object* v___x_5839_; 
v___x_5839_ = l_Lake_computeTextFileHash(v_info_5837_);
if (lean_obj_tag(v___x_5839_) == 0)
{
lean_object* v_a_5840_; lean_object* v___x_5841_; 
v_a_5840_ = lean_ctor_get(v___x_5839_, 0);
lean_inc(v_a_5840_);
lean_dec_ref(v___x_5839_);
v___x_5841_ = lean_io_metadata(v_info_5837_);
if (lean_obj_tag(v___x_5841_) == 0)
{
lean_object* v_a_5842_; lean_object* v___x_5844_; uint8_t v_isShared_5845_; uint8_t v_isSharedCheck_5853_; 
v_a_5842_ = lean_ctor_get(v___x_5841_, 0);
v_isSharedCheck_5853_ = !lean_is_exclusive(v___x_5841_);
if (v_isSharedCheck_5853_ == 0)
{
v___x_5844_ = v___x_5841_;
v_isShared_5845_ = v_isSharedCheck_5853_;
goto v_resetjp_5843_;
}
else
{
lean_inc(v_a_5842_);
lean_dec(v___x_5841_);
v___x_5844_ = lean_box(0);
v_isShared_5845_ = v_isSharedCheck_5853_;
goto v_resetjp_5843_;
}
v_resetjp_5843_:
{
lean_object* v_modified_5846_; lean_object* v___x_5847_; lean_object* v___x_5848_; uint64_t v___x_5849_; lean_object* v___x_5851_; 
v_modified_5846_ = lean_ctor_get(v_a_5842_, 1);
lean_inc_ref(v_modified_5846_);
lean_dec(v_a_5842_);
v___x_5847_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_5848_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_5848_, 0, v_info_5837_);
lean_ctor_set(v___x_5848_, 1, v___x_5847_);
lean_ctor_set(v___x_5848_, 2, v_modified_5846_);
v___x_5849_ = lean_unbox_uint64(v_a_5840_);
lean_dec(v_a_5840_);
lean_ctor_set_uint64(v___x_5848_, sizeof(void*)*3, v___x_5849_);
if (v_isShared_5845_ == 0)
{
lean_ctor_set(v___x_5844_, 0, v___x_5848_);
v___x_5851_ = v___x_5844_;
goto v_reusejp_5850_;
}
else
{
lean_object* v_reuseFailAlloc_5852_; 
v_reuseFailAlloc_5852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5852_, 0, v___x_5848_);
v___x_5851_ = v_reuseFailAlloc_5852_;
goto v_reusejp_5850_;
}
v_reusejp_5850_:
{
return v___x_5851_;
}
}
}
else
{
lean_object* v_a_5854_; lean_object* v___x_5856_; uint8_t v_isShared_5857_; uint8_t v_isSharedCheck_5861_; 
lean_dec(v_a_5840_);
lean_dec_ref(v_info_5837_);
v_a_5854_ = lean_ctor_get(v___x_5841_, 0);
v_isSharedCheck_5861_ = !lean_is_exclusive(v___x_5841_);
if (v_isSharedCheck_5861_ == 0)
{
v___x_5856_ = v___x_5841_;
v_isShared_5857_ = v_isSharedCheck_5861_;
goto v_resetjp_5855_;
}
else
{
lean_inc(v_a_5854_);
lean_dec(v___x_5841_);
v___x_5856_ = lean_box(0);
v_isShared_5857_ = v_isSharedCheck_5861_;
goto v_resetjp_5855_;
}
v_resetjp_5855_:
{
lean_object* v___x_5859_; 
if (v_isShared_5857_ == 0)
{
v___x_5859_ = v___x_5856_;
goto v_reusejp_5858_;
}
else
{
lean_object* v_reuseFailAlloc_5860_; 
v_reuseFailAlloc_5860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5860_, 0, v_a_5854_);
v___x_5859_ = v_reuseFailAlloc_5860_;
goto v_reusejp_5858_;
}
v_reusejp_5858_:
{
return v___x_5859_;
}
}
}
}
else
{
lean_object* v_a_5862_; lean_object* v___x_5864_; uint8_t v_isShared_5865_; uint8_t v_isSharedCheck_5869_; 
lean_dec_ref(v_info_5837_);
v_a_5862_ = lean_ctor_get(v___x_5839_, 0);
v_isSharedCheck_5869_ = !lean_is_exclusive(v___x_5839_);
if (v_isSharedCheck_5869_ == 0)
{
v___x_5864_ = v___x_5839_;
v_isShared_5865_ = v_isSharedCheck_5869_;
goto v_resetjp_5863_;
}
else
{
lean_inc(v_a_5862_);
lean_dec(v___x_5839_);
v___x_5864_ = lean_box(0);
v_isShared_5865_ = v_isSharedCheck_5869_;
goto v_resetjp_5863_;
}
v_resetjp_5863_:
{
lean_object* v___x_5867_; 
if (v_isShared_5865_ == 0)
{
v___x_5867_ = v___x_5864_;
goto v_reusejp_5866_;
}
else
{
lean_object* v_reuseFailAlloc_5868_; 
v_reuseFailAlloc_5868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5868_, 0, v_a_5862_);
v___x_5867_ = v_reuseFailAlloc_5868_;
goto v_reusejp_5866_;
}
v_reusejp_5866_:
{
return v___x_5867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0___boxed(lean_object* v_info_5870_, lean_object* v_a_5871_){
_start:
{
lean_object* v_res_5872_; 
v_res_5872_ = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(v_info_5870_);
return v_res_5872_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0(lean_object* v_path_5873_, lean_object* v___y_5874_, lean_object* v___y_5875_, lean_object* v___y_5876_, lean_object* v___y_5877_, lean_object* v___y_5878_, lean_object* v___y_5879_){
_start:
{
lean_object* v_log_5881_; uint8_t v_action_5882_; uint8_t v_wantsRebuild_5883_; lean_object* v_trace_5884_; lean_object* v_buildTime_5885_; lean_object* v___x_5887_; uint8_t v_isShared_5888_; uint8_t v_isSharedCheck_5905_; 
v_log_5881_ = lean_ctor_get(v___y_5879_, 0);
v_action_5882_ = lean_ctor_get_uint8(v___y_5879_, sizeof(void*)*3);
v_wantsRebuild_5883_ = lean_ctor_get_uint8(v___y_5879_, sizeof(void*)*3 + 1);
v_trace_5884_ = lean_ctor_get(v___y_5879_, 1);
v_buildTime_5885_ = lean_ctor_get(v___y_5879_, 2);
v_isSharedCheck_5905_ = !lean_is_exclusive(v___y_5879_);
if (v_isSharedCheck_5905_ == 0)
{
v___x_5887_ = v___y_5879_;
v_isShared_5888_ = v_isSharedCheck_5905_;
goto v_resetjp_5886_;
}
else
{
lean_inc(v_buildTime_5885_);
lean_inc(v_trace_5884_);
lean_inc(v_log_5881_);
lean_dec(v___y_5879_);
v___x_5887_ = lean_box(0);
v_isShared_5888_ = v_isSharedCheck_5905_;
goto v_resetjp_5886_;
}
v_resetjp_5886_:
{
lean_object* v___x_5889_; 
lean_inc_ref(v_path_5873_);
v___x_5889_ = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(v_path_5873_);
if (lean_obj_tag(v___x_5889_) == 0)
{
lean_object* v_a_5890_; lean_object* v___x_5892_; 
lean_dec_ref(v_trace_5884_);
v_a_5890_ = lean_ctor_get(v___x_5889_, 0);
lean_inc(v_a_5890_);
lean_dec_ref(v___x_5889_);
if (v_isShared_5888_ == 0)
{
lean_ctor_set(v___x_5887_, 1, v_a_5890_);
v___x_5892_ = v___x_5887_;
goto v_reusejp_5891_;
}
else
{
lean_object* v_reuseFailAlloc_5894_; 
v_reuseFailAlloc_5894_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5894_, 0, v_log_5881_);
lean_ctor_set(v_reuseFailAlloc_5894_, 1, v_a_5890_);
lean_ctor_set(v_reuseFailAlloc_5894_, 2, v_buildTime_5885_);
lean_ctor_set_uint8(v_reuseFailAlloc_5894_, sizeof(void*)*3, v_action_5882_);
lean_ctor_set_uint8(v_reuseFailAlloc_5894_, sizeof(void*)*3 + 1, v_wantsRebuild_5883_);
v___x_5892_ = v_reuseFailAlloc_5894_;
goto v_reusejp_5891_;
}
v_reusejp_5891_:
{
lean_object* v___x_5893_; 
v___x_5893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5893_, 0, v_path_5873_);
lean_ctor_set(v___x_5893_, 1, v___x_5892_);
return v___x_5893_;
}
}
else
{
lean_object* v_a_5895_; lean_object* v___x_5896_; uint8_t v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5902_; 
lean_dec_ref(v_path_5873_);
v_a_5895_ = lean_ctor_get(v___x_5889_, 0);
lean_inc(v_a_5895_);
lean_dec_ref(v___x_5889_);
v___x_5896_ = lean_io_error_to_string(v_a_5895_);
v___x_5897_ = 3;
v___x_5898_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5898_, 0, v___x_5896_);
lean_ctor_set_uint8(v___x_5898_, sizeof(void*)*1, v___x_5897_);
v___x_5899_ = lean_array_get_size(v_log_5881_);
v___x_5900_ = lean_array_push(v_log_5881_, v___x_5898_);
if (v_isShared_5888_ == 0)
{
lean_ctor_set(v___x_5887_, 0, v___x_5900_);
v___x_5902_ = v___x_5887_;
goto v_reusejp_5901_;
}
else
{
lean_object* v_reuseFailAlloc_5904_; 
v_reuseFailAlloc_5904_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5904_, 0, v___x_5900_);
lean_ctor_set(v_reuseFailAlloc_5904_, 1, v_trace_5884_);
lean_ctor_set(v_reuseFailAlloc_5904_, 2, v_buildTime_5885_);
lean_ctor_set_uint8(v_reuseFailAlloc_5904_, sizeof(void*)*3, v_action_5882_);
lean_ctor_set_uint8(v_reuseFailAlloc_5904_, sizeof(void*)*3 + 1, v_wantsRebuild_5883_);
v___x_5902_ = v_reuseFailAlloc_5904_;
goto v_reusejp_5901_;
}
v_reusejp_5901_:
{
lean_object* v___x_5903_; 
v___x_5903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5903_, 0, v___x_5899_);
lean_ctor_set(v___x_5903_, 1, v___x_5902_);
return v___x_5903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0___boxed(lean_object* v_path_5906_, lean_object* v___y_5907_, lean_object* v___y_5908_, lean_object* v___y_5909_, lean_object* v___y_5910_, lean_object* v___y_5911_, lean_object* v___y_5912_, lean_object* v___y_5913_){
_start:
{
lean_object* v_res_5914_; 
v_res_5914_ = l_Lake_inputTextFile___redArg___lam__0(v_path_5906_, v___y_5907_, v___y_5908_, v___y_5909_, v___y_5910_, v___y_5911_, v___y_5912_);
lean_dec_ref(v___y_5911_);
lean_dec(v___y_5910_);
lean_dec(v___y_5909_);
lean_dec(v___y_5908_);
lean_dec_ref(v___y_5907_);
return v_res_5914_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg(lean_object* v_path_5915_, lean_object* v_a_5916_, lean_object* v_a_5917_, lean_object* v_a_5918_, lean_object* v_a_5919_, lean_object* v_a_5920_){
_start:
{
lean_object* v___f_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; 
v___f_5922_ = lean_alloc_closure((void*)(l_Lake_inputTextFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5922_, 0, v_path_5915_);
v___x_5923_ = l_Lake_instDataKindFilePath;
v___x_5924_ = lean_unsigned_to_nat(0u);
v___x_5925_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
v___x_5926_ = l_Lake_Job_async___redArg(v___x_5923_, v___f_5922_, v___x_5924_, v___x_5925_, v_a_5916_, v_a_5917_, v_a_5918_, v_a_5919_, v_a_5920_);
return v___x_5926_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___boxed(lean_object* v_path_5927_, lean_object* v_a_5928_, lean_object* v_a_5929_, lean_object* v_a_5930_, lean_object* v_a_5931_, lean_object* v_a_5932_, lean_object* v_a_5933_){
_start:
{
lean_object* v_res_5934_; 
v_res_5934_ = l_Lake_inputTextFile___redArg(v_path_5927_, v_a_5928_, v_a_5929_, v_a_5930_, v_a_5931_, v_a_5932_);
lean_dec_ref(v_a_5932_);
lean_dec(v_a_5931_);
lean_dec(v_a_5930_);
lean_dec(v_a_5929_);
return v_res_5934_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object* v_path_5935_, lean_object* v_a_5936_, lean_object* v_a_5937_, lean_object* v_a_5938_, lean_object* v_a_5939_, lean_object* v_a_5940_, lean_object* v_a_5941_){
_start:
{
lean_object* v___x_5943_; 
v___x_5943_ = l_Lake_inputTextFile___redArg(v_path_5935_, v_a_5936_, v_a_5937_, v_a_5938_, v_a_5939_, v_a_5940_);
return v___x_5943_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___boxed(lean_object* v_path_5944_, lean_object* v_a_5945_, lean_object* v_a_5946_, lean_object* v_a_5947_, lean_object* v_a_5948_, lean_object* v_a_5949_, lean_object* v_a_5950_, lean_object* v_a_5951_){
_start:
{
lean_object* v_res_5952_; 
v_res_5952_ = l_Lake_inputTextFile(v_path_5944_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_);
lean_dec_ref(v_a_5950_);
lean_dec_ref(v_a_5949_);
lean_dec(v_a_5948_);
lean_dec(v_a_5947_);
lean_dec(v_a_5946_);
return v_res_5952_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg(lean_object* v_path_5953_, uint8_t v_text_5954_, lean_object* v_a_5955_, lean_object* v_a_5956_, lean_object* v_a_5957_, lean_object* v_a_5958_, lean_object* v_a_5959_){
_start:
{
if (v_text_5954_ == 0)
{
lean_object* v___x_5961_; 
v___x_5961_ = l_Lake_inputBinFile___redArg(v_path_5953_, v_a_5955_, v_a_5956_, v_a_5957_, v_a_5958_, v_a_5959_);
return v___x_5961_;
}
else
{
lean_object* v___x_5962_; 
v___x_5962_ = l_Lake_inputTextFile___redArg(v_path_5953_, v_a_5955_, v_a_5956_, v_a_5957_, v_a_5958_, v_a_5959_);
return v___x_5962_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg___boxed(lean_object* v_path_5963_, lean_object* v_text_5964_, lean_object* v_a_5965_, lean_object* v_a_5966_, lean_object* v_a_5967_, lean_object* v_a_5968_, lean_object* v_a_5969_, lean_object* v_a_5970_){
_start:
{
uint8_t v_text_boxed_5971_; lean_object* v_res_5972_; 
v_text_boxed_5971_ = lean_unbox(v_text_5964_);
v_res_5972_ = l_Lake_inputFile___redArg(v_path_5963_, v_text_boxed_5971_, v_a_5965_, v_a_5966_, v_a_5967_, v_a_5968_, v_a_5969_);
lean_dec_ref(v_a_5969_);
lean_dec(v_a_5968_);
lean_dec(v_a_5967_);
lean_dec(v_a_5966_);
return v_res_5972_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object* v_path_5973_, uint8_t v_text_5974_, lean_object* v_a_5975_, lean_object* v_a_5976_, lean_object* v_a_5977_, lean_object* v_a_5978_, lean_object* v_a_5979_, lean_object* v_a_5980_){
_start:
{
if (v_text_5974_ == 0)
{
lean_object* v___x_5982_; 
v___x_5982_ = l_Lake_inputBinFile___redArg(v_path_5973_, v_a_5975_, v_a_5976_, v_a_5977_, v_a_5978_, v_a_5979_);
return v___x_5982_;
}
else
{
lean_object* v___x_5983_; 
v___x_5983_ = l_Lake_inputTextFile___redArg(v_path_5973_, v_a_5975_, v_a_5976_, v_a_5977_, v_a_5978_, v_a_5979_);
return v___x_5983_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object* v_path_5984_, lean_object* v_text_5985_, lean_object* v_a_5986_, lean_object* v_a_5987_, lean_object* v_a_5988_, lean_object* v_a_5989_, lean_object* v_a_5990_, lean_object* v_a_5991_, lean_object* v_a_5992_){
_start:
{
uint8_t v_text_boxed_5993_; lean_object* v_res_5994_; 
v_text_boxed_5993_ = lean_unbox(v_text_5985_);
v_res_5994_ = l_Lake_inputFile(v_path_5984_, v_text_boxed_5993_, v_a_5986_, v_a_5987_, v_a_5988_, v_a_5989_, v_a_5990_, v_a_5991_);
lean_dec_ref(v_a_5991_);
lean_dec_ref(v_a_5990_);
lean_dec(v_a_5989_);
lean_dec(v_a_5988_);
lean_dec(v_a_5987_);
return v_res_5994_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0(lean_object* v_x_5995_){
_start:
{
uint8_t v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; 
v___x_5997_ = 1;
v___x_5998_ = lean_box(v___x_5997_);
v___x_5999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5999_, 0, v___x_5998_);
return v___x_5999_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0___boxed(lean_object* v_x_6000_, lean_object* v___y_6001_){
_start:
{
lean_object* v_res_6002_; 
v_res_6002_ = l_Lake_inputDir___lam__0(v_x_6000_);
lean_dec_ref(v_x_6000_);
return v_res_6002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(lean_object* v_filter_6003_, lean_object* v_as_6004_, size_t v_i_6005_, size_t v_stop_6006_, lean_object* v_b_6007_, lean_object* v___y_6008_){
_start:
{
lean_object* v_a_6011_; lean_object* v_a_6012_; uint8_t v___x_6016_; 
v___x_6016_ = lean_usize_dec_eq(v_i_6005_, v_stop_6006_);
if (v___x_6016_ == 0)
{
lean_object* v___x_6017_; uint8_t v___x_6018_; 
v___x_6017_ = lean_array_uget_borrowed(v_as_6004_, v_i_6005_);
v___x_6018_ = l_System_FilePath_isDir(v___x_6017_);
if (v___x_6018_ == 0)
{
lean_object* v___x_6019_; uint8_t v___x_6020_; 
lean_inc_ref(v_filter_6003_);
lean_inc(v___x_6017_);
v___x_6019_ = lean_apply_1(v_filter_6003_, v___x_6017_);
v___x_6020_ = lean_unbox(v___x_6019_);
if (v___x_6020_ == 0)
{
v_a_6011_ = v_b_6007_;
v_a_6012_ = v___y_6008_;
goto v___jp_6010_;
}
else
{
lean_object* v___x_6021_; 
lean_inc(v___x_6017_);
v___x_6021_ = lean_array_push(v_b_6007_, v___x_6017_);
v_a_6011_ = v___x_6021_;
v_a_6012_ = v___y_6008_;
goto v___jp_6010_;
}
}
else
{
v_a_6011_ = v_b_6007_;
v_a_6012_ = v___y_6008_;
goto v___jp_6010_;
}
}
else
{
lean_object* v___x_6022_; 
lean_dec_ref(v_filter_6003_);
v___x_6022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6022_, 0, v_b_6007_);
lean_ctor_set(v___x_6022_, 1, v___y_6008_);
return v___x_6022_;
}
v___jp_6010_:
{
size_t v___x_6013_; size_t v___x_6014_; 
v___x_6013_ = ((size_t)1ULL);
v___x_6014_ = lean_usize_add(v_i_6005_, v___x_6013_);
v_i_6005_ = v___x_6014_;
v_b_6007_ = v_a_6011_;
v___y_6008_ = v_a_6012_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg___boxed(lean_object* v_filter_6023_, lean_object* v_as_6024_, lean_object* v_i_6025_, lean_object* v_stop_6026_, lean_object* v_b_6027_, lean_object* v___y_6028_, lean_object* v___y_6029_){
_start:
{
size_t v_i_boxed_6030_; size_t v_stop_boxed_6031_; lean_object* v_res_6032_; 
v_i_boxed_6030_ = lean_unbox_usize(v_i_6025_);
lean_dec(v_i_6025_);
v_stop_boxed_6031_ = lean_unbox_usize(v_stop_6026_);
lean_dec(v_stop_6026_);
v_res_6032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6023_, v_as_6024_, v_i_boxed_6030_, v_stop_boxed_6031_, v_b_6027_, v___y_6028_);
lean_dec_ref(v_as_6024_);
return v_res_6032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(lean_object* v_hi_6033_, lean_object* v_pivot_6034_, lean_object* v_as_6035_, lean_object* v_i_6036_, lean_object* v_k_6037_){
_start:
{
uint8_t v___x_6038_; 
v___x_6038_ = lean_nat_dec_lt(v_k_6037_, v_hi_6033_);
if (v___x_6038_ == 0)
{
lean_object* v___x_6039_; lean_object* v___x_6040_; 
lean_dec(v_k_6037_);
v___x_6039_ = lean_array_fswap(v_as_6035_, v_i_6036_, v_hi_6033_);
v___x_6040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6040_, 0, v_i_6036_);
lean_ctor_set(v___x_6040_, 1, v___x_6039_);
return v___x_6040_;
}
else
{
lean_object* v___x_6041_; uint8_t v___x_6042_; 
v___x_6041_ = lean_array_fget_borrowed(v_as_6035_, v_k_6037_);
v___x_6042_ = lean_string_dec_lt(v___x_6041_, v_pivot_6034_);
if (v___x_6042_ == 0)
{
lean_object* v___x_6043_; lean_object* v___x_6044_; 
v___x_6043_ = lean_unsigned_to_nat(1u);
v___x_6044_ = lean_nat_add(v_k_6037_, v___x_6043_);
lean_dec(v_k_6037_);
v_k_6037_ = v___x_6044_;
goto _start;
}
else
{
lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; 
v___x_6046_ = lean_array_fswap(v_as_6035_, v_i_6036_, v_k_6037_);
v___x_6047_ = lean_unsigned_to_nat(1u);
v___x_6048_ = lean_nat_add(v_i_6036_, v___x_6047_);
lean_dec(v_i_6036_);
v___x_6049_ = lean_nat_add(v_k_6037_, v___x_6047_);
lean_dec(v_k_6037_);
v_as_6035_ = v___x_6046_;
v_i_6036_ = v___x_6048_;
v_k_6037_ = v___x_6049_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg___boxed(lean_object* v_hi_6051_, lean_object* v_pivot_6052_, lean_object* v_as_6053_, lean_object* v_i_6054_, lean_object* v_k_6055_){
_start:
{
lean_object* v_res_6056_; 
v_res_6056_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(v_hi_6051_, v_pivot_6052_, v_as_6053_, v_i_6054_, v_k_6055_);
lean_dec_ref(v_pivot_6052_);
lean_dec(v_hi_6051_);
return v_res_6056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(lean_object* v_n_6057_, lean_object* v_as_6058_, lean_object* v_lo_6059_, lean_object* v_hi_6060_){
_start:
{
lean_object* v___y_6062_; uint8_t v___x_6072_; 
v___x_6072_ = lean_nat_dec_lt(v_lo_6059_, v_hi_6060_);
if (v___x_6072_ == 0)
{
lean_dec(v_lo_6059_);
return v_as_6058_;
}
else
{
lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v_mid_6075_; lean_object* v___y_6077_; lean_object* v___y_6083_; lean_object* v___x_6088_; lean_object* v___x_6089_; uint8_t v___x_6090_; 
v___x_6073_ = lean_nat_add(v_lo_6059_, v_hi_6060_);
v___x_6074_ = lean_unsigned_to_nat(1u);
v_mid_6075_ = lean_nat_shiftr(v___x_6073_, v___x_6074_);
lean_dec(v___x_6073_);
v___x_6088_ = lean_array_fget_borrowed(v_as_6058_, v_mid_6075_);
v___x_6089_ = lean_array_fget_borrowed(v_as_6058_, v_lo_6059_);
v___x_6090_ = lean_string_dec_lt(v___x_6088_, v___x_6089_);
if (v___x_6090_ == 0)
{
v___y_6083_ = v_as_6058_;
goto v___jp_6082_;
}
else
{
lean_object* v___x_6091_; 
v___x_6091_ = lean_array_fswap(v_as_6058_, v_lo_6059_, v_mid_6075_);
v___y_6083_ = v___x_6091_;
goto v___jp_6082_;
}
v___jp_6076_:
{
lean_object* v___x_6078_; lean_object* v___x_6079_; uint8_t v___x_6080_; 
v___x_6078_ = lean_array_fget_borrowed(v___y_6077_, v_mid_6075_);
v___x_6079_ = lean_array_fget_borrowed(v___y_6077_, v_hi_6060_);
v___x_6080_ = lean_string_dec_lt(v___x_6078_, v___x_6079_);
if (v___x_6080_ == 0)
{
lean_dec(v_mid_6075_);
v___y_6062_ = v___y_6077_;
goto v___jp_6061_;
}
else
{
lean_object* v___x_6081_; 
v___x_6081_ = lean_array_fswap(v___y_6077_, v_mid_6075_, v_hi_6060_);
lean_dec(v_mid_6075_);
v___y_6062_ = v___x_6081_;
goto v___jp_6061_;
}
}
v___jp_6082_:
{
lean_object* v___x_6084_; lean_object* v___x_6085_; uint8_t v___x_6086_; 
v___x_6084_ = lean_array_fget_borrowed(v___y_6083_, v_hi_6060_);
v___x_6085_ = lean_array_fget_borrowed(v___y_6083_, v_lo_6059_);
v___x_6086_ = lean_string_dec_lt(v___x_6084_, v___x_6085_);
if (v___x_6086_ == 0)
{
v___y_6077_ = v___y_6083_;
goto v___jp_6076_;
}
else
{
lean_object* v___x_6087_; 
v___x_6087_ = lean_array_fswap(v___y_6083_, v_lo_6059_, v_hi_6060_);
v___y_6077_ = v___x_6087_;
goto v___jp_6076_;
}
}
}
v___jp_6061_:
{
lean_object* v_pivot_6063_; lean_object* v___x_6064_; lean_object* v_fst_6065_; lean_object* v_snd_6066_; uint8_t v___x_6067_; 
v_pivot_6063_ = lean_array_fget(v___y_6062_, v_hi_6060_);
lean_inc_n(v_lo_6059_, 2);
v___x_6064_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(v_hi_6060_, v_pivot_6063_, v___y_6062_, v_lo_6059_, v_lo_6059_);
lean_dec(v_pivot_6063_);
v_fst_6065_ = lean_ctor_get(v___x_6064_, 0);
lean_inc(v_fst_6065_);
v_snd_6066_ = lean_ctor_get(v___x_6064_, 1);
lean_inc(v_snd_6066_);
lean_dec_ref(v___x_6064_);
v___x_6067_ = lean_nat_dec_le(v_hi_6060_, v_fst_6065_);
if (v___x_6067_ == 0)
{
lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; 
v___x_6068_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_n_6057_, v_snd_6066_, v_lo_6059_, v_fst_6065_);
v___x_6069_ = lean_unsigned_to_nat(1u);
v___x_6070_ = lean_nat_add(v_fst_6065_, v___x_6069_);
lean_dec(v_fst_6065_);
v_as_6058_ = v___x_6068_;
v_lo_6059_ = v___x_6070_;
goto _start;
}
else
{
lean_dec(v_fst_6065_);
lean_dec(v_lo_6059_);
return v_snd_6066_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___boxed(lean_object* v_n_6092_, lean_object* v_as_6093_, lean_object* v_lo_6094_, lean_object* v_hi_6095_){
_start:
{
lean_object* v_res_6096_; 
v_res_6096_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_n_6092_, v_as_6093_, v_lo_6094_, v_hi_6095_);
lean_dec(v_hi_6095_);
lean_dec(v_n_6092_);
return v_res_6096_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1(lean_object* v_path_6099_, lean_object* v___f_6100_, lean_object* v_filter_6101_, lean_object* v___y_6102_, lean_object* v___y_6103_, lean_object* v___y_6104_, lean_object* v___y_6105_, lean_object* v___y_6106_, lean_object* v___y_6107_){
_start:
{
lean_object* v___y_6110_; lean_object* v___y_6111_; lean_object* v___y_6114_; lean_object* v___y_6115_; lean_object* v___y_6116_; lean_object* v___y_6117_; lean_object* v___y_6118_; lean_object* v___y_6121_; lean_object* v___y_6122_; lean_object* v___y_6123_; lean_object* v___y_6124_; lean_object* v___y_6125_; lean_object* v_log_6127_; uint8_t v_action_6128_; uint8_t v_wantsRebuild_6129_; lean_object* v_trace_6130_; lean_object* v_buildTime_6131_; lean_object* v___x_6132_; 
v_log_6127_ = lean_ctor_get(v___y_6107_, 0);
v_action_6128_ = lean_ctor_get_uint8(v___y_6107_, sizeof(void*)*3);
v_wantsRebuild_6129_ = lean_ctor_get_uint8(v___y_6107_, sizeof(void*)*3 + 1);
v_trace_6130_ = lean_ctor_get(v___y_6107_, 1);
v_buildTime_6131_ = lean_ctor_get(v___y_6107_, 2);
v___x_6132_ = l_System_FilePath_walkDir(v_path_6099_, v___f_6100_);
if (lean_obj_tag(v___x_6132_) == 0)
{
lean_object* v_a_6133_; lean_object* v___x_6134_; lean_object* v_a_6136_; lean_object* v_a_6137_; lean_object* v___y_6144_; lean_object* v___x_6147_; lean_object* v___x_6148_; uint8_t v___x_6149_; 
v_a_6133_ = lean_ctor_get(v___x_6132_, 0);
lean_inc(v_a_6133_);
lean_dec_ref(v___x_6132_);
v___x_6134_ = lean_unsigned_to_nat(0u);
v___x_6147_ = lean_array_get_size(v_a_6133_);
v___x_6148_ = ((lean_object*)(l_Lake_inputDir___lam__1___closed__0));
v___x_6149_ = lean_nat_dec_lt(v___x_6134_, v___x_6147_);
if (v___x_6149_ == 0)
{
lean_dec(v_a_6133_);
lean_dec_ref(v_filter_6101_);
v_a_6136_ = v___x_6148_;
v_a_6137_ = v___y_6107_;
goto v___jp_6135_;
}
else
{
uint8_t v___x_6150_; 
v___x_6150_ = lean_nat_dec_le(v___x_6147_, v___x_6147_);
if (v___x_6150_ == 0)
{
if (v___x_6149_ == 0)
{
lean_dec(v_a_6133_);
lean_dec_ref(v_filter_6101_);
v_a_6136_ = v___x_6148_;
v_a_6137_ = v___y_6107_;
goto v___jp_6135_;
}
else
{
size_t v___x_6151_; size_t v___x_6152_; lean_object* v___x_6153_; 
v___x_6151_ = ((size_t)0ULL);
v___x_6152_ = lean_usize_of_nat(v___x_6147_);
v___x_6153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6101_, v_a_6133_, v___x_6151_, v___x_6152_, v___x_6148_, v___y_6107_);
lean_dec(v_a_6133_);
v___y_6144_ = v___x_6153_;
goto v___jp_6143_;
}
}
else
{
size_t v___x_6154_; size_t v___x_6155_; lean_object* v___x_6156_; 
v___x_6154_ = ((size_t)0ULL);
v___x_6155_ = lean_usize_of_nat(v___x_6147_);
v___x_6156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6101_, v_a_6133_, v___x_6154_, v___x_6155_, v___x_6148_, v___y_6107_);
lean_dec(v_a_6133_);
v___y_6144_ = v___x_6156_;
goto v___jp_6143_;
}
}
v___jp_6135_:
{
lean_object* v___x_6138_; uint8_t v___x_6139_; 
v___x_6138_ = lean_array_get_size(v_a_6136_);
v___x_6139_ = lean_nat_dec_eq(v___x_6138_, v___x_6134_);
if (v___x_6139_ == 0)
{
lean_object* v___x_6140_; lean_object* v___x_6141_; uint8_t v___x_6142_; 
v___x_6140_ = lean_unsigned_to_nat(1u);
v___x_6141_ = lean_nat_sub(v___x_6138_, v___x_6140_);
v___x_6142_ = lean_nat_dec_le(v___x_6134_, v___x_6141_);
if (v___x_6142_ == 0)
{
lean_inc(v___x_6141_);
v___y_6121_ = v___x_6141_;
v___y_6122_ = v___x_6138_;
v___y_6123_ = v_a_6136_;
v___y_6124_ = v_a_6137_;
v___y_6125_ = v___x_6141_;
goto v___jp_6120_;
}
else
{
v___y_6121_ = v___x_6141_;
v___y_6122_ = v___x_6138_;
v___y_6123_ = v_a_6136_;
v___y_6124_ = v_a_6137_;
v___y_6125_ = v___x_6134_;
goto v___jp_6120_;
}
}
else
{
v___y_6110_ = v_a_6137_;
v___y_6111_ = v_a_6136_;
goto v___jp_6109_;
}
}
v___jp_6143_:
{
if (lean_obj_tag(v___y_6144_) == 0)
{
lean_object* v_a_6145_; lean_object* v_a_6146_; 
v_a_6145_ = lean_ctor_get(v___y_6144_, 0);
lean_inc(v_a_6145_);
v_a_6146_ = lean_ctor_get(v___y_6144_, 1);
lean_inc(v_a_6146_);
lean_dec_ref(v___y_6144_);
v_a_6136_ = v_a_6145_;
v_a_6137_ = v_a_6146_;
goto v___jp_6135_;
}
else
{
return v___y_6144_;
}
}
}
else
{
lean_object* v___x_6158_; uint8_t v_isShared_6159_; uint8_t v_isSharedCheck_6170_; 
lean_inc(v_buildTime_6131_);
lean_inc_ref(v_trace_6130_);
lean_inc_ref(v_log_6127_);
lean_dec_ref(v_filter_6101_);
v_isSharedCheck_6170_ = !lean_is_exclusive(v___y_6107_);
if (v_isSharedCheck_6170_ == 0)
{
lean_object* v_unused_6171_; lean_object* v_unused_6172_; lean_object* v_unused_6173_; 
v_unused_6171_ = lean_ctor_get(v___y_6107_, 2);
lean_dec(v_unused_6171_);
v_unused_6172_ = lean_ctor_get(v___y_6107_, 1);
lean_dec(v_unused_6172_);
v_unused_6173_ = lean_ctor_get(v___y_6107_, 0);
lean_dec(v_unused_6173_);
v___x_6158_ = v___y_6107_;
v_isShared_6159_ = v_isSharedCheck_6170_;
goto v_resetjp_6157_;
}
else
{
lean_dec(v___y_6107_);
v___x_6158_ = lean_box(0);
v_isShared_6159_ = v_isSharedCheck_6170_;
goto v_resetjp_6157_;
}
v_resetjp_6157_:
{
lean_object* v_a_6160_; lean_object* v___x_6161_; uint8_t v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6167_; 
v_a_6160_ = lean_ctor_get(v___x_6132_, 0);
lean_inc(v_a_6160_);
lean_dec_ref(v___x_6132_);
v___x_6161_ = lean_io_error_to_string(v_a_6160_);
v___x_6162_ = 3;
v___x_6163_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6163_, 0, v___x_6161_);
lean_ctor_set_uint8(v___x_6163_, sizeof(void*)*1, v___x_6162_);
v___x_6164_ = lean_array_get_size(v_log_6127_);
v___x_6165_ = lean_array_push(v_log_6127_, v___x_6163_);
if (v_isShared_6159_ == 0)
{
lean_ctor_set(v___x_6158_, 0, v___x_6165_);
v___x_6167_ = v___x_6158_;
goto v_reusejp_6166_;
}
else
{
lean_object* v_reuseFailAlloc_6169_; 
v_reuseFailAlloc_6169_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6169_, 0, v___x_6165_);
lean_ctor_set(v_reuseFailAlloc_6169_, 1, v_trace_6130_);
lean_ctor_set(v_reuseFailAlloc_6169_, 2, v_buildTime_6131_);
lean_ctor_set_uint8(v_reuseFailAlloc_6169_, sizeof(void*)*3, v_action_6128_);
lean_ctor_set_uint8(v_reuseFailAlloc_6169_, sizeof(void*)*3 + 1, v_wantsRebuild_6129_);
v___x_6167_ = v_reuseFailAlloc_6169_;
goto v_reusejp_6166_;
}
v_reusejp_6166_:
{
lean_object* v___x_6168_; 
v___x_6168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6168_, 0, v___x_6164_);
lean_ctor_set(v___x_6168_, 1, v___x_6167_);
return v___x_6168_;
}
}
}
v___jp_6109_:
{
lean_object* v___x_6112_; 
v___x_6112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6112_, 0, v___y_6111_);
lean_ctor_set(v___x_6112_, 1, v___y_6110_);
return v___x_6112_;
}
v___jp_6113_:
{
lean_object* v___x_6119_; 
v___x_6119_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v___y_6114_, v___y_6115_, v___y_6116_, v___y_6118_);
lean_dec(v___y_6118_);
lean_dec(v___y_6114_);
v___y_6110_ = v___y_6117_;
v___y_6111_ = v___x_6119_;
goto v___jp_6109_;
}
v___jp_6120_:
{
uint8_t v___x_6126_; 
v___x_6126_ = lean_nat_dec_le(v___y_6125_, v___y_6121_);
if (v___x_6126_ == 0)
{
lean_dec(v___y_6121_);
lean_inc(v___y_6125_);
v___y_6114_ = v___y_6122_;
v___y_6115_ = v___y_6123_;
v___y_6116_ = v___y_6125_;
v___y_6117_ = v___y_6124_;
v___y_6118_ = v___y_6125_;
goto v___jp_6113_;
}
else
{
v___y_6114_ = v___y_6122_;
v___y_6115_ = v___y_6123_;
v___y_6116_ = v___y_6125_;
v___y_6117_ = v___y_6124_;
v___y_6118_ = v___y_6121_;
goto v___jp_6113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1___boxed(lean_object* v_path_6174_, lean_object* v___f_6175_, lean_object* v_filter_6176_, lean_object* v___y_6177_, lean_object* v___y_6178_, lean_object* v___y_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_, lean_object* v___y_6182_, lean_object* v___y_6183_){
_start:
{
lean_object* v_res_6184_; 
v_res_6184_ = l_Lake_inputDir___lam__1(v_path_6174_, v___f_6175_, v_filter_6176_, v___y_6177_, v___y_6178_, v___y_6179_, v___y_6180_, v___y_6181_, v___y_6182_);
lean_dec_ref(v___y_6181_);
lean_dec(v___y_6180_);
lean_dec(v___y_6179_);
lean_dec(v___y_6178_);
lean_dec_ref(v___y_6177_);
return v_res_6184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(uint8_t v_text_6185_, size_t v_sz_6186_, size_t v_i_6187_, lean_object* v_bs_6188_, lean_object* v___y_6189_, lean_object* v___y_6190_, lean_object* v___y_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_, lean_object* v___y_6194_){
_start:
{
uint8_t v___x_6196_; 
v___x_6196_ = lean_usize_dec_lt(v_i_6187_, v_sz_6186_);
if (v___x_6196_ == 0)
{
lean_object* v___x_6197_; 
lean_dec_ref(v___y_6189_);
v___x_6197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6197_, 0, v_bs_6188_);
lean_ctor_set(v___x_6197_, 1, v___y_6194_);
return v___x_6197_;
}
else
{
lean_object* v_v_6198_; lean_object* v___x_6199_; lean_object* v_bs_x27_6200_; lean_object* v___y_6202_; 
v_v_6198_ = lean_array_uget(v_bs_6188_, v_i_6187_);
v___x_6199_ = lean_unsigned_to_nat(0u);
v_bs_x27_6200_ = lean_array_uset(v_bs_6188_, v_i_6187_, v___x_6199_);
if (v_text_6185_ == 0)
{
lean_object* v___x_6207_; 
lean_inc_ref(v___y_6189_);
v___x_6207_ = l_Lake_inputBinFile___redArg(v_v_6198_, v___y_6189_, v___y_6190_, v___y_6191_, v___y_6192_, v___y_6193_);
v___y_6202_ = v___x_6207_;
goto v___jp_6201_;
}
else
{
lean_object* v___x_6208_; 
lean_inc_ref(v___y_6189_);
v___x_6208_ = l_Lake_inputTextFile___redArg(v_v_6198_, v___y_6189_, v___y_6190_, v___y_6191_, v___y_6192_, v___y_6193_);
v___y_6202_ = v___x_6208_;
goto v___jp_6201_;
}
v___jp_6201_:
{
size_t v___x_6203_; size_t v___x_6204_; lean_object* v___x_6205_; 
v___x_6203_ = ((size_t)1ULL);
v___x_6204_ = lean_usize_add(v_i_6187_, v___x_6203_);
v___x_6205_ = lean_array_uset(v_bs_x27_6200_, v_i_6187_, v___y_6202_);
v_i_6187_ = v___x_6204_;
v_bs_6188_ = v___x_6205_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0___boxed(lean_object* v_text_6209_, lean_object* v_sz_6210_, lean_object* v_i_6211_, lean_object* v_bs_6212_, lean_object* v___y_6213_, lean_object* v___y_6214_, lean_object* v___y_6215_, lean_object* v___y_6216_, lean_object* v___y_6217_, lean_object* v___y_6218_, lean_object* v___y_6219_){
_start:
{
uint8_t v_text_boxed_6220_; size_t v_sz_boxed_6221_; size_t v_i_boxed_6222_; lean_object* v_res_6223_; 
v_text_boxed_6220_ = lean_unbox(v_text_6209_);
v_sz_boxed_6221_ = lean_unbox_usize(v_sz_6210_);
lean_dec(v_sz_6210_);
v_i_boxed_6222_ = lean_unbox_usize(v_i_6211_);
lean_dec(v_i_6211_);
v_res_6223_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(v_text_boxed_6220_, v_sz_boxed_6221_, v_i_boxed_6222_, v_bs_6212_, v___y_6213_, v___y_6214_, v___y_6215_, v___y_6216_, v___y_6217_, v___y_6218_);
lean_dec_ref(v___y_6217_);
lean_dec(v___y_6216_);
lean_dec(v___y_6215_);
lean_dec(v___y_6214_);
return v_res_6223_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2(uint8_t v_text_6224_, lean_object* v_path_6225_, lean_object* v_ps_6226_, lean_object* v___y_6227_, lean_object* v___y_6228_, lean_object* v___y_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_){
_start:
{
size_t v_sz_6234_; size_t v___x_6235_; lean_object* v___x_6236_; 
v_sz_6234_ = lean_array_size(v_ps_6226_);
v___x_6235_ = ((size_t)0ULL);
v___x_6236_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(v_text_6224_, v_sz_6234_, v___x_6235_, v_ps_6226_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_, v___y_6231_, v___y_6232_);
if (lean_obj_tag(v___x_6236_) == 0)
{
lean_object* v_a_6237_; lean_object* v_a_6238_; lean_object* v___x_6240_; uint8_t v_isShared_6241_; uint8_t v_isSharedCheck_6246_; 
v_a_6237_ = lean_ctor_get(v___x_6236_, 0);
v_a_6238_ = lean_ctor_get(v___x_6236_, 1);
v_isSharedCheck_6246_ = !lean_is_exclusive(v___x_6236_);
if (v_isSharedCheck_6246_ == 0)
{
v___x_6240_ = v___x_6236_;
v_isShared_6241_ = v_isSharedCheck_6246_;
goto v_resetjp_6239_;
}
else
{
lean_inc(v_a_6238_);
lean_inc(v_a_6237_);
lean_dec(v___x_6236_);
v___x_6240_ = lean_box(0);
v_isShared_6241_ = v_isSharedCheck_6246_;
goto v_resetjp_6239_;
}
v_resetjp_6239_:
{
lean_object* v___x_6242_; lean_object* v___x_6244_; 
v___x_6242_ = l_Lake_Job_collectArray___redArg(v_a_6237_, v_path_6225_);
lean_dec(v_a_6237_);
if (v_isShared_6241_ == 0)
{
lean_ctor_set(v___x_6240_, 0, v___x_6242_);
v___x_6244_ = v___x_6240_;
goto v_reusejp_6243_;
}
else
{
lean_object* v_reuseFailAlloc_6245_; 
v_reuseFailAlloc_6245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6245_, 0, v___x_6242_);
lean_ctor_set(v_reuseFailAlloc_6245_, 1, v_a_6238_);
v___x_6244_ = v_reuseFailAlloc_6245_;
goto v_reusejp_6243_;
}
v_reusejp_6243_:
{
return v___x_6244_;
}
}
}
else
{
lean_object* v_a_6247_; lean_object* v_a_6248_; lean_object* v___x_6250_; uint8_t v_isShared_6251_; uint8_t v_isSharedCheck_6255_; 
lean_dec_ref(v_path_6225_);
v_a_6247_ = lean_ctor_get(v___x_6236_, 0);
v_a_6248_ = lean_ctor_get(v___x_6236_, 1);
v_isSharedCheck_6255_ = !lean_is_exclusive(v___x_6236_);
if (v_isSharedCheck_6255_ == 0)
{
v___x_6250_ = v___x_6236_;
v_isShared_6251_ = v_isSharedCheck_6255_;
goto v_resetjp_6249_;
}
else
{
lean_inc(v_a_6248_);
lean_inc(v_a_6247_);
lean_dec(v___x_6236_);
v___x_6250_ = lean_box(0);
v_isShared_6251_ = v_isSharedCheck_6255_;
goto v_resetjp_6249_;
}
v_resetjp_6249_:
{
lean_object* v___x_6253_; 
if (v_isShared_6251_ == 0)
{
v___x_6253_ = v___x_6250_;
goto v_reusejp_6252_;
}
else
{
lean_object* v_reuseFailAlloc_6254_; 
v_reuseFailAlloc_6254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6254_, 0, v_a_6247_);
lean_ctor_set(v_reuseFailAlloc_6254_, 1, v_a_6248_);
v___x_6253_ = v_reuseFailAlloc_6254_;
goto v_reusejp_6252_;
}
v_reusejp_6252_:
{
return v___x_6253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2___boxed(lean_object* v_text_6256_, lean_object* v_path_6257_, lean_object* v_ps_6258_, lean_object* v___y_6259_, lean_object* v___y_6260_, lean_object* v___y_6261_, lean_object* v___y_6262_, lean_object* v___y_6263_, lean_object* v___y_6264_, lean_object* v___y_6265_){
_start:
{
uint8_t v_text_boxed_6266_; lean_object* v_res_6267_; 
v_text_boxed_6266_ = lean_unbox(v_text_6256_);
v_res_6267_ = l_Lake_inputDir___lam__2(v_text_boxed_6266_, v_path_6257_, v_ps_6258_, v___y_6259_, v___y_6260_, v___y_6261_, v___y_6262_, v___y_6263_, v___y_6264_);
lean_dec_ref(v___y_6263_);
lean_dec(v___y_6262_);
lean_dec(v___y_6261_);
lean_dec(v___y_6260_);
return v_res_6267_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir(lean_object* v_path_6269_, uint8_t v_text_6270_, lean_object* v_filter_6271_, lean_object* v_a_6272_, lean_object* v_a_6273_, lean_object* v_a_6274_, lean_object* v_a_6275_, lean_object* v_a_6276_, lean_object* v_a_6277_){
_start:
{
lean_object* v___f_6279_; lean_object* v___f_6280_; lean_object* v___x_6281_; lean_object* v___x_6282_; lean_object* v___x_6283_; lean_object* v___x_6284_; lean_object* v___x_6285_; lean_object* v___f_6286_; uint8_t v___x_6287_; lean_object* v___x_6288_; 
v___f_6279_ = ((lean_object*)(l_Lake_inputDir___closed__0));
lean_inc_ref(v_path_6269_);
v___f_6280_ = lean_alloc_closure((void*)(l_Lake_inputDir___lam__1___boxed), 10, 3);
lean_closure_set(v___f_6280_, 0, v_path_6269_);
lean_closure_set(v___f_6280_, 1, v___f_6279_);
lean_closure_set(v___f_6280_, 2, v_filter_6271_);
v___x_6281_ = lean_box(0);
v___x_6282_ = lean_unsigned_to_nat(0u);
v___x_6283_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
lean_inc_ref(v_a_6272_);
v___x_6284_ = l_Lake_Job_async___redArg(v___x_6281_, v___f_6280_, v___x_6282_, v___x_6283_, v_a_6272_, v_a_6273_, v_a_6274_, v_a_6275_, v_a_6276_);
v___x_6285_ = lean_box(v_text_6270_);
v___f_6286_ = lean_alloc_closure((void*)(l_Lake_inputDir___lam__2___boxed), 10, 2);
lean_closure_set(v___f_6286_, 0, v___x_6285_);
lean_closure_set(v___f_6286_, 1, v_path_6269_);
v___x_6287_ = 0;
v___x_6288_ = l_Lake_Job_bindM___redArg(v___x_6281_, v___x_6284_, v___f_6286_, v___x_6282_, v___x_6287_, v_a_6272_, v_a_6273_, v_a_6274_, v_a_6275_, v_a_6276_, v_a_6277_);
return v___x_6288_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___boxed(lean_object* v_path_6289_, lean_object* v_text_6290_, lean_object* v_filter_6291_, lean_object* v_a_6292_, lean_object* v_a_6293_, lean_object* v_a_6294_, lean_object* v_a_6295_, lean_object* v_a_6296_, lean_object* v_a_6297_, lean_object* v_a_6298_){
_start:
{
uint8_t v_text_boxed_6299_; lean_object* v_res_6300_; 
v_text_boxed_6299_ = lean_unbox(v_text_6290_);
v_res_6300_ = l_Lake_inputDir(v_path_6289_, v_text_boxed_6299_, v_filter_6291_, v_a_6292_, v_a_6293_, v_a_6294_, v_a_6295_, v_a_6296_, v_a_6297_);
lean_dec_ref(v_a_6297_);
lean_dec_ref(v_a_6296_);
lean_dec(v_a_6295_);
lean_dec(v_a_6294_);
lean_dec(v_a_6293_);
return v_res_6300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(lean_object* v_n_6301_, lean_object* v_as_6302_, lean_object* v_lo_6303_, lean_object* v_hi_6304_, lean_object* v_w_6305_, lean_object* v_hlo_6306_, lean_object* v_hhi_6307_){
_start:
{
lean_object* v___x_6308_; 
v___x_6308_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_n_6301_, v_as_6302_, v_lo_6303_, v_hi_6304_);
return v___x_6308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___boxed(lean_object* v_n_6309_, lean_object* v_as_6310_, lean_object* v_lo_6311_, lean_object* v_hi_6312_, lean_object* v_w_6313_, lean_object* v_hlo_6314_, lean_object* v_hhi_6315_){
_start:
{
lean_object* v_res_6316_; 
v_res_6316_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(v_n_6309_, v_as_6310_, v_lo_6311_, v_hi_6312_, v_w_6313_, v_hlo_6314_, v_hhi_6315_);
lean_dec(v_hi_6312_);
lean_dec(v_n_6309_);
return v_res_6316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(lean_object* v_filter_6317_, lean_object* v_as_6318_, size_t v_i_6319_, size_t v_stop_6320_, lean_object* v_b_6321_, lean_object* v___y_6322_, lean_object* v___y_6323_, lean_object* v___y_6324_, lean_object* v___y_6325_, lean_object* v___y_6326_, lean_object* v___y_6327_){
_start:
{
lean_object* v___x_6329_; 
v___x_6329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6317_, v_as_6318_, v_i_6319_, v_stop_6320_, v_b_6321_, v___y_6327_);
return v___x_6329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___boxed(lean_object* v_filter_6330_, lean_object* v_as_6331_, lean_object* v_i_6332_, lean_object* v_stop_6333_, lean_object* v_b_6334_, lean_object* v___y_6335_, lean_object* v___y_6336_, lean_object* v___y_6337_, lean_object* v___y_6338_, lean_object* v___y_6339_, lean_object* v___y_6340_, lean_object* v___y_6341_){
_start:
{
size_t v_i_boxed_6342_; size_t v_stop_boxed_6343_; lean_object* v_res_6344_; 
v_i_boxed_6342_ = lean_unbox_usize(v_i_6332_);
lean_dec(v_i_6332_);
v_stop_boxed_6343_ = lean_unbox_usize(v_stop_6333_);
lean_dec(v_stop_6333_);
v_res_6344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(v_filter_6330_, v_as_6331_, v_i_boxed_6342_, v_stop_boxed_6343_, v_b_6334_, v___y_6335_, v___y_6336_, v___y_6337_, v___y_6338_, v___y_6339_, v___y_6340_);
lean_dec_ref(v___y_6339_);
lean_dec(v___y_6338_);
lean_dec(v___y_6337_);
lean_dec(v___y_6336_);
lean_dec_ref(v___y_6335_);
lean_dec_ref(v_as_6331_);
return v_res_6344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1(lean_object* v_n_6345_, lean_object* v_lo_6346_, lean_object* v_hi_6347_, lean_object* v_hhi_6348_, lean_object* v_pivot_6349_, lean_object* v_as_6350_, lean_object* v_i_6351_, lean_object* v_k_6352_, lean_object* v_ilo_6353_, lean_object* v_ik_6354_, lean_object* v_w_6355_){
_start:
{
lean_object* v___x_6356_; 
v___x_6356_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(v_hi_6347_, v_pivot_6349_, v_as_6350_, v_i_6351_, v_k_6352_);
return v___x_6356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___boxed(lean_object* v_n_6357_, lean_object* v_lo_6358_, lean_object* v_hi_6359_, lean_object* v_hhi_6360_, lean_object* v_pivot_6361_, lean_object* v_as_6362_, lean_object* v_i_6363_, lean_object* v_k_6364_, lean_object* v_ilo_6365_, lean_object* v_ik_6366_, lean_object* v_w_6367_){
_start:
{
lean_object* v_res_6368_; 
v_res_6368_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1(v_n_6357_, v_lo_6358_, v_hi_6359_, v_hhi_6360_, v_pivot_6361_, v_as_6362_, v_i_6363_, v_k_6364_, v_ilo_6365_, v_ik_6366_, v_w_6367_);
lean_dec_ref(v_pivot_6361_);
lean_dec(v_hi_6359_);
lean_dec(v_lo_6358_);
lean_dec(v_n_6357_);
return v_res_6368_;
}
}
LEAN_EXPORT uint64_t l_Lake_buildO___lam__0(uint64_t v_ts_6369_, lean_object* v_t_6370_){
_start:
{
uint64_t v___x_6371_; uint64_t v___x_6372_; uint64_t v___x_6373_; uint64_t v___x_6374_; 
v___x_6371_ = l_Lake_Hash_nil;
v___x_6372_ = lean_string_hash(v_t_6370_);
v___x_6373_ = lean_uint64_mix_hash(v___x_6371_, v___x_6372_);
v___x_6374_ = lean_uint64_mix_hash(v_ts_6369_, v___x_6373_);
return v___x_6374_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__0___boxed(lean_object* v_ts_6375_, lean_object* v_t_6376_){
_start:
{
uint64_t v_ts_boxed_6377_; uint64_t v_res_6378_; lean_object* v_r_6379_; 
v_ts_boxed_6377_ = lean_unbox_uint64(v_ts_6375_);
lean_dec_ref(v_ts_6375_);
v_res_6378_ = l_Lake_buildO___lam__0(v_ts_boxed_6377_, v_t_6376_);
lean_dec_ref(v_t_6376_);
v_r_6379_ = lean_box_uint64(v_res_6378_);
return v_r_6379_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1(lean_object* v_oFile_6380_, lean_object* v_srcFile_6381_, lean_object* v___x_6382_, lean_object* v_compiler_6383_, lean_object* v___y_6384_, lean_object* v___y_6385_, lean_object* v___y_6386_, lean_object* v___y_6387_, lean_object* v___y_6388_, lean_object* v___y_6389_){
_start:
{
lean_object* v_log_6391_; uint8_t v_action_6392_; uint8_t v_wantsRebuild_6393_; lean_object* v_trace_6394_; lean_object* v_buildTime_6395_; lean_object* v___x_6397_; uint8_t v_isShared_6398_; uint8_t v_isSharedCheck_6424_; 
v_log_6391_ = lean_ctor_get(v___y_6389_, 0);
v_action_6392_ = lean_ctor_get_uint8(v___y_6389_, sizeof(void*)*3);
v_wantsRebuild_6393_ = lean_ctor_get_uint8(v___y_6389_, sizeof(void*)*3 + 1);
v_trace_6394_ = lean_ctor_get(v___y_6389_, 1);
v_buildTime_6395_ = lean_ctor_get(v___y_6389_, 2);
v_isSharedCheck_6424_ = !lean_is_exclusive(v___y_6389_);
if (v_isSharedCheck_6424_ == 0)
{
v___x_6397_ = v___y_6389_;
v_isShared_6398_ = v_isSharedCheck_6424_;
goto v_resetjp_6396_;
}
else
{
lean_inc(v_buildTime_6395_);
lean_inc(v_trace_6394_);
lean_inc(v_log_6391_);
lean_dec(v___y_6389_);
v___x_6397_ = lean_box(0);
v_isShared_6398_ = v_isSharedCheck_6424_;
goto v_resetjp_6396_;
}
v_resetjp_6396_:
{
lean_object* v___x_6399_; 
v___x_6399_ = l_Lake_compileO(v_oFile_6380_, v_srcFile_6381_, v___x_6382_, v_compiler_6383_, v_log_6391_);
if (lean_obj_tag(v___x_6399_) == 0)
{
lean_object* v_a_6400_; lean_object* v_a_6401_; lean_object* v___x_6403_; uint8_t v_isShared_6404_; uint8_t v_isSharedCheck_6411_; 
v_a_6400_ = lean_ctor_get(v___x_6399_, 0);
v_a_6401_ = lean_ctor_get(v___x_6399_, 1);
v_isSharedCheck_6411_ = !lean_is_exclusive(v___x_6399_);
if (v_isSharedCheck_6411_ == 0)
{
v___x_6403_ = v___x_6399_;
v_isShared_6404_ = v_isSharedCheck_6411_;
goto v_resetjp_6402_;
}
else
{
lean_inc(v_a_6401_);
lean_inc(v_a_6400_);
lean_dec(v___x_6399_);
v___x_6403_ = lean_box(0);
v_isShared_6404_ = v_isSharedCheck_6411_;
goto v_resetjp_6402_;
}
v_resetjp_6402_:
{
lean_object* v___x_6406_; 
if (v_isShared_6398_ == 0)
{
lean_ctor_set(v___x_6397_, 0, v_a_6401_);
v___x_6406_ = v___x_6397_;
goto v_reusejp_6405_;
}
else
{
lean_object* v_reuseFailAlloc_6410_; 
v_reuseFailAlloc_6410_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6410_, 0, v_a_6401_);
lean_ctor_set(v_reuseFailAlloc_6410_, 1, v_trace_6394_);
lean_ctor_set(v_reuseFailAlloc_6410_, 2, v_buildTime_6395_);
lean_ctor_set_uint8(v_reuseFailAlloc_6410_, sizeof(void*)*3, v_action_6392_);
lean_ctor_set_uint8(v_reuseFailAlloc_6410_, sizeof(void*)*3 + 1, v_wantsRebuild_6393_);
v___x_6406_ = v_reuseFailAlloc_6410_;
goto v_reusejp_6405_;
}
v_reusejp_6405_:
{
lean_object* v___x_6408_; 
if (v_isShared_6404_ == 0)
{
lean_ctor_set(v___x_6403_, 1, v___x_6406_);
v___x_6408_ = v___x_6403_;
goto v_reusejp_6407_;
}
else
{
lean_object* v_reuseFailAlloc_6409_; 
v_reuseFailAlloc_6409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6409_, 0, v_a_6400_);
lean_ctor_set(v_reuseFailAlloc_6409_, 1, v___x_6406_);
v___x_6408_ = v_reuseFailAlloc_6409_;
goto v_reusejp_6407_;
}
v_reusejp_6407_:
{
return v___x_6408_;
}
}
}
}
else
{
lean_object* v_a_6412_; lean_object* v_a_6413_; lean_object* v___x_6415_; uint8_t v_isShared_6416_; uint8_t v_isSharedCheck_6423_; 
v_a_6412_ = lean_ctor_get(v___x_6399_, 0);
v_a_6413_ = lean_ctor_get(v___x_6399_, 1);
v_isSharedCheck_6423_ = !lean_is_exclusive(v___x_6399_);
if (v_isSharedCheck_6423_ == 0)
{
v___x_6415_ = v___x_6399_;
v_isShared_6416_ = v_isSharedCheck_6423_;
goto v_resetjp_6414_;
}
else
{
lean_inc(v_a_6413_);
lean_inc(v_a_6412_);
lean_dec(v___x_6399_);
v___x_6415_ = lean_box(0);
v_isShared_6416_ = v_isSharedCheck_6423_;
goto v_resetjp_6414_;
}
v_resetjp_6414_:
{
lean_object* v___x_6418_; 
if (v_isShared_6398_ == 0)
{
lean_ctor_set(v___x_6397_, 0, v_a_6413_);
v___x_6418_ = v___x_6397_;
goto v_reusejp_6417_;
}
else
{
lean_object* v_reuseFailAlloc_6422_; 
v_reuseFailAlloc_6422_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6422_, 0, v_a_6413_);
lean_ctor_set(v_reuseFailAlloc_6422_, 1, v_trace_6394_);
lean_ctor_set(v_reuseFailAlloc_6422_, 2, v_buildTime_6395_);
lean_ctor_set_uint8(v_reuseFailAlloc_6422_, sizeof(void*)*3, v_action_6392_);
lean_ctor_set_uint8(v_reuseFailAlloc_6422_, sizeof(void*)*3 + 1, v_wantsRebuild_6393_);
v___x_6418_ = v_reuseFailAlloc_6422_;
goto v_reusejp_6417_;
}
v_reusejp_6417_:
{
lean_object* v___x_6420_; 
if (v_isShared_6416_ == 0)
{
lean_ctor_set(v___x_6415_, 1, v___x_6418_);
v___x_6420_ = v___x_6415_;
goto v_reusejp_6419_;
}
else
{
lean_object* v_reuseFailAlloc_6421_; 
v_reuseFailAlloc_6421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6421_, 0, v_a_6412_);
lean_ctor_set(v_reuseFailAlloc_6421_, 1, v___x_6418_);
v___x_6420_ = v_reuseFailAlloc_6421_;
goto v_reusejp_6419_;
}
v_reusejp_6419_:
{
return v___x_6420_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1___boxed(lean_object* v_oFile_6425_, lean_object* v_srcFile_6426_, lean_object* v___x_6427_, lean_object* v_compiler_6428_, lean_object* v___y_6429_, lean_object* v___y_6430_, lean_object* v___y_6431_, lean_object* v___y_6432_, lean_object* v___y_6433_, lean_object* v___y_6434_, lean_object* v___y_6435_){
_start:
{
lean_object* v_res_6436_; 
v_res_6436_ = l_Lake_buildO___lam__1(v_oFile_6425_, v_srcFile_6426_, v___x_6427_, v_compiler_6428_, v___y_6429_, v___y_6430_, v___y_6431_, v___y_6432_, v___y_6433_, v___y_6434_);
lean_dec_ref(v___y_6433_);
lean_dec(v___y_6432_);
lean_dec(v___y_6431_);
lean_dec(v___y_6430_);
lean_dec_ref(v___y_6429_);
lean_dec_ref(v___x_6427_);
return v_res_6436_;
}
}
static lean_object* _init_l_Lake_buildO___lam__2___boxed__const__1(void){
_start:
{
uint64_t v___x_6440_; lean_object* v___x_6441_; 
v___x_6440_ = l_Lake_Hash_nil;
v___x_6441_ = lean_box_uint64(v___x_6440_);
return v___x_6441_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2(lean_object* v_traceArgs_6442_, lean_object* v___f_6443_, lean_object* v_extraDepTrace_6444_, lean_object* v_weakArgs_6445_, lean_object* v_oFile_6446_, lean_object* v_compiler_6447_, lean_object* v___x_6448_, lean_object* v___f_6449_, lean_object* v_srcFile_6450_, lean_object* v___y_6451_, lean_object* v___y_6452_, lean_object* v___y_6453_, lean_object* v___y_6454_, lean_object* v___y_6455_, lean_object* v___y_6456_){
_start:
{
lean_object* v_log_6458_; uint8_t v_action_6459_; uint8_t v_wantsRebuild_6460_; lean_object* v_trace_6461_; lean_object* v_buildTime_6462_; lean_object* v___x_6464_; uint8_t v_isShared_6465_; uint8_t v_isSharedCheck_6547_; 
v_log_6458_ = lean_ctor_get(v___y_6456_, 0);
v_action_6459_ = lean_ctor_get_uint8(v___y_6456_, sizeof(void*)*3);
v_wantsRebuild_6460_ = lean_ctor_get_uint8(v___y_6456_, sizeof(void*)*3 + 1);
v_trace_6461_ = lean_ctor_get(v___y_6456_, 1);
v_buildTime_6462_ = lean_ctor_get(v___y_6456_, 2);
v_isSharedCheck_6547_ = !lean_is_exclusive(v___y_6456_);
if (v_isSharedCheck_6547_ == 0)
{
v___x_6464_ = v___y_6456_;
v_isShared_6465_ = v_isSharedCheck_6547_;
goto v_resetjp_6463_;
}
else
{
lean_inc(v_buildTime_6462_);
lean_inc(v_trace_6461_);
lean_inc(v_log_6458_);
lean_dec(v___y_6456_);
v___x_6464_ = lean_box(0);
v_isShared_6465_ = v_isSharedCheck_6547_;
goto v_resetjp_6463_;
}
v_resetjp_6463_:
{
lean_object* v___x_6466_; lean_object* v___x_6467_; uint64_t v___y_6469_; uint64_t v___x_6532_; lean_object* v___x_6533_; lean_object* v___x_6534_; uint8_t v___x_6535_; 
v___x_6466_ = l_Lake_platformTrace;
v___x_6467_ = l_Lake_BuildTrace_mix(v_trace_6461_, v___x_6466_);
v___x_6532_ = l_Lake_Hash_nil;
v___x_6533_ = lean_unsigned_to_nat(0u);
v___x_6534_ = lean_array_get_size(v_traceArgs_6442_);
v___x_6535_ = lean_nat_dec_lt(v___x_6533_, v___x_6534_);
if (v___x_6535_ == 0)
{
lean_dec_ref(v___f_6449_);
lean_dec_ref(v___x_6448_);
v___y_6469_ = v___x_6532_;
goto v___jp_6468_;
}
else
{
uint8_t v___x_6536_; 
v___x_6536_ = lean_nat_dec_le(v___x_6534_, v___x_6534_);
if (v___x_6536_ == 0)
{
if (v___x_6535_ == 0)
{
lean_dec_ref(v___f_6449_);
lean_dec_ref(v___x_6448_);
v___y_6469_ = v___x_6532_;
goto v___jp_6468_;
}
else
{
size_t v___x_6537_; size_t v___x_6538_; lean_object* v___x_6539_; lean_object* v___x_6540_; uint64_t v___x_6541_; 
v___x_6537_ = ((size_t)0ULL);
v___x_6538_ = lean_usize_of_nat(v___x_6534_);
v___x_6539_ = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(v_traceArgs_6442_);
v___x_6540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_6448_, v___f_6449_, v_traceArgs_6442_, v___x_6537_, v___x_6538_, v___x_6539_);
v___x_6541_ = lean_unbox_uint64(v___x_6540_);
lean_dec(v___x_6540_);
v___y_6469_ = v___x_6541_;
goto v___jp_6468_;
}
}
else
{
size_t v___x_6542_; size_t v___x_6543_; lean_object* v___x_6544_; lean_object* v___x_6545_; uint64_t v___x_6546_; 
v___x_6542_ = ((size_t)0ULL);
v___x_6543_ = lean_usize_of_nat(v___x_6534_);
v___x_6544_ = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(v_traceArgs_6442_);
v___x_6545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_6448_, v___f_6449_, v_traceArgs_6442_, v___x_6542_, v___x_6543_, v___x_6544_);
v___x_6546_ = lean_unbox_uint64(v___x_6545_);
lean_dec(v___x_6545_);
v___y_6469_ = v___x_6546_;
goto v___jp_6468_;
}
}
v___jp_6468_:
{
lean_object* v___x_6470_; lean_object* v___x_6471_; lean_object* v___x_6472_; lean_object* v___x_6473_; lean_object* v___x_6474_; lean_object* v___x_6475_; lean_object* v___x_6476_; lean_object* v___x_6477_; lean_object* v___x_6478_; lean_object* v___x_6479_; lean_object* v___x_6481_; 
v___x_6470_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_6471_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_6442_);
v___x_6472_ = lean_array_to_list(v_traceArgs_6442_);
v___x_6473_ = l_List_toString___redArg(v___f_6443_, v___x_6472_);
v___x_6474_ = lean_string_append(v___x_6471_, v___x_6473_);
lean_dec_ref(v___x_6473_);
v___x_6475_ = lean_string_append(v___x_6470_, v___x_6474_);
lean_dec_ref(v___x_6474_);
v___x_6476_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_6477_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_6478_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6478_, 0, v___x_6475_);
lean_ctor_set(v___x_6478_, 1, v___x_6476_);
lean_ctor_set(v___x_6478_, 2, v___x_6477_);
lean_ctor_set_uint64(v___x_6478_, sizeof(void*)*3, v___y_6469_);
v___x_6479_ = l_Lake_BuildTrace_mix(v___x_6467_, v___x_6478_);
if (v_isShared_6465_ == 0)
{
lean_ctor_set(v___x_6464_, 1, v___x_6479_);
v___x_6481_ = v___x_6464_;
goto v_reusejp_6480_;
}
else
{
lean_object* v_reuseFailAlloc_6531_; 
v_reuseFailAlloc_6531_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6531_, 0, v_log_6458_);
lean_ctor_set(v_reuseFailAlloc_6531_, 1, v___x_6479_);
lean_ctor_set(v_reuseFailAlloc_6531_, 2, v_buildTime_6462_);
lean_ctor_set_uint8(v_reuseFailAlloc_6531_, sizeof(void*)*3, v_action_6459_);
lean_ctor_set_uint8(v_reuseFailAlloc_6531_, sizeof(void*)*3 + 1, v_wantsRebuild_6460_);
v___x_6481_ = v_reuseFailAlloc_6531_;
goto v_reusejp_6480_;
}
v_reusejp_6480_:
{
lean_object* v___x_6482_; 
lean_inc_ref(v___y_6455_);
lean_inc(v___y_6454_);
lean_inc(v___y_6453_);
lean_inc(v___y_6452_);
lean_inc_ref(v___y_6451_);
v___x_6482_ = lean_apply_7(v_extraDepTrace_6444_, v___y_6451_, v___y_6452_, v___y_6453_, v___y_6454_, v___y_6455_, v___x_6481_, lean_box(0));
if (lean_obj_tag(v___x_6482_) == 0)
{
lean_object* v_a_6483_; lean_object* v_a_6484_; lean_object* v_log_6485_; uint8_t v_action_6486_; uint8_t v_wantsRebuild_6487_; lean_object* v_trace_6488_; lean_object* v_buildTime_6489_; lean_object* v___x_6491_; uint8_t v_isShared_6492_; uint8_t v_isSharedCheck_6521_; 
v_a_6483_ = lean_ctor_get(v___x_6482_, 1);
lean_inc(v_a_6483_);
v_a_6484_ = lean_ctor_get(v___x_6482_, 0);
lean_inc(v_a_6484_);
lean_dec_ref(v___x_6482_);
v_log_6485_ = lean_ctor_get(v_a_6483_, 0);
v_action_6486_ = lean_ctor_get_uint8(v_a_6483_, sizeof(void*)*3);
v_wantsRebuild_6487_ = lean_ctor_get_uint8(v_a_6483_, sizeof(void*)*3 + 1);
v_trace_6488_ = lean_ctor_get(v_a_6483_, 1);
v_buildTime_6489_ = lean_ctor_get(v_a_6483_, 2);
v_isSharedCheck_6521_ = !lean_is_exclusive(v_a_6483_);
if (v_isSharedCheck_6521_ == 0)
{
v___x_6491_ = v_a_6483_;
v_isShared_6492_ = v_isSharedCheck_6521_;
goto v_resetjp_6490_;
}
else
{
lean_inc(v_buildTime_6489_);
lean_inc(v_trace_6488_);
lean_inc(v_log_6485_);
lean_dec(v_a_6483_);
v___x_6491_ = lean_box(0);
v_isShared_6492_ = v_isSharedCheck_6521_;
goto v_resetjp_6490_;
}
v_resetjp_6490_:
{
lean_object* v___x_6493_; lean_object* v___x_6495_; 
v___x_6493_ = l_Lake_BuildTrace_mix(v_trace_6488_, v_a_6484_);
if (v_isShared_6492_ == 0)
{
lean_ctor_set(v___x_6491_, 1, v___x_6493_);
v___x_6495_ = v___x_6491_;
goto v_reusejp_6494_;
}
else
{
lean_object* v_reuseFailAlloc_6520_; 
v_reuseFailAlloc_6520_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6520_, 0, v_log_6485_);
lean_ctor_set(v_reuseFailAlloc_6520_, 1, v___x_6493_);
lean_ctor_set(v_reuseFailAlloc_6520_, 2, v_buildTime_6489_);
lean_ctor_set_uint8(v_reuseFailAlloc_6520_, sizeof(void*)*3, v_action_6486_);
lean_ctor_set_uint8(v_reuseFailAlloc_6520_, sizeof(void*)*3 + 1, v_wantsRebuild_6487_);
v___x_6495_ = v_reuseFailAlloc_6520_;
goto v_reusejp_6494_;
}
v_reusejp_6494_:
{
lean_object* v___x_6496_; lean_object* v___f_6497_; uint8_t v___x_6498_; lean_object* v___x_6499_; lean_object* v___x_6500_; 
v___x_6496_ = l_Array_append___redArg(v_weakArgs_6445_, v_traceArgs_6442_);
lean_dec_ref(v_traceArgs_6442_);
lean_inc_ref(v_oFile_6446_);
v___f_6497_ = lean_alloc_closure((void*)(l_Lake_buildO___lam__1___boxed), 11, 4);
lean_closure_set(v___f_6497_, 0, v_oFile_6446_);
lean_closure_set(v___f_6497_, 1, v_srcFile_6450_);
lean_closure_set(v___f_6497_, 2, v___x_6496_);
lean_closure_set(v___f_6497_, 3, v_compiler_6447_);
v___x_6498_ = 0;
v___x_6499_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
v___x_6500_ = l_Lake_buildArtifactUnlessUpToDate(v_oFile_6446_, v___f_6497_, v___x_6498_, v___x_6499_, v___x_6498_, v___x_6498_, v___x_6498_, v___y_6451_, v___y_6452_, v___y_6453_, v___y_6454_, v___y_6455_, v___x_6495_);
if (lean_obj_tag(v___x_6500_) == 0)
{
lean_object* v_a_6501_; lean_object* v_a_6502_; lean_object* v___x_6504_; uint8_t v_isShared_6505_; uint8_t v_isSharedCheck_6510_; 
v_a_6501_ = lean_ctor_get(v___x_6500_, 0);
v_a_6502_ = lean_ctor_get(v___x_6500_, 1);
v_isSharedCheck_6510_ = !lean_is_exclusive(v___x_6500_);
if (v_isSharedCheck_6510_ == 0)
{
v___x_6504_ = v___x_6500_;
v_isShared_6505_ = v_isSharedCheck_6510_;
goto v_resetjp_6503_;
}
else
{
lean_inc(v_a_6502_);
lean_inc(v_a_6501_);
lean_dec(v___x_6500_);
v___x_6504_ = lean_box(0);
v_isShared_6505_ = v_isSharedCheck_6510_;
goto v_resetjp_6503_;
}
v_resetjp_6503_:
{
lean_object* v_path_6506_; lean_object* v___x_6508_; 
v_path_6506_ = lean_ctor_get(v_a_6501_, 1);
lean_inc_ref(v_path_6506_);
lean_dec(v_a_6501_);
if (v_isShared_6505_ == 0)
{
lean_ctor_set(v___x_6504_, 0, v_path_6506_);
v___x_6508_ = v___x_6504_;
goto v_reusejp_6507_;
}
else
{
lean_object* v_reuseFailAlloc_6509_; 
v_reuseFailAlloc_6509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6509_, 0, v_path_6506_);
lean_ctor_set(v_reuseFailAlloc_6509_, 1, v_a_6502_);
v___x_6508_ = v_reuseFailAlloc_6509_;
goto v_reusejp_6507_;
}
v_reusejp_6507_:
{
return v___x_6508_;
}
}
}
else
{
lean_object* v_a_6511_; lean_object* v_a_6512_; lean_object* v___x_6514_; uint8_t v_isShared_6515_; uint8_t v_isSharedCheck_6519_; 
v_a_6511_ = lean_ctor_get(v___x_6500_, 0);
v_a_6512_ = lean_ctor_get(v___x_6500_, 1);
v_isSharedCheck_6519_ = !lean_is_exclusive(v___x_6500_);
if (v_isSharedCheck_6519_ == 0)
{
v___x_6514_ = v___x_6500_;
v_isShared_6515_ = v_isSharedCheck_6519_;
goto v_resetjp_6513_;
}
else
{
lean_inc(v_a_6512_);
lean_inc(v_a_6511_);
lean_dec(v___x_6500_);
v___x_6514_ = lean_box(0);
v_isShared_6515_ = v_isSharedCheck_6519_;
goto v_resetjp_6513_;
}
v_resetjp_6513_:
{
lean_object* v___x_6517_; 
if (v_isShared_6515_ == 0)
{
v___x_6517_ = v___x_6514_;
goto v_reusejp_6516_;
}
else
{
lean_object* v_reuseFailAlloc_6518_; 
v_reuseFailAlloc_6518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6518_, 0, v_a_6511_);
lean_ctor_set(v_reuseFailAlloc_6518_, 1, v_a_6512_);
v___x_6517_ = v_reuseFailAlloc_6518_;
goto v_reusejp_6516_;
}
v_reusejp_6516_:
{
return v___x_6517_;
}
}
}
}
}
}
else
{
lean_object* v_a_6522_; lean_object* v_a_6523_; lean_object* v___x_6525_; uint8_t v_isShared_6526_; uint8_t v_isSharedCheck_6530_; 
lean_dec_ref(v___y_6451_);
lean_dec_ref(v_srcFile_6450_);
lean_dec_ref(v_compiler_6447_);
lean_dec_ref(v_oFile_6446_);
lean_dec_ref(v_weakArgs_6445_);
lean_dec_ref(v_traceArgs_6442_);
v_a_6522_ = lean_ctor_get(v___x_6482_, 0);
v_a_6523_ = lean_ctor_get(v___x_6482_, 1);
v_isSharedCheck_6530_ = !lean_is_exclusive(v___x_6482_);
if (v_isSharedCheck_6530_ == 0)
{
v___x_6525_ = v___x_6482_;
v_isShared_6526_ = v_isSharedCheck_6530_;
goto v_resetjp_6524_;
}
else
{
lean_inc(v_a_6523_);
lean_inc(v_a_6522_);
lean_dec(v___x_6482_);
v___x_6525_ = lean_box(0);
v_isShared_6526_ = v_isSharedCheck_6530_;
goto v_resetjp_6524_;
}
v_resetjp_6524_:
{
lean_object* v___x_6528_; 
if (v_isShared_6526_ == 0)
{
v___x_6528_ = v___x_6525_;
goto v_reusejp_6527_;
}
else
{
lean_object* v_reuseFailAlloc_6529_; 
v_reuseFailAlloc_6529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6529_, 0, v_a_6522_);
lean_ctor_set(v_reuseFailAlloc_6529_, 1, v_a_6523_);
v___x_6528_ = v_reuseFailAlloc_6529_;
goto v_reusejp_6527_;
}
v_reusejp_6527_:
{
return v___x_6528_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed(lean_object* v_traceArgs_6548_, lean_object* v___f_6549_, lean_object* v_extraDepTrace_6550_, lean_object* v_weakArgs_6551_, lean_object* v_oFile_6552_, lean_object* v_compiler_6553_, lean_object* v___x_6554_, lean_object* v___f_6555_, lean_object* v_srcFile_6556_, lean_object* v___y_6557_, lean_object* v___y_6558_, lean_object* v___y_6559_, lean_object* v___y_6560_, lean_object* v___y_6561_, lean_object* v___y_6562_, lean_object* v___y_6563_){
_start:
{
lean_object* v_res_6564_; 
v_res_6564_ = l_Lake_buildO___lam__2(v_traceArgs_6548_, v___f_6549_, v_extraDepTrace_6550_, v_weakArgs_6551_, v_oFile_6552_, v_compiler_6553_, v___x_6554_, v___f_6555_, v_srcFile_6556_, v___y_6557_, v___y_6558_, v___y_6559_, v___y_6560_, v___y_6561_, v___y_6562_);
lean_dec_ref(v___y_6561_);
lean_dec(v___y_6560_);
lean_dec(v___y_6559_);
lean_dec(v___y_6558_);
return v_res_6564_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object* v_oFile_6567_, lean_object* v_srcJob_6568_, lean_object* v_weakArgs_6569_, lean_object* v_traceArgs_6570_, lean_object* v_compiler_6571_, lean_object* v_extraDepTrace_6572_, lean_object* v_a_6573_, lean_object* v_a_6574_, lean_object* v_a_6575_, lean_object* v_a_6576_, lean_object* v_a_6577_, lean_object* v_a_6578_){
_start:
{
lean_object* v___f_6580_; lean_object* v___x_6581_; lean_object* v___f_6582_; lean_object* v___x_6583_; lean_object* v___f_6584_; lean_object* v___x_6585_; uint8_t v___x_6586_; lean_object* v___x_6587_; 
v___f_6580_ = ((lean_object*)(l_Lake_buildO___closed__0));
v___x_6581_ = l_Lake_instDataKindFilePath;
v___f_6582_ = ((lean_object*)(l_Lake_buildO___closed__1));
v___x_6583_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__9));
v___f_6584_ = lean_alloc_closure((void*)(l_Lake_buildO___lam__2___boxed), 16, 8);
lean_closure_set(v___f_6584_, 0, v_traceArgs_6570_);
lean_closure_set(v___f_6584_, 1, v___f_6582_);
lean_closure_set(v___f_6584_, 2, v_extraDepTrace_6572_);
lean_closure_set(v___f_6584_, 3, v_weakArgs_6569_);
lean_closure_set(v___f_6584_, 4, v_oFile_6567_);
lean_closure_set(v___f_6584_, 5, v_compiler_6571_);
lean_closure_set(v___f_6584_, 6, v___x_6583_);
lean_closure_set(v___f_6584_, 7, v___f_6580_);
v___x_6585_ = lean_unsigned_to_nat(0u);
v___x_6586_ = 0;
v___x_6587_ = l_Lake_Job_mapM___redArg(v___x_6581_, v_srcJob_6568_, v___f_6584_, v___x_6585_, v___x_6586_, v_a_6573_, v_a_6574_, v_a_6575_, v_a_6576_, v_a_6577_, v_a_6578_);
return v___x_6587_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___boxed(lean_object* v_oFile_6588_, lean_object* v_srcJob_6589_, lean_object* v_weakArgs_6590_, lean_object* v_traceArgs_6591_, lean_object* v_compiler_6592_, lean_object* v_extraDepTrace_6593_, lean_object* v_a_6594_, lean_object* v_a_6595_, lean_object* v_a_6596_, lean_object* v_a_6597_, lean_object* v_a_6598_, lean_object* v_a_6599_, lean_object* v_a_6600_){
_start:
{
lean_object* v_res_6601_; 
v_res_6601_ = l_Lake_buildO(v_oFile_6588_, v_srcJob_6589_, v_weakArgs_6590_, v_traceArgs_6591_, v_compiler_6592_, v_extraDepTrace_6593_, v_a_6594_, v_a_6595_, v_a_6596_, v_a_6597_, v_a_6598_, v_a_6599_);
lean_dec_ref(v_a_6599_);
lean_dec_ref(v_a_6598_);
lean_dec(v_a_6597_);
lean_dec(v_a_6596_);
lean_dec(v_a_6595_);
return v_res_6601_;
}
}
static lean_object* _init_l_Lake_buildLeanO___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6603_; lean_object* v___x_6604_; lean_object* v___x_6605_; lean_object* v___x_6606_; 
v___x_6603_ = ((lean_object*)(l_Lake_buildLeanO___lam__0___closed__0));
v___x_6604_ = lean_unsigned_to_nat(2u);
v___x_6605_ = lean_mk_empty_array_with_capacity(v___x_6604_);
v___x_6606_ = lean_array_push(v___x_6605_, v___x_6603_);
return v___x_6606_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0(lean_object* v_weakArgs_6607_, lean_object* v_traceArgs_6608_, lean_object* v_oFile_6609_, lean_object* v_srcFile_6610_, lean_object* v_leanIncludeDir_x3f_6611_, lean_object* v___y_6612_, lean_object* v___y_6613_, lean_object* v___y_6614_, lean_object* v___y_6615_, lean_object* v___y_6616_, lean_object* v___y_6617_){
_start:
{
lean_object* v_toContext_6619_; lean_object* v_lakeEnv_6620_; lean_object* v_log_6621_; uint8_t v_action_6622_; uint8_t v_wantsRebuild_6623_; lean_object* v_trace_6624_; lean_object* v_buildTime_6625_; lean_object* v___x_6627_; uint8_t v_isShared_6628_; uint8_t v_isSharedCheck_6666_; 
v_toContext_6619_ = lean_ctor_get(v___y_6616_, 1);
v_lakeEnv_6620_ = lean_ctor_get(v_toContext_6619_, 0);
v_log_6621_ = lean_ctor_get(v___y_6617_, 0);
v_action_6622_ = lean_ctor_get_uint8(v___y_6617_, sizeof(void*)*3);
v_wantsRebuild_6623_ = lean_ctor_get_uint8(v___y_6617_, sizeof(void*)*3 + 1);
v_trace_6624_ = lean_ctor_get(v___y_6617_, 1);
v_buildTime_6625_ = lean_ctor_get(v___y_6617_, 2);
v_isSharedCheck_6666_ = !lean_is_exclusive(v___y_6617_);
if (v_isSharedCheck_6666_ == 0)
{
v___x_6627_ = v___y_6617_;
v_isShared_6628_ = v_isSharedCheck_6666_;
goto v_resetjp_6626_;
}
else
{
lean_inc(v_buildTime_6625_);
lean_inc(v_trace_6624_);
lean_inc(v_log_6621_);
lean_dec(v___y_6617_);
v___x_6627_ = lean_box(0);
v_isShared_6628_ = v_isSharedCheck_6666_;
goto v_resetjp_6626_;
}
v_resetjp_6626_:
{
lean_object* v_lean_6629_; lean_object* v___y_6631_; 
v_lean_6629_ = lean_ctor_get(v_lakeEnv_6620_, 1);
if (lean_obj_tag(v_leanIncludeDir_x3f_6611_) == 0)
{
lean_object* v_includeDir_6664_; 
v_includeDir_6664_ = lean_ctor_get(v_lean_6629_, 4);
lean_inc_ref(v_includeDir_6664_);
v___y_6631_ = v_includeDir_6664_;
goto v___jp_6630_;
}
else
{
lean_object* v_val_6665_; 
v_val_6665_ = lean_ctor_get(v_leanIncludeDir_x3f_6611_, 0);
lean_inc(v_val_6665_);
lean_dec_ref(v_leanIncludeDir_x3f_6611_);
v___y_6631_ = v_val_6665_;
goto v___jp_6630_;
}
v___jp_6630_:
{
lean_object* v_cc_6632_; lean_object* v_ccFlags_6633_; lean_object* v___x_6634_; lean_object* v___x_6635_; lean_object* v___x_6636_; lean_object* v___x_6637_; lean_object* v___x_6638_; lean_object* v___x_6639_; 
v_cc_6632_ = lean_ctor_get(v_lean_6629_, 14);
v_ccFlags_6633_ = lean_ctor_get(v_lean_6629_, 18);
v___x_6634_ = lean_obj_once(&l_Lake_buildLeanO___lam__0___closed__1, &l_Lake_buildLeanO___lam__0___closed__1_once, _init_l_Lake_buildLeanO___lam__0___closed__1);
v___x_6635_ = lean_array_push(v___x_6634_, v___y_6631_);
v___x_6636_ = l_Array_append___redArg(v___x_6635_, v_ccFlags_6633_);
v___x_6637_ = l_Array_append___redArg(v___x_6636_, v_weakArgs_6607_);
v___x_6638_ = l_Array_append___redArg(v___x_6637_, v_traceArgs_6608_);
lean_inc_ref(v_cc_6632_);
v___x_6639_ = l_Lake_compileO(v_oFile_6609_, v_srcFile_6610_, v___x_6638_, v_cc_6632_, v_log_6621_);
lean_dec_ref(v___x_6638_);
if (lean_obj_tag(v___x_6639_) == 0)
{
lean_object* v_a_6640_; lean_object* v_a_6641_; lean_object* v___x_6643_; uint8_t v_isShared_6644_; uint8_t v_isSharedCheck_6651_; 
v_a_6640_ = lean_ctor_get(v___x_6639_, 0);
v_a_6641_ = lean_ctor_get(v___x_6639_, 1);
v_isSharedCheck_6651_ = !lean_is_exclusive(v___x_6639_);
if (v_isSharedCheck_6651_ == 0)
{
v___x_6643_ = v___x_6639_;
v_isShared_6644_ = v_isSharedCheck_6651_;
goto v_resetjp_6642_;
}
else
{
lean_inc(v_a_6641_);
lean_inc(v_a_6640_);
lean_dec(v___x_6639_);
v___x_6643_ = lean_box(0);
v_isShared_6644_ = v_isSharedCheck_6651_;
goto v_resetjp_6642_;
}
v_resetjp_6642_:
{
lean_object* v___x_6646_; 
if (v_isShared_6628_ == 0)
{
lean_ctor_set(v___x_6627_, 0, v_a_6641_);
v___x_6646_ = v___x_6627_;
goto v_reusejp_6645_;
}
else
{
lean_object* v_reuseFailAlloc_6650_; 
v_reuseFailAlloc_6650_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6650_, 0, v_a_6641_);
lean_ctor_set(v_reuseFailAlloc_6650_, 1, v_trace_6624_);
lean_ctor_set(v_reuseFailAlloc_6650_, 2, v_buildTime_6625_);
lean_ctor_set_uint8(v_reuseFailAlloc_6650_, sizeof(void*)*3, v_action_6622_);
lean_ctor_set_uint8(v_reuseFailAlloc_6650_, sizeof(void*)*3 + 1, v_wantsRebuild_6623_);
v___x_6646_ = v_reuseFailAlloc_6650_;
goto v_reusejp_6645_;
}
v_reusejp_6645_:
{
lean_object* v___x_6648_; 
if (v_isShared_6644_ == 0)
{
lean_ctor_set(v___x_6643_, 1, v___x_6646_);
v___x_6648_ = v___x_6643_;
goto v_reusejp_6647_;
}
else
{
lean_object* v_reuseFailAlloc_6649_; 
v_reuseFailAlloc_6649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6649_, 0, v_a_6640_);
lean_ctor_set(v_reuseFailAlloc_6649_, 1, v___x_6646_);
v___x_6648_ = v_reuseFailAlloc_6649_;
goto v_reusejp_6647_;
}
v_reusejp_6647_:
{
return v___x_6648_;
}
}
}
}
else
{
lean_object* v_a_6652_; lean_object* v_a_6653_; lean_object* v___x_6655_; uint8_t v_isShared_6656_; uint8_t v_isSharedCheck_6663_; 
v_a_6652_ = lean_ctor_get(v___x_6639_, 0);
v_a_6653_ = lean_ctor_get(v___x_6639_, 1);
v_isSharedCheck_6663_ = !lean_is_exclusive(v___x_6639_);
if (v_isSharedCheck_6663_ == 0)
{
v___x_6655_ = v___x_6639_;
v_isShared_6656_ = v_isSharedCheck_6663_;
goto v_resetjp_6654_;
}
else
{
lean_inc(v_a_6653_);
lean_inc(v_a_6652_);
lean_dec(v___x_6639_);
v___x_6655_ = lean_box(0);
v_isShared_6656_ = v_isSharedCheck_6663_;
goto v_resetjp_6654_;
}
v_resetjp_6654_:
{
lean_object* v___x_6658_; 
if (v_isShared_6628_ == 0)
{
lean_ctor_set(v___x_6627_, 0, v_a_6653_);
v___x_6658_ = v___x_6627_;
goto v_reusejp_6657_;
}
else
{
lean_object* v_reuseFailAlloc_6662_; 
v_reuseFailAlloc_6662_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6662_, 0, v_a_6653_);
lean_ctor_set(v_reuseFailAlloc_6662_, 1, v_trace_6624_);
lean_ctor_set(v_reuseFailAlloc_6662_, 2, v_buildTime_6625_);
lean_ctor_set_uint8(v_reuseFailAlloc_6662_, sizeof(void*)*3, v_action_6622_);
lean_ctor_set_uint8(v_reuseFailAlloc_6662_, sizeof(void*)*3 + 1, v_wantsRebuild_6623_);
v___x_6658_ = v_reuseFailAlloc_6662_;
goto v_reusejp_6657_;
}
v_reusejp_6657_:
{
lean_object* v___x_6660_; 
if (v_isShared_6656_ == 0)
{
lean_ctor_set(v___x_6655_, 1, v___x_6658_);
v___x_6660_ = v___x_6655_;
goto v_reusejp_6659_;
}
else
{
lean_object* v_reuseFailAlloc_6661_; 
v_reuseFailAlloc_6661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6661_, 0, v_a_6652_);
lean_ctor_set(v_reuseFailAlloc_6661_, 1, v___x_6658_);
v___x_6660_ = v_reuseFailAlloc_6661_;
goto v_reusejp_6659_;
}
v_reusejp_6659_:
{
return v___x_6660_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0___boxed(lean_object* v_weakArgs_6667_, lean_object* v_traceArgs_6668_, lean_object* v_oFile_6669_, lean_object* v_srcFile_6670_, lean_object* v_leanIncludeDir_x3f_6671_, lean_object* v___y_6672_, lean_object* v___y_6673_, lean_object* v___y_6674_, lean_object* v___y_6675_, lean_object* v___y_6676_, lean_object* v___y_6677_, lean_object* v___y_6678_){
_start:
{
lean_object* v_res_6679_; 
v_res_6679_ = l_Lake_buildLeanO___lam__0(v_weakArgs_6667_, v_traceArgs_6668_, v_oFile_6669_, v_srcFile_6670_, v_leanIncludeDir_x3f_6671_, v___y_6672_, v___y_6673_, v___y_6674_, v___y_6675_, v___y_6676_, v___y_6677_);
lean_dec_ref(v___y_6676_);
lean_dec(v___y_6675_);
lean_dec(v___y_6674_);
lean_dec(v___y_6673_);
lean_dec_ref(v___y_6672_);
lean_dec_ref(v_traceArgs_6668_);
lean_dec_ref(v_weakArgs_6667_);
return v_res_6679_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(lean_object* v_as_6680_, size_t v_i_6681_, size_t v_stop_6682_, uint64_t v_b_6683_){
_start:
{
uint8_t v___x_6684_; 
v___x_6684_ = lean_usize_dec_eq(v_i_6681_, v_stop_6682_);
if (v___x_6684_ == 0)
{
lean_object* v___x_6685_; uint64_t v___x_6686_; uint64_t v___x_6687_; uint64_t v___x_6688_; uint64_t v___x_6689_; size_t v___x_6690_; size_t v___x_6691_; 
v___x_6685_ = lean_array_uget_borrowed(v_as_6680_, v_i_6681_);
v___x_6686_ = l_Lake_Hash_nil;
v___x_6687_ = lean_string_hash(v___x_6685_);
v___x_6688_ = lean_uint64_mix_hash(v___x_6686_, v___x_6687_);
v___x_6689_ = lean_uint64_mix_hash(v_b_6683_, v___x_6688_);
v___x_6690_ = ((size_t)1ULL);
v___x_6691_ = lean_usize_add(v_i_6681_, v___x_6690_);
v_i_6681_ = v___x_6691_;
v_b_6683_ = v___x_6689_;
goto _start;
}
else
{
return v_b_6683_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1___boxed(lean_object* v_as_6693_, lean_object* v_i_6694_, lean_object* v_stop_6695_, lean_object* v_b_6696_){
_start:
{
size_t v_i_boxed_6697_; size_t v_stop_boxed_6698_; uint64_t v_b_boxed_6699_; uint64_t v_res_6700_; lean_object* v_r_6701_; 
v_i_boxed_6697_ = lean_unbox_usize(v_i_6694_);
lean_dec(v_i_6694_);
v_stop_boxed_6698_ = lean_unbox_usize(v_stop_6695_);
lean_dec(v_stop_6695_);
v_b_boxed_6699_ = lean_unbox_uint64(v_b_6696_);
lean_dec_ref(v_b_6696_);
v_res_6700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_as_6693_, v_i_boxed_6697_, v_stop_boxed_6698_, v_b_boxed_6699_);
lean_dec_ref(v_as_6693_);
v_r_6701_ = lean_box_uint64(v_res_6700_);
return v_r_6701_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(lean_object* v_x_6703_, lean_object* v_x_6704_){
_start:
{
if (lean_obj_tag(v_x_6704_) == 0)
{
return v_x_6703_;
}
else
{
lean_object* v_head_6705_; lean_object* v_tail_6706_; lean_object* v___x_6707_; lean_object* v___x_6708_; lean_object* v___x_6709_; 
v_head_6705_ = lean_ctor_get(v_x_6704_, 0);
v_tail_6706_ = lean_ctor_get(v_x_6704_, 1);
v___x_6707_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0));
v___x_6708_ = lean_string_append(v_x_6703_, v___x_6707_);
v___x_6709_ = lean_string_append(v___x_6708_, v_head_6705_);
v_x_6703_ = v___x_6709_;
v_x_6704_ = v_tail_6706_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___boxed(lean_object* v_x_6711_, lean_object* v_x_6712_){
_start:
{
lean_object* v_res_6713_; 
v_res_6713_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(v_x_6711_, v_x_6712_);
lean_dec(v_x_6712_);
return v_res_6713_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0(lean_object* v_x_6717_){
_start:
{
if (lean_obj_tag(v_x_6717_) == 0)
{
lean_object* v___x_6718_; 
v___x_6718_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0));
return v___x_6718_;
}
else
{
lean_object* v_tail_6719_; 
v_tail_6719_ = lean_ctor_get(v_x_6717_, 1);
if (lean_obj_tag(v_tail_6719_) == 0)
{
lean_object* v_head_6720_; lean_object* v___x_6721_; lean_object* v___x_6722_; lean_object* v___x_6723_; lean_object* v___x_6724_; 
v_head_6720_ = lean_ctor_get(v_x_6717_, 0);
v___x_6721_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1));
v___x_6722_ = lean_string_append(v___x_6721_, v_head_6720_);
v___x_6723_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2));
v___x_6724_ = lean_string_append(v___x_6722_, v___x_6723_);
return v___x_6724_;
}
else
{
lean_object* v_head_6725_; lean_object* v___x_6726_; lean_object* v___x_6727_; lean_object* v___x_6728_; uint32_t v___x_6729_; lean_object* v___x_6730_; 
v_head_6725_ = lean_ctor_get(v_x_6717_, 0);
v___x_6726_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1));
v___x_6727_ = lean_string_append(v___x_6726_, v_head_6725_);
v___x_6728_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(v___x_6727_, v_tail_6719_);
v___x_6729_ = 93;
v___x_6730_ = lean_string_push(v___x_6728_, v___x_6729_);
return v___x_6730_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___boxed(lean_object* v_x_6731_){
_start:
{
lean_object* v_res_6732_; 
v_res_6732_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v_x_6731_);
lean_dec(v_x_6731_);
return v_res_6732_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1(lean_object* v_weakArgs_6733_, lean_object* v_traceArgs_6734_, lean_object* v_oFile_6735_, lean_object* v_leanIncludeDir_x3f_6736_, lean_object* v_srcFile_6737_, lean_object* v___y_6738_, lean_object* v___y_6739_, lean_object* v___y_6740_, lean_object* v___y_6741_, lean_object* v___y_6742_, lean_object* v___y_6743_){
_start:
{
lean_object* v_log_6745_; uint8_t v_action_6746_; uint8_t v_wantsRebuild_6747_; lean_object* v_trace_6748_; lean_object* v_buildTime_6749_; lean_object* v___x_6751_; uint8_t v_isShared_6752_; uint8_t v_isSharedCheck_6806_; 
v_log_6745_ = lean_ctor_get(v___y_6743_, 0);
v_action_6746_ = lean_ctor_get_uint8(v___y_6743_, sizeof(void*)*3);
v_wantsRebuild_6747_ = lean_ctor_get_uint8(v___y_6743_, sizeof(void*)*3 + 1);
v_trace_6748_ = lean_ctor_get(v___y_6743_, 1);
v_buildTime_6749_ = lean_ctor_get(v___y_6743_, 2);
v_isSharedCheck_6806_ = !lean_is_exclusive(v___y_6743_);
if (v_isSharedCheck_6806_ == 0)
{
v___x_6751_ = v___y_6743_;
v_isShared_6752_ = v_isSharedCheck_6806_;
goto v_resetjp_6750_;
}
else
{
lean_inc(v_buildTime_6749_);
lean_inc(v_trace_6748_);
lean_inc(v_log_6745_);
lean_dec(v___y_6743_);
v___x_6751_ = lean_box(0);
v_isShared_6752_ = v_isSharedCheck_6806_;
goto v_resetjp_6750_;
}
v_resetjp_6750_:
{
lean_object* v_leanTrace_6753_; lean_object* v___f_6754_; lean_object* v___x_6755_; uint64_t v___y_6757_; uint64_t v___x_6795_; lean_object* v___x_6796_; lean_object* v___x_6797_; uint8_t v___x_6798_; 
v_leanTrace_6753_ = lean_ctor_get(v___y_6742_, 2);
lean_inc_ref(v_oFile_6735_);
lean_inc_ref(v_traceArgs_6734_);
v___f_6754_ = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__0___boxed), 12, 5);
lean_closure_set(v___f_6754_, 0, v_weakArgs_6733_);
lean_closure_set(v___f_6754_, 1, v_traceArgs_6734_);
lean_closure_set(v___f_6754_, 2, v_oFile_6735_);
lean_closure_set(v___f_6754_, 3, v_srcFile_6737_);
lean_closure_set(v___f_6754_, 4, v_leanIncludeDir_x3f_6736_);
lean_inc_ref(v_leanTrace_6753_);
v___x_6755_ = l_Lake_BuildTrace_mix(v_trace_6748_, v_leanTrace_6753_);
v___x_6795_ = l_Lake_Hash_nil;
v___x_6796_ = lean_unsigned_to_nat(0u);
v___x_6797_ = lean_array_get_size(v_traceArgs_6734_);
v___x_6798_ = lean_nat_dec_lt(v___x_6796_, v___x_6797_);
if (v___x_6798_ == 0)
{
v___y_6757_ = v___x_6795_;
goto v___jp_6756_;
}
else
{
uint8_t v___x_6799_; 
v___x_6799_ = lean_nat_dec_le(v___x_6797_, v___x_6797_);
if (v___x_6799_ == 0)
{
if (v___x_6798_ == 0)
{
v___y_6757_ = v___x_6795_;
goto v___jp_6756_;
}
else
{
size_t v___x_6800_; size_t v___x_6801_; uint64_t v___x_6802_; 
v___x_6800_ = ((size_t)0ULL);
v___x_6801_ = lean_usize_of_nat(v___x_6797_);
v___x_6802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_6734_, v___x_6800_, v___x_6801_, v___x_6795_);
v___y_6757_ = v___x_6802_;
goto v___jp_6756_;
}
}
else
{
size_t v___x_6803_; size_t v___x_6804_; uint64_t v___x_6805_; 
v___x_6803_ = ((size_t)0ULL);
v___x_6804_ = lean_usize_of_nat(v___x_6797_);
v___x_6805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_6734_, v___x_6803_, v___x_6804_, v___x_6795_);
v___y_6757_ = v___x_6805_;
goto v___jp_6756_;
}
}
v___jp_6756_:
{
lean_object* v___x_6758_; lean_object* v___x_6759_; lean_object* v___x_6760_; lean_object* v___x_6761_; lean_object* v___x_6762_; lean_object* v___x_6763_; lean_object* v___x_6764_; lean_object* v___x_6765_; lean_object* v___x_6766_; lean_object* v___x_6767_; lean_object* v___x_6768_; lean_object* v___x_6769_; lean_object* v___x_6771_; 
v___x_6758_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_6759_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_6760_ = lean_array_to_list(v_traceArgs_6734_);
v___x_6761_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_6760_);
lean_dec(v___x_6760_);
v___x_6762_ = lean_string_append(v___x_6759_, v___x_6761_);
lean_dec_ref(v___x_6761_);
v___x_6763_ = lean_string_append(v___x_6758_, v___x_6762_);
lean_dec_ref(v___x_6762_);
v___x_6764_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_6765_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_6766_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6766_, 0, v___x_6763_);
lean_ctor_set(v___x_6766_, 1, v___x_6764_);
lean_ctor_set(v___x_6766_, 2, v___x_6765_);
lean_ctor_set_uint64(v___x_6766_, sizeof(void*)*3, v___y_6757_);
v___x_6767_ = l_Lake_BuildTrace_mix(v___x_6755_, v___x_6766_);
v___x_6768_ = l_Lake_platformTrace;
v___x_6769_ = l_Lake_BuildTrace_mix(v___x_6767_, v___x_6768_);
if (v_isShared_6752_ == 0)
{
lean_ctor_set(v___x_6751_, 1, v___x_6769_);
v___x_6771_ = v___x_6751_;
goto v_reusejp_6770_;
}
else
{
lean_object* v_reuseFailAlloc_6794_; 
v_reuseFailAlloc_6794_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6794_, 0, v_log_6745_);
lean_ctor_set(v_reuseFailAlloc_6794_, 1, v___x_6769_);
lean_ctor_set(v_reuseFailAlloc_6794_, 2, v_buildTime_6749_);
lean_ctor_set_uint8(v_reuseFailAlloc_6794_, sizeof(void*)*3, v_action_6746_);
lean_ctor_set_uint8(v_reuseFailAlloc_6794_, sizeof(void*)*3 + 1, v_wantsRebuild_6747_);
v___x_6771_ = v_reuseFailAlloc_6794_;
goto v_reusejp_6770_;
}
v_reusejp_6770_:
{
uint8_t v___x_6772_; lean_object* v___x_6773_; lean_object* v___x_6774_; 
v___x_6772_ = 0;
v___x_6773_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
v___x_6774_ = l_Lake_buildArtifactUnlessUpToDate(v_oFile_6735_, v___f_6754_, v___x_6772_, v___x_6773_, v___x_6772_, v___x_6772_, v___x_6772_, v___y_6738_, v___y_6739_, v___y_6740_, v___y_6741_, v___y_6742_, v___x_6771_);
if (lean_obj_tag(v___x_6774_) == 0)
{
lean_object* v_a_6775_; lean_object* v_a_6776_; lean_object* v___x_6778_; uint8_t v_isShared_6779_; uint8_t v_isSharedCheck_6784_; 
v_a_6775_ = lean_ctor_get(v___x_6774_, 0);
v_a_6776_ = lean_ctor_get(v___x_6774_, 1);
v_isSharedCheck_6784_ = !lean_is_exclusive(v___x_6774_);
if (v_isSharedCheck_6784_ == 0)
{
v___x_6778_ = v___x_6774_;
v_isShared_6779_ = v_isSharedCheck_6784_;
goto v_resetjp_6777_;
}
else
{
lean_inc(v_a_6776_);
lean_inc(v_a_6775_);
lean_dec(v___x_6774_);
v___x_6778_ = lean_box(0);
v_isShared_6779_ = v_isSharedCheck_6784_;
goto v_resetjp_6777_;
}
v_resetjp_6777_:
{
lean_object* v_path_6780_; lean_object* v___x_6782_; 
v_path_6780_ = lean_ctor_get(v_a_6775_, 1);
lean_inc_ref(v_path_6780_);
lean_dec(v_a_6775_);
if (v_isShared_6779_ == 0)
{
lean_ctor_set(v___x_6778_, 0, v_path_6780_);
v___x_6782_ = v___x_6778_;
goto v_reusejp_6781_;
}
else
{
lean_object* v_reuseFailAlloc_6783_; 
v_reuseFailAlloc_6783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6783_, 0, v_path_6780_);
lean_ctor_set(v_reuseFailAlloc_6783_, 1, v_a_6776_);
v___x_6782_ = v_reuseFailAlloc_6783_;
goto v_reusejp_6781_;
}
v_reusejp_6781_:
{
return v___x_6782_;
}
}
}
else
{
lean_object* v_a_6785_; lean_object* v_a_6786_; lean_object* v___x_6788_; uint8_t v_isShared_6789_; uint8_t v_isSharedCheck_6793_; 
v_a_6785_ = lean_ctor_get(v___x_6774_, 0);
v_a_6786_ = lean_ctor_get(v___x_6774_, 1);
v_isSharedCheck_6793_ = !lean_is_exclusive(v___x_6774_);
if (v_isSharedCheck_6793_ == 0)
{
v___x_6788_ = v___x_6774_;
v_isShared_6789_ = v_isSharedCheck_6793_;
goto v_resetjp_6787_;
}
else
{
lean_inc(v_a_6786_);
lean_inc(v_a_6785_);
lean_dec(v___x_6774_);
v___x_6788_ = lean_box(0);
v_isShared_6789_ = v_isSharedCheck_6793_;
goto v_resetjp_6787_;
}
v_resetjp_6787_:
{
lean_object* v___x_6791_; 
if (v_isShared_6789_ == 0)
{
v___x_6791_ = v___x_6788_;
goto v_reusejp_6790_;
}
else
{
lean_object* v_reuseFailAlloc_6792_; 
v_reuseFailAlloc_6792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6792_, 0, v_a_6785_);
lean_ctor_set(v_reuseFailAlloc_6792_, 1, v_a_6786_);
v___x_6791_ = v_reuseFailAlloc_6792_;
goto v_reusejp_6790_;
}
v_reusejp_6790_:
{
return v___x_6791_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1___boxed(lean_object* v_weakArgs_6807_, lean_object* v_traceArgs_6808_, lean_object* v_oFile_6809_, lean_object* v_leanIncludeDir_x3f_6810_, lean_object* v_srcFile_6811_, lean_object* v___y_6812_, lean_object* v___y_6813_, lean_object* v___y_6814_, lean_object* v___y_6815_, lean_object* v___y_6816_, lean_object* v___y_6817_, lean_object* v___y_6818_){
_start:
{
lean_object* v_res_6819_; 
v_res_6819_ = l_Lake_buildLeanO___lam__1(v_weakArgs_6807_, v_traceArgs_6808_, v_oFile_6809_, v_leanIncludeDir_x3f_6810_, v_srcFile_6811_, v___y_6812_, v___y_6813_, v___y_6814_, v___y_6815_, v___y_6816_, v___y_6817_);
lean_dec_ref(v___y_6816_);
lean_dec(v___y_6815_);
lean_dec(v___y_6814_);
lean_dec(v___y_6813_);
return v_res_6819_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object* v_oFile_6820_, lean_object* v_srcJob_6821_, lean_object* v_weakArgs_6822_, lean_object* v_traceArgs_6823_, lean_object* v_leanIncludeDir_x3f_6824_, lean_object* v_a_6825_, lean_object* v_a_6826_, lean_object* v_a_6827_, lean_object* v_a_6828_, lean_object* v_a_6829_, lean_object* v_a_6830_){
_start:
{
lean_object* v___f_6832_; lean_object* v___x_6833_; lean_object* v___x_6834_; uint8_t v___x_6835_; lean_object* v___x_6836_; 
v___f_6832_ = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__1___boxed), 12, 4);
lean_closure_set(v___f_6832_, 0, v_weakArgs_6822_);
lean_closure_set(v___f_6832_, 1, v_traceArgs_6823_);
lean_closure_set(v___f_6832_, 2, v_oFile_6820_);
lean_closure_set(v___f_6832_, 3, v_leanIncludeDir_x3f_6824_);
v___x_6833_ = l_Lake_instDataKindFilePath;
v___x_6834_ = lean_unsigned_to_nat(0u);
v___x_6835_ = 0;
v___x_6836_ = l_Lake_Job_mapM___redArg(v___x_6833_, v_srcJob_6821_, v___f_6832_, v___x_6834_, v___x_6835_, v_a_6825_, v_a_6826_, v_a_6827_, v_a_6828_, v_a_6829_, v_a_6830_);
return v___x_6836_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___boxed(lean_object* v_oFile_6837_, lean_object* v_srcJob_6838_, lean_object* v_weakArgs_6839_, lean_object* v_traceArgs_6840_, lean_object* v_leanIncludeDir_x3f_6841_, lean_object* v_a_6842_, lean_object* v_a_6843_, lean_object* v_a_6844_, lean_object* v_a_6845_, lean_object* v_a_6846_, lean_object* v_a_6847_, lean_object* v_a_6848_){
_start:
{
lean_object* v_res_6849_; 
v_res_6849_ = l_Lake_buildLeanO(v_oFile_6837_, v_srcJob_6838_, v_weakArgs_6839_, v_traceArgs_6840_, v_leanIncludeDir_x3f_6841_, v_a_6842_, v_a_6843_, v_a_6844_, v_a_6845_, v_a_6846_, v_a_6847_);
lean_dec_ref(v_a_6847_);
lean_dec_ref(v_a_6846_);
lean_dec(v_a_6845_);
lean_dec(v_a_6844_);
lean_dec(v_a_6843_);
return v_res_6849_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0(lean_object* v_libFile_6850_, lean_object* v_oFiles_6851_, uint8_t v_thin_6852_, lean_object* v___y_6853_, lean_object* v___y_6854_, lean_object* v___y_6855_, lean_object* v___y_6856_, lean_object* v___y_6857_, lean_object* v___y_6858_){
_start:
{
lean_object* v_toContext_6860_; lean_object* v_lakeEnv_6861_; lean_object* v_lean_6862_; lean_object* v_log_6863_; uint8_t v_action_6864_; uint8_t v_wantsRebuild_6865_; lean_object* v_trace_6866_; lean_object* v_buildTime_6867_; lean_object* v___x_6869_; uint8_t v_isShared_6870_; uint8_t v_isSharedCheck_6897_; 
v_toContext_6860_ = lean_ctor_get(v___y_6857_, 1);
v_lakeEnv_6861_ = lean_ctor_get(v_toContext_6860_, 0);
v_lean_6862_ = lean_ctor_get(v_lakeEnv_6861_, 1);
v_log_6863_ = lean_ctor_get(v___y_6858_, 0);
v_action_6864_ = lean_ctor_get_uint8(v___y_6858_, sizeof(void*)*3);
v_wantsRebuild_6865_ = lean_ctor_get_uint8(v___y_6858_, sizeof(void*)*3 + 1);
v_trace_6866_ = lean_ctor_get(v___y_6858_, 1);
v_buildTime_6867_ = lean_ctor_get(v___y_6858_, 2);
v_isSharedCheck_6897_ = !lean_is_exclusive(v___y_6858_);
if (v_isSharedCheck_6897_ == 0)
{
v___x_6869_ = v___y_6858_;
v_isShared_6870_ = v_isSharedCheck_6897_;
goto v_resetjp_6868_;
}
else
{
lean_inc(v_buildTime_6867_);
lean_inc(v_trace_6866_);
lean_inc(v_log_6863_);
lean_dec(v___y_6858_);
v___x_6869_ = lean_box(0);
v_isShared_6870_ = v_isSharedCheck_6897_;
goto v_resetjp_6868_;
}
v_resetjp_6868_:
{
lean_object* v_ar_6871_; lean_object* v___x_6872_; 
v_ar_6871_ = lean_ctor_get(v_lean_6862_, 13);
lean_inc_ref(v_ar_6871_);
v___x_6872_ = l_Lake_compileStaticLib(v_libFile_6850_, v_oFiles_6851_, v_ar_6871_, v_thin_6852_, v_log_6863_);
if (lean_obj_tag(v___x_6872_) == 0)
{
lean_object* v_a_6873_; lean_object* v_a_6874_; lean_object* v___x_6876_; uint8_t v_isShared_6877_; uint8_t v_isSharedCheck_6884_; 
v_a_6873_ = lean_ctor_get(v___x_6872_, 0);
v_a_6874_ = lean_ctor_get(v___x_6872_, 1);
v_isSharedCheck_6884_ = !lean_is_exclusive(v___x_6872_);
if (v_isSharedCheck_6884_ == 0)
{
v___x_6876_ = v___x_6872_;
v_isShared_6877_ = v_isSharedCheck_6884_;
goto v_resetjp_6875_;
}
else
{
lean_inc(v_a_6874_);
lean_inc(v_a_6873_);
lean_dec(v___x_6872_);
v___x_6876_ = lean_box(0);
v_isShared_6877_ = v_isSharedCheck_6884_;
goto v_resetjp_6875_;
}
v_resetjp_6875_:
{
lean_object* v___x_6879_; 
if (v_isShared_6870_ == 0)
{
lean_ctor_set(v___x_6869_, 0, v_a_6874_);
v___x_6879_ = v___x_6869_;
goto v_reusejp_6878_;
}
else
{
lean_object* v_reuseFailAlloc_6883_; 
v_reuseFailAlloc_6883_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6883_, 0, v_a_6874_);
lean_ctor_set(v_reuseFailAlloc_6883_, 1, v_trace_6866_);
lean_ctor_set(v_reuseFailAlloc_6883_, 2, v_buildTime_6867_);
lean_ctor_set_uint8(v_reuseFailAlloc_6883_, sizeof(void*)*3, v_action_6864_);
lean_ctor_set_uint8(v_reuseFailAlloc_6883_, sizeof(void*)*3 + 1, v_wantsRebuild_6865_);
v___x_6879_ = v_reuseFailAlloc_6883_;
goto v_reusejp_6878_;
}
v_reusejp_6878_:
{
lean_object* v___x_6881_; 
if (v_isShared_6877_ == 0)
{
lean_ctor_set(v___x_6876_, 1, v___x_6879_);
v___x_6881_ = v___x_6876_;
goto v_reusejp_6880_;
}
else
{
lean_object* v_reuseFailAlloc_6882_; 
v_reuseFailAlloc_6882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6882_, 0, v_a_6873_);
lean_ctor_set(v_reuseFailAlloc_6882_, 1, v___x_6879_);
v___x_6881_ = v_reuseFailAlloc_6882_;
goto v_reusejp_6880_;
}
v_reusejp_6880_:
{
return v___x_6881_;
}
}
}
}
else
{
lean_object* v_a_6885_; lean_object* v_a_6886_; lean_object* v___x_6888_; uint8_t v_isShared_6889_; uint8_t v_isSharedCheck_6896_; 
v_a_6885_ = lean_ctor_get(v___x_6872_, 0);
v_a_6886_ = lean_ctor_get(v___x_6872_, 1);
v_isSharedCheck_6896_ = !lean_is_exclusive(v___x_6872_);
if (v_isSharedCheck_6896_ == 0)
{
v___x_6888_ = v___x_6872_;
v_isShared_6889_ = v_isSharedCheck_6896_;
goto v_resetjp_6887_;
}
else
{
lean_inc(v_a_6886_);
lean_inc(v_a_6885_);
lean_dec(v___x_6872_);
v___x_6888_ = lean_box(0);
v_isShared_6889_ = v_isSharedCheck_6896_;
goto v_resetjp_6887_;
}
v_resetjp_6887_:
{
lean_object* v___x_6891_; 
if (v_isShared_6870_ == 0)
{
lean_ctor_set(v___x_6869_, 0, v_a_6886_);
v___x_6891_ = v___x_6869_;
goto v_reusejp_6890_;
}
else
{
lean_object* v_reuseFailAlloc_6895_; 
v_reuseFailAlloc_6895_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6895_, 0, v_a_6886_);
lean_ctor_set(v_reuseFailAlloc_6895_, 1, v_trace_6866_);
lean_ctor_set(v_reuseFailAlloc_6895_, 2, v_buildTime_6867_);
lean_ctor_set_uint8(v_reuseFailAlloc_6895_, sizeof(void*)*3, v_action_6864_);
lean_ctor_set_uint8(v_reuseFailAlloc_6895_, sizeof(void*)*3 + 1, v_wantsRebuild_6865_);
v___x_6891_ = v_reuseFailAlloc_6895_;
goto v_reusejp_6890_;
}
v_reusejp_6890_:
{
lean_object* v___x_6893_; 
if (v_isShared_6889_ == 0)
{
lean_ctor_set(v___x_6888_, 1, v___x_6891_);
v___x_6893_ = v___x_6888_;
goto v_reusejp_6892_;
}
else
{
lean_object* v_reuseFailAlloc_6894_; 
v_reuseFailAlloc_6894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6894_, 0, v_a_6885_);
lean_ctor_set(v_reuseFailAlloc_6894_, 1, v___x_6891_);
v___x_6893_ = v_reuseFailAlloc_6894_;
goto v_reusejp_6892_;
}
v_reusejp_6892_:
{
return v___x_6893_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0___boxed(lean_object* v_libFile_6898_, lean_object* v_oFiles_6899_, lean_object* v_thin_6900_, lean_object* v___y_6901_, lean_object* v___y_6902_, lean_object* v___y_6903_, lean_object* v___y_6904_, lean_object* v___y_6905_, lean_object* v___y_6906_, lean_object* v___y_6907_){
_start:
{
uint8_t v_thin_boxed_6908_; lean_object* v_res_6909_; 
v_thin_boxed_6908_ = lean_unbox(v_thin_6900_);
v_res_6909_ = l_Lake_buildStaticLib___lam__0(v_libFile_6898_, v_oFiles_6899_, v_thin_boxed_6908_, v___y_6901_, v___y_6902_, v___y_6903_, v___y_6904_, v___y_6905_, v___y_6906_);
lean_dec_ref(v___y_6905_);
lean_dec(v___y_6904_);
lean_dec(v___y_6903_);
lean_dec(v___y_6902_);
lean_dec_ref(v___y_6901_);
return v_res_6909_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1(lean_object* v_libFile_6911_, uint8_t v_thin_6912_, lean_object* v_oFiles_6913_, lean_object* v___y_6914_, lean_object* v___y_6915_, lean_object* v___y_6916_, lean_object* v___y_6917_, lean_object* v___y_6918_, lean_object* v___y_6919_){
_start:
{
lean_object* v___x_6921_; lean_object* v___f_6922_; uint8_t v___x_6923_; lean_object* v___x_6924_; uint8_t v___x_6925_; lean_object* v___x_6926_; 
v___x_6921_ = lean_box(v_thin_6912_);
lean_inc_ref(v_libFile_6911_);
v___f_6922_ = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6922_, 0, v_libFile_6911_);
lean_closure_set(v___f_6922_, 1, v_oFiles_6913_);
lean_closure_set(v___f_6922_, 2, v___x_6921_);
v___x_6923_ = 0;
v___x_6924_ = ((lean_object*)(l_Lake_buildStaticLib___lam__1___closed__0));
v___x_6925_ = 1;
v___x_6926_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_6911_, v___f_6922_, v___x_6923_, v___x_6924_, v___x_6925_, v___x_6923_, v___x_6923_, v___y_6914_, v___y_6915_, v___y_6916_, v___y_6917_, v___y_6918_, v___y_6919_);
if (lean_obj_tag(v___x_6926_) == 0)
{
lean_object* v_a_6927_; lean_object* v_a_6928_; lean_object* v___x_6930_; uint8_t v_isShared_6931_; uint8_t v_isSharedCheck_6936_; 
v_a_6927_ = lean_ctor_get(v___x_6926_, 0);
v_a_6928_ = lean_ctor_get(v___x_6926_, 1);
v_isSharedCheck_6936_ = !lean_is_exclusive(v___x_6926_);
if (v_isSharedCheck_6936_ == 0)
{
v___x_6930_ = v___x_6926_;
v_isShared_6931_ = v_isSharedCheck_6936_;
goto v_resetjp_6929_;
}
else
{
lean_inc(v_a_6928_);
lean_inc(v_a_6927_);
lean_dec(v___x_6926_);
v___x_6930_ = lean_box(0);
v_isShared_6931_ = v_isSharedCheck_6936_;
goto v_resetjp_6929_;
}
v_resetjp_6929_:
{
lean_object* v_path_6932_; lean_object* v___x_6934_; 
v_path_6932_ = lean_ctor_get(v_a_6927_, 1);
lean_inc_ref(v_path_6932_);
lean_dec(v_a_6927_);
if (v_isShared_6931_ == 0)
{
lean_ctor_set(v___x_6930_, 0, v_path_6932_);
v___x_6934_ = v___x_6930_;
goto v_reusejp_6933_;
}
else
{
lean_object* v_reuseFailAlloc_6935_; 
v_reuseFailAlloc_6935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6935_, 0, v_path_6932_);
lean_ctor_set(v_reuseFailAlloc_6935_, 1, v_a_6928_);
v___x_6934_ = v_reuseFailAlloc_6935_;
goto v_reusejp_6933_;
}
v_reusejp_6933_:
{
return v___x_6934_;
}
}
}
else
{
lean_object* v_a_6937_; lean_object* v_a_6938_; lean_object* v___x_6940_; uint8_t v_isShared_6941_; uint8_t v_isSharedCheck_6945_; 
v_a_6937_ = lean_ctor_get(v___x_6926_, 0);
v_a_6938_ = lean_ctor_get(v___x_6926_, 1);
v_isSharedCheck_6945_ = !lean_is_exclusive(v___x_6926_);
if (v_isSharedCheck_6945_ == 0)
{
v___x_6940_ = v___x_6926_;
v_isShared_6941_ = v_isSharedCheck_6945_;
goto v_resetjp_6939_;
}
else
{
lean_inc(v_a_6938_);
lean_inc(v_a_6937_);
lean_dec(v___x_6926_);
v___x_6940_ = lean_box(0);
v_isShared_6941_ = v_isSharedCheck_6945_;
goto v_resetjp_6939_;
}
v_resetjp_6939_:
{
lean_object* v___x_6943_; 
if (v_isShared_6941_ == 0)
{
v___x_6943_ = v___x_6940_;
goto v_reusejp_6942_;
}
else
{
lean_object* v_reuseFailAlloc_6944_; 
v_reuseFailAlloc_6944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6944_, 0, v_a_6937_);
lean_ctor_set(v_reuseFailAlloc_6944_, 1, v_a_6938_);
v___x_6943_ = v_reuseFailAlloc_6944_;
goto v_reusejp_6942_;
}
v_reusejp_6942_:
{
return v___x_6943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1___boxed(lean_object* v_libFile_6946_, lean_object* v_thin_6947_, lean_object* v_oFiles_6948_, lean_object* v___y_6949_, lean_object* v___y_6950_, lean_object* v___y_6951_, lean_object* v___y_6952_, lean_object* v___y_6953_, lean_object* v___y_6954_, lean_object* v___y_6955_){
_start:
{
uint8_t v_thin_boxed_6956_; lean_object* v_res_6957_; 
v_thin_boxed_6956_ = lean_unbox(v_thin_6947_);
v_res_6957_ = l_Lake_buildStaticLib___lam__1(v_libFile_6946_, v_thin_boxed_6956_, v_oFiles_6948_, v___y_6949_, v___y_6950_, v___y_6951_, v___y_6952_, v___y_6953_, v___y_6954_);
lean_dec_ref(v___y_6953_);
lean_dec(v___y_6952_);
lean_dec(v___y_6951_);
lean_dec(v___y_6950_);
return v_res_6957_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object* v_libFile_6959_, lean_object* v_oFileJobs_6960_, uint8_t v_thin_6961_, lean_object* v_a_6962_, lean_object* v_a_6963_, lean_object* v_a_6964_, lean_object* v_a_6965_, lean_object* v_a_6966_, lean_object* v_a_6967_){
_start:
{
lean_object* v___x_6969_; lean_object* v___f_6970_; lean_object* v___x_6971_; lean_object* v___x_6972_; lean_object* v___x_6973_; lean_object* v___x_6974_; uint8_t v___x_6975_; lean_object* v___x_6976_; 
v___x_6969_ = lean_box(v_thin_6961_);
v___f_6970_ = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__1___boxed), 10, 2);
lean_closure_set(v___f_6970_, 0, v_libFile_6959_);
lean_closure_set(v___f_6970_, 1, v___x_6969_);
v___x_6971_ = l_Lake_instDataKindFilePath;
v___x_6972_ = ((lean_object*)(l_Lake_buildStaticLib___closed__0));
v___x_6973_ = l_Lake_Job_collectArray___redArg(v_oFileJobs_6960_, v___x_6972_);
v___x_6974_ = lean_unsigned_to_nat(0u);
v___x_6975_ = 0;
v___x_6976_ = l_Lake_Job_mapM___redArg(v___x_6971_, v___x_6973_, v___f_6970_, v___x_6974_, v___x_6975_, v_a_6962_, v_a_6963_, v_a_6964_, v_a_6965_, v_a_6966_, v_a_6967_);
return v___x_6976_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object* v_libFile_6977_, lean_object* v_oFileJobs_6978_, lean_object* v_thin_6979_, lean_object* v_a_6980_, lean_object* v_a_6981_, lean_object* v_a_6982_, lean_object* v_a_6983_, lean_object* v_a_6984_, lean_object* v_a_6985_, lean_object* v_a_6986_){
_start:
{
uint8_t v_thin_boxed_6987_; lean_object* v_res_6988_; 
v_thin_boxed_6987_ = lean_unbox(v_thin_6979_);
v_res_6988_ = l_Lake_buildStaticLib(v_libFile_6977_, v_oFileJobs_6978_, v_thin_boxed_6987_, v_a_6980_, v_a_6981_, v_a_6982_, v_a_6983_, v_a_6984_, v_a_6985_);
lean_dec_ref(v_a_6985_);
lean_dec_ref(v_a_6984_);
lean_dec(v_a_6983_);
lean_dec(v_a_6982_);
lean_dec(v_a_6981_);
lean_dec_ref(v_oFileJobs_6978_);
return v_res_6988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(lean_object* v_as_6989_, size_t v_sz_6990_, size_t v_i_6991_, lean_object* v_b_6992_){
_start:
{
uint8_t v___x_6993_; 
v___x_6993_ = lean_usize_dec_lt(v_i_6991_, v_sz_6990_);
if (v___x_6993_ == 0)
{
return v_b_6992_;
}
else
{
lean_object* v_a_6994_; lean_object* v___x_6995_; size_t v___x_6996_; size_t v___x_6997_; 
v_a_6994_ = lean_array_uget_borrowed(v_as_6989_, v_i_6991_);
lean_inc(v_a_6994_);
v___x_6995_ = lean_array_push(v_b_6992_, v_a_6994_);
v___x_6996_ = ((size_t)1ULL);
v___x_6997_ = lean_usize_add(v_i_6991_, v___x_6996_);
v_i_6991_ = v___x_6997_;
v_b_6992_ = v___x_6995_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0___boxed(lean_object* v_as_6999_, lean_object* v_sz_7000_, lean_object* v_i_7001_, lean_object* v_b_7002_){
_start:
{
size_t v_sz_boxed_7003_; size_t v_i_boxed_7004_; lean_object* v_res_7005_; 
v_sz_boxed_7003_ = lean_unbox_usize(v_sz_7000_);
lean_dec(v_sz_7000_);
v_i_boxed_7004_ = lean_unbox_usize(v_i_7001_);
lean_dec(v_i_7001_);
v_res_7005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(v_as_6999_, v_sz_boxed_7003_, v_i_boxed_7004_, v_b_7002_);
lean_dec_ref(v_as_6999_);
return v_res_7005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(lean_object* v_as_7008_, size_t v_sz_7009_, size_t v_i_7010_, lean_object* v_b_7011_){
_start:
{
uint8_t v___x_7012_; 
v___x_7012_ = lean_usize_dec_lt(v_i_7010_, v_sz_7009_);
if (v___x_7012_ == 0)
{
return v_b_7011_;
}
else
{
lean_object* v_a_7013_; lean_object* v_args_7015_; lean_object* v___x_7023_; 
v_a_7013_ = lean_array_uget_borrowed(v_as_7008_, v_i_7010_);
lean_inc(v_a_7013_);
v___x_7023_ = l_Lake_Dynlib_dir_x3f(v_a_7013_);
if (lean_obj_tag(v___x_7023_) == 1)
{
lean_object* v_val_7024_; lean_object* v___x_7025_; lean_object* v___x_7026_; lean_object* v___x_7027_; 
v_val_7024_ = lean_ctor_get(v___x_7023_, 0);
lean_inc(v_val_7024_);
lean_dec_ref(v___x_7023_);
v___x_7025_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
v___x_7026_ = lean_string_append(v___x_7025_, v_val_7024_);
lean_dec(v_val_7024_);
v___x_7027_ = lean_array_push(v_b_7011_, v___x_7026_);
v_args_7015_ = v___x_7027_;
goto v___jp_7014_;
}
else
{
lean_dec(v___x_7023_);
v_args_7015_ = v_b_7011_;
goto v___jp_7014_;
}
v___jp_7014_:
{
lean_object* v_name_7016_; lean_object* v___x_7017_; lean_object* v___x_7018_; lean_object* v___x_7019_; size_t v___x_7020_; size_t v___x_7021_; 
v_name_7016_ = lean_ctor_get(v_a_7013_, 1);
v___x_7017_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0));
v___x_7018_ = lean_string_append(v___x_7017_, v_name_7016_);
v___x_7019_ = lean_array_push(v_args_7015_, v___x_7018_);
v___x_7020_ = ((size_t)1ULL);
v___x_7021_ = lean_usize_add(v_i_7010_, v___x_7020_);
v_i_7010_ = v___x_7021_;
v_b_7011_ = v___x_7019_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___boxed(lean_object* v_as_7028_, lean_object* v_sz_7029_, lean_object* v_i_7030_, lean_object* v_b_7031_){
_start:
{
size_t v_sz_boxed_7032_; size_t v_i_boxed_7033_; lean_object* v_res_7034_; 
v_sz_boxed_7032_ = lean_unbox_usize(v_sz_7029_);
lean_dec(v_sz_7029_);
v_i_boxed_7033_ = lean_unbox_usize(v_i_7030_);
lean_dec(v_i_7030_);
v_res_7034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(v_as_7028_, v_sz_boxed_7032_, v_i_boxed_7033_, v_b_7031_);
lean_dec_ref(v_as_7028_);
return v_res_7034_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(lean_object* v_objs_7035_, lean_object* v_libs_7036_){
_start:
{
lean_object* v_args_7037_; size_t v_sz_7038_; size_t v___x_7039_; lean_object* v___x_7040_; size_t v_sz_7041_; lean_object* v___x_7042_; 
v_args_7037_ = ((lean_object*)(l_Lake_inputDir___lam__1___closed__0));
v_sz_7038_ = lean_array_size(v_objs_7035_);
v___x_7039_ = ((size_t)0ULL);
v___x_7040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(v_objs_7035_, v_sz_7038_, v___x_7039_, v_args_7037_);
v_sz_7041_ = lean_array_size(v_libs_7036_);
v___x_7042_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(v_libs_7036_, v_sz_7041_, v___x_7039_, v___x_7040_);
return v___x_7042_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs___boxed(lean_object* v_objs_7043_, lean_object* v_libs_7044_){
_start:
{
lean_object* v_res_7045_; 
v_res_7045_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7043_, v_libs_7044_);
lean_dec_ref(v_libs_7044_);
lean_dec_ref(v_objs_7043_);
return v_res_7045_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(lean_object* v_k_7046_, lean_object* v_t_7047_){
_start:
{
if (lean_obj_tag(v_t_7047_) == 0)
{
lean_object* v_k_7048_; lean_object* v_l_7049_; lean_object* v_r_7050_; uint8_t v___x_7051_; 
v_k_7048_ = lean_ctor_get(v_t_7047_, 1);
v_l_7049_ = lean_ctor_get(v_t_7047_, 3);
v_r_7050_ = lean_ctor_get(v_t_7047_, 4);
v___x_7051_ = lean_string_dec_lt(v_k_7046_, v_k_7048_);
if (v___x_7051_ == 0)
{
uint8_t v___x_7052_; 
v___x_7052_ = lean_string_dec_eq(v_k_7046_, v_k_7048_);
if (v___x_7052_ == 0)
{
v_t_7047_ = v_r_7050_;
goto _start;
}
else
{
return v___x_7052_;
}
}
else
{
v_t_7047_ = v_l_7049_;
goto _start;
}
}
else
{
uint8_t v___x_7055_; 
v___x_7055_ = 0;
return v___x_7055_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg___boxed(lean_object* v_k_7056_, lean_object* v_t_7057_){
_start:
{
uint8_t v_res_7058_; lean_object* v_r_7059_; 
v_res_7058_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_k_7056_, v_t_7057_);
lean_dec(v_t_7057_);
lean_dec_ref(v_k_7056_);
v_r_7059_ = lean_box(v_res_7058_);
return v_r_7059_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(lean_object* v_a_7060_, lean_object* v_x_7061_){
_start:
{
if (lean_obj_tag(v_x_7061_) == 0)
{
uint8_t v___x_7062_; 
v___x_7062_ = 0;
return v___x_7062_;
}
else
{
lean_object* v_head_7063_; lean_object* v_tail_7064_; uint8_t v___x_7065_; 
v_head_7063_ = lean_ctor_get(v_x_7061_, 0);
v_tail_7064_ = lean_ctor_get(v_x_7061_, 1);
v___x_7065_ = lean_string_dec_eq(v_a_7060_, v_head_7063_);
if (v___x_7065_ == 0)
{
v_x_7061_ = v_tail_7064_;
goto _start;
}
else
{
return v___x_7065_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1___boxed(lean_object* v_a_7067_, lean_object* v_x_7068_){
_start:
{
uint8_t v_res_7069_; lean_object* v_r_7070_; 
v_res_7069_ = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(v_a_7067_, v_x_7068_);
lean_dec(v_x_7068_);
lean_dec_ref(v_a_7067_);
v_r_7070_ = lean_box(v_res_7069_);
return v_r_7070_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(lean_object* v_k_7071_, lean_object* v_v_7072_, lean_object* v_t_7073_){
_start:
{
if (lean_obj_tag(v_t_7073_) == 0)
{
lean_object* v_size_7074_; lean_object* v_k_7075_; lean_object* v_v_7076_; lean_object* v_l_7077_; lean_object* v_r_7078_; lean_object* v___x_7080_; uint8_t v_isShared_7081_; uint8_t v_isSharedCheck_7359_; 
v_size_7074_ = lean_ctor_get(v_t_7073_, 0);
v_k_7075_ = lean_ctor_get(v_t_7073_, 1);
v_v_7076_ = lean_ctor_get(v_t_7073_, 2);
v_l_7077_ = lean_ctor_get(v_t_7073_, 3);
v_r_7078_ = lean_ctor_get(v_t_7073_, 4);
v_isSharedCheck_7359_ = !lean_is_exclusive(v_t_7073_);
if (v_isSharedCheck_7359_ == 0)
{
v___x_7080_ = v_t_7073_;
v_isShared_7081_ = v_isSharedCheck_7359_;
goto v_resetjp_7079_;
}
else
{
lean_inc(v_r_7078_);
lean_inc(v_l_7077_);
lean_inc(v_v_7076_);
lean_inc(v_k_7075_);
lean_inc(v_size_7074_);
lean_dec(v_t_7073_);
v___x_7080_ = lean_box(0);
v_isShared_7081_ = v_isSharedCheck_7359_;
goto v_resetjp_7079_;
}
v_resetjp_7079_:
{
uint8_t v___x_7082_; 
v___x_7082_ = lean_string_dec_lt(v_k_7071_, v_k_7075_);
if (v___x_7082_ == 0)
{
uint8_t v___x_7083_; 
v___x_7083_ = lean_string_dec_eq(v_k_7071_, v_k_7075_);
if (v___x_7083_ == 0)
{
lean_object* v_impl_7084_; lean_object* v___x_7085_; 
lean_dec(v_size_7074_);
v_impl_7084_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7071_, v_v_7072_, v_r_7078_);
v___x_7085_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_7077_) == 0)
{
lean_object* v_size_7086_; lean_object* v_size_7087_; lean_object* v_k_7088_; lean_object* v_v_7089_; lean_object* v_l_7090_; lean_object* v_r_7091_; lean_object* v___x_7092_; lean_object* v___x_7093_; uint8_t v___x_7094_; 
v_size_7086_ = lean_ctor_get(v_l_7077_, 0);
v_size_7087_ = lean_ctor_get(v_impl_7084_, 0);
lean_inc(v_size_7087_);
v_k_7088_ = lean_ctor_get(v_impl_7084_, 1);
lean_inc(v_k_7088_);
v_v_7089_ = lean_ctor_get(v_impl_7084_, 2);
lean_inc(v_v_7089_);
v_l_7090_ = lean_ctor_get(v_impl_7084_, 3);
lean_inc(v_l_7090_);
v_r_7091_ = lean_ctor_get(v_impl_7084_, 4);
lean_inc(v_r_7091_);
v___x_7092_ = lean_unsigned_to_nat(3u);
v___x_7093_ = lean_nat_mul(v___x_7092_, v_size_7086_);
v___x_7094_ = lean_nat_dec_lt(v___x_7093_, v_size_7087_);
lean_dec(v___x_7093_);
if (v___x_7094_ == 0)
{
lean_object* v___x_7095_; lean_object* v___x_7096_; lean_object* v___x_7098_; 
lean_dec(v_r_7091_);
lean_dec(v_l_7090_);
lean_dec(v_v_7089_);
lean_dec(v_k_7088_);
v___x_7095_ = lean_nat_add(v___x_7085_, v_size_7086_);
v___x_7096_ = lean_nat_add(v___x_7095_, v_size_7087_);
lean_dec(v_size_7087_);
lean_dec(v___x_7095_);
if (v_isShared_7081_ == 0)
{
lean_ctor_set(v___x_7080_, 4, v_impl_7084_);
lean_ctor_set(v___x_7080_, 0, v___x_7096_);
v___x_7098_ = v___x_7080_;
goto v_reusejp_7097_;
}
else
{
lean_object* v_reuseFailAlloc_7099_; 
v_reuseFailAlloc_7099_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7099_, 0, v___x_7096_);
lean_ctor_set(v_reuseFailAlloc_7099_, 1, v_k_7075_);
lean_ctor_set(v_reuseFailAlloc_7099_, 2, v_v_7076_);
lean_ctor_set(v_reuseFailAlloc_7099_, 3, v_l_7077_);
lean_ctor_set(v_reuseFailAlloc_7099_, 4, v_impl_7084_);
v___x_7098_ = v_reuseFailAlloc_7099_;
goto v_reusejp_7097_;
}
v_reusejp_7097_:
{
return v___x_7098_;
}
}
else
{
lean_object* v___x_7101_; uint8_t v_isShared_7102_; uint8_t v_isSharedCheck_7163_; 
v_isSharedCheck_7163_ = !lean_is_exclusive(v_impl_7084_);
if (v_isSharedCheck_7163_ == 0)
{
lean_object* v_unused_7164_; lean_object* v_unused_7165_; lean_object* v_unused_7166_; lean_object* v_unused_7167_; lean_object* v_unused_7168_; 
v_unused_7164_ = lean_ctor_get(v_impl_7084_, 4);
lean_dec(v_unused_7164_);
v_unused_7165_ = lean_ctor_get(v_impl_7084_, 3);
lean_dec(v_unused_7165_);
v_unused_7166_ = lean_ctor_get(v_impl_7084_, 2);
lean_dec(v_unused_7166_);
v_unused_7167_ = lean_ctor_get(v_impl_7084_, 1);
lean_dec(v_unused_7167_);
v_unused_7168_ = lean_ctor_get(v_impl_7084_, 0);
lean_dec(v_unused_7168_);
v___x_7101_ = v_impl_7084_;
v_isShared_7102_ = v_isSharedCheck_7163_;
goto v_resetjp_7100_;
}
else
{
lean_dec(v_impl_7084_);
v___x_7101_ = lean_box(0);
v_isShared_7102_ = v_isSharedCheck_7163_;
goto v_resetjp_7100_;
}
v_resetjp_7100_:
{
lean_object* v_size_7103_; lean_object* v_k_7104_; lean_object* v_v_7105_; lean_object* v_l_7106_; lean_object* v_r_7107_; lean_object* v_size_7108_; lean_object* v___x_7109_; lean_object* v___x_7110_; uint8_t v___x_7111_; 
v_size_7103_ = lean_ctor_get(v_l_7090_, 0);
v_k_7104_ = lean_ctor_get(v_l_7090_, 1);
v_v_7105_ = lean_ctor_get(v_l_7090_, 2);
v_l_7106_ = lean_ctor_get(v_l_7090_, 3);
v_r_7107_ = lean_ctor_get(v_l_7090_, 4);
v_size_7108_ = lean_ctor_get(v_r_7091_, 0);
v___x_7109_ = lean_unsigned_to_nat(2u);
v___x_7110_ = lean_nat_mul(v___x_7109_, v_size_7108_);
v___x_7111_ = lean_nat_dec_lt(v_size_7103_, v___x_7110_);
lean_dec(v___x_7110_);
if (v___x_7111_ == 0)
{
lean_object* v___x_7113_; uint8_t v_isShared_7114_; uint8_t v_isSharedCheck_7139_; 
lean_inc(v_r_7107_);
lean_inc(v_l_7106_);
lean_inc(v_v_7105_);
lean_inc(v_k_7104_);
v_isSharedCheck_7139_ = !lean_is_exclusive(v_l_7090_);
if (v_isSharedCheck_7139_ == 0)
{
lean_object* v_unused_7140_; lean_object* v_unused_7141_; lean_object* v_unused_7142_; lean_object* v_unused_7143_; lean_object* v_unused_7144_; 
v_unused_7140_ = lean_ctor_get(v_l_7090_, 4);
lean_dec(v_unused_7140_);
v_unused_7141_ = lean_ctor_get(v_l_7090_, 3);
lean_dec(v_unused_7141_);
v_unused_7142_ = lean_ctor_get(v_l_7090_, 2);
lean_dec(v_unused_7142_);
v_unused_7143_ = lean_ctor_get(v_l_7090_, 1);
lean_dec(v_unused_7143_);
v_unused_7144_ = lean_ctor_get(v_l_7090_, 0);
lean_dec(v_unused_7144_);
v___x_7113_ = v_l_7090_;
v_isShared_7114_ = v_isSharedCheck_7139_;
goto v_resetjp_7112_;
}
else
{
lean_dec(v_l_7090_);
v___x_7113_ = lean_box(0);
v_isShared_7114_ = v_isSharedCheck_7139_;
goto v_resetjp_7112_;
}
v_resetjp_7112_:
{
lean_object* v___x_7115_; lean_object* v___x_7116_; lean_object* v___y_7118_; lean_object* v___y_7119_; lean_object* v___y_7120_; lean_object* v___y_7129_; 
v___x_7115_ = lean_nat_add(v___x_7085_, v_size_7086_);
v___x_7116_ = lean_nat_add(v___x_7115_, v_size_7087_);
lean_dec(v_size_7087_);
if (lean_obj_tag(v_l_7106_) == 0)
{
lean_object* v_size_7137_; 
v_size_7137_ = lean_ctor_get(v_l_7106_, 0);
lean_inc(v_size_7137_);
v___y_7129_ = v_size_7137_;
goto v___jp_7128_;
}
else
{
lean_object* v___x_7138_; 
v___x_7138_ = lean_unsigned_to_nat(0u);
v___y_7129_ = v___x_7138_;
goto v___jp_7128_;
}
v___jp_7117_:
{
lean_object* v___x_7121_; lean_object* v___x_7123_; 
v___x_7121_ = lean_nat_add(v___y_7118_, v___y_7120_);
lean_dec(v___y_7120_);
lean_dec(v___y_7118_);
if (v_isShared_7114_ == 0)
{
lean_ctor_set(v___x_7113_, 4, v_r_7091_);
lean_ctor_set(v___x_7113_, 3, v_r_7107_);
lean_ctor_set(v___x_7113_, 2, v_v_7089_);
lean_ctor_set(v___x_7113_, 1, v_k_7088_);
lean_ctor_set(v___x_7113_, 0, v___x_7121_);
v___x_7123_ = v___x_7113_;
goto v_reusejp_7122_;
}
else
{
lean_object* v_reuseFailAlloc_7127_; 
v_reuseFailAlloc_7127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7127_, 0, v___x_7121_);
lean_ctor_set(v_reuseFailAlloc_7127_, 1, v_k_7088_);
lean_ctor_set(v_reuseFailAlloc_7127_, 2, v_v_7089_);
lean_ctor_set(v_reuseFailAlloc_7127_, 3, v_r_7107_);
lean_ctor_set(v_reuseFailAlloc_7127_, 4, v_r_7091_);
v___x_7123_ = v_reuseFailAlloc_7127_;
goto v_reusejp_7122_;
}
v_reusejp_7122_:
{
lean_object* v___x_7125_; 
if (v_isShared_7102_ == 0)
{
lean_ctor_set(v___x_7101_, 4, v___x_7123_);
lean_ctor_set(v___x_7101_, 3, v___y_7119_);
lean_ctor_set(v___x_7101_, 2, v_v_7105_);
lean_ctor_set(v___x_7101_, 1, v_k_7104_);
lean_ctor_set(v___x_7101_, 0, v___x_7116_);
v___x_7125_ = v___x_7101_;
goto v_reusejp_7124_;
}
else
{
lean_object* v_reuseFailAlloc_7126_; 
v_reuseFailAlloc_7126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7126_, 0, v___x_7116_);
lean_ctor_set(v_reuseFailAlloc_7126_, 1, v_k_7104_);
lean_ctor_set(v_reuseFailAlloc_7126_, 2, v_v_7105_);
lean_ctor_set(v_reuseFailAlloc_7126_, 3, v___y_7119_);
lean_ctor_set(v_reuseFailAlloc_7126_, 4, v___x_7123_);
v___x_7125_ = v_reuseFailAlloc_7126_;
goto v_reusejp_7124_;
}
v_reusejp_7124_:
{
return v___x_7125_;
}
}
}
v___jp_7128_:
{
lean_object* v___x_7130_; lean_object* v___x_7132_; 
v___x_7130_ = lean_nat_add(v___x_7115_, v___y_7129_);
lean_dec(v___y_7129_);
lean_dec(v___x_7115_);
if (v_isShared_7081_ == 0)
{
lean_ctor_set(v___x_7080_, 4, v_l_7106_);
lean_ctor_set(v___x_7080_, 0, v___x_7130_);
v___x_7132_ = v___x_7080_;
goto v_reusejp_7131_;
}
else
{
lean_object* v_reuseFailAlloc_7136_; 
v_reuseFailAlloc_7136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7136_, 0, v___x_7130_);
lean_ctor_set(v_reuseFailAlloc_7136_, 1, v_k_7075_);
lean_ctor_set(v_reuseFailAlloc_7136_, 2, v_v_7076_);
lean_ctor_set(v_reuseFailAlloc_7136_, 3, v_l_7077_);
lean_ctor_set(v_reuseFailAlloc_7136_, 4, v_l_7106_);
v___x_7132_ = v_reuseFailAlloc_7136_;
goto v_reusejp_7131_;
}
v_reusejp_7131_:
{
lean_object* v___x_7133_; 
v___x_7133_ = lean_nat_add(v___x_7085_, v_size_7108_);
if (lean_obj_tag(v_r_7107_) == 0)
{
lean_object* v_size_7134_; 
v_size_7134_ = lean_ctor_get(v_r_7107_, 0);
lean_inc(v_size_7134_);
v___y_7118_ = v___x_7133_;
v___y_7119_ = v___x_7132_;
v___y_7120_ = v_size_7134_;
goto v___jp_7117_;
}
else
{
lean_object* v___x_7135_; 
v___x_7135_ = lean_unsigned_to_nat(0u);
v___y_7118_ = v___x_7133_;
v___y_7119_ = v___x_7132_;
v___y_7120_ = v___x_7135_;
goto v___jp_7117_;
}
}
}
}
}
else
{
lean_object* v___x_7145_; lean_object* v___x_7146_; lean_object* v___x_7147_; lean_object* v___x_7149_; 
lean_del_object(v___x_7080_);
v___x_7145_ = lean_nat_add(v___x_7085_, v_size_7086_);
v___x_7146_ = lean_nat_add(v___x_7145_, v_size_7087_);
lean_dec(v_size_7087_);
v___x_7147_ = lean_nat_add(v___x_7145_, v_size_7103_);
lean_dec(v___x_7145_);
lean_inc_ref(v_l_7077_);
if (v_isShared_7102_ == 0)
{
lean_ctor_set(v___x_7101_, 4, v_l_7090_);
lean_ctor_set(v___x_7101_, 3, v_l_7077_);
lean_ctor_set(v___x_7101_, 2, v_v_7076_);
lean_ctor_set(v___x_7101_, 1, v_k_7075_);
lean_ctor_set(v___x_7101_, 0, v___x_7147_);
v___x_7149_ = v___x_7101_;
goto v_reusejp_7148_;
}
else
{
lean_object* v_reuseFailAlloc_7162_; 
v_reuseFailAlloc_7162_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7162_, 0, v___x_7147_);
lean_ctor_set(v_reuseFailAlloc_7162_, 1, v_k_7075_);
lean_ctor_set(v_reuseFailAlloc_7162_, 2, v_v_7076_);
lean_ctor_set(v_reuseFailAlloc_7162_, 3, v_l_7077_);
lean_ctor_set(v_reuseFailAlloc_7162_, 4, v_l_7090_);
v___x_7149_ = v_reuseFailAlloc_7162_;
goto v_reusejp_7148_;
}
v_reusejp_7148_:
{
lean_object* v___x_7151_; uint8_t v_isShared_7152_; uint8_t v_isSharedCheck_7156_; 
v_isSharedCheck_7156_ = !lean_is_exclusive(v_l_7077_);
if (v_isSharedCheck_7156_ == 0)
{
lean_object* v_unused_7157_; lean_object* v_unused_7158_; lean_object* v_unused_7159_; lean_object* v_unused_7160_; lean_object* v_unused_7161_; 
v_unused_7157_ = lean_ctor_get(v_l_7077_, 4);
lean_dec(v_unused_7157_);
v_unused_7158_ = lean_ctor_get(v_l_7077_, 3);
lean_dec(v_unused_7158_);
v_unused_7159_ = lean_ctor_get(v_l_7077_, 2);
lean_dec(v_unused_7159_);
v_unused_7160_ = lean_ctor_get(v_l_7077_, 1);
lean_dec(v_unused_7160_);
v_unused_7161_ = lean_ctor_get(v_l_7077_, 0);
lean_dec(v_unused_7161_);
v___x_7151_ = v_l_7077_;
v_isShared_7152_ = v_isSharedCheck_7156_;
goto v_resetjp_7150_;
}
else
{
lean_dec(v_l_7077_);
v___x_7151_ = lean_box(0);
v_isShared_7152_ = v_isSharedCheck_7156_;
goto v_resetjp_7150_;
}
v_resetjp_7150_:
{
lean_object* v___x_7154_; 
if (v_isShared_7152_ == 0)
{
lean_ctor_set(v___x_7151_, 4, v_r_7091_);
lean_ctor_set(v___x_7151_, 3, v___x_7149_);
lean_ctor_set(v___x_7151_, 2, v_v_7089_);
lean_ctor_set(v___x_7151_, 1, v_k_7088_);
lean_ctor_set(v___x_7151_, 0, v___x_7146_);
v___x_7154_ = v___x_7151_;
goto v_reusejp_7153_;
}
else
{
lean_object* v_reuseFailAlloc_7155_; 
v_reuseFailAlloc_7155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7155_, 0, v___x_7146_);
lean_ctor_set(v_reuseFailAlloc_7155_, 1, v_k_7088_);
lean_ctor_set(v_reuseFailAlloc_7155_, 2, v_v_7089_);
lean_ctor_set(v_reuseFailAlloc_7155_, 3, v___x_7149_);
lean_ctor_set(v_reuseFailAlloc_7155_, 4, v_r_7091_);
v___x_7154_ = v_reuseFailAlloc_7155_;
goto v_reusejp_7153_;
}
v_reusejp_7153_:
{
return v___x_7154_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_7169_; 
v_l_7169_ = lean_ctor_get(v_impl_7084_, 3);
lean_inc(v_l_7169_);
if (lean_obj_tag(v_l_7169_) == 0)
{
lean_object* v_r_7170_; lean_object* v_k_7171_; lean_object* v_v_7172_; lean_object* v___x_7174_; uint8_t v_isShared_7175_; uint8_t v_isSharedCheck_7195_; 
v_r_7170_ = lean_ctor_get(v_impl_7084_, 4);
v_k_7171_ = lean_ctor_get(v_impl_7084_, 1);
v_v_7172_ = lean_ctor_get(v_impl_7084_, 2);
v_isSharedCheck_7195_ = !lean_is_exclusive(v_impl_7084_);
if (v_isSharedCheck_7195_ == 0)
{
lean_object* v_unused_7196_; lean_object* v_unused_7197_; 
v_unused_7196_ = lean_ctor_get(v_impl_7084_, 3);
lean_dec(v_unused_7196_);
v_unused_7197_ = lean_ctor_get(v_impl_7084_, 0);
lean_dec(v_unused_7197_);
v___x_7174_ = v_impl_7084_;
v_isShared_7175_ = v_isSharedCheck_7195_;
goto v_resetjp_7173_;
}
else
{
lean_inc(v_r_7170_);
lean_inc(v_v_7172_);
lean_inc(v_k_7171_);
lean_dec(v_impl_7084_);
v___x_7174_ = lean_box(0);
v_isShared_7175_ = v_isSharedCheck_7195_;
goto v_resetjp_7173_;
}
v_resetjp_7173_:
{
lean_object* v_k_7176_; lean_object* v_v_7177_; lean_object* v___x_7179_; uint8_t v_isShared_7180_; uint8_t v_isSharedCheck_7191_; 
v_k_7176_ = lean_ctor_get(v_l_7169_, 1);
v_v_7177_ = lean_ctor_get(v_l_7169_, 2);
v_isSharedCheck_7191_ = !lean_is_exclusive(v_l_7169_);
if (v_isSharedCheck_7191_ == 0)
{
lean_object* v_unused_7192_; lean_object* v_unused_7193_; lean_object* v_unused_7194_; 
v_unused_7192_ = lean_ctor_get(v_l_7169_, 4);
lean_dec(v_unused_7192_);
v_unused_7193_ = lean_ctor_get(v_l_7169_, 3);
lean_dec(v_unused_7193_);
v_unused_7194_ = lean_ctor_get(v_l_7169_, 0);
lean_dec(v_unused_7194_);
v___x_7179_ = v_l_7169_;
v_isShared_7180_ = v_isSharedCheck_7191_;
goto v_resetjp_7178_;
}
else
{
lean_inc(v_v_7177_);
lean_inc(v_k_7176_);
lean_dec(v_l_7169_);
v___x_7179_ = lean_box(0);
v_isShared_7180_ = v_isSharedCheck_7191_;
goto v_resetjp_7178_;
}
v_resetjp_7178_:
{
lean_object* v___x_7181_; lean_object* v___x_7183_; 
v___x_7181_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_7170_, 2);
if (v_isShared_7180_ == 0)
{
lean_ctor_set(v___x_7179_, 4, v_r_7170_);
lean_ctor_set(v___x_7179_, 3, v_r_7170_);
lean_ctor_set(v___x_7179_, 2, v_v_7076_);
lean_ctor_set(v___x_7179_, 1, v_k_7075_);
lean_ctor_set(v___x_7179_, 0, v___x_7085_);
v___x_7183_ = v___x_7179_;
goto v_reusejp_7182_;
}
else
{
lean_object* v_reuseFailAlloc_7190_; 
v_reuseFailAlloc_7190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7190_, 0, v___x_7085_);
lean_ctor_set(v_reuseFailAlloc_7190_, 1, v_k_7075_);
lean_ctor_set(v_reuseFailAlloc_7190_, 2, v_v_7076_);
lean_ctor_set(v_reuseFailAlloc_7190_, 3, v_r_7170_);
lean_ctor_set(v_reuseFailAlloc_7190_, 4, v_r_7170_);
v___x_7183_ = v_reuseFailAlloc_7190_;
goto v_reusejp_7182_;
}
v_reusejp_7182_:
{
lean_object* v___x_7185_; 
lean_inc(v_r_7170_);
if (v_isShared_7175_ == 0)
{
lean_ctor_set(v___x_7174_, 3, v_r_7170_);
lean_ctor_set(v___x_7174_, 0, v___x_7085_);
v___x_7185_ = v___x_7174_;
goto v_reusejp_7184_;
}
else
{
lean_object* v_reuseFailAlloc_7189_; 
v_reuseFailAlloc_7189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7189_, 0, v___x_7085_);
lean_ctor_set(v_reuseFailAlloc_7189_, 1, v_k_7171_);
lean_ctor_set(v_reuseFailAlloc_7189_, 2, v_v_7172_);
lean_ctor_set(v_reuseFailAlloc_7189_, 3, v_r_7170_);
lean_ctor_set(v_reuseFailAlloc_7189_, 4, v_r_7170_);
v___x_7185_ = v_reuseFailAlloc_7189_;
goto v_reusejp_7184_;
}
v_reusejp_7184_:
{
lean_object* v___x_7187_; 
if (v_isShared_7081_ == 0)
{
lean_ctor_set(v___x_7080_, 4, v___x_7185_);
lean_ctor_set(v___x_7080_, 3, v___x_7183_);
lean_ctor_set(v___x_7080_, 2, v_v_7177_);
lean_ctor_set(v___x_7080_, 1, v_k_7176_);
lean_ctor_set(v___x_7080_, 0, v___x_7181_);
v___x_7187_ = v___x_7080_;
goto v_reusejp_7186_;
}
else
{
lean_object* v_reuseFailAlloc_7188_; 
v_reuseFailAlloc_7188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7188_, 0, v___x_7181_);
lean_ctor_set(v_reuseFailAlloc_7188_, 1, v_k_7176_);
lean_ctor_set(v_reuseFailAlloc_7188_, 2, v_v_7177_);
lean_ctor_set(v_reuseFailAlloc_7188_, 3, v___x_7183_);
lean_ctor_set(v_reuseFailAlloc_7188_, 4, v___x_7185_);
v___x_7187_ = v_reuseFailAlloc_7188_;
goto v_reusejp_7186_;
}
v_reusejp_7186_:
{
return v___x_7187_;
}
}
}
}
}
}
else
{
lean_object* v_r_7198_; 
v_r_7198_ = lean_ctor_get(v_impl_7084_, 4);
lean_inc(v_r_7198_);
if (lean_obj_tag(v_r_7198_) == 0)
{
lean_object* v_k_7199_; lean_object* v_v_7200_; lean_object* v___x_7202_; uint8_t v_isShared_7203_; uint8_t v_isSharedCheck_7211_; 
v_k_7199_ = lean_ctor_get(v_impl_7084_, 1);
v_v_7200_ = lean_ctor_get(v_impl_7084_, 2);
v_isSharedCheck_7211_ = !lean_is_exclusive(v_impl_7084_);
if (v_isSharedCheck_7211_ == 0)
{
lean_object* v_unused_7212_; lean_object* v_unused_7213_; lean_object* v_unused_7214_; 
v_unused_7212_ = lean_ctor_get(v_impl_7084_, 4);
lean_dec(v_unused_7212_);
v_unused_7213_ = lean_ctor_get(v_impl_7084_, 3);
lean_dec(v_unused_7213_);
v_unused_7214_ = lean_ctor_get(v_impl_7084_, 0);
lean_dec(v_unused_7214_);
v___x_7202_ = v_impl_7084_;
v_isShared_7203_ = v_isSharedCheck_7211_;
goto v_resetjp_7201_;
}
else
{
lean_inc(v_v_7200_);
lean_inc(v_k_7199_);
lean_dec(v_impl_7084_);
v___x_7202_ = lean_box(0);
v_isShared_7203_ = v_isSharedCheck_7211_;
goto v_resetjp_7201_;
}
v_resetjp_7201_:
{
lean_object* v___x_7204_; lean_object* v___x_7206_; 
v___x_7204_ = lean_unsigned_to_nat(3u);
if (v_isShared_7203_ == 0)
{
lean_ctor_set(v___x_7202_, 4, v_l_7169_);
lean_ctor_set(v___x_7202_, 2, v_v_7076_);
lean_ctor_set(v___x_7202_, 1, v_k_7075_);
lean_ctor_set(v___x_7202_, 0, v___x_7085_);
v___x_7206_ = v___x_7202_;
goto v_reusejp_7205_;
}
else
{
lean_object* v_reuseFailAlloc_7210_; 
v_reuseFailAlloc_7210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7210_, 0, v___x_7085_);
lean_ctor_set(v_reuseFailAlloc_7210_, 1, v_k_7075_);
lean_ctor_set(v_reuseFailAlloc_7210_, 2, v_v_7076_);
lean_ctor_set(v_reuseFailAlloc_7210_, 3, v_l_7169_);
lean_ctor_set(v_reuseFailAlloc_7210_, 4, v_l_7169_);
v___x_7206_ = v_reuseFailAlloc_7210_;
goto v_reusejp_7205_;
}
v_reusejp_7205_:
{
lean_object* v___x_7208_; 
if (v_isShared_7081_ == 0)
{
lean_ctor_set(v___x_7080_, 4, v_r_7198_);
lean_ctor_set(v___x_7080_, 3, v___x_7206_);
lean_ctor_set(v___x_7080_, 2, v_v_7200_);
lean_ctor_set(v___x_7080_, 1, v_k_7199_);
lean_ctor_set(v___x_7080_, 0, v___x_7204_);
v___x_7208_ = v___x_7080_;
goto v_reusejp_7207_;
}
else
{
lean_object* v_reuseFailAlloc_7209_; 
v_reuseFailAlloc_7209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7209_, 0, v___x_7204_);
lean_ctor_set(v_reuseFailAlloc_7209_, 1, v_k_7199_);
lean_ctor_set(v_reuseFailAlloc_7209_, 2, v_v_7200_);
lean_ctor_set(v_reuseFailAlloc_7209_, 3, v___x_7206_);
lean_ctor_set(v_reuseFailAlloc_7209_, 4, v_r_7198_);
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
lean_object* v___x_7215_; lean_object* v___x_7217_; 
v___x_7215_ = lean_unsigned_to_nat(2u);
if (v_isShared_7081_ == 0)
{
lean_ctor_set(v___x_7080_, 4, v_impl_7084_);
lean_ctor_set(v___x_7080_, 3, v_r_7198_);
lean_ctor_set(v___x_7080_, 0, v___x_7215_);
v___x_7217_ = v___x_7080_;
goto v_reusejp_7216_;
}
else
{
lean_object* v_reuseFailAlloc_7218_; 
v_reuseFailAlloc_7218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7218_, 0, v___x_7215_);
lean_ctor_set(v_reuseFailAlloc_7218_, 1, v_k_7075_);
lean_ctor_set(v_reuseFailAlloc_7218_, 2, v_v_7076_);
lean_ctor_set(v_reuseFailAlloc_7218_, 3, v_r_7198_);
lean_ctor_set(v_reuseFailAlloc_7218_, 4, v_impl_7084_);
v___x_7217_ = v_reuseFailAlloc_7218_;
goto v_reusejp_7216_;
}
v_reusejp_7216_:
{
return v___x_7217_;
}
}
}
}
}
else
{
lean_object* v___x_7220_; 
lean_dec(v_v_7076_);
lean_dec(v_k_7075_);
if (v_isShared_7081_ == 0)
{
lean_ctor_set(v___x_7080_, 2, v_v_7072_);
lean_ctor_set(v___x_7080_, 1, v_k_7071_);
v___x_7220_ = v___x_7080_;
goto v_reusejp_7219_;
}
else
{
lean_object* v_reuseFailAlloc_7221_; 
v_reuseFailAlloc_7221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7221_, 0, v_size_7074_);
lean_ctor_set(v_reuseFailAlloc_7221_, 1, v_k_7071_);
lean_ctor_set(v_reuseFailAlloc_7221_, 2, v_v_7072_);
lean_ctor_set(v_reuseFailAlloc_7221_, 3, v_l_7077_);
lean_ctor_set(v_reuseFailAlloc_7221_, 4, v_r_7078_);
v___x_7220_ = v_reuseFailAlloc_7221_;
goto v_reusejp_7219_;
}
v_reusejp_7219_:
{
return v___x_7220_;
}
}
}
else
{
lean_object* v_impl_7222_; lean_object* v___x_7223_; 
lean_dec(v_size_7074_);
v_impl_7222_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7071_, v_v_7072_, v_l_7077_);
v___x_7223_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_7078_) == 0)
{
lean_object* v_size_7224_; lean_object* v_size_7225_; lean_object* v_k_7226_; lean_object* v_v_7227_; lean_object* v_l_7228_; lean_object* v_r_7229_; lean_object* v___x_7230_; lean_object* v___x_7231_; uint8_t v___x_7232_; 
v_size_7224_ = lean_ctor_get(v_r_7078_, 0);
v_size_7225_ = lean_ctor_get(v_impl_7222_, 0);
lean_inc(v_size_7225_);
v_k_7226_ = lean_ctor_get(v_impl_7222_, 1);
lean_inc(v_k_7226_);
v_v_7227_ = lean_ctor_get(v_impl_7222_, 2);
lean_inc(v_v_7227_);
v_l_7228_ = lean_ctor_get(v_impl_7222_, 3);
lean_inc(v_l_7228_);
v_r_7229_ = lean_ctor_get(v_impl_7222_, 4);
lean_inc(v_r_7229_);
v___x_7230_ = lean_unsigned_to_nat(3u);
v___x_7231_ = lean_nat_mul(v___x_7230_, v_size_7224_);
v___x_7232_ = lean_nat_dec_lt(v___x_7231_, v_size_7225_);
lean_dec(v___x_7231_);
if (v___x_7232_ == 0)
{
lean_object* v___x_7233_; lean_object* v___x_7234_; lean_object* v___x_7236_; 
lean_dec(v_r_7229_);
lean_dec(v_l_7228_);
lean_dec(v_v_7227_);
lean_dec(v_k_7226_);
v___x_7233_ = lean_nat_add(v___x_7223_, v_size_7225_);
lean_dec(v_size_7225_);
v___x_7234_ = lean_nat_add(v___x_7233_, v_size_7224_);
lean_dec(v___x_7233_);
if (v_isShared_7081_ == 0)
{
lean_ctor_set(v___x_7080_, 3, v_impl_7222_);
lean_ctor_set(v___x_7080_, 0, v___x_7234_);
v___x_7236_ = v___x_7080_;
goto v_reusejp_7235_;
}
else
{
lean_object* v_reuseFailAlloc_7237_; 
v_reuseFailAlloc_7237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7237_, 0, v___x_7234_);
lean_ctor_set(v_reuseFailAlloc_7237_, 1, v_k_7075_);
lean_ctor_set(v_reuseFailAlloc_7237_, 2, v_v_7076_);
lean_ctor_set(v_reuseFailAlloc_7237_, 3, v_impl_7222_);
lean_ctor_set(v_reuseFailAlloc_7237_, 4, v_r_7078_);
v___x_7236_ = v_reuseFailAlloc_7237_;
goto v_reusejp_7235_;
}
v_reusejp_7235_:
{
return v___x_7236_;
}
}
else
{
lean_object* v___x_7239_; uint8_t v_isShared_7240_; uint8_t v_isSharedCheck_7303_; 
v_isSharedCheck_7303_ = !lean_is_exclusive(v_impl_7222_);
if (v_isSharedCheck_7303_ == 0)
{
lean_object* v_unused_7304_; lean_object* v_unused_7305_; lean_object* v_unused_7306_; lean_object* v_unused_7307_; lean_object* v_unused_7308_; 
v_unused_7304_ = lean_ctor_get(v_impl_7222_, 4);
lean_dec(v_unused_7304_);
v_unused_7305_ = lean_ctor_get(v_impl_7222_, 3);
lean_dec(v_unused_7305_);
v_unused_7306_ = lean_ctor_get(v_impl_7222_, 2);
lean_dec(v_unused_7306_);
v_unused_7307_ = lean_ctor_get(v_impl_7222_, 1);
lean_dec(v_unused_7307_);
v_unused_7308_ = lean_ctor_get(v_impl_7222_, 0);
lean_dec(v_unused_7308_);
v___x_7239_ = v_impl_7222_;
v_isShared_7240_ = v_isSharedCheck_7303_;
goto v_resetjp_7238_;
}
else
{
lean_dec(v_impl_7222_);
v___x_7239_ = lean_box(0);
v_isShared_7240_ = v_isSharedCheck_7303_;
goto v_resetjp_7238_;
}
v_resetjp_7238_:
{
lean_object* v_size_7241_; lean_object* v_size_7242_; lean_object* v_k_7243_; lean_object* v_v_7244_; lean_object* v_l_7245_; lean_object* v_r_7246_; lean_object* v___x_7247_; lean_object* v___x_7248_; uint8_t v___x_7249_; 
v_size_7241_ = lean_ctor_get(v_l_7228_, 0);
v_size_7242_ = lean_ctor_get(v_r_7229_, 0);
v_k_7243_ = lean_ctor_get(v_r_7229_, 1);
v_v_7244_ = lean_ctor_get(v_r_7229_, 2);
v_l_7245_ = lean_ctor_get(v_r_7229_, 3);
v_r_7246_ = lean_ctor_get(v_r_7229_, 4);
v___x_7247_ = lean_unsigned_to_nat(2u);
v___x_7248_ = lean_nat_mul(v___x_7247_, v_size_7241_);
v___x_7249_ = lean_nat_dec_lt(v_size_7242_, v___x_7248_);
lean_dec(v___x_7248_);
if (v___x_7249_ == 0)
{
lean_object* v___x_7251_; uint8_t v_isShared_7252_; uint8_t v_isSharedCheck_7278_; 
lean_inc(v_r_7246_);
lean_inc(v_l_7245_);
lean_inc(v_v_7244_);
lean_inc(v_k_7243_);
v_isSharedCheck_7278_ = !lean_is_exclusive(v_r_7229_);
if (v_isSharedCheck_7278_ == 0)
{
lean_object* v_unused_7279_; lean_object* v_unused_7280_; lean_object* v_unused_7281_; lean_object* v_unused_7282_; lean_object* v_unused_7283_; 
v_unused_7279_ = lean_ctor_get(v_r_7229_, 4);
lean_dec(v_unused_7279_);
v_unused_7280_ = lean_ctor_get(v_r_7229_, 3);
lean_dec(v_unused_7280_);
v_unused_7281_ = lean_ctor_get(v_r_7229_, 2);
lean_dec(v_unused_7281_);
v_unused_7282_ = lean_ctor_get(v_r_7229_, 1);
lean_dec(v_unused_7282_);
v_unused_7283_ = lean_ctor_get(v_r_7229_, 0);
lean_dec(v_unused_7283_);
v___x_7251_ = v_r_7229_;
v_isShared_7252_ = v_isSharedCheck_7278_;
goto v_resetjp_7250_;
}
else
{
lean_dec(v_r_7229_);
v___x_7251_ = lean_box(0);
v_isShared_7252_ = v_isSharedCheck_7278_;
goto v_resetjp_7250_;
}
v_resetjp_7250_:
{
lean_object* v___x_7253_; lean_object* v___x_7254_; lean_object* v___y_7256_; lean_object* v___y_7257_; lean_object* v___y_7258_; lean_object* v___x_7266_; lean_object* v___y_7268_; 
v___x_7253_ = lean_nat_add(v___x_7223_, v_size_7225_);
lean_dec(v_size_7225_);
v___x_7254_ = lean_nat_add(v___x_7253_, v_size_7224_);
lean_dec(v___x_7253_);
v___x_7266_ = lean_nat_add(v___x_7223_, v_size_7241_);
if (lean_obj_tag(v_l_7245_) == 0)
{
lean_object* v_size_7276_; 
v_size_7276_ = lean_ctor_get(v_l_7245_, 0);
lean_inc(v_size_7276_);
v___y_7268_ = v_size_7276_;
goto v___jp_7267_;
}
else
{
lean_object* v___x_7277_; 
v___x_7277_ = lean_unsigned_to_nat(0u);
v___y_7268_ = v___x_7277_;
goto v___jp_7267_;
}
v___jp_7255_:
{
lean_object* v___x_7259_; lean_object* v___x_7261_; 
v___x_7259_ = lean_nat_add(v___y_7257_, v___y_7258_);
lean_dec(v___y_7258_);
lean_dec(v___y_7257_);
if (v_isShared_7252_ == 0)
{
lean_ctor_set(v___x_7251_, 4, v_r_7078_);
lean_ctor_set(v___x_7251_, 3, v_r_7246_);
lean_ctor_set(v___x_7251_, 2, v_v_7076_);
lean_ctor_set(v___x_7251_, 1, v_k_7075_);
lean_ctor_set(v___x_7251_, 0, v___x_7259_);
v___x_7261_ = v___x_7251_;
goto v_reusejp_7260_;
}
else
{
lean_object* v_reuseFailAlloc_7265_; 
v_reuseFailAlloc_7265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7265_, 0, v___x_7259_);
lean_ctor_set(v_reuseFailAlloc_7265_, 1, v_k_7075_);
lean_ctor_set(v_reuseFailAlloc_7265_, 2, v_v_7076_);
lean_ctor_set(v_reuseFailAlloc_7265_, 3, v_r_7246_);
lean_ctor_set(v_reuseFailAlloc_7265_, 4, v_r_7078_);
v___x_7261_ = v_reuseFailAlloc_7265_;
goto v_reusejp_7260_;
}
v_reusejp_7260_:
{
lean_object* v___x_7263_; 
if (v_isShared_7240_ == 0)
{
lean_ctor_set(v___x_7239_, 4, v___x_7261_);
lean_ctor_set(v___x_7239_, 3, v___y_7256_);
lean_ctor_set(v___x_7239_, 2, v_v_7244_);
lean_ctor_set(v___x_7239_, 1, v_k_7243_);
lean_ctor_set(v___x_7239_, 0, v___x_7254_);
v___x_7263_ = v___x_7239_;
goto v_reusejp_7262_;
}
else
{
lean_object* v_reuseFailAlloc_7264_; 
v_reuseFailAlloc_7264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7264_, 0, v___x_7254_);
lean_ctor_set(v_reuseFailAlloc_7264_, 1, v_k_7243_);
lean_ctor_set(v_reuseFailAlloc_7264_, 2, v_v_7244_);
lean_ctor_set(v_reuseFailAlloc_7264_, 3, v___y_7256_);
lean_ctor_set(v_reuseFailAlloc_7264_, 4, v___x_7261_);
v___x_7263_ = v_reuseFailAlloc_7264_;
goto v_reusejp_7262_;
}
v_reusejp_7262_:
{
return v___x_7263_;
}
}
}
v___jp_7267_:
{
lean_object* v___x_7269_; lean_object* v___x_7271_; 
v___x_7269_ = lean_nat_add(v___x_7266_, v___y_7268_);
lean_dec(v___y_7268_);
lean_dec(v___x_7266_);
if (v_isShared_7081_ == 0)
{
lean_ctor_set(v___x_7080_, 4, v_l_7245_);
lean_ctor_set(v___x_7080_, 3, v_l_7228_);
lean_ctor_set(v___x_7080_, 2, v_v_7227_);
lean_ctor_set(v___x_7080_, 1, v_k_7226_);
lean_ctor_set(v___x_7080_, 0, v___x_7269_);
v___x_7271_ = v___x_7080_;
goto v_reusejp_7270_;
}
else
{
lean_object* v_reuseFailAlloc_7275_; 
v_reuseFailAlloc_7275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7275_, 0, v___x_7269_);
lean_ctor_set(v_reuseFailAlloc_7275_, 1, v_k_7226_);
lean_ctor_set(v_reuseFailAlloc_7275_, 2, v_v_7227_);
lean_ctor_set(v_reuseFailAlloc_7275_, 3, v_l_7228_);
lean_ctor_set(v_reuseFailAlloc_7275_, 4, v_l_7245_);
v___x_7271_ = v_reuseFailAlloc_7275_;
goto v_reusejp_7270_;
}
v_reusejp_7270_:
{
lean_object* v___x_7272_; 
v___x_7272_ = lean_nat_add(v___x_7223_, v_size_7224_);
if (lean_obj_tag(v_r_7246_) == 0)
{
lean_object* v_size_7273_; 
v_size_7273_ = lean_ctor_get(v_r_7246_, 0);
lean_inc(v_size_7273_);
v___y_7256_ = v___x_7271_;
v___y_7257_ = v___x_7272_;
v___y_7258_ = v_size_7273_;
goto v___jp_7255_;
}
else
{
lean_object* v___x_7274_; 
v___x_7274_ = lean_unsigned_to_nat(0u);
v___y_7256_ = v___x_7271_;
v___y_7257_ = v___x_7272_;
v___y_7258_ = v___x_7274_;
goto v___jp_7255_;
}
}
}
}
}
else
{
lean_object* v___x_7284_; lean_object* v___x_7285_; lean_object* v___x_7286_; lean_object* v___x_7287_; lean_object* v___x_7289_; 
lean_del_object(v___x_7080_);
v___x_7284_ = lean_nat_add(v___x_7223_, v_size_7225_);
lean_dec(v_size_7225_);
v___x_7285_ = lean_nat_add(v___x_7284_, v_size_7224_);
lean_dec(v___x_7284_);
v___x_7286_ = lean_nat_add(v___x_7223_, v_size_7224_);
v___x_7287_ = lean_nat_add(v___x_7286_, v_size_7242_);
lean_dec(v___x_7286_);
lean_inc_ref(v_r_7078_);
if (v_isShared_7240_ == 0)
{
lean_ctor_set(v___x_7239_, 4, v_r_7078_);
lean_ctor_set(v___x_7239_, 3, v_r_7229_);
lean_ctor_set(v___x_7239_, 2, v_v_7076_);
lean_ctor_set(v___x_7239_, 1, v_k_7075_);
lean_ctor_set(v___x_7239_, 0, v___x_7287_);
v___x_7289_ = v___x_7239_;
goto v_reusejp_7288_;
}
else
{
lean_object* v_reuseFailAlloc_7302_; 
v_reuseFailAlloc_7302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7302_, 0, v___x_7287_);
lean_ctor_set(v_reuseFailAlloc_7302_, 1, v_k_7075_);
lean_ctor_set(v_reuseFailAlloc_7302_, 2, v_v_7076_);
lean_ctor_set(v_reuseFailAlloc_7302_, 3, v_r_7229_);
lean_ctor_set(v_reuseFailAlloc_7302_, 4, v_r_7078_);
v___x_7289_ = v_reuseFailAlloc_7302_;
goto v_reusejp_7288_;
}
v_reusejp_7288_:
{
lean_object* v___x_7291_; uint8_t v_isShared_7292_; uint8_t v_isSharedCheck_7296_; 
v_isSharedCheck_7296_ = !lean_is_exclusive(v_r_7078_);
if (v_isSharedCheck_7296_ == 0)
{
lean_object* v_unused_7297_; lean_object* v_unused_7298_; lean_object* v_unused_7299_; lean_object* v_unused_7300_; lean_object* v_unused_7301_; 
v_unused_7297_ = lean_ctor_get(v_r_7078_, 4);
lean_dec(v_unused_7297_);
v_unused_7298_ = lean_ctor_get(v_r_7078_, 3);
lean_dec(v_unused_7298_);
v_unused_7299_ = lean_ctor_get(v_r_7078_, 2);
lean_dec(v_unused_7299_);
v_unused_7300_ = lean_ctor_get(v_r_7078_, 1);
lean_dec(v_unused_7300_);
v_unused_7301_ = lean_ctor_get(v_r_7078_, 0);
lean_dec(v_unused_7301_);
v___x_7291_ = v_r_7078_;
v_isShared_7292_ = v_isSharedCheck_7296_;
goto v_resetjp_7290_;
}
else
{
lean_dec(v_r_7078_);
v___x_7291_ = lean_box(0);
v_isShared_7292_ = v_isSharedCheck_7296_;
goto v_resetjp_7290_;
}
v_resetjp_7290_:
{
lean_object* v___x_7294_; 
if (v_isShared_7292_ == 0)
{
lean_ctor_set(v___x_7291_, 4, v___x_7289_);
lean_ctor_set(v___x_7291_, 3, v_l_7228_);
lean_ctor_set(v___x_7291_, 2, v_v_7227_);
lean_ctor_set(v___x_7291_, 1, v_k_7226_);
lean_ctor_set(v___x_7291_, 0, v___x_7285_);
v___x_7294_ = v___x_7291_;
goto v_reusejp_7293_;
}
else
{
lean_object* v_reuseFailAlloc_7295_; 
v_reuseFailAlloc_7295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7295_, 0, v___x_7285_);
lean_ctor_set(v_reuseFailAlloc_7295_, 1, v_k_7226_);
lean_ctor_set(v_reuseFailAlloc_7295_, 2, v_v_7227_);
lean_ctor_set(v_reuseFailAlloc_7295_, 3, v_l_7228_);
lean_ctor_set(v_reuseFailAlloc_7295_, 4, v___x_7289_);
v___x_7294_ = v_reuseFailAlloc_7295_;
goto v_reusejp_7293_;
}
v_reusejp_7293_:
{
return v___x_7294_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_7309_; 
v_l_7309_ = lean_ctor_get(v_impl_7222_, 3);
lean_inc(v_l_7309_);
if (lean_obj_tag(v_l_7309_) == 0)
{
lean_object* v_r_7310_; lean_object* v_k_7311_; lean_object* v_v_7312_; lean_object* v___x_7314_; uint8_t v_isShared_7315_; uint8_t v_isSharedCheck_7323_; 
v_r_7310_ = lean_ctor_get(v_impl_7222_, 4);
v_k_7311_ = lean_ctor_get(v_impl_7222_, 1);
v_v_7312_ = lean_ctor_get(v_impl_7222_, 2);
v_isSharedCheck_7323_ = !lean_is_exclusive(v_impl_7222_);
if (v_isSharedCheck_7323_ == 0)
{
lean_object* v_unused_7324_; lean_object* v_unused_7325_; 
v_unused_7324_ = lean_ctor_get(v_impl_7222_, 3);
lean_dec(v_unused_7324_);
v_unused_7325_ = lean_ctor_get(v_impl_7222_, 0);
lean_dec(v_unused_7325_);
v___x_7314_ = v_impl_7222_;
v_isShared_7315_ = v_isSharedCheck_7323_;
goto v_resetjp_7313_;
}
else
{
lean_inc(v_r_7310_);
lean_inc(v_v_7312_);
lean_inc(v_k_7311_);
lean_dec(v_impl_7222_);
v___x_7314_ = lean_box(0);
v_isShared_7315_ = v_isSharedCheck_7323_;
goto v_resetjp_7313_;
}
v_resetjp_7313_:
{
lean_object* v___x_7316_; lean_object* v___x_7318_; 
v___x_7316_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_7310_);
if (v_isShared_7315_ == 0)
{
lean_ctor_set(v___x_7314_, 3, v_r_7310_);
lean_ctor_set(v___x_7314_, 2, v_v_7076_);
lean_ctor_set(v___x_7314_, 1, v_k_7075_);
lean_ctor_set(v___x_7314_, 0, v___x_7223_);
v___x_7318_ = v___x_7314_;
goto v_reusejp_7317_;
}
else
{
lean_object* v_reuseFailAlloc_7322_; 
v_reuseFailAlloc_7322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7322_, 0, v___x_7223_);
lean_ctor_set(v_reuseFailAlloc_7322_, 1, v_k_7075_);
lean_ctor_set(v_reuseFailAlloc_7322_, 2, v_v_7076_);
lean_ctor_set(v_reuseFailAlloc_7322_, 3, v_r_7310_);
lean_ctor_set(v_reuseFailAlloc_7322_, 4, v_r_7310_);
v___x_7318_ = v_reuseFailAlloc_7322_;
goto v_reusejp_7317_;
}
v_reusejp_7317_:
{
lean_object* v___x_7320_; 
if (v_isShared_7081_ == 0)
{
lean_ctor_set(v___x_7080_, 4, v___x_7318_);
lean_ctor_set(v___x_7080_, 3, v_l_7309_);
lean_ctor_set(v___x_7080_, 2, v_v_7312_);
lean_ctor_set(v___x_7080_, 1, v_k_7311_);
lean_ctor_set(v___x_7080_, 0, v___x_7316_);
v___x_7320_ = v___x_7080_;
goto v_reusejp_7319_;
}
else
{
lean_object* v_reuseFailAlloc_7321_; 
v_reuseFailAlloc_7321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7321_, 0, v___x_7316_);
lean_ctor_set(v_reuseFailAlloc_7321_, 1, v_k_7311_);
lean_ctor_set(v_reuseFailAlloc_7321_, 2, v_v_7312_);
lean_ctor_set(v_reuseFailAlloc_7321_, 3, v_l_7309_);
lean_ctor_set(v_reuseFailAlloc_7321_, 4, v___x_7318_);
v___x_7320_ = v_reuseFailAlloc_7321_;
goto v_reusejp_7319_;
}
v_reusejp_7319_:
{
return v___x_7320_;
}
}
}
}
else
{
lean_object* v_r_7326_; 
v_r_7326_ = lean_ctor_get(v_impl_7222_, 4);
lean_inc(v_r_7326_);
if (lean_obj_tag(v_r_7326_) == 0)
{
lean_object* v_k_7327_; lean_object* v_v_7328_; lean_object* v___x_7330_; uint8_t v_isShared_7331_; uint8_t v_isSharedCheck_7351_; 
v_k_7327_ = lean_ctor_get(v_impl_7222_, 1);
v_v_7328_ = lean_ctor_get(v_impl_7222_, 2);
v_isSharedCheck_7351_ = !lean_is_exclusive(v_impl_7222_);
if (v_isSharedCheck_7351_ == 0)
{
lean_object* v_unused_7352_; lean_object* v_unused_7353_; lean_object* v_unused_7354_; 
v_unused_7352_ = lean_ctor_get(v_impl_7222_, 4);
lean_dec(v_unused_7352_);
v_unused_7353_ = lean_ctor_get(v_impl_7222_, 3);
lean_dec(v_unused_7353_);
v_unused_7354_ = lean_ctor_get(v_impl_7222_, 0);
lean_dec(v_unused_7354_);
v___x_7330_ = v_impl_7222_;
v_isShared_7331_ = v_isSharedCheck_7351_;
goto v_resetjp_7329_;
}
else
{
lean_inc(v_v_7328_);
lean_inc(v_k_7327_);
lean_dec(v_impl_7222_);
v___x_7330_ = lean_box(0);
v_isShared_7331_ = v_isSharedCheck_7351_;
goto v_resetjp_7329_;
}
v_resetjp_7329_:
{
lean_object* v_k_7332_; lean_object* v_v_7333_; lean_object* v___x_7335_; uint8_t v_isShared_7336_; uint8_t v_isSharedCheck_7347_; 
v_k_7332_ = lean_ctor_get(v_r_7326_, 1);
v_v_7333_ = lean_ctor_get(v_r_7326_, 2);
v_isSharedCheck_7347_ = !lean_is_exclusive(v_r_7326_);
if (v_isSharedCheck_7347_ == 0)
{
lean_object* v_unused_7348_; lean_object* v_unused_7349_; lean_object* v_unused_7350_; 
v_unused_7348_ = lean_ctor_get(v_r_7326_, 4);
lean_dec(v_unused_7348_);
v_unused_7349_ = lean_ctor_get(v_r_7326_, 3);
lean_dec(v_unused_7349_);
v_unused_7350_ = lean_ctor_get(v_r_7326_, 0);
lean_dec(v_unused_7350_);
v___x_7335_ = v_r_7326_;
v_isShared_7336_ = v_isSharedCheck_7347_;
goto v_resetjp_7334_;
}
else
{
lean_inc(v_v_7333_);
lean_inc(v_k_7332_);
lean_dec(v_r_7326_);
v___x_7335_ = lean_box(0);
v_isShared_7336_ = v_isSharedCheck_7347_;
goto v_resetjp_7334_;
}
v_resetjp_7334_:
{
lean_object* v___x_7337_; lean_object* v___x_7339_; 
v___x_7337_ = lean_unsigned_to_nat(3u);
if (v_isShared_7336_ == 0)
{
lean_ctor_set(v___x_7335_, 4, v_l_7309_);
lean_ctor_set(v___x_7335_, 3, v_l_7309_);
lean_ctor_set(v___x_7335_, 2, v_v_7328_);
lean_ctor_set(v___x_7335_, 1, v_k_7327_);
lean_ctor_set(v___x_7335_, 0, v___x_7223_);
v___x_7339_ = v___x_7335_;
goto v_reusejp_7338_;
}
else
{
lean_object* v_reuseFailAlloc_7346_; 
v_reuseFailAlloc_7346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7346_, 0, v___x_7223_);
lean_ctor_set(v_reuseFailAlloc_7346_, 1, v_k_7327_);
lean_ctor_set(v_reuseFailAlloc_7346_, 2, v_v_7328_);
lean_ctor_set(v_reuseFailAlloc_7346_, 3, v_l_7309_);
lean_ctor_set(v_reuseFailAlloc_7346_, 4, v_l_7309_);
v___x_7339_ = v_reuseFailAlloc_7346_;
goto v_reusejp_7338_;
}
v_reusejp_7338_:
{
lean_object* v___x_7341_; 
if (v_isShared_7331_ == 0)
{
lean_ctor_set(v___x_7330_, 4, v_l_7309_);
lean_ctor_set(v___x_7330_, 2, v_v_7076_);
lean_ctor_set(v___x_7330_, 1, v_k_7075_);
lean_ctor_set(v___x_7330_, 0, v___x_7223_);
v___x_7341_ = v___x_7330_;
goto v_reusejp_7340_;
}
else
{
lean_object* v_reuseFailAlloc_7345_; 
v_reuseFailAlloc_7345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7345_, 0, v___x_7223_);
lean_ctor_set(v_reuseFailAlloc_7345_, 1, v_k_7075_);
lean_ctor_set(v_reuseFailAlloc_7345_, 2, v_v_7076_);
lean_ctor_set(v_reuseFailAlloc_7345_, 3, v_l_7309_);
lean_ctor_set(v_reuseFailAlloc_7345_, 4, v_l_7309_);
v___x_7341_ = v_reuseFailAlloc_7345_;
goto v_reusejp_7340_;
}
v_reusejp_7340_:
{
lean_object* v___x_7343_; 
if (v_isShared_7081_ == 0)
{
lean_ctor_set(v___x_7080_, 4, v___x_7341_);
lean_ctor_set(v___x_7080_, 3, v___x_7339_);
lean_ctor_set(v___x_7080_, 2, v_v_7333_);
lean_ctor_set(v___x_7080_, 1, v_k_7332_);
lean_ctor_set(v___x_7080_, 0, v___x_7337_);
v___x_7343_ = v___x_7080_;
goto v_reusejp_7342_;
}
else
{
lean_object* v_reuseFailAlloc_7344_; 
v_reuseFailAlloc_7344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7344_, 0, v___x_7337_);
lean_ctor_set(v_reuseFailAlloc_7344_, 1, v_k_7332_);
lean_ctor_set(v_reuseFailAlloc_7344_, 2, v_v_7333_);
lean_ctor_set(v_reuseFailAlloc_7344_, 3, v___x_7339_);
lean_ctor_set(v_reuseFailAlloc_7344_, 4, v___x_7341_);
v___x_7343_ = v_reuseFailAlloc_7344_;
goto v_reusejp_7342_;
}
v_reusejp_7342_:
{
return v___x_7343_;
}
}
}
}
}
}
else
{
lean_object* v___x_7355_; lean_object* v___x_7357_; 
v___x_7355_ = lean_unsigned_to_nat(2u);
if (v_isShared_7081_ == 0)
{
lean_ctor_set(v___x_7080_, 4, v_r_7326_);
lean_ctor_set(v___x_7080_, 3, v_impl_7222_);
lean_ctor_set(v___x_7080_, 0, v___x_7355_);
v___x_7357_ = v___x_7080_;
goto v_reusejp_7356_;
}
else
{
lean_object* v_reuseFailAlloc_7358_; 
v_reuseFailAlloc_7358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7358_, 0, v___x_7355_);
lean_ctor_set(v_reuseFailAlloc_7358_, 1, v_k_7075_);
lean_ctor_set(v_reuseFailAlloc_7358_, 2, v_v_7076_);
lean_ctor_set(v_reuseFailAlloc_7358_, 3, v_impl_7222_);
lean_ctor_set(v_reuseFailAlloc_7358_, 4, v_r_7326_);
v___x_7357_ = v_reuseFailAlloc_7358_;
goto v_reusejp_7356_;
}
v_reusejp_7356_:
{
return v___x_7357_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_7360_; lean_object* v___x_7361_; 
v___x_7360_ = lean_unsigned_to_nat(1u);
v___x_7361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_7361_, 0, v___x_7360_);
lean_ctor_set(v___x_7361_, 1, v_k_7071_);
lean_ctor_set(v___x_7361_, 2, v_v_7072_);
lean_ctor_set(v___x_7361_, 3, v_t_7073_);
lean_ctor_set(v___x_7361_, 4, v_t_7073_);
return v___x_7361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(lean_object* v_lib_7362_, lean_object* v_ps_7363_, lean_object* v_v_7364_, lean_object* v_o_7365_){
_start:
{
lean_object* v_name_7366_; lean_object* v_deps_7367_; lean_object* v_o_7368_; uint8_t v___x_7369_; 
v_name_7366_ = lean_ctor_get(v_lib_7362_, 1);
lean_inc_ref(v_name_7366_);
v_deps_7367_ = lean_ctor_get(v_lib_7362_, 2);
lean_inc_ref(v_deps_7367_);
v_o_7368_ = lean_array_push(v_o_7365_, v_lib_7362_);
v___x_7369_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_name_7366_, v_v_7364_);
if (v___x_7369_ == 0)
{
uint8_t v___x_7370_; 
v___x_7370_ = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(v_name_7366_, v_ps_7363_);
if (v___x_7370_ == 0)
{
lean_object* v_ps_7371_; lean_object* v___y_7373_; 
lean_inc_ref(v_name_7366_);
v_ps_7371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_ps_7371_, 0, v_name_7366_);
lean_ctor_set(v_ps_7371_, 1, v_ps_7363_);
if (v___x_7369_ == 0)
{
lean_object* v___x_7387_; lean_object* v___x_7388_; 
v___x_7387_ = lean_box(0);
v___x_7388_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_name_7366_, v___x_7387_, v_v_7364_);
v___y_7373_ = v___x_7388_;
goto v___jp_7372_;
}
else
{
lean_dec_ref(v_name_7366_);
v___y_7373_ = v_v_7364_;
goto v___jp_7372_;
}
v___jp_7372_:
{
lean_object* v___x_7374_; lean_object* v___x_7375_; lean_object* v___x_7376_; uint8_t v___x_7377_; 
v___x_7374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7374_, 0, v___y_7373_);
lean_ctor_set(v___x_7374_, 1, v_o_7368_);
v___x_7375_ = lean_unsigned_to_nat(0u);
v___x_7376_ = lean_array_get_size(v_deps_7367_);
v___x_7377_ = lean_nat_dec_lt(v___x_7375_, v___x_7376_);
if (v___x_7377_ == 0)
{
lean_object* v___x_7378_; 
lean_dec_ref(v_ps_7371_);
lean_dec_ref(v_deps_7367_);
v___x_7378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7378_, 0, v___x_7374_);
return v___x_7378_;
}
else
{
uint8_t v___x_7379_; 
v___x_7379_ = lean_nat_dec_le(v___x_7376_, v___x_7376_);
if (v___x_7379_ == 0)
{
if (v___x_7377_ == 0)
{
lean_object* v___x_7380_; 
lean_dec_ref(v_ps_7371_);
lean_dec_ref(v_deps_7367_);
v___x_7380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7380_, 0, v___x_7374_);
return v___x_7380_;
}
else
{
size_t v___x_7381_; size_t v___x_7382_; lean_object* v___x_7383_; 
v___x_7381_ = ((size_t)0ULL);
v___x_7382_ = lean_usize_of_nat(v___x_7376_);
v___x_7383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7371_, v_deps_7367_, v___x_7381_, v___x_7382_, v___x_7374_);
lean_dec_ref(v_deps_7367_);
return v___x_7383_;
}
}
else
{
size_t v___x_7384_; size_t v___x_7385_; lean_object* v___x_7386_; 
v___x_7384_ = ((size_t)0ULL);
v___x_7385_ = lean_usize_of_nat(v___x_7376_);
v___x_7386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7371_, v_deps_7367_, v___x_7384_, v___x_7385_, v___x_7374_);
lean_dec_ref(v_deps_7367_);
return v___x_7386_;
}
}
}
}
else
{
lean_object* v___x_7389_; lean_object* v___x_7390_; 
lean_dec_ref(v_o_7368_);
lean_dec_ref(v_deps_7367_);
lean_dec(v_v_7364_);
v___x_7389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7389_, 0, v_name_7366_);
lean_ctor_set(v___x_7389_, 1, v_ps_7363_);
v___x_7390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7390_, 0, v___x_7389_);
return v___x_7390_;
}
}
else
{
lean_object* v___x_7391_; lean_object* v___x_7392_; 
lean_dec_ref(v_deps_7367_);
lean_dec_ref(v_name_7366_);
lean_dec(v_ps_7363_);
v___x_7391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7391_, 0, v_v_7364_);
lean_ctor_set(v___x_7391_, 1, v_o_7368_);
v___x_7392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7392_, 0, v___x_7391_);
return v___x_7392_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(lean_object* v_ps_7393_, lean_object* v_as_7394_, size_t v_i_7395_, size_t v_stop_7396_, lean_object* v_b_7397_){
_start:
{
uint8_t v___x_7398_; 
v___x_7398_ = lean_usize_dec_eq(v_i_7395_, v_stop_7396_);
if (v___x_7398_ == 0)
{
lean_object* v_fst_7399_; lean_object* v_snd_7400_; lean_object* v___x_7401_; lean_object* v___x_7402_; 
v_fst_7399_ = lean_ctor_get(v_b_7397_, 0);
lean_inc(v_fst_7399_);
v_snd_7400_ = lean_ctor_get(v_b_7397_, 1);
lean_inc(v_snd_7400_);
lean_dec_ref(v_b_7397_);
v___x_7401_ = lean_array_uget_borrowed(v_as_7394_, v_i_7395_);
lean_inc(v_ps_7393_);
lean_inc(v___x_7401_);
v___x_7402_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(v___x_7401_, v_ps_7393_, v_fst_7399_, v_snd_7400_);
if (lean_obj_tag(v___x_7402_) == 0)
{
lean_dec(v_ps_7393_);
return v___x_7402_;
}
else
{
lean_object* v_a_7403_; size_t v___x_7404_; size_t v___x_7405_; 
v_a_7403_ = lean_ctor_get(v___x_7402_, 0);
lean_inc(v_a_7403_);
lean_dec_ref(v___x_7402_);
v___x_7404_ = ((size_t)1ULL);
v___x_7405_ = lean_usize_add(v_i_7395_, v___x_7404_);
v_i_7395_ = v___x_7405_;
v_b_7397_ = v_a_7403_;
goto _start;
}
}
else
{
lean_object* v___x_7407_; 
lean_dec(v_ps_7393_);
v___x_7407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7407_, 0, v_b_7397_);
return v___x_7407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2___boxed(lean_object* v_ps_7408_, lean_object* v_as_7409_, lean_object* v_i_7410_, lean_object* v_stop_7411_, lean_object* v_b_7412_){
_start:
{
size_t v_i_boxed_7413_; size_t v_stop_boxed_7414_; lean_object* v_res_7415_; 
v_i_boxed_7413_ = lean_unbox_usize(v_i_7410_);
lean_dec(v_i_7410_);
v_stop_boxed_7414_ = lean_unbox_usize(v_stop_7411_);
lean_dec(v_stop_7411_);
v_res_7415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7408_, v_as_7409_, v_i_boxed_7413_, v_stop_boxed_7414_, v_b_7412_);
lean_dec_ref(v_as_7409_);
return v_res_7415_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(lean_object* v_00_u03b2_7416_, lean_object* v_k_7417_, lean_object* v_t_7418_){
_start:
{
uint8_t v___x_7419_; 
v___x_7419_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_k_7417_, v_t_7418_);
return v___x_7419_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___boxed(lean_object* v_00_u03b2_7420_, lean_object* v_k_7421_, lean_object* v_t_7422_){
_start:
{
uint8_t v_res_7423_; lean_object* v_r_7424_; 
v_res_7423_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(v_00_u03b2_7420_, v_k_7421_, v_t_7422_);
lean_dec(v_t_7422_);
lean_dec_ref(v_k_7421_);
v_r_7424_ = lean_box(v_res_7423_);
return v_r_7424_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3(lean_object* v_00_u03b2_7425_, lean_object* v_k_7426_, lean_object* v_v_7427_, lean_object* v_t_7428_, lean_object* v_hl_7429_){
_start:
{
lean_object* v___x_7430_; 
v___x_7430_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7426_, v_v_7427_, v_t_7428_);
return v___x_7430_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0(lean_object* v_a_7432_, lean_object* v_a_7433_){
_start:
{
if (lean_obj_tag(v_a_7432_) == 0)
{
lean_object* v___x_7434_; 
v___x_7434_ = l_List_reverse___redArg(v_a_7433_);
return v___x_7434_;
}
else
{
lean_object* v_head_7435_; lean_object* v_tail_7436_; lean_object* v___x_7438_; uint8_t v_isShared_7439_; uint8_t v_isSharedCheck_7446_; 
v_head_7435_ = lean_ctor_get(v_a_7432_, 0);
v_tail_7436_ = lean_ctor_get(v_a_7432_, 1);
v_isSharedCheck_7446_ = !lean_is_exclusive(v_a_7432_);
if (v_isSharedCheck_7446_ == 0)
{
v___x_7438_ = v_a_7432_;
v_isShared_7439_ = v_isSharedCheck_7446_;
goto v_resetjp_7437_;
}
else
{
lean_inc(v_tail_7436_);
lean_inc(v_head_7435_);
lean_dec(v_a_7432_);
v___x_7438_ = lean_box(0);
v_isShared_7439_ = v_isSharedCheck_7446_;
goto v_resetjp_7437_;
}
v_resetjp_7437_:
{
lean_object* v___x_7440_; lean_object* v___x_7441_; lean_object* v___x_7443_; 
v___x_7440_ = ((lean_object*)(l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0));
v___x_7441_ = lean_string_append(v___x_7440_, v_head_7435_);
lean_dec(v_head_7435_);
if (v_isShared_7439_ == 0)
{
lean_ctor_set(v___x_7438_, 1, v_a_7433_);
lean_ctor_set(v___x_7438_, 0, v___x_7441_);
v___x_7443_ = v___x_7438_;
goto v_reusejp_7442_;
}
else
{
lean_object* v_reuseFailAlloc_7445_; 
v_reuseFailAlloc_7445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7445_, 0, v___x_7441_);
lean_ctor_set(v_reuseFailAlloc_7445_, 1, v_a_7433_);
v___x_7443_ = v_reuseFailAlloc_7445_;
goto v_reusejp_7442_;
}
v_reusejp_7442_:
{
v_a_7432_ = v_tail_7436_;
v_a_7433_ = v___x_7443_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(lean_object* v_cycle_7447_){
_start:
{
lean_object* v___x_7448_; lean_object* v___x_7449_; lean_object* v___x_7450_; lean_object* v___x_7451_; 
v___x_7448_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__1));
v___x_7449_ = lean_box(0);
v___x_7450_ = l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0(v_cycle_7447_, v___x_7449_);
v___x_7451_ = l_String_intercalate(v___x_7448_, v___x_7450_);
return v___x_7451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(lean_object* v_as_7452_, size_t v_i_7453_, size_t v_stop_7454_, lean_object* v_b_7455_){
_start:
{
uint8_t v___x_7456_; 
v___x_7456_ = lean_usize_dec_eq(v_i_7453_, v_stop_7454_);
if (v___x_7456_ == 0)
{
lean_object* v_fst_7457_; lean_object* v_snd_7458_; lean_object* v___x_7459_; lean_object* v___x_7460_; lean_object* v___x_7461_; 
v_fst_7457_ = lean_ctor_get(v_b_7455_, 0);
lean_inc(v_fst_7457_);
v_snd_7458_ = lean_ctor_get(v_b_7455_, 1);
lean_inc(v_snd_7458_);
lean_dec_ref(v_b_7455_);
v___x_7459_ = lean_array_uget_borrowed(v_as_7452_, v_i_7453_);
v___x_7460_ = lean_box(0);
lean_inc(v___x_7459_);
v___x_7461_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(v___x_7459_, v___x_7460_, v_fst_7457_, v_snd_7458_);
if (lean_obj_tag(v___x_7461_) == 0)
{
return v___x_7461_;
}
else
{
lean_object* v_a_7462_; size_t v___x_7463_; size_t v___x_7464_; 
v_a_7462_ = lean_ctor_get(v___x_7461_, 0);
lean_inc(v_a_7462_);
lean_dec_ref(v___x_7461_);
v___x_7463_ = ((size_t)1ULL);
v___x_7464_ = lean_usize_add(v_i_7453_, v___x_7463_);
v_i_7453_ = v___x_7464_;
v_b_7455_ = v_a_7462_;
goto _start;
}
}
else
{
lean_object* v___x_7466_; 
v___x_7466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7466_, 0, v_b_7455_);
return v___x_7466_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1___boxed(lean_object* v_as_7467_, lean_object* v_i_7468_, lean_object* v_stop_7469_, lean_object* v_b_7470_){
_start:
{
size_t v_i_boxed_7471_; size_t v_stop_boxed_7472_; lean_object* v_res_7473_; 
v_i_boxed_7471_ = lean_unbox_usize(v_i_7468_);
lean_dec(v_i_7468_);
v_stop_boxed_7472_ = lean_unbox_usize(v_stop_7469_);
lean_dec(v_stop_7469_);
v_res_7473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(v_as_7467_, v_i_boxed_7471_, v_stop_boxed_7472_, v_b_7470_);
lean_dec_ref(v_as_7467_);
return v_res_7473_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(lean_object* v_libs_7480_, lean_object* v_a_7481_){
_start:
{
lean_object* v_snd_7484_; lean_object* v___y_7487_; lean_object* v___x_7511_; lean_object* v___x_7512_; lean_object* v___x_7513_; uint8_t v___x_7514_; 
v___x_7511_ = lean_unsigned_to_nat(0u);
v___x_7512_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1));
v___x_7513_ = lean_array_get_size(v_libs_7480_);
v___x_7514_ = lean_nat_dec_lt(v___x_7511_, v___x_7513_);
if (v___x_7514_ == 0)
{
v_snd_7484_ = v___x_7512_;
goto v___jp_7483_;
}
else
{
lean_object* v___x_7515_; uint8_t v___x_7516_; 
v___x_7515_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2));
v___x_7516_ = lean_nat_dec_le(v___x_7513_, v___x_7513_);
if (v___x_7516_ == 0)
{
if (v___x_7514_ == 0)
{
v_snd_7484_ = v___x_7512_;
goto v___jp_7483_;
}
else
{
size_t v___x_7517_; size_t v___x_7518_; lean_object* v___x_7519_; 
v___x_7517_ = ((size_t)0ULL);
v___x_7518_ = lean_usize_of_nat(v___x_7513_);
v___x_7519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(v_libs_7480_, v___x_7517_, v___x_7518_, v___x_7515_);
v___y_7487_ = v___x_7519_;
goto v___jp_7486_;
}
}
else
{
size_t v___x_7520_; size_t v___x_7521_; lean_object* v___x_7522_; 
v___x_7520_ = ((size_t)0ULL);
v___x_7521_ = lean_usize_of_nat(v___x_7513_);
v___x_7522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(v_libs_7480_, v___x_7520_, v___x_7521_, v___x_7515_);
v___y_7487_ = v___x_7522_;
goto v___jp_7486_;
}
}
v___jp_7483_:
{
lean_object* v___x_7485_; 
v___x_7485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7485_, 0, v_snd_7484_);
lean_ctor_set(v___x_7485_, 1, v_a_7481_);
return v___x_7485_;
}
v___jp_7486_:
{
if (lean_obj_tag(v___y_7487_) == 0)
{
lean_object* v_a_7488_; lean_object* v_log_7489_; uint8_t v_action_7490_; uint8_t v_wantsRebuild_7491_; lean_object* v_trace_7492_; lean_object* v_buildTime_7493_; lean_object* v___x_7495_; uint8_t v_isShared_7496_; uint8_t v_isSharedCheck_7508_; 
v_a_7488_ = lean_ctor_get(v___y_7487_, 0);
lean_inc(v_a_7488_);
lean_dec_ref(v___y_7487_);
v_log_7489_ = lean_ctor_get(v_a_7481_, 0);
v_action_7490_ = lean_ctor_get_uint8(v_a_7481_, sizeof(void*)*3);
v_wantsRebuild_7491_ = lean_ctor_get_uint8(v_a_7481_, sizeof(void*)*3 + 1);
v_trace_7492_ = lean_ctor_get(v_a_7481_, 1);
v_buildTime_7493_ = lean_ctor_get(v_a_7481_, 2);
v_isSharedCheck_7508_ = !lean_is_exclusive(v_a_7481_);
if (v_isSharedCheck_7508_ == 0)
{
v___x_7495_ = v_a_7481_;
v_isShared_7496_ = v_isSharedCheck_7508_;
goto v_resetjp_7494_;
}
else
{
lean_inc(v_buildTime_7493_);
lean_inc(v_trace_7492_);
lean_inc(v_log_7489_);
lean_dec(v_a_7481_);
v___x_7495_ = lean_box(0);
v_isShared_7496_ = v_isSharedCheck_7508_;
goto v_resetjp_7494_;
}
v_resetjp_7494_:
{
lean_object* v___x_7497_; lean_object* v___x_7498_; lean_object* v___x_7499_; uint8_t v___x_7500_; lean_object* v___x_7501_; lean_object* v___x_7502_; lean_object* v___x_7503_; lean_object* v___x_7505_; 
v___x_7497_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0));
v___x_7498_ = l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(v_a_7488_);
v___x_7499_ = lean_string_append(v___x_7497_, v___x_7498_);
lean_dec_ref(v___x_7498_);
v___x_7500_ = 3;
v___x_7501_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7501_, 0, v___x_7499_);
lean_ctor_set_uint8(v___x_7501_, sizeof(void*)*1, v___x_7500_);
v___x_7502_ = lean_array_get_size(v_log_7489_);
v___x_7503_ = lean_array_push(v_log_7489_, v___x_7501_);
if (v_isShared_7496_ == 0)
{
lean_ctor_set(v___x_7495_, 0, v___x_7503_);
v___x_7505_ = v___x_7495_;
goto v_reusejp_7504_;
}
else
{
lean_object* v_reuseFailAlloc_7507_; 
v_reuseFailAlloc_7507_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7507_, 0, v___x_7503_);
lean_ctor_set(v_reuseFailAlloc_7507_, 1, v_trace_7492_);
lean_ctor_set(v_reuseFailAlloc_7507_, 2, v_buildTime_7493_);
lean_ctor_set_uint8(v_reuseFailAlloc_7507_, sizeof(void*)*3, v_action_7490_);
lean_ctor_set_uint8(v_reuseFailAlloc_7507_, sizeof(void*)*3 + 1, v_wantsRebuild_7491_);
v___x_7505_ = v_reuseFailAlloc_7507_;
goto v_reusejp_7504_;
}
v_reusejp_7504_:
{
lean_object* v___x_7506_; 
v___x_7506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7506_, 0, v___x_7502_);
lean_ctor_set(v___x_7506_, 1, v___x_7505_);
return v___x_7506_;
}
}
}
else
{
lean_object* v_a_7509_; lean_object* v_snd_7510_; 
v_a_7509_ = lean_ctor_get(v___y_7487_, 0);
lean_inc(v_a_7509_);
lean_dec_ref(v___y_7487_);
v_snd_7510_ = lean_ctor_get(v_a_7509_, 1);
lean_inc(v_snd_7510_);
lean_dec(v_a_7509_);
v_snd_7484_ = v_snd_7510_;
goto v___jp_7483_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___boxed(lean_object* v_libs_7523_, lean_object* v_a_7524_, lean_object* v_a_7525_){
_start:
{
lean_object* v_res_7526_; 
v_res_7526_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7523_, v_a_7524_);
lean_dec_ref(v_libs_7523_);
return v_res_7526_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder(lean_object* v_libs_7527_, lean_object* v_a_7528_, lean_object* v_a_7529_, lean_object* v_a_7530_, lean_object* v_a_7531_, lean_object* v_a_7532_, lean_object* v_a_7533_){
_start:
{
lean_object* v___x_7535_; 
v___x_7535_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7527_, v_a_7533_);
return v___x_7535_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___boxed(lean_object* v_libs_7536_, lean_object* v_a_7537_, lean_object* v_a_7538_, lean_object* v_a_7539_, lean_object* v_a_7540_, lean_object* v_a_7541_, lean_object* v_a_7542_, lean_object* v_a_7543_){
_start:
{
lean_object* v_res_7544_; 
v_res_7544_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder(v_libs_7536_, v_a_7537_, v_a_7538_, v_a_7539_, v_a_7540_, v_a_7541_, v_a_7542_);
lean_dec_ref(v_a_7541_);
lean_dec(v_a_7540_);
lean_dec(v_a_7539_);
lean_dec(v_a_7538_);
lean_dec_ref(v_a_7537_);
lean_dec_ref(v_libs_7536_);
return v_res_7544_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0(lean_object* v_objs_7545_, lean_object* v_weakArgs_7546_, lean_object* v_traceArgs_7547_, lean_object* v_libFile_7548_, lean_object* v_linker_7549_, lean_object* v_libs_7550_, lean_object* v___y_7551_, lean_object* v___y_7552_, lean_object* v___y_7553_, lean_object* v___y_7554_, lean_object* v___y_7555_, lean_object* v___y_7556_){
_start:
{
lean_object* v_log_7558_; uint8_t v_action_7559_; uint8_t v_wantsRebuild_7560_; lean_object* v_trace_7561_; lean_object* v_buildTime_7562_; lean_object* v___x_7564_; uint8_t v_isShared_7565_; uint8_t v_isSharedCheck_7594_; 
v_log_7558_ = lean_ctor_get(v___y_7556_, 0);
v_action_7559_ = lean_ctor_get_uint8(v___y_7556_, sizeof(void*)*3);
v_wantsRebuild_7560_ = lean_ctor_get_uint8(v___y_7556_, sizeof(void*)*3 + 1);
v_trace_7561_ = lean_ctor_get(v___y_7556_, 1);
v_buildTime_7562_ = lean_ctor_get(v___y_7556_, 2);
v_isSharedCheck_7594_ = !lean_is_exclusive(v___y_7556_);
if (v_isSharedCheck_7594_ == 0)
{
v___x_7564_ = v___y_7556_;
v_isShared_7565_ = v_isSharedCheck_7594_;
goto v_resetjp_7563_;
}
else
{
lean_inc(v_buildTime_7562_);
lean_inc(v_trace_7561_);
lean_inc(v_log_7558_);
lean_dec(v___y_7556_);
v___x_7564_ = lean_box(0);
v_isShared_7565_ = v_isSharedCheck_7594_;
goto v_resetjp_7563_;
}
v_resetjp_7563_:
{
lean_object* v___x_7566_; lean_object* v___x_7567_; lean_object* v___x_7568_; lean_object* v___x_7569_; 
v___x_7566_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7545_, v_libs_7550_);
v___x_7567_ = l_Array_append___redArg(v___x_7566_, v_weakArgs_7546_);
v___x_7568_ = l_Array_append___redArg(v___x_7567_, v_traceArgs_7547_);
v___x_7569_ = l_Lake_compileSharedLib(v_libFile_7548_, v___x_7568_, v_linker_7549_, v_log_7558_);
lean_dec_ref(v___x_7568_);
if (lean_obj_tag(v___x_7569_) == 0)
{
lean_object* v_a_7570_; lean_object* v_a_7571_; lean_object* v___x_7573_; uint8_t v_isShared_7574_; uint8_t v_isSharedCheck_7581_; 
v_a_7570_ = lean_ctor_get(v___x_7569_, 0);
v_a_7571_ = lean_ctor_get(v___x_7569_, 1);
v_isSharedCheck_7581_ = !lean_is_exclusive(v___x_7569_);
if (v_isSharedCheck_7581_ == 0)
{
v___x_7573_ = v___x_7569_;
v_isShared_7574_ = v_isSharedCheck_7581_;
goto v_resetjp_7572_;
}
else
{
lean_inc(v_a_7571_);
lean_inc(v_a_7570_);
lean_dec(v___x_7569_);
v___x_7573_ = lean_box(0);
v_isShared_7574_ = v_isSharedCheck_7581_;
goto v_resetjp_7572_;
}
v_resetjp_7572_:
{
lean_object* v___x_7576_; 
if (v_isShared_7565_ == 0)
{
lean_ctor_set(v___x_7564_, 0, v_a_7571_);
v___x_7576_ = v___x_7564_;
goto v_reusejp_7575_;
}
else
{
lean_object* v_reuseFailAlloc_7580_; 
v_reuseFailAlloc_7580_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7580_, 0, v_a_7571_);
lean_ctor_set(v_reuseFailAlloc_7580_, 1, v_trace_7561_);
lean_ctor_set(v_reuseFailAlloc_7580_, 2, v_buildTime_7562_);
lean_ctor_set_uint8(v_reuseFailAlloc_7580_, sizeof(void*)*3, v_action_7559_);
lean_ctor_set_uint8(v_reuseFailAlloc_7580_, sizeof(void*)*3 + 1, v_wantsRebuild_7560_);
v___x_7576_ = v_reuseFailAlloc_7580_;
goto v_reusejp_7575_;
}
v_reusejp_7575_:
{
lean_object* v___x_7578_; 
if (v_isShared_7574_ == 0)
{
lean_ctor_set(v___x_7573_, 1, v___x_7576_);
v___x_7578_ = v___x_7573_;
goto v_reusejp_7577_;
}
else
{
lean_object* v_reuseFailAlloc_7579_; 
v_reuseFailAlloc_7579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7579_, 0, v_a_7570_);
lean_ctor_set(v_reuseFailAlloc_7579_, 1, v___x_7576_);
v___x_7578_ = v_reuseFailAlloc_7579_;
goto v_reusejp_7577_;
}
v_reusejp_7577_:
{
return v___x_7578_;
}
}
}
}
else
{
lean_object* v_a_7582_; lean_object* v_a_7583_; lean_object* v___x_7585_; uint8_t v_isShared_7586_; uint8_t v_isSharedCheck_7593_; 
v_a_7582_ = lean_ctor_get(v___x_7569_, 0);
v_a_7583_ = lean_ctor_get(v___x_7569_, 1);
v_isSharedCheck_7593_ = !lean_is_exclusive(v___x_7569_);
if (v_isSharedCheck_7593_ == 0)
{
v___x_7585_ = v___x_7569_;
v_isShared_7586_ = v_isSharedCheck_7593_;
goto v_resetjp_7584_;
}
else
{
lean_inc(v_a_7583_);
lean_inc(v_a_7582_);
lean_dec(v___x_7569_);
v___x_7585_ = lean_box(0);
v_isShared_7586_ = v_isSharedCheck_7593_;
goto v_resetjp_7584_;
}
v_resetjp_7584_:
{
lean_object* v___x_7588_; 
if (v_isShared_7565_ == 0)
{
lean_ctor_set(v___x_7564_, 0, v_a_7583_);
v___x_7588_ = v___x_7564_;
goto v_reusejp_7587_;
}
else
{
lean_object* v_reuseFailAlloc_7592_; 
v_reuseFailAlloc_7592_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7592_, 0, v_a_7583_);
lean_ctor_set(v_reuseFailAlloc_7592_, 1, v_trace_7561_);
lean_ctor_set(v_reuseFailAlloc_7592_, 2, v_buildTime_7562_);
lean_ctor_set_uint8(v_reuseFailAlloc_7592_, sizeof(void*)*3, v_action_7559_);
lean_ctor_set_uint8(v_reuseFailAlloc_7592_, sizeof(void*)*3 + 1, v_wantsRebuild_7560_);
v___x_7588_ = v_reuseFailAlloc_7592_;
goto v_reusejp_7587_;
}
v_reusejp_7587_:
{
lean_object* v___x_7590_; 
if (v_isShared_7586_ == 0)
{
lean_ctor_set(v___x_7585_, 1, v___x_7588_);
v___x_7590_ = v___x_7585_;
goto v_reusejp_7589_;
}
else
{
lean_object* v_reuseFailAlloc_7591_; 
v_reuseFailAlloc_7591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7591_, 0, v_a_7582_);
lean_ctor_set(v_reuseFailAlloc_7591_, 1, v___x_7588_);
v___x_7590_ = v_reuseFailAlloc_7591_;
goto v_reusejp_7589_;
}
v_reusejp_7589_:
{
return v___x_7590_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object* v_objs_7595_, lean_object* v_weakArgs_7596_, lean_object* v_traceArgs_7597_, lean_object* v_libFile_7598_, lean_object* v_linker_7599_, lean_object* v_libs_7600_, lean_object* v___y_7601_, lean_object* v___y_7602_, lean_object* v___y_7603_, lean_object* v___y_7604_, lean_object* v___y_7605_, lean_object* v___y_7606_, lean_object* v___y_7607_){
_start:
{
lean_object* v_res_7608_; 
v_res_7608_ = l_Lake_buildSharedLib___lam__0(v_objs_7595_, v_weakArgs_7596_, v_traceArgs_7597_, v_libFile_7598_, v_linker_7599_, v_libs_7600_, v___y_7601_, v___y_7602_, v___y_7603_, v___y_7604_, v___y_7605_, v___y_7606_);
lean_dec_ref(v___y_7605_);
lean_dec(v___y_7604_);
lean_dec(v___y_7603_);
lean_dec(v___y_7602_);
lean_dec_ref(v___y_7601_);
lean_dec_ref(v_libs_7600_);
lean_dec_ref(v_traceArgs_7597_);
lean_dec_ref(v_weakArgs_7596_);
lean_dec_ref(v_objs_7595_);
return v_res_7608_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1(uint8_t v_linkDeps_7609_, lean_object* v___x_7610_, lean_object* v___f_7611_, lean_object* v_libs_7612_, lean_object* v___y_7613_, lean_object* v___y_7614_, lean_object* v___y_7615_, lean_object* v___y_7616_, lean_object* v___y_7617_, lean_object* v___y_7618_){
_start:
{
if (v_linkDeps_7609_ == 0)
{
lean_object* v___x_7620_; lean_object* v___x_7621_; 
v___x_7620_ = lean_mk_empty_array_with_capacity(v___x_7610_);
lean_inc_ref(v___y_7617_);
lean_inc(v___y_7616_);
lean_inc(v___y_7615_);
lean_inc(v___y_7614_);
v___x_7621_ = lean_apply_8(v___f_7611_, v___x_7620_, v___y_7613_, v___y_7614_, v___y_7615_, v___y_7616_, v___y_7617_, v___y_7618_, lean_box(0));
return v___x_7621_;
}
else
{
lean_object* v___x_7622_; 
v___x_7622_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7612_, v___y_7618_);
if (lean_obj_tag(v___x_7622_) == 0)
{
lean_object* v_a_7623_; lean_object* v_a_7624_; lean_object* v___x_7625_; 
v_a_7623_ = lean_ctor_get(v___x_7622_, 0);
lean_inc(v_a_7623_);
v_a_7624_ = lean_ctor_get(v___x_7622_, 1);
lean_inc(v_a_7624_);
lean_dec_ref(v___x_7622_);
lean_inc_ref(v___y_7617_);
lean_inc(v___y_7616_);
lean_inc(v___y_7615_);
lean_inc(v___y_7614_);
v___x_7625_ = lean_apply_8(v___f_7611_, v_a_7623_, v___y_7613_, v___y_7614_, v___y_7615_, v___y_7616_, v___y_7617_, v_a_7624_, lean_box(0));
return v___x_7625_;
}
else
{
lean_object* v_a_7626_; lean_object* v_a_7627_; lean_object* v___x_7629_; uint8_t v_isShared_7630_; uint8_t v_isSharedCheck_7634_; 
lean_dec_ref(v___y_7613_);
lean_dec_ref(v___f_7611_);
v_a_7626_ = lean_ctor_get(v___x_7622_, 0);
v_a_7627_ = lean_ctor_get(v___x_7622_, 1);
v_isSharedCheck_7634_ = !lean_is_exclusive(v___x_7622_);
if (v_isSharedCheck_7634_ == 0)
{
v___x_7629_ = v___x_7622_;
v_isShared_7630_ = v_isSharedCheck_7634_;
goto v_resetjp_7628_;
}
else
{
lean_inc(v_a_7627_);
lean_inc(v_a_7626_);
lean_dec(v___x_7622_);
v___x_7629_ = lean_box(0);
v_isShared_7630_ = v_isSharedCheck_7634_;
goto v_resetjp_7628_;
}
v_resetjp_7628_:
{
lean_object* v___x_7632_; 
if (v_isShared_7630_ == 0)
{
v___x_7632_ = v___x_7629_;
goto v_reusejp_7631_;
}
else
{
lean_object* v_reuseFailAlloc_7633_; 
v_reuseFailAlloc_7633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7633_, 0, v_a_7626_);
lean_ctor_set(v_reuseFailAlloc_7633_, 1, v_a_7627_);
v___x_7632_ = v_reuseFailAlloc_7633_;
goto v_reusejp_7631_;
}
v_reusejp_7631_:
{
return v___x_7632_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1___boxed(lean_object* v_linkDeps_7635_, lean_object* v___x_7636_, lean_object* v___f_7637_, lean_object* v_libs_7638_, lean_object* v___y_7639_, lean_object* v___y_7640_, lean_object* v___y_7641_, lean_object* v___y_7642_, lean_object* v___y_7643_, lean_object* v___y_7644_, lean_object* v___y_7645_){
_start:
{
uint8_t v_linkDeps_boxed_7646_; lean_object* v_res_7647_; 
v_linkDeps_boxed_7646_ = lean_unbox(v_linkDeps_7635_);
v_res_7647_ = l_Lake_buildSharedLib___lam__1(v_linkDeps_boxed_7646_, v___x_7636_, v___f_7637_, v_libs_7638_, v___y_7639_, v___y_7640_, v___y_7641_, v___y_7642_, v___y_7643_, v___y_7644_);
lean_dec_ref(v___y_7643_);
lean_dec(v___y_7642_);
lean_dec(v___y_7641_);
lean_dec(v___y_7640_);
lean_dec_ref(v_libs_7638_);
lean_dec(v___x_7636_);
return v_res_7647_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2(lean_object* v_traceArgs_7648_, lean_object* v_extraDepTrace_7649_, uint8_t v_linkDeps_7650_, lean_object* v___f_7651_, lean_object* v_libFile_7652_, lean_object* v_libName_7653_, uint8_t v_plugin_7654_, lean_object* v_libs_7655_, lean_object* v___y_7656_, lean_object* v___y_7657_, lean_object* v___y_7658_, lean_object* v___y_7659_, lean_object* v___y_7660_, lean_object* v___y_7661_){
_start:
{
uint64_t v___y_7664_; uint64_t v___x_7741_; lean_object* v___x_7742_; lean_object* v___x_7743_; uint8_t v___x_7744_; 
v___x_7741_ = l_Lake_Hash_nil;
v___x_7742_ = lean_unsigned_to_nat(0u);
v___x_7743_ = lean_array_get_size(v_traceArgs_7648_);
v___x_7744_ = lean_nat_dec_lt(v___x_7742_, v___x_7743_);
if (v___x_7744_ == 0)
{
v___y_7664_ = v___x_7741_;
goto v___jp_7663_;
}
else
{
uint8_t v___x_7745_; 
v___x_7745_ = lean_nat_dec_le(v___x_7743_, v___x_7743_);
if (v___x_7745_ == 0)
{
if (v___x_7744_ == 0)
{
v___y_7664_ = v___x_7741_;
goto v___jp_7663_;
}
else
{
size_t v___x_7746_; size_t v___x_7747_; uint64_t v___x_7748_; 
v___x_7746_ = ((size_t)0ULL);
v___x_7747_ = lean_usize_of_nat(v___x_7743_);
v___x_7748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7648_, v___x_7746_, v___x_7747_, v___x_7741_);
v___y_7664_ = v___x_7748_;
goto v___jp_7663_;
}
}
else
{
size_t v___x_7749_; size_t v___x_7750_; uint64_t v___x_7751_; 
v___x_7749_ = ((size_t)0ULL);
v___x_7750_ = lean_usize_of_nat(v___x_7743_);
v___x_7751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7648_, v___x_7749_, v___x_7750_, v___x_7741_);
v___y_7664_ = v___x_7751_;
goto v___jp_7663_;
}
}
v___jp_7663_:
{
lean_object* v_log_7665_; uint8_t v_action_7666_; uint8_t v_wantsRebuild_7667_; lean_object* v_trace_7668_; lean_object* v_buildTime_7669_; lean_object* v___x_7671_; uint8_t v_isShared_7672_; uint8_t v_isSharedCheck_7740_; 
v_log_7665_ = lean_ctor_get(v___y_7661_, 0);
v_action_7666_ = lean_ctor_get_uint8(v___y_7661_, sizeof(void*)*3);
v_wantsRebuild_7667_ = lean_ctor_get_uint8(v___y_7661_, sizeof(void*)*3 + 1);
v_trace_7668_ = lean_ctor_get(v___y_7661_, 1);
v_buildTime_7669_ = lean_ctor_get(v___y_7661_, 2);
v_isSharedCheck_7740_ = !lean_is_exclusive(v___y_7661_);
if (v_isSharedCheck_7740_ == 0)
{
v___x_7671_ = v___y_7661_;
v_isShared_7672_ = v_isSharedCheck_7740_;
goto v_resetjp_7670_;
}
else
{
lean_inc(v_buildTime_7669_);
lean_inc(v_trace_7668_);
lean_inc(v_log_7665_);
lean_dec(v___y_7661_);
v___x_7671_ = lean_box(0);
v_isShared_7672_ = v_isSharedCheck_7740_;
goto v_resetjp_7670_;
}
v_resetjp_7670_:
{
lean_object* v___x_7673_; lean_object* v___x_7674_; lean_object* v___x_7675_; lean_object* v___x_7676_; lean_object* v___x_7677_; lean_object* v___x_7678_; lean_object* v___x_7679_; lean_object* v___x_7680_; lean_object* v___x_7681_; lean_object* v___x_7682_; lean_object* v___x_7683_; lean_object* v___x_7684_; lean_object* v___x_7685_; lean_object* v___x_7687_; 
v___x_7673_ = lean_unsigned_to_nat(0u);
v___x_7674_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_7675_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_7676_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_7677_ = lean_array_to_list(v_traceArgs_7648_);
v___x_7678_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_7677_);
lean_dec(v___x_7677_);
v___x_7679_ = lean_string_append(v___x_7676_, v___x_7678_);
lean_dec_ref(v___x_7678_);
v___x_7680_ = lean_string_append(v___x_7675_, v___x_7679_);
lean_dec_ref(v___x_7679_);
v___x_7681_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_7682_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_7682_, 0, v___x_7680_);
lean_ctor_set(v___x_7682_, 1, v___x_7674_);
lean_ctor_set(v___x_7682_, 2, v___x_7681_);
lean_ctor_set_uint64(v___x_7682_, sizeof(void*)*3, v___y_7664_);
v___x_7683_ = l_Lake_BuildTrace_mix(v_trace_7668_, v___x_7682_);
v___x_7684_ = l_Lake_platformTrace;
v___x_7685_ = l_Lake_BuildTrace_mix(v___x_7683_, v___x_7684_);
if (v_isShared_7672_ == 0)
{
lean_ctor_set(v___x_7671_, 1, v___x_7685_);
v___x_7687_ = v___x_7671_;
goto v_reusejp_7686_;
}
else
{
lean_object* v_reuseFailAlloc_7739_; 
v_reuseFailAlloc_7739_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7739_, 0, v_log_7665_);
lean_ctor_set(v_reuseFailAlloc_7739_, 1, v___x_7685_);
lean_ctor_set(v_reuseFailAlloc_7739_, 2, v_buildTime_7669_);
lean_ctor_set_uint8(v_reuseFailAlloc_7739_, sizeof(void*)*3, v_action_7666_);
lean_ctor_set_uint8(v_reuseFailAlloc_7739_, sizeof(void*)*3 + 1, v_wantsRebuild_7667_);
v___x_7687_ = v_reuseFailAlloc_7739_;
goto v_reusejp_7686_;
}
v_reusejp_7686_:
{
lean_object* v___x_7688_; 
lean_inc_ref(v___y_7660_);
lean_inc(v___y_7659_);
lean_inc(v___y_7658_);
lean_inc(v___y_7657_);
lean_inc_ref(v___y_7656_);
v___x_7688_ = lean_apply_7(v_extraDepTrace_7649_, v___y_7656_, v___y_7657_, v___y_7658_, v___y_7659_, v___y_7660_, v___x_7687_, lean_box(0));
if (lean_obj_tag(v___x_7688_) == 0)
{
lean_object* v_a_7689_; lean_object* v_a_7690_; lean_object* v_log_7691_; uint8_t v_action_7692_; uint8_t v_wantsRebuild_7693_; lean_object* v_trace_7694_; lean_object* v_buildTime_7695_; lean_object* v___x_7697_; uint8_t v_isShared_7698_; uint8_t v_isSharedCheck_7729_; 
v_a_7689_ = lean_ctor_get(v___x_7688_, 1);
lean_inc(v_a_7689_);
v_a_7690_ = lean_ctor_get(v___x_7688_, 0);
lean_inc(v_a_7690_);
lean_dec_ref(v___x_7688_);
v_log_7691_ = lean_ctor_get(v_a_7689_, 0);
v_action_7692_ = lean_ctor_get_uint8(v_a_7689_, sizeof(void*)*3);
v_wantsRebuild_7693_ = lean_ctor_get_uint8(v_a_7689_, sizeof(void*)*3 + 1);
v_trace_7694_ = lean_ctor_get(v_a_7689_, 1);
v_buildTime_7695_ = lean_ctor_get(v_a_7689_, 2);
v_isSharedCheck_7729_ = !lean_is_exclusive(v_a_7689_);
if (v_isSharedCheck_7729_ == 0)
{
v___x_7697_ = v_a_7689_;
v_isShared_7698_ = v_isSharedCheck_7729_;
goto v_resetjp_7696_;
}
else
{
lean_inc(v_buildTime_7695_);
lean_inc(v_trace_7694_);
lean_inc(v_log_7691_);
lean_dec(v_a_7689_);
v___x_7697_ = lean_box(0);
v_isShared_7698_ = v_isSharedCheck_7729_;
goto v_resetjp_7696_;
}
v_resetjp_7696_:
{
lean_object* v___x_7699_; lean_object* v___y_7700_; lean_object* v___x_7701_; lean_object* v___x_7703_; 
v___x_7699_ = lean_box(v_linkDeps_7650_);
lean_inc_ref(v_libs_7655_);
v___y_7700_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__1___boxed), 11, 4);
lean_closure_set(v___y_7700_, 0, v___x_7699_);
lean_closure_set(v___y_7700_, 1, v___x_7673_);
lean_closure_set(v___y_7700_, 2, v___f_7651_);
lean_closure_set(v___y_7700_, 3, v_libs_7655_);
v___x_7701_ = l_Lake_BuildTrace_mix(v_trace_7694_, v_a_7690_);
if (v_isShared_7698_ == 0)
{
lean_ctor_set(v___x_7697_, 1, v___x_7701_);
v___x_7703_ = v___x_7697_;
goto v_reusejp_7702_;
}
else
{
lean_object* v_reuseFailAlloc_7728_; 
v_reuseFailAlloc_7728_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7728_, 0, v_log_7691_);
lean_ctor_set(v_reuseFailAlloc_7728_, 1, v___x_7701_);
lean_ctor_set(v_reuseFailAlloc_7728_, 2, v_buildTime_7695_);
lean_ctor_set_uint8(v_reuseFailAlloc_7728_, sizeof(void*)*3, v_action_7692_);
lean_ctor_set_uint8(v_reuseFailAlloc_7728_, sizeof(void*)*3 + 1, v_wantsRebuild_7693_);
v___x_7703_ = v_reuseFailAlloc_7728_;
goto v_reusejp_7702_;
}
v_reusejp_7702_:
{
uint8_t v___x_7704_; uint8_t v___x_7705_; lean_object* v___x_7706_; lean_object* v___x_7707_; 
v___x_7704_ = 1;
v___x_7705_ = 0;
v___x_7706_ = l_Lake_sharedLibExt;
v___x_7707_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_7652_, v___y_7700_, v___x_7705_, v___x_7706_, v___x_7704_, v___x_7705_, v___x_7705_, v___y_7656_, v___y_7657_, v___y_7658_, v___y_7659_, v___y_7660_, v___x_7703_);
if (lean_obj_tag(v___x_7707_) == 0)
{
lean_object* v_a_7708_; lean_object* v_a_7709_; lean_object* v___x_7711_; uint8_t v_isShared_7712_; uint8_t v_isSharedCheck_7718_; 
v_a_7708_ = lean_ctor_get(v___x_7707_, 0);
v_a_7709_ = lean_ctor_get(v___x_7707_, 1);
v_isSharedCheck_7718_ = !lean_is_exclusive(v___x_7707_);
if (v_isSharedCheck_7718_ == 0)
{
v___x_7711_ = v___x_7707_;
v_isShared_7712_ = v_isSharedCheck_7718_;
goto v_resetjp_7710_;
}
else
{
lean_inc(v_a_7709_);
lean_inc(v_a_7708_);
lean_dec(v___x_7707_);
v___x_7711_ = lean_box(0);
v_isShared_7712_ = v_isSharedCheck_7718_;
goto v_resetjp_7710_;
}
v_resetjp_7710_:
{
lean_object* v_path_7713_; lean_object* v___x_7714_; lean_object* v___x_7716_; 
v_path_7713_ = lean_ctor_get(v_a_7708_, 1);
lean_inc_ref(v_path_7713_);
lean_dec(v_a_7708_);
v___x_7714_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_7714_, 0, v_path_7713_);
lean_ctor_set(v___x_7714_, 1, v_libName_7653_);
lean_ctor_set(v___x_7714_, 2, v_libs_7655_);
lean_ctor_set_uint8(v___x_7714_, sizeof(void*)*3, v_plugin_7654_);
if (v_isShared_7712_ == 0)
{
lean_ctor_set(v___x_7711_, 0, v___x_7714_);
v___x_7716_ = v___x_7711_;
goto v_reusejp_7715_;
}
else
{
lean_object* v_reuseFailAlloc_7717_; 
v_reuseFailAlloc_7717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7717_, 0, v___x_7714_);
lean_ctor_set(v_reuseFailAlloc_7717_, 1, v_a_7709_);
v___x_7716_ = v_reuseFailAlloc_7717_;
goto v_reusejp_7715_;
}
v_reusejp_7715_:
{
return v___x_7716_;
}
}
}
else
{
lean_object* v_a_7719_; lean_object* v_a_7720_; lean_object* v___x_7722_; uint8_t v_isShared_7723_; uint8_t v_isSharedCheck_7727_; 
lean_dec_ref(v_libs_7655_);
lean_dec_ref(v_libName_7653_);
v_a_7719_ = lean_ctor_get(v___x_7707_, 0);
v_a_7720_ = lean_ctor_get(v___x_7707_, 1);
v_isSharedCheck_7727_ = !lean_is_exclusive(v___x_7707_);
if (v_isSharedCheck_7727_ == 0)
{
v___x_7722_ = v___x_7707_;
v_isShared_7723_ = v_isSharedCheck_7727_;
goto v_resetjp_7721_;
}
else
{
lean_inc(v_a_7720_);
lean_inc(v_a_7719_);
lean_dec(v___x_7707_);
v___x_7722_ = lean_box(0);
v_isShared_7723_ = v_isSharedCheck_7727_;
goto v_resetjp_7721_;
}
v_resetjp_7721_:
{
lean_object* v___x_7725_; 
if (v_isShared_7723_ == 0)
{
v___x_7725_ = v___x_7722_;
goto v_reusejp_7724_;
}
else
{
lean_object* v_reuseFailAlloc_7726_; 
v_reuseFailAlloc_7726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7726_, 0, v_a_7719_);
lean_ctor_set(v_reuseFailAlloc_7726_, 1, v_a_7720_);
v___x_7725_ = v_reuseFailAlloc_7726_;
goto v_reusejp_7724_;
}
v_reusejp_7724_:
{
return v___x_7725_;
}
}
}
}
}
}
else
{
lean_object* v_a_7730_; lean_object* v_a_7731_; lean_object* v___x_7733_; uint8_t v_isShared_7734_; uint8_t v_isSharedCheck_7738_; 
lean_dec_ref(v___y_7656_);
lean_dec_ref(v_libs_7655_);
lean_dec_ref(v_libName_7653_);
lean_dec_ref(v_libFile_7652_);
lean_dec_ref(v___f_7651_);
v_a_7730_ = lean_ctor_get(v___x_7688_, 0);
v_a_7731_ = lean_ctor_get(v___x_7688_, 1);
v_isSharedCheck_7738_ = !lean_is_exclusive(v___x_7688_);
if (v_isSharedCheck_7738_ == 0)
{
v___x_7733_ = v___x_7688_;
v_isShared_7734_ = v_isSharedCheck_7738_;
goto v_resetjp_7732_;
}
else
{
lean_inc(v_a_7731_);
lean_inc(v_a_7730_);
lean_dec(v___x_7688_);
v___x_7733_ = lean_box(0);
v_isShared_7734_ = v_isSharedCheck_7738_;
goto v_resetjp_7732_;
}
v_resetjp_7732_:
{
lean_object* v___x_7736_; 
if (v_isShared_7734_ == 0)
{
v___x_7736_ = v___x_7733_;
goto v_reusejp_7735_;
}
else
{
lean_object* v_reuseFailAlloc_7737_; 
v_reuseFailAlloc_7737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7737_, 0, v_a_7730_);
lean_ctor_set(v_reuseFailAlloc_7737_, 1, v_a_7731_);
v___x_7736_ = v_reuseFailAlloc_7737_;
goto v_reusejp_7735_;
}
v_reusejp_7735_:
{
return v___x_7736_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2___boxed(lean_object* v_traceArgs_7752_, lean_object* v_extraDepTrace_7753_, lean_object* v_linkDeps_7754_, lean_object* v___f_7755_, lean_object* v_libFile_7756_, lean_object* v_libName_7757_, lean_object* v_plugin_7758_, lean_object* v_libs_7759_, lean_object* v___y_7760_, lean_object* v___y_7761_, lean_object* v___y_7762_, lean_object* v___y_7763_, lean_object* v___y_7764_, lean_object* v___y_7765_, lean_object* v___y_7766_){
_start:
{
uint8_t v_linkDeps_boxed_7767_; uint8_t v_plugin_boxed_7768_; lean_object* v_res_7769_; 
v_linkDeps_boxed_7767_ = lean_unbox(v_linkDeps_7754_);
v_plugin_boxed_7768_ = lean_unbox(v_plugin_7758_);
v_res_7769_ = l_Lake_buildSharedLib___lam__2(v_traceArgs_7752_, v_extraDepTrace_7753_, v_linkDeps_boxed_7767_, v___f_7755_, v_libFile_7756_, v_libName_7757_, v_plugin_boxed_7768_, v_libs_7759_, v___y_7760_, v___y_7761_, v___y_7762_, v___y_7763_, v___y_7764_, v___y_7765_);
lean_dec_ref(v___y_7764_);
lean_dec(v___y_7763_);
lean_dec(v___y_7762_);
lean_dec(v___y_7761_);
return v_res_7769_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3(lean_object* v_weakArgs_7771_, lean_object* v_traceArgs_7772_, lean_object* v_libFile_7773_, lean_object* v_linker_7774_, lean_object* v_extraDepTrace_7775_, uint8_t v_linkDeps_7776_, lean_object* v_libName_7777_, uint8_t v_plugin_7778_, lean_object* v_linkLibs_7779_, lean_object* v___x_7780_, lean_object* v_objs_7781_, lean_object* v___y_7782_, lean_object* v___y_7783_, lean_object* v___y_7784_, lean_object* v___y_7785_, lean_object* v___y_7786_, lean_object* v___y_7787_){
_start:
{
lean_object* v_trace_7789_; lean_object* v___f_7790_; lean_object* v___x_7791_; lean_object* v___x_7792_; lean_object* v___f_7793_; lean_object* v___x_7794_; lean_object* v___x_7795_; lean_object* v___x_7796_; uint8_t v___x_7797_; lean_object* v___x_7798_; lean_object* v___x_7799_; 
v_trace_7789_ = lean_ctor_get(v___y_7787_, 1);
lean_inc_ref(v_libFile_7773_);
lean_inc_ref(v_traceArgs_7772_);
v___f_7790_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__0___boxed), 13, 5);
lean_closure_set(v___f_7790_, 0, v_objs_7781_);
lean_closure_set(v___f_7790_, 1, v_weakArgs_7771_);
lean_closure_set(v___f_7790_, 2, v_traceArgs_7772_);
lean_closure_set(v___f_7790_, 3, v_libFile_7773_);
lean_closure_set(v___f_7790_, 4, v_linker_7774_);
v___x_7791_ = lean_box(v_linkDeps_7776_);
v___x_7792_ = lean_box(v_plugin_7778_);
v___f_7793_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__2___boxed), 15, 7);
lean_closure_set(v___f_7793_, 0, v_traceArgs_7772_);
lean_closure_set(v___f_7793_, 1, v_extraDepTrace_7775_);
lean_closure_set(v___f_7793_, 2, v___x_7791_);
lean_closure_set(v___f_7793_, 3, v___f_7790_);
lean_closure_set(v___f_7793_, 4, v_libFile_7773_);
lean_closure_set(v___f_7793_, 5, v_libName_7777_);
lean_closure_set(v___f_7793_, 6, v___x_7792_);
v___x_7794_ = ((lean_object*)(l_Lake_buildSharedLib___lam__3___closed__0));
v___x_7795_ = l_Lake_Job_collectArray___redArg(v_linkLibs_7779_, v___x_7794_);
v___x_7796_ = lean_unsigned_to_nat(0u);
v___x_7797_ = 0;
v___x_7798_ = l_Lake_Job_mapM___redArg(v___x_7780_, v___x_7795_, v___f_7793_, v___x_7796_, v___x_7797_, v___y_7782_, v___y_7783_, v___y_7784_, v___y_7785_, v___y_7786_, v_trace_7789_);
v___x_7799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7799_, 0, v___x_7798_);
lean_ctor_set(v___x_7799_, 1, v___y_7787_);
return v___x_7799_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3___boxed(lean_object** _args){
lean_object* v_weakArgs_7800_ = _args[0];
lean_object* v_traceArgs_7801_ = _args[1];
lean_object* v_libFile_7802_ = _args[2];
lean_object* v_linker_7803_ = _args[3];
lean_object* v_extraDepTrace_7804_ = _args[4];
lean_object* v_linkDeps_7805_ = _args[5];
lean_object* v_libName_7806_ = _args[6];
lean_object* v_plugin_7807_ = _args[7];
lean_object* v_linkLibs_7808_ = _args[8];
lean_object* v___x_7809_ = _args[9];
lean_object* v_objs_7810_ = _args[10];
lean_object* v___y_7811_ = _args[11];
lean_object* v___y_7812_ = _args[12];
lean_object* v___y_7813_ = _args[13];
lean_object* v___y_7814_ = _args[14];
lean_object* v___y_7815_ = _args[15];
lean_object* v___y_7816_ = _args[16];
lean_object* v___y_7817_ = _args[17];
_start:
{
uint8_t v_linkDeps_boxed_7818_; uint8_t v_plugin_boxed_7819_; lean_object* v_res_7820_; 
v_linkDeps_boxed_7818_ = lean_unbox(v_linkDeps_7805_);
v_plugin_boxed_7819_ = lean_unbox(v_plugin_7807_);
v_res_7820_ = l_Lake_buildSharedLib___lam__3(v_weakArgs_7800_, v_traceArgs_7801_, v_libFile_7802_, v_linker_7803_, v_extraDepTrace_7804_, v_linkDeps_boxed_7818_, v_libName_7806_, v_plugin_boxed_7819_, v_linkLibs_7808_, v___x_7809_, v_objs_7810_, v___y_7811_, v___y_7812_, v___y_7813_, v___y_7814_, v___y_7815_, v___y_7816_);
lean_dec_ref(v___y_7815_);
lean_dec(v___y_7814_);
lean_dec(v___y_7813_);
lean_dec(v___y_7812_);
lean_dec_ref(v_linkLibs_7808_);
return v_res_7820_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib(lean_object* v_libName_7822_, lean_object* v_libFile_7823_, lean_object* v_linkObjs_7824_, lean_object* v_linkLibs_7825_, lean_object* v_weakArgs_7826_, lean_object* v_traceArgs_7827_, lean_object* v_linker_7828_, lean_object* v_extraDepTrace_7829_, uint8_t v_plugin_7830_, uint8_t v_linkDeps_7831_, lean_object* v_a_7832_, lean_object* v_a_7833_, lean_object* v_a_7834_, lean_object* v_a_7835_, lean_object* v_a_7836_, lean_object* v_a_7837_){
_start:
{
lean_object* v___x_7839_; lean_object* v___x_7840_; lean_object* v___x_7841_; lean_object* v___f_7842_; lean_object* v___x_7843_; lean_object* v___x_7844_; lean_object* v___x_7845_; uint8_t v___x_7846_; lean_object* v___x_7847_; 
v___x_7839_ = l_Lake_instDataKindDynlib;
v___x_7840_ = lean_box(v_linkDeps_7831_);
v___x_7841_ = lean_box(v_plugin_7830_);
v___f_7842_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__3___boxed), 18, 10);
lean_closure_set(v___f_7842_, 0, v_weakArgs_7826_);
lean_closure_set(v___f_7842_, 1, v_traceArgs_7827_);
lean_closure_set(v___f_7842_, 2, v_libFile_7823_);
lean_closure_set(v___f_7842_, 3, v_linker_7828_);
lean_closure_set(v___f_7842_, 4, v_extraDepTrace_7829_);
lean_closure_set(v___f_7842_, 5, v___x_7840_);
lean_closure_set(v___f_7842_, 6, v_libName_7822_);
lean_closure_set(v___f_7842_, 7, v___x_7841_);
lean_closure_set(v___f_7842_, 8, v_linkLibs_7825_);
lean_closure_set(v___f_7842_, 9, v___x_7839_);
v___x_7843_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_7844_ = l_Lake_Job_collectArray___redArg(v_linkObjs_7824_, v___x_7843_);
v___x_7845_ = lean_unsigned_to_nat(0u);
v___x_7846_ = 1;
v___x_7847_ = l_Lake_Job_bindM___redArg(v___x_7839_, v___x_7844_, v___f_7842_, v___x_7845_, v___x_7846_, v_a_7832_, v_a_7833_, v_a_7834_, v_a_7835_, v_a_7836_, v_a_7837_);
return v___x_7847_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___boxed(lean_object** _args){
lean_object* v_libName_7848_ = _args[0];
lean_object* v_libFile_7849_ = _args[1];
lean_object* v_linkObjs_7850_ = _args[2];
lean_object* v_linkLibs_7851_ = _args[3];
lean_object* v_weakArgs_7852_ = _args[4];
lean_object* v_traceArgs_7853_ = _args[5];
lean_object* v_linker_7854_ = _args[6];
lean_object* v_extraDepTrace_7855_ = _args[7];
lean_object* v_plugin_7856_ = _args[8];
lean_object* v_linkDeps_7857_ = _args[9];
lean_object* v_a_7858_ = _args[10];
lean_object* v_a_7859_ = _args[11];
lean_object* v_a_7860_ = _args[12];
lean_object* v_a_7861_ = _args[13];
lean_object* v_a_7862_ = _args[14];
lean_object* v_a_7863_ = _args[15];
lean_object* v_a_7864_ = _args[16];
_start:
{
uint8_t v_plugin_boxed_7865_; uint8_t v_linkDeps_boxed_7866_; lean_object* v_res_7867_; 
v_plugin_boxed_7865_ = lean_unbox(v_plugin_7856_);
v_linkDeps_boxed_7866_ = lean_unbox(v_linkDeps_7857_);
v_res_7867_ = l_Lake_buildSharedLib(v_libName_7848_, v_libFile_7849_, v_linkObjs_7850_, v_linkLibs_7851_, v_weakArgs_7852_, v_traceArgs_7853_, v_linker_7854_, v_extraDepTrace_7855_, v_plugin_boxed_7865_, v_linkDeps_boxed_7866_, v_a_7858_, v_a_7859_, v_a_7860_, v_a_7861_, v_a_7862_, v_a_7863_);
lean_dec_ref(v_a_7863_);
lean_dec_ref(v_a_7862_);
lean_dec(v_a_7861_);
lean_dec(v_a_7860_);
lean_dec(v_a_7859_);
lean_dec_ref(v_linkObjs_7850_);
return v_res_7867_;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLib___lam__0___closed__0(void){
_start:
{
lean_object* v___x_7868_; lean_object* v___x_7869_; lean_object* v___x_7870_; lean_object* v___x_7871_; 
v___x_7868_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
v___x_7869_ = lean_unsigned_to_nat(2u);
v___x_7870_ = lean_mk_empty_array_with_capacity(v___x_7869_);
v___x_7871_ = lean_array_push(v___x_7870_, v___x_7868_);
return v___x_7871_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object* v_objs_7872_, lean_object* v_weakArgs_7873_, lean_object* v_traceArgs_7874_, lean_object* v_libFile_7875_, uint8_t v_linkDeps_7876_, lean_object* v_libs_7877_, lean_object* v___y_7878_, lean_object* v___y_7879_, lean_object* v___y_7880_, lean_object* v___y_7881_, lean_object* v___y_7882_, lean_object* v___y_7883_){
_start:
{
lean_object* v_toContext_7885_; lean_object* v_lakeEnv_7886_; lean_object* v_lean_7887_; lean_object* v_libs_7889_; lean_object* v___y_7890_; 
v_toContext_7885_ = lean_ctor_get(v___y_7882_, 1);
v_lakeEnv_7886_ = lean_ctor_get(v_toContext_7885_, 0);
v_lean_7887_ = lean_ctor_get(v_lakeEnv_7886_, 1);
if (v_linkDeps_7876_ == 0)
{
lean_object* v___x_7935_; 
v___x_7935_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1));
v_libs_7889_ = v___x_7935_;
v___y_7890_ = v___y_7883_;
goto v___jp_7888_;
}
else
{
lean_object* v___x_7936_; 
v___x_7936_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_7877_, v___y_7883_);
if (lean_obj_tag(v___x_7936_) == 0)
{
lean_object* v_a_7937_; lean_object* v_a_7938_; 
v_a_7937_ = lean_ctor_get(v___x_7936_, 0);
lean_inc(v_a_7937_);
v_a_7938_ = lean_ctor_get(v___x_7936_, 1);
lean_inc(v_a_7938_);
lean_dec_ref(v___x_7936_);
v_libs_7889_ = v_a_7937_;
v___y_7890_ = v_a_7938_;
goto v___jp_7888_;
}
else
{
lean_object* v_a_7939_; lean_object* v_a_7940_; lean_object* v___x_7942_; uint8_t v_isShared_7943_; uint8_t v_isSharedCheck_7947_; 
lean_dec_ref(v_libFile_7875_);
v_a_7939_ = lean_ctor_get(v___x_7936_, 0);
v_a_7940_ = lean_ctor_get(v___x_7936_, 1);
v_isSharedCheck_7947_ = !lean_is_exclusive(v___x_7936_);
if (v_isSharedCheck_7947_ == 0)
{
v___x_7942_ = v___x_7936_;
v_isShared_7943_ = v_isSharedCheck_7947_;
goto v_resetjp_7941_;
}
else
{
lean_inc(v_a_7940_);
lean_inc(v_a_7939_);
lean_dec(v___x_7936_);
v___x_7942_ = lean_box(0);
v_isShared_7943_ = v_isSharedCheck_7947_;
goto v_resetjp_7941_;
}
v_resetjp_7941_:
{
lean_object* v___x_7945_; 
if (v_isShared_7943_ == 0)
{
v___x_7945_ = v___x_7942_;
goto v_reusejp_7944_;
}
else
{
lean_object* v_reuseFailAlloc_7946_; 
v_reuseFailAlloc_7946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7946_, 0, v_a_7939_);
lean_ctor_set(v_reuseFailAlloc_7946_, 1, v_a_7940_);
v___x_7945_ = v_reuseFailAlloc_7946_;
goto v_reusejp_7944_;
}
v_reusejp_7944_:
{
return v___x_7945_;
}
}
}
}
v___jp_7888_:
{
lean_object* v_leanLibDir_7891_; lean_object* v_cc_7892_; lean_object* v_ccLinkSharedFlags_7893_; lean_object* v_log_7894_; uint8_t v_action_7895_; uint8_t v_wantsRebuild_7896_; lean_object* v_trace_7897_; lean_object* v_buildTime_7898_; lean_object* v___x_7900_; uint8_t v_isShared_7901_; uint8_t v_isSharedCheck_7934_; 
v_leanLibDir_7891_ = lean_ctor_get(v_lean_7887_, 3);
v_cc_7892_ = lean_ctor_get(v_lean_7887_, 14);
v_ccLinkSharedFlags_7893_ = lean_ctor_get(v_lean_7887_, 20);
v_log_7894_ = lean_ctor_get(v___y_7890_, 0);
v_action_7895_ = lean_ctor_get_uint8(v___y_7890_, sizeof(void*)*3);
v_wantsRebuild_7896_ = lean_ctor_get_uint8(v___y_7890_, sizeof(void*)*3 + 1);
v_trace_7897_ = lean_ctor_get(v___y_7890_, 1);
v_buildTime_7898_ = lean_ctor_get(v___y_7890_, 2);
v_isSharedCheck_7934_ = !lean_is_exclusive(v___y_7890_);
if (v_isSharedCheck_7934_ == 0)
{
v___x_7900_ = v___y_7890_;
v_isShared_7901_ = v_isSharedCheck_7934_;
goto v_resetjp_7899_;
}
else
{
lean_inc(v_buildTime_7898_);
lean_inc(v_trace_7897_);
lean_inc(v_log_7894_);
lean_dec(v___y_7890_);
v___x_7900_ = lean_box(0);
v_isShared_7901_ = v_isSharedCheck_7934_;
goto v_resetjp_7899_;
}
v_resetjp_7899_:
{
lean_object* v___x_7902_; lean_object* v___x_7903_; lean_object* v___x_7904_; lean_object* v___x_7905_; lean_object* v___x_7906_; lean_object* v___x_7907_; lean_object* v___x_7908_; lean_object* v___x_7909_; 
v___x_7902_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7872_, v_libs_7889_);
lean_dec_ref(v_libs_7889_);
v___x_7903_ = l_Array_append___redArg(v___x_7902_, v_weakArgs_7873_);
v___x_7904_ = l_Array_append___redArg(v___x_7903_, v_traceArgs_7874_);
v___x_7905_ = lean_obj_once(&l_Lake_buildLeanSharedLib___lam__0___closed__0, &l_Lake_buildLeanSharedLib___lam__0___closed__0_once, _init_l_Lake_buildLeanSharedLib___lam__0___closed__0);
lean_inc_ref(v_leanLibDir_7891_);
v___x_7906_ = lean_array_push(v___x_7905_, v_leanLibDir_7891_);
v___x_7907_ = l_Array_append___redArg(v___x_7904_, v___x_7906_);
lean_dec_ref(v___x_7906_);
v___x_7908_ = l_Array_append___redArg(v___x_7907_, v_ccLinkSharedFlags_7893_);
lean_inc_ref(v_cc_7892_);
v___x_7909_ = l_Lake_compileSharedLib(v_libFile_7875_, v___x_7908_, v_cc_7892_, v_log_7894_);
lean_dec_ref(v___x_7908_);
if (lean_obj_tag(v___x_7909_) == 0)
{
lean_object* v_a_7910_; lean_object* v_a_7911_; lean_object* v___x_7913_; uint8_t v_isShared_7914_; uint8_t v_isSharedCheck_7921_; 
v_a_7910_ = lean_ctor_get(v___x_7909_, 0);
v_a_7911_ = lean_ctor_get(v___x_7909_, 1);
v_isSharedCheck_7921_ = !lean_is_exclusive(v___x_7909_);
if (v_isSharedCheck_7921_ == 0)
{
v___x_7913_ = v___x_7909_;
v_isShared_7914_ = v_isSharedCheck_7921_;
goto v_resetjp_7912_;
}
else
{
lean_inc(v_a_7911_);
lean_inc(v_a_7910_);
lean_dec(v___x_7909_);
v___x_7913_ = lean_box(0);
v_isShared_7914_ = v_isSharedCheck_7921_;
goto v_resetjp_7912_;
}
v_resetjp_7912_:
{
lean_object* v___x_7916_; 
if (v_isShared_7901_ == 0)
{
lean_ctor_set(v___x_7900_, 0, v_a_7911_);
v___x_7916_ = v___x_7900_;
goto v_reusejp_7915_;
}
else
{
lean_object* v_reuseFailAlloc_7920_; 
v_reuseFailAlloc_7920_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7920_, 0, v_a_7911_);
lean_ctor_set(v_reuseFailAlloc_7920_, 1, v_trace_7897_);
lean_ctor_set(v_reuseFailAlloc_7920_, 2, v_buildTime_7898_);
lean_ctor_set_uint8(v_reuseFailAlloc_7920_, sizeof(void*)*3, v_action_7895_);
lean_ctor_set_uint8(v_reuseFailAlloc_7920_, sizeof(void*)*3 + 1, v_wantsRebuild_7896_);
v___x_7916_ = v_reuseFailAlloc_7920_;
goto v_reusejp_7915_;
}
v_reusejp_7915_:
{
lean_object* v___x_7918_; 
if (v_isShared_7914_ == 0)
{
lean_ctor_set(v___x_7913_, 1, v___x_7916_);
v___x_7918_ = v___x_7913_;
goto v_reusejp_7917_;
}
else
{
lean_object* v_reuseFailAlloc_7919_; 
v_reuseFailAlloc_7919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7919_, 0, v_a_7910_);
lean_ctor_set(v_reuseFailAlloc_7919_, 1, v___x_7916_);
v___x_7918_ = v_reuseFailAlloc_7919_;
goto v_reusejp_7917_;
}
v_reusejp_7917_:
{
return v___x_7918_;
}
}
}
}
else
{
lean_object* v_a_7922_; lean_object* v_a_7923_; lean_object* v___x_7925_; uint8_t v_isShared_7926_; uint8_t v_isSharedCheck_7933_; 
v_a_7922_ = lean_ctor_get(v___x_7909_, 0);
v_a_7923_ = lean_ctor_get(v___x_7909_, 1);
v_isSharedCheck_7933_ = !lean_is_exclusive(v___x_7909_);
if (v_isSharedCheck_7933_ == 0)
{
v___x_7925_ = v___x_7909_;
v_isShared_7926_ = v_isSharedCheck_7933_;
goto v_resetjp_7924_;
}
else
{
lean_inc(v_a_7923_);
lean_inc(v_a_7922_);
lean_dec(v___x_7909_);
v___x_7925_ = lean_box(0);
v_isShared_7926_ = v_isSharedCheck_7933_;
goto v_resetjp_7924_;
}
v_resetjp_7924_:
{
lean_object* v___x_7928_; 
if (v_isShared_7901_ == 0)
{
lean_ctor_set(v___x_7900_, 0, v_a_7923_);
v___x_7928_ = v___x_7900_;
goto v_reusejp_7927_;
}
else
{
lean_object* v_reuseFailAlloc_7932_; 
v_reuseFailAlloc_7932_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7932_, 0, v_a_7923_);
lean_ctor_set(v_reuseFailAlloc_7932_, 1, v_trace_7897_);
lean_ctor_set(v_reuseFailAlloc_7932_, 2, v_buildTime_7898_);
lean_ctor_set_uint8(v_reuseFailAlloc_7932_, sizeof(void*)*3, v_action_7895_);
lean_ctor_set_uint8(v_reuseFailAlloc_7932_, sizeof(void*)*3 + 1, v_wantsRebuild_7896_);
v___x_7928_ = v_reuseFailAlloc_7932_;
goto v_reusejp_7927_;
}
v_reusejp_7927_:
{
lean_object* v___x_7930_; 
if (v_isShared_7926_ == 0)
{
lean_ctor_set(v___x_7925_, 1, v___x_7928_);
v___x_7930_ = v___x_7925_;
goto v_reusejp_7929_;
}
else
{
lean_object* v_reuseFailAlloc_7931_; 
v_reuseFailAlloc_7931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7931_, 0, v_a_7922_);
lean_ctor_set(v_reuseFailAlloc_7931_, 1, v___x_7928_);
v___x_7930_ = v_reuseFailAlloc_7931_;
goto v_reusejp_7929_;
}
v_reusejp_7929_:
{
return v___x_7930_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object* v_objs_7948_, lean_object* v_weakArgs_7949_, lean_object* v_traceArgs_7950_, lean_object* v_libFile_7951_, lean_object* v_linkDeps_7952_, lean_object* v_libs_7953_, lean_object* v___y_7954_, lean_object* v___y_7955_, lean_object* v___y_7956_, lean_object* v___y_7957_, lean_object* v___y_7958_, lean_object* v___y_7959_, lean_object* v___y_7960_){
_start:
{
uint8_t v_linkDeps_boxed_7961_; lean_object* v_res_7962_; 
v_linkDeps_boxed_7961_ = lean_unbox(v_linkDeps_7952_);
v_res_7962_ = l_Lake_buildLeanSharedLib___lam__0(v_objs_7948_, v_weakArgs_7949_, v_traceArgs_7950_, v_libFile_7951_, v_linkDeps_boxed_7961_, v_libs_7953_, v___y_7954_, v___y_7955_, v___y_7956_, v___y_7957_, v___y_7958_, v___y_7959_);
lean_dec_ref(v___y_7958_);
lean_dec(v___y_7957_);
lean_dec(v___y_7956_);
lean_dec(v___y_7955_);
lean_dec_ref(v___y_7954_);
lean_dec_ref(v_libs_7953_);
lean_dec_ref(v_traceArgs_7950_);
lean_dec_ref(v_weakArgs_7949_);
lean_dec_ref(v_objs_7948_);
return v_res_7962_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object* v_objs_7963_, lean_object* v_weakArgs_7964_, lean_object* v_traceArgs_7965_, lean_object* v_libFile_7966_, uint8_t v_linkDeps_7967_, lean_object* v_libName_7968_, uint8_t v_plugin_7969_, lean_object* v_libs_7970_, lean_object* v___y_7971_, lean_object* v___y_7972_, lean_object* v___y_7973_, lean_object* v___y_7974_, lean_object* v___y_7975_, lean_object* v___y_7976_){
_start:
{
lean_object* v_log_7978_; uint8_t v_action_7979_; uint8_t v_wantsRebuild_7980_; lean_object* v_trace_7981_; lean_object* v_buildTime_7982_; lean_object* v___x_7984_; uint8_t v_isShared_7985_; uint8_t v_isSharedCheck_8042_; 
v_log_7978_ = lean_ctor_get(v___y_7976_, 0);
v_action_7979_ = lean_ctor_get_uint8(v___y_7976_, sizeof(void*)*3);
v_wantsRebuild_7980_ = lean_ctor_get_uint8(v___y_7976_, sizeof(void*)*3 + 1);
v_trace_7981_ = lean_ctor_get(v___y_7976_, 1);
v_buildTime_7982_ = lean_ctor_get(v___y_7976_, 2);
v_isSharedCheck_8042_ = !lean_is_exclusive(v___y_7976_);
if (v_isSharedCheck_8042_ == 0)
{
v___x_7984_ = v___y_7976_;
v_isShared_7985_ = v_isSharedCheck_8042_;
goto v_resetjp_7983_;
}
else
{
lean_inc(v_buildTime_7982_);
lean_inc(v_trace_7981_);
lean_inc(v_log_7978_);
lean_dec(v___y_7976_);
v___x_7984_ = lean_box(0);
v_isShared_7985_ = v_isSharedCheck_8042_;
goto v_resetjp_7983_;
}
v_resetjp_7983_:
{
lean_object* v_leanTrace_7986_; lean_object* v___x_7987_; lean_object* v___f_7988_; lean_object* v___x_7989_; uint64_t v___y_7991_; uint64_t v___x_8031_; lean_object* v___x_8032_; lean_object* v___x_8033_; uint8_t v___x_8034_; 
v_leanTrace_7986_ = lean_ctor_get(v___y_7975_, 2);
v___x_7987_ = lean_box(v_linkDeps_7967_);
lean_inc_ref(v_libs_7970_);
lean_inc_ref(v_libFile_7966_);
lean_inc_ref(v_traceArgs_7965_);
v___f_7988_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__0___boxed), 13, 6);
lean_closure_set(v___f_7988_, 0, v_objs_7963_);
lean_closure_set(v___f_7988_, 1, v_weakArgs_7964_);
lean_closure_set(v___f_7988_, 2, v_traceArgs_7965_);
lean_closure_set(v___f_7988_, 3, v_libFile_7966_);
lean_closure_set(v___f_7988_, 4, v___x_7987_);
lean_closure_set(v___f_7988_, 5, v_libs_7970_);
lean_inc_ref(v_leanTrace_7986_);
v___x_7989_ = l_Lake_BuildTrace_mix(v_trace_7981_, v_leanTrace_7986_);
v___x_8031_ = l_Lake_Hash_nil;
v___x_8032_ = lean_unsigned_to_nat(0u);
v___x_8033_ = lean_array_get_size(v_traceArgs_7965_);
v___x_8034_ = lean_nat_dec_lt(v___x_8032_, v___x_8033_);
if (v___x_8034_ == 0)
{
v___y_7991_ = v___x_8031_;
goto v___jp_7990_;
}
else
{
uint8_t v___x_8035_; 
v___x_8035_ = lean_nat_dec_le(v___x_8033_, v___x_8033_);
if (v___x_8035_ == 0)
{
if (v___x_8034_ == 0)
{
v___y_7991_ = v___x_8031_;
goto v___jp_7990_;
}
else
{
size_t v___x_8036_; size_t v___x_8037_; uint64_t v___x_8038_; 
v___x_8036_ = ((size_t)0ULL);
v___x_8037_ = lean_usize_of_nat(v___x_8033_);
v___x_8038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7965_, v___x_8036_, v___x_8037_, v___x_8031_);
v___y_7991_ = v___x_8038_;
goto v___jp_7990_;
}
}
else
{
size_t v___x_8039_; size_t v___x_8040_; uint64_t v___x_8041_; 
v___x_8039_ = ((size_t)0ULL);
v___x_8040_ = lean_usize_of_nat(v___x_8033_);
v___x_8041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_7965_, v___x_8039_, v___x_8040_, v___x_8031_);
v___y_7991_ = v___x_8041_;
goto v___jp_7990_;
}
}
v___jp_7990_:
{
lean_object* v___x_7992_; lean_object* v___x_7993_; lean_object* v___x_7994_; lean_object* v___x_7995_; lean_object* v___x_7996_; lean_object* v___x_7997_; lean_object* v___x_7998_; lean_object* v___x_7999_; lean_object* v___x_8000_; lean_object* v___x_8001_; lean_object* v___x_8002_; lean_object* v___x_8003_; lean_object* v___x_8005_; 
v___x_7992_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_7993_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_7994_ = lean_array_to_list(v_traceArgs_7965_);
v___x_7995_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_7994_);
lean_dec(v___x_7994_);
v___x_7996_ = lean_string_append(v___x_7993_, v___x_7995_);
lean_dec_ref(v___x_7995_);
v___x_7997_ = lean_string_append(v___x_7992_, v___x_7996_);
lean_dec_ref(v___x_7996_);
v___x_7998_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_7999_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_8000_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_8000_, 0, v___x_7997_);
lean_ctor_set(v___x_8000_, 1, v___x_7998_);
lean_ctor_set(v___x_8000_, 2, v___x_7999_);
lean_ctor_set_uint64(v___x_8000_, sizeof(void*)*3, v___y_7991_);
v___x_8001_ = l_Lake_BuildTrace_mix(v___x_7989_, v___x_8000_);
v___x_8002_ = l_Lake_platformTrace;
v___x_8003_ = l_Lake_BuildTrace_mix(v___x_8001_, v___x_8002_);
if (v_isShared_7985_ == 0)
{
lean_ctor_set(v___x_7984_, 1, v___x_8003_);
v___x_8005_ = v___x_7984_;
goto v_reusejp_8004_;
}
else
{
lean_object* v_reuseFailAlloc_8030_; 
v_reuseFailAlloc_8030_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8030_, 0, v_log_7978_);
lean_ctor_set(v_reuseFailAlloc_8030_, 1, v___x_8003_);
lean_ctor_set(v_reuseFailAlloc_8030_, 2, v_buildTime_7982_);
lean_ctor_set_uint8(v_reuseFailAlloc_8030_, sizeof(void*)*3, v_action_7979_);
lean_ctor_set_uint8(v_reuseFailAlloc_8030_, sizeof(void*)*3 + 1, v_wantsRebuild_7980_);
v___x_8005_ = v_reuseFailAlloc_8030_;
goto v_reusejp_8004_;
}
v_reusejp_8004_:
{
uint8_t v___x_8006_; lean_object* v___x_8007_; uint8_t v___x_8008_; lean_object* v___x_8009_; 
v___x_8006_ = 0;
v___x_8007_ = l_Lake_sharedLibExt;
v___x_8008_ = 1;
v___x_8009_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_7966_, v___f_7988_, v___x_8006_, v___x_8007_, v___x_8008_, v___x_8006_, v___x_8006_, v___y_7971_, v___y_7972_, v___y_7973_, v___y_7974_, v___y_7975_, v___x_8005_);
if (lean_obj_tag(v___x_8009_) == 0)
{
lean_object* v_a_8010_; lean_object* v_a_8011_; lean_object* v___x_8013_; uint8_t v_isShared_8014_; uint8_t v_isSharedCheck_8020_; 
v_a_8010_ = lean_ctor_get(v___x_8009_, 0);
v_a_8011_ = lean_ctor_get(v___x_8009_, 1);
v_isSharedCheck_8020_ = !lean_is_exclusive(v___x_8009_);
if (v_isSharedCheck_8020_ == 0)
{
v___x_8013_ = v___x_8009_;
v_isShared_8014_ = v_isSharedCheck_8020_;
goto v_resetjp_8012_;
}
else
{
lean_inc(v_a_8011_);
lean_inc(v_a_8010_);
lean_dec(v___x_8009_);
v___x_8013_ = lean_box(0);
v_isShared_8014_ = v_isSharedCheck_8020_;
goto v_resetjp_8012_;
}
v_resetjp_8012_:
{
lean_object* v_path_8015_; lean_object* v___x_8016_; lean_object* v___x_8018_; 
v_path_8015_ = lean_ctor_get(v_a_8010_, 1);
lean_inc_ref(v_path_8015_);
lean_dec(v_a_8010_);
v___x_8016_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_8016_, 0, v_path_8015_);
lean_ctor_set(v___x_8016_, 1, v_libName_7968_);
lean_ctor_set(v___x_8016_, 2, v_libs_7970_);
lean_ctor_set_uint8(v___x_8016_, sizeof(void*)*3, v_plugin_7969_);
if (v_isShared_8014_ == 0)
{
lean_ctor_set(v___x_8013_, 0, v___x_8016_);
v___x_8018_ = v___x_8013_;
goto v_reusejp_8017_;
}
else
{
lean_object* v_reuseFailAlloc_8019_; 
v_reuseFailAlloc_8019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8019_, 0, v___x_8016_);
lean_ctor_set(v_reuseFailAlloc_8019_, 1, v_a_8011_);
v___x_8018_ = v_reuseFailAlloc_8019_;
goto v_reusejp_8017_;
}
v_reusejp_8017_:
{
return v___x_8018_;
}
}
}
else
{
lean_object* v_a_8021_; lean_object* v_a_8022_; lean_object* v___x_8024_; uint8_t v_isShared_8025_; uint8_t v_isSharedCheck_8029_; 
lean_dec_ref(v_libs_7970_);
lean_dec_ref(v_libName_7968_);
v_a_8021_ = lean_ctor_get(v___x_8009_, 0);
v_a_8022_ = lean_ctor_get(v___x_8009_, 1);
v_isSharedCheck_8029_ = !lean_is_exclusive(v___x_8009_);
if (v_isSharedCheck_8029_ == 0)
{
v___x_8024_ = v___x_8009_;
v_isShared_8025_ = v_isSharedCheck_8029_;
goto v_resetjp_8023_;
}
else
{
lean_inc(v_a_8022_);
lean_inc(v_a_8021_);
lean_dec(v___x_8009_);
v___x_8024_ = lean_box(0);
v_isShared_8025_ = v_isSharedCheck_8029_;
goto v_resetjp_8023_;
}
v_resetjp_8023_:
{
lean_object* v___x_8027_; 
if (v_isShared_8025_ == 0)
{
v___x_8027_ = v___x_8024_;
goto v_reusejp_8026_;
}
else
{
lean_object* v_reuseFailAlloc_8028_; 
v_reuseFailAlloc_8028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8028_, 0, v_a_8021_);
lean_ctor_set(v_reuseFailAlloc_8028_, 1, v_a_8022_);
v___x_8027_ = v_reuseFailAlloc_8028_;
goto v_reusejp_8026_;
}
v_reusejp_8026_:
{
return v___x_8027_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1___boxed(lean_object* v_objs_8043_, lean_object* v_weakArgs_8044_, lean_object* v_traceArgs_8045_, lean_object* v_libFile_8046_, lean_object* v_linkDeps_8047_, lean_object* v_libName_8048_, lean_object* v_plugin_8049_, lean_object* v_libs_8050_, lean_object* v___y_8051_, lean_object* v___y_8052_, lean_object* v___y_8053_, lean_object* v___y_8054_, lean_object* v___y_8055_, lean_object* v___y_8056_, lean_object* v___y_8057_){
_start:
{
uint8_t v_linkDeps_boxed_8058_; uint8_t v_plugin_boxed_8059_; lean_object* v_res_8060_; 
v_linkDeps_boxed_8058_ = lean_unbox(v_linkDeps_8047_);
v_plugin_boxed_8059_ = lean_unbox(v_plugin_8049_);
v_res_8060_ = l_Lake_buildLeanSharedLib___lam__1(v_objs_8043_, v_weakArgs_8044_, v_traceArgs_8045_, v_libFile_8046_, v_linkDeps_boxed_8058_, v_libName_8048_, v_plugin_boxed_8059_, v_libs_8050_, v___y_8051_, v___y_8052_, v___y_8053_, v___y_8054_, v___y_8055_, v___y_8056_);
lean_dec_ref(v___y_8055_);
lean_dec(v___y_8054_);
lean_dec(v___y_8053_);
lean_dec(v___y_8052_);
return v_res_8060_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2(lean_object* v_weakArgs_8061_, lean_object* v_traceArgs_8062_, lean_object* v_libFile_8063_, uint8_t v_linkDeps_8064_, lean_object* v_libName_8065_, uint8_t v_plugin_8066_, lean_object* v_linkLibs_8067_, lean_object* v___x_8068_, lean_object* v_objs_8069_, lean_object* v___y_8070_, lean_object* v___y_8071_, lean_object* v___y_8072_, lean_object* v___y_8073_, lean_object* v___y_8074_, lean_object* v___y_8075_){
_start:
{
lean_object* v_trace_8077_; lean_object* v___x_8078_; lean_object* v___x_8079_; lean_object* v___f_8080_; lean_object* v___x_8081_; lean_object* v___x_8082_; lean_object* v___x_8083_; uint8_t v___x_8084_; lean_object* v___x_8085_; lean_object* v___x_8086_; 
v_trace_8077_ = lean_ctor_get(v___y_8075_, 1);
v___x_8078_ = lean_box(v_linkDeps_8064_);
v___x_8079_ = lean_box(v_plugin_8066_);
v___f_8080_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__1___boxed), 15, 7);
lean_closure_set(v___f_8080_, 0, v_objs_8069_);
lean_closure_set(v___f_8080_, 1, v_weakArgs_8061_);
lean_closure_set(v___f_8080_, 2, v_traceArgs_8062_);
lean_closure_set(v___f_8080_, 3, v_libFile_8063_);
lean_closure_set(v___f_8080_, 4, v___x_8078_);
lean_closure_set(v___f_8080_, 5, v_libName_8065_);
lean_closure_set(v___f_8080_, 6, v___x_8079_);
v___x_8081_ = ((lean_object*)(l_Lake_buildSharedLib___lam__3___closed__0));
v___x_8082_ = l_Lake_Job_collectArray___redArg(v_linkLibs_8067_, v___x_8081_);
v___x_8083_ = lean_unsigned_to_nat(0u);
v___x_8084_ = 0;
v___x_8085_ = l_Lake_Job_mapM___redArg(v___x_8068_, v___x_8082_, v___f_8080_, v___x_8083_, v___x_8084_, v___y_8070_, v___y_8071_, v___y_8072_, v___y_8073_, v___y_8074_, v_trace_8077_);
v___x_8086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8086_, 0, v___x_8085_);
lean_ctor_set(v___x_8086_, 1, v___y_8075_);
return v___x_8086_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2___boxed(lean_object* v_weakArgs_8087_, lean_object* v_traceArgs_8088_, lean_object* v_libFile_8089_, lean_object* v_linkDeps_8090_, lean_object* v_libName_8091_, lean_object* v_plugin_8092_, lean_object* v_linkLibs_8093_, lean_object* v___x_8094_, lean_object* v_objs_8095_, lean_object* v___y_8096_, lean_object* v___y_8097_, lean_object* v___y_8098_, lean_object* v___y_8099_, lean_object* v___y_8100_, lean_object* v___y_8101_, lean_object* v___y_8102_){
_start:
{
uint8_t v_linkDeps_boxed_8103_; uint8_t v_plugin_boxed_8104_; lean_object* v_res_8105_; 
v_linkDeps_boxed_8103_ = lean_unbox(v_linkDeps_8090_);
v_plugin_boxed_8104_ = lean_unbox(v_plugin_8092_);
v_res_8105_ = l_Lake_buildLeanSharedLib___lam__2(v_weakArgs_8087_, v_traceArgs_8088_, v_libFile_8089_, v_linkDeps_boxed_8103_, v_libName_8091_, v_plugin_boxed_8104_, v_linkLibs_8093_, v___x_8094_, v_objs_8095_, v___y_8096_, v___y_8097_, v___y_8098_, v___y_8099_, v___y_8100_, v___y_8101_);
lean_dec_ref(v___y_8100_);
lean_dec(v___y_8099_);
lean_dec(v___y_8098_);
lean_dec(v___y_8097_);
lean_dec_ref(v_linkLibs_8093_);
return v_res_8105_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object* v_libName_8106_, lean_object* v_libFile_8107_, lean_object* v_linkObjs_8108_, lean_object* v_linkLibs_8109_, lean_object* v_weakArgs_8110_, lean_object* v_traceArgs_8111_, uint8_t v_plugin_8112_, uint8_t v_linkDeps_8113_, lean_object* v_a_8114_, lean_object* v_a_8115_, lean_object* v_a_8116_, lean_object* v_a_8117_, lean_object* v_a_8118_, lean_object* v_a_8119_){
_start:
{
lean_object* v___x_8121_; lean_object* v___x_8122_; lean_object* v___x_8123_; lean_object* v___f_8124_; lean_object* v___x_8125_; lean_object* v___x_8126_; lean_object* v___x_8127_; uint8_t v___x_8128_; lean_object* v___x_8129_; 
v___x_8121_ = l_Lake_instDataKindDynlib;
v___x_8122_ = lean_box(v_linkDeps_8113_);
v___x_8123_ = lean_box(v_plugin_8112_);
v___f_8124_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__2___boxed), 16, 8);
lean_closure_set(v___f_8124_, 0, v_weakArgs_8110_);
lean_closure_set(v___f_8124_, 1, v_traceArgs_8111_);
lean_closure_set(v___f_8124_, 2, v_libFile_8107_);
lean_closure_set(v___f_8124_, 3, v___x_8122_);
lean_closure_set(v___f_8124_, 4, v_libName_8106_);
lean_closure_set(v___f_8124_, 5, v___x_8123_);
lean_closure_set(v___f_8124_, 6, v_linkLibs_8109_);
lean_closure_set(v___f_8124_, 7, v___x_8121_);
v___x_8125_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8126_ = l_Lake_Job_collectArray___redArg(v_linkObjs_8108_, v___x_8125_);
v___x_8127_ = lean_unsigned_to_nat(0u);
v___x_8128_ = 1;
v___x_8129_ = l_Lake_Job_bindM___redArg(v___x_8121_, v___x_8126_, v___f_8124_, v___x_8127_, v___x_8128_, v_a_8114_, v_a_8115_, v_a_8116_, v_a_8117_, v_a_8118_, v_a_8119_);
return v___x_8129_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object* v_libName_8130_, lean_object* v_libFile_8131_, lean_object* v_linkObjs_8132_, lean_object* v_linkLibs_8133_, lean_object* v_weakArgs_8134_, lean_object* v_traceArgs_8135_, lean_object* v_plugin_8136_, lean_object* v_linkDeps_8137_, lean_object* v_a_8138_, lean_object* v_a_8139_, lean_object* v_a_8140_, lean_object* v_a_8141_, lean_object* v_a_8142_, lean_object* v_a_8143_, lean_object* v_a_8144_){
_start:
{
uint8_t v_plugin_boxed_8145_; uint8_t v_linkDeps_boxed_8146_; lean_object* v_res_8147_; 
v_plugin_boxed_8145_ = lean_unbox(v_plugin_8136_);
v_linkDeps_boxed_8146_ = lean_unbox(v_linkDeps_8137_);
v_res_8147_ = l_Lake_buildLeanSharedLib(v_libName_8130_, v_libFile_8131_, v_linkObjs_8132_, v_linkLibs_8133_, v_weakArgs_8134_, v_traceArgs_8135_, v_plugin_boxed_8145_, v_linkDeps_boxed_8146_, v_a_8138_, v_a_8139_, v_a_8140_, v_a_8141_, v_a_8142_, v_a_8143_);
lean_dec_ref(v_a_8143_);
lean_dec_ref(v_a_8142_);
lean_dec(v_a_8141_);
lean_dec(v_a_8140_);
lean_dec(v_a_8139_);
lean_dec_ref(v_linkObjs_8132_);
return v_res_8147_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0(lean_object* v_libs_8148_, lean_object* v_objs_8149_, lean_object* v_weakArgs_8150_, lean_object* v_traceArgs_8151_, uint8_t v_sharedLean_8152_, lean_object* v_exeFile_8153_, lean_object* v___y_8154_, lean_object* v___y_8155_, lean_object* v___y_8156_, lean_object* v___y_8157_, lean_object* v___y_8158_, lean_object* v___y_8159_){
_start:
{
lean_object* v___x_8161_; 
v___x_8161_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(v_libs_8148_, v___y_8159_);
if (lean_obj_tag(v___x_8161_) == 0)
{
lean_object* v_toContext_8162_; lean_object* v_lakeEnv_8163_; lean_object* v_lean_8164_; lean_object* v_a_8165_; lean_object* v_a_8166_; lean_object* v_leanLibDir_8167_; lean_object* v_cc_8168_; lean_object* v_log_8169_; uint8_t v_action_8170_; uint8_t v_wantsRebuild_8171_; lean_object* v_trace_8172_; lean_object* v_buildTime_8173_; lean_object* v___x_8175_; uint8_t v_isShared_8176_; uint8_t v_isSharedCheck_8212_; 
v_toContext_8162_ = lean_ctor_get(v___y_8158_, 1);
v_lakeEnv_8163_ = lean_ctor_get(v_toContext_8162_, 0);
v_lean_8164_ = lean_ctor_get(v_lakeEnv_8163_, 1);
v_a_8165_ = lean_ctor_get(v___x_8161_, 1);
lean_inc(v_a_8165_);
v_a_8166_ = lean_ctor_get(v___x_8161_, 0);
lean_inc(v_a_8166_);
lean_dec_ref(v___x_8161_);
v_leanLibDir_8167_ = lean_ctor_get(v_lean_8164_, 3);
v_cc_8168_ = lean_ctor_get(v_lean_8164_, 14);
v_log_8169_ = lean_ctor_get(v_a_8165_, 0);
v_action_8170_ = lean_ctor_get_uint8(v_a_8165_, sizeof(void*)*3);
v_wantsRebuild_8171_ = lean_ctor_get_uint8(v_a_8165_, sizeof(void*)*3 + 1);
v_trace_8172_ = lean_ctor_get(v_a_8165_, 1);
v_buildTime_8173_ = lean_ctor_get(v_a_8165_, 2);
v_isSharedCheck_8212_ = !lean_is_exclusive(v_a_8165_);
if (v_isSharedCheck_8212_ == 0)
{
v___x_8175_ = v_a_8165_;
v_isShared_8176_ = v_isSharedCheck_8212_;
goto v_resetjp_8174_;
}
else
{
lean_inc(v_buildTime_8173_);
lean_inc(v_trace_8172_);
lean_inc(v_log_8169_);
lean_dec(v_a_8165_);
v___x_8175_ = lean_box(0);
v_isShared_8176_ = v_isSharedCheck_8212_;
goto v_resetjp_8174_;
}
v_resetjp_8174_:
{
lean_object* v___x_8177_; lean_object* v___x_8178_; lean_object* v___x_8179_; lean_object* v___x_8180_; lean_object* v___x_8181_; lean_object* v___x_8182_; lean_object* v___x_8183_; lean_object* v___x_8184_; lean_object* v___x_8185_; lean_object* v___x_8186_; lean_object* v___x_8187_; 
v___x_8177_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_8149_, v_a_8166_);
lean_dec(v_a_8166_);
v___x_8178_ = l_Array_append___redArg(v___x_8177_, v_weakArgs_8150_);
v___x_8179_ = l_Array_append___redArg(v___x_8178_, v_traceArgs_8151_);
v___x_8180_ = lean_unsigned_to_nat(2u);
v___x_8181_ = lean_mk_empty_array_with_capacity(v___x_8180_);
lean_dec_ref(v___x_8181_);
v___x_8182_ = lean_obj_once(&l_Lake_buildLeanSharedLib___lam__0___closed__0, &l_Lake_buildLeanSharedLib___lam__0___closed__0_once, _init_l_Lake_buildLeanSharedLib___lam__0___closed__0);
lean_inc_ref(v_leanLibDir_8167_);
v___x_8183_ = lean_array_push(v___x_8182_, v_leanLibDir_8167_);
v___x_8184_ = l_Array_append___redArg(v___x_8179_, v___x_8183_);
lean_dec_ref(v___x_8183_);
v___x_8185_ = l_Lake_LeanInstall_ccLinkFlags(v_sharedLean_8152_, v_lean_8164_);
v___x_8186_ = l_Array_append___redArg(v___x_8184_, v___x_8185_);
lean_dec_ref(v___x_8185_);
lean_inc_ref(v_cc_8168_);
v___x_8187_ = l_Lake_compileExe(v_exeFile_8153_, v___x_8186_, v_cc_8168_, v_log_8169_);
lean_dec_ref(v___x_8186_);
if (lean_obj_tag(v___x_8187_) == 0)
{
lean_object* v_a_8188_; lean_object* v_a_8189_; lean_object* v___x_8191_; uint8_t v_isShared_8192_; uint8_t v_isSharedCheck_8199_; 
v_a_8188_ = lean_ctor_get(v___x_8187_, 0);
v_a_8189_ = lean_ctor_get(v___x_8187_, 1);
v_isSharedCheck_8199_ = !lean_is_exclusive(v___x_8187_);
if (v_isSharedCheck_8199_ == 0)
{
v___x_8191_ = v___x_8187_;
v_isShared_8192_ = v_isSharedCheck_8199_;
goto v_resetjp_8190_;
}
else
{
lean_inc(v_a_8189_);
lean_inc(v_a_8188_);
lean_dec(v___x_8187_);
v___x_8191_ = lean_box(0);
v_isShared_8192_ = v_isSharedCheck_8199_;
goto v_resetjp_8190_;
}
v_resetjp_8190_:
{
lean_object* v___x_8194_; 
if (v_isShared_8176_ == 0)
{
lean_ctor_set(v___x_8175_, 0, v_a_8189_);
v___x_8194_ = v___x_8175_;
goto v_reusejp_8193_;
}
else
{
lean_object* v_reuseFailAlloc_8198_; 
v_reuseFailAlloc_8198_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8198_, 0, v_a_8189_);
lean_ctor_set(v_reuseFailAlloc_8198_, 1, v_trace_8172_);
lean_ctor_set(v_reuseFailAlloc_8198_, 2, v_buildTime_8173_);
lean_ctor_set_uint8(v_reuseFailAlloc_8198_, sizeof(void*)*3, v_action_8170_);
lean_ctor_set_uint8(v_reuseFailAlloc_8198_, sizeof(void*)*3 + 1, v_wantsRebuild_8171_);
v___x_8194_ = v_reuseFailAlloc_8198_;
goto v_reusejp_8193_;
}
v_reusejp_8193_:
{
lean_object* v___x_8196_; 
if (v_isShared_8192_ == 0)
{
lean_ctor_set(v___x_8191_, 1, v___x_8194_);
v___x_8196_ = v___x_8191_;
goto v_reusejp_8195_;
}
else
{
lean_object* v_reuseFailAlloc_8197_; 
v_reuseFailAlloc_8197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8197_, 0, v_a_8188_);
lean_ctor_set(v_reuseFailAlloc_8197_, 1, v___x_8194_);
v___x_8196_ = v_reuseFailAlloc_8197_;
goto v_reusejp_8195_;
}
v_reusejp_8195_:
{
return v___x_8196_;
}
}
}
}
else
{
lean_object* v_a_8200_; lean_object* v_a_8201_; lean_object* v___x_8203_; uint8_t v_isShared_8204_; uint8_t v_isSharedCheck_8211_; 
v_a_8200_ = lean_ctor_get(v___x_8187_, 0);
v_a_8201_ = lean_ctor_get(v___x_8187_, 1);
v_isSharedCheck_8211_ = !lean_is_exclusive(v___x_8187_);
if (v_isSharedCheck_8211_ == 0)
{
v___x_8203_ = v___x_8187_;
v_isShared_8204_ = v_isSharedCheck_8211_;
goto v_resetjp_8202_;
}
else
{
lean_inc(v_a_8201_);
lean_inc(v_a_8200_);
lean_dec(v___x_8187_);
v___x_8203_ = lean_box(0);
v_isShared_8204_ = v_isSharedCheck_8211_;
goto v_resetjp_8202_;
}
v_resetjp_8202_:
{
lean_object* v___x_8206_; 
if (v_isShared_8176_ == 0)
{
lean_ctor_set(v___x_8175_, 0, v_a_8201_);
v___x_8206_ = v___x_8175_;
goto v_reusejp_8205_;
}
else
{
lean_object* v_reuseFailAlloc_8210_; 
v_reuseFailAlloc_8210_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8210_, 0, v_a_8201_);
lean_ctor_set(v_reuseFailAlloc_8210_, 1, v_trace_8172_);
lean_ctor_set(v_reuseFailAlloc_8210_, 2, v_buildTime_8173_);
lean_ctor_set_uint8(v_reuseFailAlloc_8210_, sizeof(void*)*3, v_action_8170_);
lean_ctor_set_uint8(v_reuseFailAlloc_8210_, sizeof(void*)*3 + 1, v_wantsRebuild_8171_);
v___x_8206_ = v_reuseFailAlloc_8210_;
goto v_reusejp_8205_;
}
v_reusejp_8205_:
{
lean_object* v___x_8208_; 
if (v_isShared_8204_ == 0)
{
lean_ctor_set(v___x_8203_, 1, v___x_8206_);
v___x_8208_ = v___x_8203_;
goto v_reusejp_8207_;
}
else
{
lean_object* v_reuseFailAlloc_8209_; 
v_reuseFailAlloc_8209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8209_, 0, v_a_8200_);
lean_ctor_set(v_reuseFailAlloc_8209_, 1, v___x_8206_);
v___x_8208_ = v_reuseFailAlloc_8209_;
goto v_reusejp_8207_;
}
v_reusejp_8207_:
{
return v___x_8208_;
}
}
}
}
}
}
else
{
lean_object* v_a_8213_; lean_object* v_a_8214_; lean_object* v___x_8216_; uint8_t v_isShared_8217_; uint8_t v_isSharedCheck_8221_; 
lean_dec_ref(v_exeFile_8153_);
v_a_8213_ = lean_ctor_get(v___x_8161_, 0);
v_a_8214_ = lean_ctor_get(v___x_8161_, 1);
v_isSharedCheck_8221_ = !lean_is_exclusive(v___x_8161_);
if (v_isSharedCheck_8221_ == 0)
{
v___x_8216_ = v___x_8161_;
v_isShared_8217_ = v_isSharedCheck_8221_;
goto v_resetjp_8215_;
}
else
{
lean_inc(v_a_8214_);
lean_inc(v_a_8213_);
lean_dec(v___x_8161_);
v___x_8216_ = lean_box(0);
v_isShared_8217_ = v_isSharedCheck_8221_;
goto v_resetjp_8215_;
}
v_resetjp_8215_:
{
lean_object* v___x_8219_; 
if (v_isShared_8217_ == 0)
{
v___x_8219_ = v___x_8216_;
goto v_reusejp_8218_;
}
else
{
lean_object* v_reuseFailAlloc_8220_; 
v_reuseFailAlloc_8220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8220_, 0, v_a_8213_);
lean_ctor_set(v_reuseFailAlloc_8220_, 1, v_a_8214_);
v___x_8219_ = v_reuseFailAlloc_8220_;
goto v_reusejp_8218_;
}
v_reusejp_8218_:
{
return v___x_8219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object* v_libs_8222_, lean_object* v_objs_8223_, lean_object* v_weakArgs_8224_, lean_object* v_traceArgs_8225_, lean_object* v_sharedLean_8226_, lean_object* v_exeFile_8227_, lean_object* v___y_8228_, lean_object* v___y_8229_, lean_object* v___y_8230_, lean_object* v___y_8231_, lean_object* v___y_8232_, lean_object* v___y_8233_, lean_object* v___y_8234_){
_start:
{
uint8_t v_sharedLean_boxed_8235_; lean_object* v_res_8236_; 
v_sharedLean_boxed_8235_ = lean_unbox(v_sharedLean_8226_);
v_res_8236_ = l_Lake_buildLeanExe___lam__0(v_libs_8222_, v_objs_8223_, v_weakArgs_8224_, v_traceArgs_8225_, v_sharedLean_boxed_8235_, v_exeFile_8227_, v___y_8228_, v___y_8229_, v___y_8230_, v___y_8231_, v___y_8232_, v___y_8233_);
lean_dec_ref(v___y_8232_);
lean_dec(v___y_8231_);
lean_dec(v___y_8230_);
lean_dec(v___y_8229_);
lean_dec_ref(v___y_8228_);
lean_dec_ref(v_traceArgs_8225_);
lean_dec_ref(v_weakArgs_8224_);
lean_dec_ref(v_objs_8223_);
lean_dec_ref(v_libs_8222_);
return v_res_8236_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object* v_objs_8237_, lean_object* v_weakArgs_8238_, lean_object* v_traceArgs_8239_, uint8_t v_sharedLean_8240_, lean_object* v_exeFile_8241_, lean_object* v_libs_8242_, lean_object* v___y_8243_, lean_object* v___y_8244_, lean_object* v___y_8245_, lean_object* v___y_8246_, lean_object* v___y_8247_, lean_object* v___y_8248_){
_start:
{
lean_object* v_log_8250_; uint8_t v_action_8251_; uint8_t v_wantsRebuild_8252_; lean_object* v_trace_8253_; lean_object* v_buildTime_8254_; lean_object* v___x_8256_; uint8_t v_isShared_8257_; uint8_t v_isSharedCheck_8313_; 
v_log_8250_ = lean_ctor_get(v___y_8248_, 0);
v_action_8251_ = lean_ctor_get_uint8(v___y_8248_, sizeof(void*)*3);
v_wantsRebuild_8252_ = lean_ctor_get_uint8(v___y_8248_, sizeof(void*)*3 + 1);
v_trace_8253_ = lean_ctor_get(v___y_8248_, 1);
v_buildTime_8254_ = lean_ctor_get(v___y_8248_, 2);
v_isSharedCheck_8313_ = !lean_is_exclusive(v___y_8248_);
if (v_isSharedCheck_8313_ == 0)
{
v___x_8256_ = v___y_8248_;
v_isShared_8257_ = v_isSharedCheck_8313_;
goto v_resetjp_8255_;
}
else
{
lean_inc(v_buildTime_8254_);
lean_inc(v_trace_8253_);
lean_inc(v_log_8250_);
lean_dec(v___y_8248_);
v___x_8256_ = lean_box(0);
v_isShared_8257_ = v_isSharedCheck_8313_;
goto v_resetjp_8255_;
}
v_resetjp_8255_:
{
lean_object* v_leanTrace_8258_; lean_object* v___x_8259_; lean_object* v___f_8260_; lean_object* v___x_8261_; uint64_t v___y_8263_; uint64_t v___x_8302_; lean_object* v___x_8303_; lean_object* v___x_8304_; uint8_t v___x_8305_; 
v_leanTrace_8258_ = lean_ctor_get(v___y_8247_, 2);
v___x_8259_ = lean_box(v_sharedLean_8240_);
lean_inc_ref(v_exeFile_8241_);
lean_inc_ref(v_traceArgs_8239_);
v___f_8260_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__0___boxed), 13, 6);
lean_closure_set(v___f_8260_, 0, v_libs_8242_);
lean_closure_set(v___f_8260_, 1, v_objs_8237_);
lean_closure_set(v___f_8260_, 2, v_weakArgs_8238_);
lean_closure_set(v___f_8260_, 3, v_traceArgs_8239_);
lean_closure_set(v___f_8260_, 4, v___x_8259_);
lean_closure_set(v___f_8260_, 5, v_exeFile_8241_);
lean_inc_ref(v_leanTrace_8258_);
v___x_8261_ = l_Lake_BuildTrace_mix(v_trace_8253_, v_leanTrace_8258_);
v___x_8302_ = l_Lake_Hash_nil;
v___x_8303_ = lean_unsigned_to_nat(0u);
v___x_8304_ = lean_array_get_size(v_traceArgs_8239_);
v___x_8305_ = lean_nat_dec_lt(v___x_8303_, v___x_8304_);
if (v___x_8305_ == 0)
{
v___y_8263_ = v___x_8302_;
goto v___jp_8262_;
}
else
{
uint8_t v___x_8306_; 
v___x_8306_ = lean_nat_dec_le(v___x_8304_, v___x_8304_);
if (v___x_8306_ == 0)
{
if (v___x_8305_ == 0)
{
v___y_8263_ = v___x_8302_;
goto v___jp_8262_;
}
else
{
size_t v___x_8307_; size_t v___x_8308_; uint64_t v___x_8309_; 
v___x_8307_ = ((size_t)0ULL);
v___x_8308_ = lean_usize_of_nat(v___x_8304_);
v___x_8309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8239_, v___x_8307_, v___x_8308_, v___x_8302_);
v___y_8263_ = v___x_8309_;
goto v___jp_8262_;
}
}
else
{
size_t v___x_8310_; size_t v___x_8311_; uint64_t v___x_8312_; 
v___x_8310_ = ((size_t)0ULL);
v___x_8311_ = lean_usize_of_nat(v___x_8304_);
v___x_8312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(v_traceArgs_8239_, v___x_8310_, v___x_8311_, v___x_8302_);
v___y_8263_ = v___x_8312_;
goto v___jp_8262_;
}
}
v___jp_8262_:
{
lean_object* v___x_8264_; lean_object* v___x_8265_; lean_object* v___x_8266_; lean_object* v___x_8267_; lean_object* v___x_8268_; lean_object* v___x_8269_; lean_object* v___x_8270_; lean_object* v___x_8271_; lean_object* v___x_8272_; lean_object* v___x_8273_; lean_object* v___x_8274_; lean_object* v___x_8275_; lean_object* v___x_8277_; 
v___x_8264_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_8265_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_8266_ = lean_array_to_list(v_traceArgs_8239_);
v___x_8267_ = l_List_toString___at___00Lake_buildLeanO_spec__0(v___x_8266_);
lean_dec(v___x_8266_);
v___x_8268_ = lean_string_append(v___x_8265_, v___x_8267_);
lean_dec_ref(v___x_8267_);
v___x_8269_ = lean_string_append(v___x_8264_, v___x_8268_);
lean_dec_ref(v___x_8268_);
v___x_8270_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_8271_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_8272_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_8272_, 0, v___x_8269_);
lean_ctor_set(v___x_8272_, 1, v___x_8270_);
lean_ctor_set(v___x_8272_, 2, v___x_8271_);
lean_ctor_set_uint64(v___x_8272_, sizeof(void*)*3, v___y_8263_);
v___x_8273_ = l_Lake_BuildTrace_mix(v___x_8261_, v___x_8272_);
v___x_8274_ = l_Lake_platformTrace;
v___x_8275_ = l_Lake_BuildTrace_mix(v___x_8273_, v___x_8274_);
if (v_isShared_8257_ == 0)
{
lean_ctor_set(v___x_8256_, 1, v___x_8275_);
v___x_8277_ = v___x_8256_;
goto v_reusejp_8276_;
}
else
{
lean_object* v_reuseFailAlloc_8301_; 
v_reuseFailAlloc_8301_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8301_, 0, v_log_8250_);
lean_ctor_set(v_reuseFailAlloc_8301_, 1, v___x_8275_);
lean_ctor_set(v_reuseFailAlloc_8301_, 2, v_buildTime_8254_);
lean_ctor_set_uint8(v_reuseFailAlloc_8301_, sizeof(void*)*3, v_action_8251_);
lean_ctor_set_uint8(v_reuseFailAlloc_8301_, sizeof(void*)*3 + 1, v_wantsRebuild_8252_);
v___x_8277_ = v_reuseFailAlloc_8301_;
goto v_reusejp_8276_;
}
v_reusejp_8276_:
{
uint8_t v___x_8278_; lean_object* v___x_8279_; uint8_t v___x_8280_; lean_object* v___x_8281_; 
v___x_8278_ = 0;
v___x_8279_ = l_System_FilePath_exeExtension;
v___x_8280_ = 1;
v___x_8281_ = l_Lake_buildArtifactUnlessUpToDate(v_exeFile_8241_, v___f_8260_, v___x_8278_, v___x_8279_, v___x_8280_, v___x_8280_, v___x_8278_, v___y_8243_, v___y_8244_, v___y_8245_, v___y_8246_, v___y_8247_, v___x_8277_);
if (lean_obj_tag(v___x_8281_) == 0)
{
lean_object* v_a_8282_; lean_object* v_a_8283_; lean_object* v___x_8285_; uint8_t v_isShared_8286_; uint8_t v_isSharedCheck_8291_; 
v_a_8282_ = lean_ctor_get(v___x_8281_, 0);
v_a_8283_ = lean_ctor_get(v___x_8281_, 1);
v_isSharedCheck_8291_ = !lean_is_exclusive(v___x_8281_);
if (v_isSharedCheck_8291_ == 0)
{
v___x_8285_ = v___x_8281_;
v_isShared_8286_ = v_isSharedCheck_8291_;
goto v_resetjp_8284_;
}
else
{
lean_inc(v_a_8283_);
lean_inc(v_a_8282_);
lean_dec(v___x_8281_);
v___x_8285_ = lean_box(0);
v_isShared_8286_ = v_isSharedCheck_8291_;
goto v_resetjp_8284_;
}
v_resetjp_8284_:
{
lean_object* v_path_8287_; lean_object* v___x_8289_; 
v_path_8287_ = lean_ctor_get(v_a_8282_, 1);
lean_inc_ref(v_path_8287_);
lean_dec(v_a_8282_);
if (v_isShared_8286_ == 0)
{
lean_ctor_set(v___x_8285_, 0, v_path_8287_);
v___x_8289_ = v___x_8285_;
goto v_reusejp_8288_;
}
else
{
lean_object* v_reuseFailAlloc_8290_; 
v_reuseFailAlloc_8290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8290_, 0, v_path_8287_);
lean_ctor_set(v_reuseFailAlloc_8290_, 1, v_a_8283_);
v___x_8289_ = v_reuseFailAlloc_8290_;
goto v_reusejp_8288_;
}
v_reusejp_8288_:
{
return v___x_8289_;
}
}
}
else
{
lean_object* v_a_8292_; lean_object* v_a_8293_; lean_object* v___x_8295_; uint8_t v_isShared_8296_; uint8_t v_isSharedCheck_8300_; 
v_a_8292_ = lean_ctor_get(v___x_8281_, 0);
v_a_8293_ = lean_ctor_get(v___x_8281_, 1);
v_isSharedCheck_8300_ = !lean_is_exclusive(v___x_8281_);
if (v_isSharedCheck_8300_ == 0)
{
v___x_8295_ = v___x_8281_;
v_isShared_8296_ = v_isSharedCheck_8300_;
goto v_resetjp_8294_;
}
else
{
lean_inc(v_a_8293_);
lean_inc(v_a_8292_);
lean_dec(v___x_8281_);
v___x_8295_ = lean_box(0);
v_isShared_8296_ = v_isSharedCheck_8300_;
goto v_resetjp_8294_;
}
v_resetjp_8294_:
{
lean_object* v___x_8298_; 
if (v_isShared_8296_ == 0)
{
v___x_8298_ = v___x_8295_;
goto v_reusejp_8297_;
}
else
{
lean_object* v_reuseFailAlloc_8299_; 
v_reuseFailAlloc_8299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8299_, 0, v_a_8292_);
lean_ctor_set(v_reuseFailAlloc_8299_, 1, v_a_8293_);
v___x_8298_ = v_reuseFailAlloc_8299_;
goto v_reusejp_8297_;
}
v_reusejp_8297_:
{
return v___x_8298_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object* v_objs_8314_, lean_object* v_weakArgs_8315_, lean_object* v_traceArgs_8316_, lean_object* v_sharedLean_8317_, lean_object* v_exeFile_8318_, lean_object* v_libs_8319_, lean_object* v___y_8320_, lean_object* v___y_8321_, lean_object* v___y_8322_, lean_object* v___y_8323_, lean_object* v___y_8324_, lean_object* v___y_8325_, lean_object* v___y_8326_){
_start:
{
uint8_t v_sharedLean_boxed_8327_; lean_object* v_res_8328_; 
v_sharedLean_boxed_8327_ = lean_unbox(v_sharedLean_8317_);
v_res_8328_ = l_Lake_buildLeanExe___lam__1(v_objs_8314_, v_weakArgs_8315_, v_traceArgs_8316_, v_sharedLean_boxed_8327_, v_exeFile_8318_, v_libs_8319_, v___y_8320_, v___y_8321_, v___y_8322_, v___y_8323_, v___y_8324_, v___y_8325_);
lean_dec_ref(v___y_8324_);
lean_dec(v___y_8323_);
lean_dec(v___y_8322_);
lean_dec(v___y_8321_);
return v_res_8328_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2(lean_object* v_weakArgs_8329_, lean_object* v_traceArgs_8330_, uint8_t v_sharedLean_8331_, lean_object* v_exeFile_8332_, lean_object* v_linkLibs_8333_, lean_object* v___x_8334_, lean_object* v_objs_8335_, lean_object* v___y_8336_, lean_object* v___y_8337_, lean_object* v___y_8338_, lean_object* v___y_8339_, lean_object* v___y_8340_, lean_object* v___y_8341_){
_start:
{
lean_object* v_trace_8343_; lean_object* v___x_8344_; lean_object* v___f_8345_; lean_object* v___x_8346_; lean_object* v___x_8347_; lean_object* v___x_8348_; uint8_t v___x_8349_; lean_object* v___x_8350_; lean_object* v___x_8351_; 
v_trace_8343_ = lean_ctor_get(v___y_8341_, 1);
v___x_8344_ = lean_box(v_sharedLean_8331_);
v___f_8345_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__1___boxed), 13, 5);
lean_closure_set(v___f_8345_, 0, v_objs_8335_);
lean_closure_set(v___f_8345_, 1, v_weakArgs_8329_);
lean_closure_set(v___f_8345_, 2, v_traceArgs_8330_);
lean_closure_set(v___f_8345_, 3, v___x_8344_);
lean_closure_set(v___f_8345_, 4, v_exeFile_8332_);
v___x_8346_ = ((lean_object*)(l_Lake_buildSharedLib___lam__3___closed__0));
v___x_8347_ = l_Lake_Job_collectArray___redArg(v_linkLibs_8333_, v___x_8346_);
v___x_8348_ = lean_unsigned_to_nat(0u);
v___x_8349_ = 0;
v___x_8350_ = l_Lake_Job_mapM___redArg(v___x_8334_, v___x_8347_, v___f_8345_, v___x_8348_, v___x_8349_, v___y_8336_, v___y_8337_, v___y_8338_, v___y_8339_, v___y_8340_, v_trace_8343_);
v___x_8351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8351_, 0, v___x_8350_);
lean_ctor_set(v___x_8351_, 1, v___y_8341_);
return v___x_8351_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2___boxed(lean_object* v_weakArgs_8352_, lean_object* v_traceArgs_8353_, lean_object* v_sharedLean_8354_, lean_object* v_exeFile_8355_, lean_object* v_linkLibs_8356_, lean_object* v___x_8357_, lean_object* v_objs_8358_, lean_object* v___y_8359_, lean_object* v___y_8360_, lean_object* v___y_8361_, lean_object* v___y_8362_, lean_object* v___y_8363_, lean_object* v___y_8364_, lean_object* v___y_8365_){
_start:
{
uint8_t v_sharedLean_boxed_8366_; lean_object* v_res_8367_; 
v_sharedLean_boxed_8366_ = lean_unbox(v_sharedLean_8354_);
v_res_8367_ = l_Lake_buildLeanExe___lam__2(v_weakArgs_8352_, v_traceArgs_8353_, v_sharedLean_boxed_8366_, v_exeFile_8355_, v_linkLibs_8356_, v___x_8357_, v_objs_8358_, v___y_8359_, v___y_8360_, v___y_8361_, v___y_8362_, v___y_8363_, v___y_8364_);
lean_dec_ref(v___y_8363_);
lean_dec(v___y_8362_);
lean_dec(v___y_8361_);
lean_dec(v___y_8360_);
lean_dec_ref(v_linkLibs_8356_);
return v_res_8367_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object* v_exeFile_8368_, lean_object* v_linkObjs_8369_, lean_object* v_linkLibs_8370_, lean_object* v_weakArgs_8371_, lean_object* v_traceArgs_8372_, uint8_t v_sharedLean_8373_, lean_object* v_a_8374_, lean_object* v_a_8375_, lean_object* v_a_8376_, lean_object* v_a_8377_, lean_object* v_a_8378_, lean_object* v_a_8379_){
_start:
{
lean_object* v___x_8381_; lean_object* v___x_8382_; lean_object* v___f_8383_; lean_object* v___x_8384_; lean_object* v___x_8385_; lean_object* v___x_8386_; uint8_t v___x_8387_; lean_object* v___x_8388_; 
v___x_8381_ = l_Lake_instDataKindFilePath;
v___x_8382_ = lean_box(v_sharedLean_8373_);
v___f_8383_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__2___boxed), 14, 6);
lean_closure_set(v___f_8383_, 0, v_weakArgs_8371_);
lean_closure_set(v___f_8383_, 1, v_traceArgs_8372_);
lean_closure_set(v___f_8383_, 2, v___x_8382_);
lean_closure_set(v___f_8383_, 3, v_exeFile_8368_);
lean_closure_set(v___f_8383_, 4, v_linkLibs_8370_);
lean_closure_set(v___f_8383_, 5, v___x_8381_);
v___x_8384_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8385_ = l_Lake_Job_collectArray___redArg(v_linkObjs_8369_, v___x_8384_);
v___x_8386_ = lean_unsigned_to_nat(0u);
v___x_8387_ = 1;
v___x_8388_ = l_Lake_Job_bindM___redArg(v___x_8381_, v___x_8385_, v___f_8383_, v___x_8386_, v___x_8387_, v_a_8374_, v_a_8375_, v_a_8376_, v_a_8377_, v_a_8378_, v_a_8379_);
return v___x_8388_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object* v_exeFile_8389_, lean_object* v_linkObjs_8390_, lean_object* v_linkLibs_8391_, lean_object* v_weakArgs_8392_, lean_object* v_traceArgs_8393_, lean_object* v_sharedLean_8394_, lean_object* v_a_8395_, lean_object* v_a_8396_, lean_object* v_a_8397_, lean_object* v_a_8398_, lean_object* v_a_8399_, lean_object* v_a_8400_, lean_object* v_a_8401_){
_start:
{
uint8_t v_sharedLean_boxed_8402_; lean_object* v_res_8403_; 
v_sharedLean_boxed_8402_ = lean_unbox(v_sharedLean_8394_);
v_res_8403_ = l_Lake_buildLeanExe(v_exeFile_8389_, v_linkObjs_8390_, v_linkLibs_8391_, v_weakArgs_8392_, v_traceArgs_8393_, v_sharedLean_boxed_8402_, v_a_8395_, v_a_8396_, v_a_8397_, v_a_8398_, v_a_8399_, v_a_8400_);
lean_dec_ref(v_a_8400_);
lean_dec_ref(v_a_8399_);
lean_dec(v_a_8398_);
lean_dec(v_a_8397_);
lean_dec(v_a_8396_);
lean_dec_ref(v_linkObjs_8390_);
return v_res_8403_;
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
