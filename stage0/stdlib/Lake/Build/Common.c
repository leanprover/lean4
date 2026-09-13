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
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
uint8_t lean_string_compare(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lake_compileStaticLib(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* lean_io_hard_link(lean_object*, lean_object*);
lean_object* l_IO_setAccessRights(lean_object*, lean_object*);
lean_object* l_Lake_copyFile(lean_object*, lean_object*);
lean_object* l_Lake_JsonObject_insertJson(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instToJsonLogEntry_toJson(lean_object*);
uint8_t l_Lake_JobAction_merge(uint8_t, uint8_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* l_Lake_removeFileIfExists(lean_object*);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
lean_object* l_Lake_ArtifactDescr_fromJson_x3f(lean_object*);
lean_object* l_Lean_Json_render(lean_object*);
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lake_CacheService_artifactUrl(uint64_t, lean_object*, lean_object*);
lean_object* l_Lake_downloadArtifactCore(uint64_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_cacheScope(lean_object*);
lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_Lake_Cache_readOutputs_x3f(lean_object*, lean_object*, uint64_t, lean_object*);
uint8_t l_IO_FS_instOrdSystemTime_ord(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*);
uint64_t lean_byte_array_hash(lean_object*);
lean_object* l_Lake_writeBinFileIfNew(lean_object*, lean_object*);
lean_object* l_String_crlfToLf(lean_object*);
lean_object* l_Lake_writeFileIfNew(lean_object*, lean_object*);
lean_object* l_Lake_computeBinFileHash(lean_object*);
lean_object* l_Lake_computeTextFileHash(lean_object*);
lean_object* l_Lake_Hash_load_x3f(lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now();
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindFilePath;
lean_object* l_Lake_Job_collectArray___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Job_mapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instDecidableEqHash___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_MTime_checkUpToDate___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Lake_sharedLibExt;
lean_object* l_Lake_Dynlib_dir_x3f(lean_object*);
lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* l_Lake_compileO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t, lean_object*);
lean_object* l_Lake_Job_async___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
lean_object* l_System_FilePath_walkDir(lean_object*, lean_object*);
extern lean_object* l_System_FilePath_exeExtension;
lean_object* l_Lake_compileExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lake_Job_bindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Prod_toJson___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(lean_object*);
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
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___boxed(lean_object*);
static const lean_string_object l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected pair, got '"};
static const lean_object* l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0 = (const lean_object*)&l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0_value;
static const lean_string_object l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__1 = (const lean_object*)&l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2(lean_object*);
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
static lean_once_cell_t l_Lake_OutputStatus_isUpToDate___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OutputStatus_isUpToDate___closed__0;
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isUpToDate(uint8_t);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isUpToDate___boxed(lean_object*);
static lean_once_cell_t l_Lake_OutputStatus_isCacheable___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OutputStatus_isCacheable___closed__0;
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
static const lean_closure_object l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0_value;
static const lean_string_object l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "input '"};
static const lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "' found in package artifact cache, but some output(s) have issues:"};
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
static const lean_string_object l_Lake_resolveArtifact___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "download succeeded, but artifact failed to resolve: "};
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
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(uint8_t, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(uint8_t, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(lean_object*, uint8_t, uint64_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, uint64_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_inputDir___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_inputDir___lam__2___closed__0 = (const lean_object*)&l_Lake_inputDir___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lake_Internal_buildLeanO___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-I"};
static const lean_object* l_Lake_Internal_buildLeanO___lam__0___closed__0 = (const lean_object*)&l_Lake_Internal_buildLeanO___lam__0___closed__0_value;
static lean_once_cell_t l_Lake_Internal_buildLeanO___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Internal_buildLeanO___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lake_Internal_buildLeanO___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Internal_buildLeanO___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_foldl___at___00List_toString___at___00Lake_Internal_buildLeanO_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_foldl___at___00List_toString___at___00Lake_Internal_buildLeanO_spec__0_spec__0___closed__0 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00Lake_Internal_buildLeanO_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_Internal_buildLeanO_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_Internal_buildLeanO_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00Lake_Internal_buildLeanO_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00Lake_Internal_buildLeanO_spec__0___closed__0 = (const lean_object*)&l_List_toString___at___00Lake_Internal_buildLeanO_spec__0___closed__0_value;
static const lean_string_object l_List_toString___at___00Lake_Internal_buildLeanO_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00Lake_Internal_buildLeanO_spec__0___closed__1 = (const lean_object*)&l_List_toString___at___00Lake_Internal_buildLeanO_spec__0___closed__1_value;
static const lean_string_object l_List_toString___at___00Lake_Internal_buildLeanO_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___at___00Lake_Internal_buildLeanO_spec__0___closed__2 = (const lean_object*)&l_List_toString___at___00Lake_Internal_buildLeanO_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_Internal_buildLeanO_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_Internal_buildLeanO_spec__0___boxed(lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Internal_buildLeanO_spec__1(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Internal_buildLeanO_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Internal_buildLeanO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Internal_buildLeanO___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Internal_buildLeanO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Internal_buildLeanO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "  "};
static const lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0_spec__0___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_mkLinkOrder___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "library dependency cycle:\n"};
static const lean_object* l_Lake_mkLinkOrder___redArg___closed__0 = (const lean_object*)&l_Lake_mkLinkOrder___redArg___closed__0_value;
static const lean_array_object l_Lake_mkLinkOrder___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_mkLinkOrder___redArg___closed__1 = (const lean_object*)&l_Lake_mkLinkOrder___redArg___closed__1_value;
static const lean_ctor_object l_Lake_mkLinkOrder___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lake_mkLinkOrder___redArg___closed__1_value)}};
static const lean_object* l_Lake_mkLinkOrder___redArg___closed__2 = (const lean_object*)&l_Lake_mkLinkOrder___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildSharedLibSync___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "MACOSX_DEPLOYMENT_TARGET: "};
static const lean_object* l_Lake_buildSharedLibSync___closed__0 = (const lean_object*)&l_Lake_buildSharedLibSync___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object**);
static const lean_string_object l_Lake_buildSharedLib___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "linkLibs"};
static const lean_object* l_Lake_buildSharedLib___lam__1___closed__0 = (const lean_object*)&l_Lake_buildSharedLib___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1___boxed(lean_object**);
static const lean_string_object l_Lake_buildSharedLib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "linkObjs"};
static const lean_object* l_Lake_buildSharedLib___closed__0 = (const lean_object*)&l_Lake_buildSharedLib___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_buildSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_80_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___x_80_, 0, lean_box(0));
lean_closure_set(v___x_80_, 1, v___x_79_);
lean_inc_ref(v___x_75_);
v___x_81_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v___x_80_, v___x_75_);
v___x_82_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v___x_81_, v___x_75_);
v___x_83_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___redArg___lam__0___boxed), 3, 2);
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
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(lean_object* v_x_321_){
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
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1___boxed(lean_object* v_x_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(v_x_324_);
lean_dec(v_x_324_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(size_t v_sz_326_, size_t v_i_327_, lean_object* v_bs_328_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = lean_usize_dec_lt(v_i_327_, v_sz_326_);
if (v___x_329_ == 0)
{
return v_bs_328_;
}
else
{
lean_object* v_v_330_; lean_object* v___x_331_; lean_object* v_bs_x27_332_; lean_object* v___x_333_; size_t v___x_334_; size_t v___x_335_; lean_object* v___x_336_; 
v_v_330_ = lean_array_uget(v_bs_328_, v_i_327_);
v___x_331_ = lean_unsigned_to_nat(0u);
v_bs_x27_332_ = lean_array_uset(v_bs_328_, v_i_327_, v___x_331_);
v___x_333_ = l_Lake_instToJsonLogEntry_toJson(v_v_330_);
lean_dec(v_v_330_);
v___x_334_ = ((size_t)1ULL);
v___x_335_ = lean_usize_add(v_i_327_, v___x_334_);
v___x_336_ = lean_array_uset(v_bs_x27_332_, v_i_327_, v___x_333_);
v_i_327_ = v___x_335_;
v_bs_328_ = v___x_336_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4___boxed(lean_object* v_sz_338_, lean_object* v_i_339_, lean_object* v_bs_340_){
_start:
{
size_t v_sz_boxed_341_; size_t v_i_boxed_342_; lean_object* v_res_343_; 
v_sz_boxed_341_ = lean_unbox_usize(v_sz_338_);
lean_dec(v_sz_338_);
v_i_boxed_342_ = lean_unbox_usize(v_i_339_);
lean_dec(v_i_339_);
v_res_343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(v_sz_boxed_341_, v_i_boxed_342_, v_bs_340_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2(lean_object* v_a_344_){
_start:
{
size_t v_sz_345_; size_t v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_sz_345_ = lean_array_size(v_a_344_);
v___x_346_ = ((size_t)0ULL);
v___x_347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(v_sz_345_, v___x_346_, v_a_344_);
v___x_348_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Prod_toJson___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0(lean_object* v_x_349_){
_start:
{
lean_object* v_fst_350_; lean_object* v_snd_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v_fst_350_ = lean_ctor_get(v_x_349_, 0);
lean_inc(v_fst_350_);
v_snd_351_ = lean_ctor_get(v_x_349_, 1);
lean_inc(v_snd_351_);
lean_dec_ref(v_x_349_);
v___x_352_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_352_, 0, v_fst_350_);
v___x_353_ = lean_unsigned_to_nat(2u);
v___x_354_ = lean_mk_empty_array_with_capacity(v___x_353_);
v___x_355_ = lean_array_push(v___x_354_, v___x_352_);
v___x_356_ = lean_array_push(v___x_355_, v_snd_351_);
v___x_357_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(size_t v_sz_358_, size_t v_i_359_, lean_object* v_bs_360_){
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
v___x_365_ = l_Lean_Prod_toJson___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0(v_v_362_);
v___x_366_ = ((size_t)1ULL);
v___x_367_ = lean_usize_add(v_i_359_, v___x_366_);
v___x_368_ = lean_array_uset(v_bs_x27_364_, v_i_359_, v___x_365_);
v_i_359_ = v___x_367_;
v_bs_360_ = v___x_368_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1___boxed(lean_object* v_sz_370_, lean_object* v_i_371_, lean_object* v_bs_372_){
_start:
{
size_t v_sz_boxed_373_; size_t v_i_boxed_374_; lean_object* v_res_375_; 
v_sz_boxed_373_ = lean_unbox_usize(v_sz_370_);
lean_dec(v_sz_370_);
v_i_boxed_374_ = lean_unbox_usize(v_i_371_);
lean_dec(v_i_371_);
v_res_375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(v_sz_boxed_373_, v_i_boxed_374_, v_bs_372_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(lean_object* v_a_376_){
_start:
{
size_t v_sz_377_; size_t v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_sz_377_ = lean_array_size(v_a_376_);
v___x_378_ = ((size_t)0ULL);
v___x_379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(v_sz_377_, v___x_378_, v_a_376_);
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
v___x_405_ = l_Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(v_inputs_395_);
v___x_406_ = l_Lake_JsonObject_insertJson(v___x_403_, v___x_404_, v___x_405_);
v___x_407_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__5));
v___x_408_ = l_Lean_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(v_outputs_x3f_396_);
lean_dec(v_outputs_x3f_396_);
v___x_409_ = l_Lake_JsonObject_insertJson(v___x_406_, v___x_407_, v___x_408_);
v___x_410_ = ((lean_object*)(l_Lake_BuildMetadata_toJson___closed__6));
v___x_411_ = l_Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2(v_log_397_);
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
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(lean_object* v_x_431_){
_start:
{
if (lean_obj_tag(v_x_431_) == 0)
{
lean_object* v___x_432_; 
v___x_432_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0));
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
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___boxed(lean_object* v_x_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(v_x_451_);
lean_dec(v_x_451_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7(lean_object* v_x_455_){
_start:
{
lean_object* v_j_457_; 
if (lean_obj_tag(v_x_455_) == 4)
{
lean_object* v_elems_465_; lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v_elems_465_ = lean_ctor_get(v_x_455_, 0);
v___x_466_ = lean_array_get_size(v_elems_465_);
v___x_467_ = lean_unsigned_to_nat(2u);
v___x_468_ = lean_nat_dec_eq(v___x_466_, v___x_467_);
if (v___x_468_ == 0)
{
v_j_457_ = v_x_455_;
goto v___jp_456_;
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
lean_inc_ref(v_elems_465_);
lean_dec_ref_known(v_x_455_, 1);
v___x_469_ = lean_unsigned_to_nat(0u);
v___x_470_ = lean_array_fget_borrowed(v_elems_465_, v___x_469_);
lean_inc(v___x_470_);
v___x_471_ = l_Lean_Json_getStr_x3f(v___x_470_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec_ref(v_elems_465_);
v_a_472_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_471_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_471_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_490_; 
v_a_480_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_490_ == 0)
{
v___x_482_ = v___x_471_;
v_isShared_483_ = v_isSharedCheck_490_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_471_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_490_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = lean_array_fget(v_elems_465_, v___x_484_);
lean_dec_ref(v_elems_465_);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v_a_480_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_486_);
v___x_488_ = v___x_482_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
else
{
v_j_457_ = v_x_455_;
goto v___jp_456_;
}
v___jp_456_:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_458_ = ((lean_object*)(l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0));
v___x_459_ = lean_unsigned_to_nat(80u);
v___x_460_ = l_Lean_Json_pretty(v_j_457_, v___x_459_);
v___x_461_ = lean_string_append(v___x_458_, v___x_460_);
lean_dec_ref(v___x_460_);
v___x_462_ = ((lean_object*)(l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__1));
v___x_463_ = lean_string_append(v___x_461_, v___x_462_);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(size_t v_sz_491_, size_t v_i_492_, lean_object* v_bs_493_){
_start:
{
uint8_t v___x_494_; 
v___x_494_ = lean_usize_dec_lt(v_i_492_, v_sz_491_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; 
v___x_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_495_, 0, v_bs_493_);
return v___x_495_;
}
else
{
lean_object* v_v_496_; lean_object* v___x_497_; 
v_v_496_ = lean_array_uget_borrowed(v_bs_493_, v_i_492_);
lean_inc(v_v_496_);
v___x_497_ = l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7(v_v_496_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_dec_ref(v_bs_493_);
v_a_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
else
{
lean_object* v_a_506_; lean_object* v___x_507_; lean_object* v_bs_x27_508_; size_t v___x_509_; size_t v___x_510_; lean_object* v___x_511_; 
v_a_506_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_506_);
lean_dec_ref_known(v___x_497_, 1);
v___x_507_ = lean_unsigned_to_nat(0u);
v_bs_x27_508_ = lean_array_uset(v_bs_493_, v_i_492_, v___x_507_);
v___x_509_ = ((size_t)1ULL);
v___x_510_ = lean_usize_add(v_i_492_, v___x_509_);
v___x_511_ = lean_array_uset(v_bs_x27_508_, v_i_492_, v_a_506_);
v_i_492_ = v___x_510_;
v_bs_493_ = v___x_511_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8___boxed(lean_object* v_sz_513_, lean_object* v_i_514_, lean_object* v_bs_515_){
_start:
{
size_t v_sz_boxed_516_; size_t v_i_boxed_517_; lean_object* v_res_518_; 
v_sz_boxed_516_ = lean_unbox_usize(v_sz_513_);
lean_dec(v_sz_513_);
v_i_boxed_517_ = lean_unbox_usize(v_i_514_);
lean_dec(v_i_514_);
v_res_518_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(v_sz_boxed_516_, v_i_boxed_517_, v_bs_515_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5(lean_object* v_x_520_){
_start:
{
if (lean_obj_tag(v_x_520_) == 4)
{
lean_object* v_elems_521_; size_t v_sz_522_; size_t v___x_523_; lean_object* v___x_524_; 
v_elems_521_ = lean_ctor_get(v_x_520_, 0);
lean_inc_ref(v_elems_521_);
lean_dec_ref_known(v_x_520_, 1);
v_sz_522_ = lean_array_size(v_elems_521_);
v___x_523_ = ((size_t)0ULL);
v___x_524_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(v_sz_522_, v___x_523_, v_elems_521_);
return v___x_524_;
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_525_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5___closed__0));
v___x_526_ = lean_unsigned_to_nat(80u);
v___x_527_ = l_Lean_Json_pretty(v_x_520_, v___x_526_);
v___x_528_ = lean_string_append(v___x_525_, v___x_527_);
lean_dec_ref(v___x_527_);
v___x_529_ = ((lean_object*)(l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__1));
v___x_530_ = lean_string_append(v___x_528_, v___x_529_);
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3(lean_object* v_x_534_){
_start:
{
if (lean_obj_tag(v_x_534_) == 0)
{
lean_object* v___x_535_; 
v___x_535_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0));
return v___x_535_;
}
else
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5(v_x_534_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_536_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_536_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_553_; 
v_a_545_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_553_ == 0)
{
v___x_547_ = v___x_536_;
v_isShared_548_ = v_isSharedCheck_553_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_536_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_553_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_549_, 0, v_a_545_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v___x_549_);
v___x_551_ = v___x_547_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(size_t v_sz_554_, size_t v_i_555_, lean_object* v_bs_556_){
_start:
{
uint8_t v___x_557_; 
v___x_557_ = lean_usize_dec_lt(v_i_555_, v_sz_554_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
v___x_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_558_, 0, v_bs_556_);
return v___x_558_;
}
else
{
lean_object* v_v_559_; lean_object* v___x_560_; 
v_v_559_ = lean_array_uget_borrowed(v_bs_556_, v_i_555_);
lean_inc(v_v_559_);
v___x_560_ = l_Lake_instFromJsonLogEntry_fromJson(v_v_559_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_dec_ref(v_bs_556_);
v_a_561_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_560_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_560_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
else
{
lean_object* v_a_569_; lean_object* v___x_570_; lean_object* v_bs_x27_571_; size_t v___x_572_; size_t v___x_573_; lean_object* v___x_574_; 
v_a_569_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_a_569_);
lean_dec_ref_known(v___x_560_, 1);
v___x_570_ = lean_unsigned_to_nat(0u);
v_bs_x27_571_ = lean_array_uset(v_bs_556_, v_i_555_, v___x_570_);
v___x_572_ = ((size_t)1ULL);
v___x_573_ = lean_usize_add(v_i_555_, v___x_572_);
v___x_574_ = lean_array_uset(v_bs_x27_571_, v_i_555_, v_a_569_);
v_i_555_ = v___x_573_;
v_bs_556_ = v___x_574_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_576_, lean_object* v_i_577_, lean_object* v_bs_578_){
_start:
{
size_t v_sz_boxed_579_; size_t v_i_boxed_580_; lean_object* v_res_581_; 
v_sz_boxed_579_ = lean_unbox_usize(v_sz_576_);
lean_dec(v_sz_576_);
v_i_boxed_580_ = lean_unbox_usize(v_i_577_);
lean_dec(v_i_577_);
v_res_581_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(v_sz_boxed_579_, v_i_boxed_580_, v_bs_578_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(lean_object* v_x_582_){
_start:
{
if (lean_obj_tag(v_x_582_) == 4)
{
lean_object* v_elems_583_; size_t v_sz_584_; size_t v___x_585_; lean_object* v___x_586_; 
v_elems_583_ = lean_ctor_get(v_x_582_, 0);
lean_inc_ref(v_elems_583_);
lean_dec_ref_known(v_x_582_, 1);
v_sz_584_ = lean_array_size(v_elems_583_);
v___x_585_ = ((size_t)0ULL);
v___x_586_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(v_sz_584_, v___x_585_, v_elems_583_);
return v___x_586_;
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_587_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5___closed__0));
v___x_588_ = lean_unsigned_to_nat(80u);
v___x_589_ = l_Lean_Json_pretty(v_x_582_, v___x_588_);
v___x_590_ = lean_string_append(v___x_587_, v___x_589_);
lean_dec_ref(v___x_589_);
v___x_591_ = ((lean_object*)(l_Lean_Prod_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__1));
v___x_592_ = lean_string_append(v___x_590_, v___x_591_);
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1(lean_object* v_x_596_){
_start:
{
if (lean_obj_tag(v_x_596_) == 0)
{
lean_object* v___x_597_; 
v___x_597_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0));
return v___x_597_;
}
else
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(v_x_596_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_598_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_615_; 
v_a_607_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_615_ == 0)
{
v___x_609_ = v___x_598_;
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_598_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_611_, 0, v_a_607_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_611_);
v___x_613_ = v___x_609_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3(lean_object* v_x_618_){
_start:
{
if (lean_obj_tag(v_x_618_) == 0)
{
lean_object* v___x_619_; 
v___x_619_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0));
return v___x_619_;
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_620_, 0, v_x_618_);
v___x_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2(lean_object* v_x_624_){
_start:
{
if (lean_obj_tag(v_x_624_) == 0)
{
lean_object* v___x_625_; 
v___x_625_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0));
return v___x_625_;
}
else
{
lean_object* v___x_626_; lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_635_; 
v___x_626_ = l_Lean_Option_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3(v_x_624_);
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_635_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_635_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_626_);
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
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f(lean_object* v_obj_651_){
_start:
{
lean_object* v___y_653_; lean_object* v___y_654_; uint64_t v___y_655_; lean_object* v___y_656_; uint8_t v_a_657_; lean_object* v___y_661_; lean_object* v___y_662_; uint64_t v___y_663_; lean_object* v___y_664_; lean_object* v___y_667_; lean_object* v___y_668_; uint64_t v___y_669_; lean_object* v_a_670_; lean_object* v___y_697_; lean_object* v___y_698_; uint64_t v___y_699_; lean_object* v___y_702_; uint64_t v___y_703_; lean_object* v_a_704_; lean_object* v___y_730_; uint64_t v___y_731_; uint64_t v___y_734_; lean_object* v_a_735_; uint64_t v___y_761_; uint64_t v_depHash_764_; lean_object* v___x_789_; lean_object* v___x_790_; 
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
lean_dec_ref_known(v___x_792_, 1);
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
lean_dec_ref_known(v___x_795_, 1);
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
lean_dec_ref_known(v___x_815_, 1);
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
lean_dec_ref_known(v___x_790_, 1);
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
lean_dec_ref_known(v___x_820_, 1);
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
lean_dec_ref_known(v___x_823_, 1);
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
lean_ctor_set(v___x_658_, 1, v___y_653_);
lean_ctor_set(v___x_658_, 2, v___y_656_);
lean_ctor_set_uint64(v___x_658_, sizeof(void*)*3, v___y_655_);
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
lean_dec_ref_known(v___x_672_, 1);
v___x_674_ = l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(v_val_673_);
lean_dec(v_val_673_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_684_; 
lean_dec_ref(v_a_670_);
lean_dec_ref(v___y_668_);
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
lean_dec_ref(v___y_668_);
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
lean_dec_ref_known(v___x_674_, 1);
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
lean_dec_ref_known(v_a_693_, 1);
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
lean_dec_ref_known(v___x_706_, 1);
v___x_708_ = l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1(v_val_707_);
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
lean_dec_ref_known(v___x_708_, 1);
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
lean_dec_ref_known(v_a_727_, 1);
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
v___y_730_ = v_a_735_;
v___y_731_ = v___y_734_;
goto v___jp_729_;
}
else
{
lean_object* v_val_738_; lean_object* v___x_739_; 
v_val_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_val_738_);
lean_dec_ref_known(v___x_737_, 1);
v___x_739_ = l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2(v_val_738_);
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
lean_dec_ref_known(v___x_739_, 1);
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
lean_dec_ref_known(v_a_758_, 1);
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
lean_dec_ref_known(v___x_766_, 1);
v___x_768_ = l_Lean_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3(v_val_767_);
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
lean_dec_ref_known(v___x_768_, 1);
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
lean_dec_ref_known(v_a_787_, 1);
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
lean_dec_ref_known(v___x_888_, 1);
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
lean_dec_ref_known(v___x_909_, 1);
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
v___x_950_ = l_Lean_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(v___x_949_);
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
lean_dec_ref_known(v_t_1017_, 1);
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
lean_dec_ref_known(v___x_1061_, 1);
v___x_1073_ = l_Lean_Json_parse(v_a_1062_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v___x_1073_, 1);
v_a_1064_ = v_a_1074_;
goto v___jp_1063_;
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1076_; 
v_a_1075_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1075_);
lean_dec_ref_known(v___x_1073_, 1);
v___x_1076_ = l_Lake_BuildMetadata_fromJson_x3f(v_a_1075_);
lean_dec(v_a_1075_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref_known(v___x_1076_, 1);
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
lean_dec_ref_known(v___x_1061_, 1);
if (lean_obj_tag(v_a_1087_) == 11)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_dec_ref_known(v_a_1087_, 2);
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
lean_dec_ref_known(v___x_1106_, 1);
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
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg(lean_object* v_k_1168_){
_start:
{
lean_inc(v_k_1168_);
return v_k_1168_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg___boxed(lean_object* v_k_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lake_OutputStatus_ctorElim___redArg(v_k_1169_);
lean_dec(v_k_1169_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim(lean_object* v_motive_1171_, lean_object* v_ctorIdx_1172_, uint8_t v_t_1173_, lean_object* v_h_1174_, lean_object* v_k_1175_){
_start:
{
lean_inc(v_k_1175_);
return v_k_1175_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___boxed(lean_object* v_motive_1176_, lean_object* v_ctorIdx_1177_, lean_object* v_t_1178_, lean_object* v_h_1179_, lean_object* v_k_1180_){
_start:
{
uint8_t v_t_boxed_1181_; lean_object* v_res_1182_; 
v_t_boxed_1181_ = lean_unbox(v_t_1178_);
v_res_1182_ = l_Lake_OutputStatus_ctorElim(v_motive_1176_, v_ctorIdx_1177_, v_t_boxed_1181_, v_h_1179_, v_k_1180_);
lean_dec(v_k_1180_);
lean_dec(v_ctorIdx_1177_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg(lean_object* v_outOfDate_1183_){
_start:
{
lean_inc(v_outOfDate_1183_);
return v_outOfDate_1183_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg___boxed(lean_object* v_outOfDate_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lake_OutputStatus_outOfDate_elim___redArg(v_outOfDate_1184_);
lean_dec(v_outOfDate_1184_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim(lean_object* v_motive_1186_, uint8_t v_t_1187_, lean_object* v_h_1188_, lean_object* v_outOfDate_1189_){
_start:
{
lean_inc(v_outOfDate_1189_);
return v_outOfDate_1189_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___boxed(lean_object* v_motive_1190_, lean_object* v_t_1191_, lean_object* v_h_1192_, lean_object* v_outOfDate_1193_){
_start:
{
uint8_t v_t_boxed_1194_; lean_object* v_res_1195_; 
v_t_boxed_1194_ = lean_unbox(v_t_1191_);
v_res_1195_ = l_Lake_OutputStatus_outOfDate_elim(v_motive_1190_, v_t_boxed_1194_, v_h_1192_, v_outOfDate_1193_);
lean_dec(v_outOfDate_1193_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg(lean_object* v_mtimeUpToDate_1196_){
_start:
{
lean_inc(v_mtimeUpToDate_1196_);
return v_mtimeUpToDate_1196_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg___boxed(lean_object* v_mtimeUpToDate_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lake_OutputStatus_mtimeUpToDate_elim___redArg(v_mtimeUpToDate_1197_);
lean_dec(v_mtimeUpToDate_1197_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim(lean_object* v_motive_1199_, uint8_t v_t_1200_, lean_object* v_h_1201_, lean_object* v_mtimeUpToDate_1202_){
_start:
{
lean_inc(v_mtimeUpToDate_1202_);
return v_mtimeUpToDate_1202_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___boxed(lean_object* v_motive_1203_, lean_object* v_t_1204_, lean_object* v_h_1205_, lean_object* v_mtimeUpToDate_1206_){
_start:
{
uint8_t v_t_boxed_1207_; lean_object* v_res_1208_; 
v_t_boxed_1207_ = lean_unbox(v_t_1204_);
v_res_1208_ = l_Lake_OutputStatus_mtimeUpToDate_elim(v_motive_1203_, v_t_boxed_1207_, v_h_1205_, v_mtimeUpToDate_1206_);
lean_dec(v_mtimeUpToDate_1206_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg(lean_object* v_hashUpToDate_1209_){
_start:
{
lean_inc(v_hashUpToDate_1209_);
return v_hashUpToDate_1209_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg___boxed(lean_object* v_hashUpToDate_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lake_OutputStatus_hashUpToDate_elim___redArg(v_hashUpToDate_1210_);
lean_dec(v_hashUpToDate_1210_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim(lean_object* v_motive_1212_, uint8_t v_t_1213_, lean_object* v_h_1214_, lean_object* v_hashUpToDate_1215_){
_start:
{
lean_inc(v_hashUpToDate_1215_);
return v_hashUpToDate_1215_;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___boxed(lean_object* v_motive_1216_, lean_object* v_t_1217_, lean_object* v_h_1218_, lean_object* v_hashUpToDate_1219_){
_start:
{
uint8_t v_t_boxed_1220_; lean_object* v_res_1221_; 
v_t_boxed_1220_ = lean_unbox(v_t_1217_);
v_res_1221_ = l_Lake_OutputStatus_hashUpToDate_elim(v_motive_1216_, v_t_boxed_1220_, v_h_1218_, v_hashUpToDate_1219_);
lean_dec(v_hashUpToDate_1219_);
return v_res_1221_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofNat(lean_object* v_n_1222_){
_start:
{
lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = lean_unsigned_to_nat(0u);
v___x_1224_ = lean_nat_dec_le(v_n_1222_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; uint8_t v___x_1226_; 
v___x_1225_ = lean_unsigned_to_nat(1u);
v___x_1226_ = lean_nat_dec_le(v_n_1222_, v___x_1225_);
if (v___x_1226_ == 0)
{
uint8_t v___x_1227_; 
v___x_1227_ = 2;
return v___x_1227_;
}
else
{
uint8_t v___x_1228_; 
v___x_1228_ = 1;
return v___x_1228_;
}
}
else
{
uint8_t v___x_1229_; 
v___x_1229_ = 0;
return v___x_1229_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofNat___boxed(lean_object* v_n_1230_){
_start:
{
uint8_t v_res_1231_; lean_object* v_r_1232_; 
v_res_1231_ = l_Lake_OutputStatus_ofNat(v_n_1230_);
lean_dec(v_n_1230_);
v_r_1232_ = lean_box(v_res_1231_);
return v_r_1232_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqOutputStatus(uint8_t v_x_1233_, uint8_t v_y_1234_){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1235_ = l_Lake_OutputStatus_ctorIdx(v_x_1233_);
v___x_1236_ = l_Lake_OutputStatus_ctorIdx(v_y_1234_);
v___x_1237_ = lean_nat_dec_eq(v___x_1235_, v___x_1236_);
lean_dec(v___x_1236_);
lean_dec(v___x_1235_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqOutputStatus___boxed(lean_object* v_x_1238_, lean_object* v_y_1239_){
_start:
{
uint8_t v_x_20__boxed_1240_; uint8_t v_y_21__boxed_1241_; uint8_t v_res_1242_; lean_object* v_r_1243_; 
v_x_20__boxed_1240_ = lean_unbox(v_x_1238_);
v_y_21__boxed_1241_ = lean_unbox(v_y_1239_);
v_res_1242_ = l_Lake_instDecidableEqOutputStatus(v_x_20__boxed_1240_, v_y_21__boxed_1241_);
v_r_1243_ = lean_box(v_res_1242_);
return v_r_1243_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofHashCheck(uint8_t v_upToDate_1244_){
_start:
{
if (v_upToDate_1244_ == 0)
{
uint8_t v___x_1245_; 
v___x_1245_ = 0;
return v___x_1245_;
}
else
{
uint8_t v___x_1246_; 
v___x_1246_ = 2;
return v___x_1246_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofHashCheck___boxed(lean_object* v_upToDate_1247_){
_start:
{
uint8_t v_upToDate_boxed_1248_; uint8_t v_res_1249_; lean_object* v_r_1250_; 
v_upToDate_boxed_1248_ = lean_unbox(v_upToDate_1247_);
v_res_1249_ = l_Lake_OutputStatus_ofHashCheck(v_upToDate_boxed_1248_);
v_r_1250_ = lean_box(v_res_1249_);
return v_r_1250_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofMTimeCheck(uint8_t v_upToDate_1251_){
_start:
{
if (v_upToDate_1251_ == 0)
{
uint8_t v___x_1252_; 
v___x_1252_ = 0;
return v___x_1252_;
}
else
{
uint8_t v___x_1253_; 
v___x_1253_ = 1;
return v___x_1253_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofMTimeCheck___boxed(lean_object* v_upToDate_1254_){
_start:
{
uint8_t v_upToDate_boxed_1255_; uint8_t v_res_1256_; lean_object* v_r_1257_; 
v_upToDate_boxed_1255_ = lean_unbox(v_upToDate_1254_);
v_res_1256_ = l_Lake_OutputStatus_ofMTimeCheck(v_upToDate_boxed_1255_);
v_r_1257_ = lean_box(v_res_1256_);
return v_r_1257_;
}
}
static lean_object* _init_l_Lake_OutputStatus_isUpToDate___closed__0(void){
_start:
{
uint8_t v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = 0;
v___x_1259_ = l_Lake_OutputStatus_ctorIdx(v___x_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isUpToDate(uint8_t v_status_1260_){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1261_ = l_Lake_OutputStatus_ctorIdx(v_status_1260_);
v___x_1262_ = lean_obj_once(&l_Lake_OutputStatus_isUpToDate___closed__0, &l_Lake_OutputStatus_isUpToDate___closed__0_once, _init_l_Lake_OutputStatus_isUpToDate___closed__0);
v___x_1263_ = lean_nat_dec_eq(v___x_1261_, v___x_1262_);
lean_dec(v___x_1261_);
if (v___x_1263_ == 0)
{
uint8_t v___x_1264_; 
v___x_1264_ = 1;
return v___x_1264_;
}
else
{
uint8_t v___x_1265_; 
v___x_1265_ = 0;
return v___x_1265_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isUpToDate___boxed(lean_object* v_status_1266_){
_start:
{
uint8_t v_status_boxed_1267_; uint8_t v_res_1268_; lean_object* v_r_1269_; 
v_status_boxed_1267_ = lean_unbox(v_status_1266_);
v_res_1268_ = l_Lake_OutputStatus_isUpToDate(v_status_boxed_1267_);
v_r_1269_ = lean_box(v_res_1268_);
return v_r_1269_;
}
}
static lean_object* _init_l_Lake_OutputStatus_isCacheable___closed__0(void){
_start:
{
uint8_t v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = 1;
v___x_1271_ = l_Lake_OutputStatus_ctorIdx(v___x_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isCacheable(uint8_t v_status_1272_){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v___x_1273_ = l_Lake_OutputStatus_ctorIdx(v_status_1272_);
v___x_1274_ = lean_obj_once(&l_Lake_OutputStatus_isCacheable___closed__0, &l_Lake_OutputStatus_isCacheable___closed__0_once, _init_l_Lake_OutputStatus_isCacheable___closed__0);
v___x_1275_ = lean_nat_dec_eq(v___x_1273_, v___x_1274_);
lean_dec(v___x_1273_);
if (v___x_1275_ == 0)
{
uint8_t v___x_1276_; 
v___x_1276_ = 1;
return v___x_1276_;
}
else
{
uint8_t v___x_1277_; 
v___x_1277_ = 0;
return v___x_1277_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isCacheable___boxed(lean_object* v_status_1278_){
_start:
{
uint8_t v_status_boxed_1279_; uint8_t v_res_1280_; lean_object* v_r_1281_; 
v_status_boxed_1279_ = lean_unbox(v_status_1278_);
v_res_1280_ = l_Lake_OutputStatus_isCacheable(v_status_boxed_1279_);
v_r_1281_ = lean_box(v_res_1280_);
return v_r_1281_;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___f_1283_; 
v___x_1282_ = lean_alloc_closure((void*)(l_Lake_instDecidableEqHash___boxed), 2, 0);
v___f_1283_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1283_, 0, v___x_1282_);
return v___f_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(lean_object* v_inst_1284_, lean_object* v_inst_1285_, lean_object* v_info_1286_, lean_object* v_depTrace_1287_, lean_object* v_depHash_1288_, lean_object* v_oldTrace_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_){
_start:
{
uint64_t v_hash_1293_; lean_object* v___f_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v_hash_1293_ = lean_ctor_get_uint64(v_depTrace_1287_, sizeof(void*)*3);
v___f_1294_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0);
v___x_1295_ = lean_box_uint64(v_hash_1293_);
v___x_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
v___x_1297_ = l_Option_instBEq_beq___redArg(v___f_1294_, v___x_1296_, v_depHash_1288_);
if (v___x_1297_ == 0)
{
lean_object* v_toBuildConfig_1298_; uint8_t v_oldMode_1299_; 
lean_dec_ref(v_inst_1284_);
v_toBuildConfig_1298_ = lean_ctor_get(v_a_1290_, 0);
v_oldMode_1299_ = lean_ctor_get_uint8(v_toBuildConfig_1298_, sizeof(void*)*4);
if (v_oldMode_1299_ == 0)
{
uint8_t v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
lean_dec(v_info_1286_);
lean_dec_ref(v_inst_1285_);
v___x_1300_ = 0;
v___x_1301_ = lean_box(v___x_1300_);
v___x_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
lean_ctor_set(v___x_1302_, 1, v_a_1291_);
return v___x_1302_;
}
else
{
uint8_t v___x_1303_; 
v___x_1303_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1285_, v_info_1286_, v_oldTrace_1289_);
if (v___x_1303_ == 0)
{
uint8_t v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1304_ = 0;
v___x_1305_ = lean_box(v___x_1304_);
v___x_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
lean_ctor_set(v___x_1306_, 1, v_a_1291_);
return v___x_1306_;
}
else
{
uint8_t v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1307_ = 1;
v___x_1308_ = lean_box(v___x_1307_);
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
lean_ctor_set(v___x_1309_, 1, v_a_1291_);
return v___x_1309_;
}
}
}
else
{
lean_object* v___x_1310_; uint8_t v___x_1311_; 
lean_dec_ref(v_inst_1285_);
v___x_1310_ = lean_apply_2(v_inst_1284_, v_info_1286_, lean_box(0));
v___x_1311_ = lean_unbox(v___x_1310_);
if (v___x_1311_ == 0)
{
uint8_t v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1312_ = 0;
v___x_1313_ = lean_box(v___x_1312_);
v___x_1314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1313_);
lean_ctor_set(v___x_1314_, 1, v_a_1291_);
return v___x_1314_;
}
else
{
uint8_t v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1315_ = 2;
v___x_1316_ = lean_box(v___x_1315_);
v___x_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
lean_ctor_set(v___x_1317_, 1, v_a_1291_);
return v___x_1317_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___boxed(lean_object* v_inst_1318_, lean_object* v_inst_1319_, lean_object* v_info_1320_, lean_object* v_depTrace_1321_, lean_object* v_depHash_1322_, lean_object* v_oldTrace_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1318_, v_inst_1319_, v_info_1320_, v_depTrace_1321_, v_depHash_1322_, v_oldTrace_1323_, v_a_1324_, v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec_ref(v_oldTrace_1323_);
lean_dec_ref(v_depTrace_1321_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27(lean_object* v_00_u03b9_1328_, lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v_info_1331_, lean_object* v_depTrace_1332_, lean_object* v_depHash_1333_, lean_object* v_oldTrace_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1329_, v_inst_1330_, v_info_1331_, v_depTrace_1332_, v_depHash_1333_, v_oldTrace_1334_, v_a_1339_, v_a_1340_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___boxed(lean_object* v_00_u03b9_1343_, lean_object* v_inst_1344_, lean_object* v_inst_1345_, lean_object* v_info_1346_, lean_object* v_depTrace_1347_, lean_object* v_depHash_1348_, lean_object* v_oldTrace_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27(v_00_u03b9_1343_, v_inst_1344_, v_inst_1345_, v_info_1346_, v_depTrace_1347_, v_depHash_1348_, v_oldTrace_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
lean_dec_ref(v_a_1354_);
lean_dec(v_a_1353_);
lean_dec(v_a_1352_);
lean_dec(v_a_1351_);
lean_dec_ref(v_a_1350_);
lean_dec_ref(v_oldTrace_1349_);
lean_dec_ref(v_depTrace_1347_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg(lean_object* v_inst_1358_, lean_object* v_inst_1359_, lean_object* v_info_1360_, lean_object* v_depTrace_1361_, lean_object* v_depHash_1362_, lean_object* v_oldTrace_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v___x_1367_; lean_object* v_a_1368_; lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1387_; 
v___x_1367_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1358_, v_inst_1359_, v_info_1360_, v_depTrace_1361_, v_depHash_1362_, v_oldTrace_1363_, v_a_1364_, v_a_1365_);
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
v_a_1369_ = lean_ctor_get(v___x_1367_, 1);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1371_ = v___x_1367_;
v_isShared_1372_ = v_isSharedCheck_1387_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_inc(v_a_1368_);
lean_dec(v___x_1367_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1387_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
uint8_t v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1373_ = lean_unbox(v_a_1368_);
lean_dec(v_a_1368_);
v___x_1374_ = l_Lake_OutputStatus_ctorIdx(v___x_1373_);
v___x_1375_ = lean_obj_once(&l_Lake_OutputStatus_isUpToDate___closed__0, &l_Lake_OutputStatus_isUpToDate___closed__0_once, _init_l_Lake_OutputStatus_isUpToDate___closed__0);
v___x_1376_ = lean_nat_dec_eq(v___x_1374_, v___x_1375_);
lean_dec(v___x_1374_);
if (v___x_1376_ == 0)
{
uint8_t v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1380_; 
v___x_1377_ = 1;
v___x_1378_ = lean_box(v___x_1377_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1378_);
v___x_1380_ = v___x_1371_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1378_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_a_1369_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
else
{
uint8_t v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1382_ = 0;
v___x_1383_ = lean_box(v___x_1382_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1383_);
v___x_1385_ = v___x_1371_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_a_1369_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg___boxed(lean_object* v_inst_1388_, lean_object* v_inst_1389_, lean_object* v_info_1390_, lean_object* v_depTrace_1391_, lean_object* v_depHash_1392_, lean_object* v_oldTrace_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lake_checkHashUpToDate___redArg(v_inst_1388_, v_inst_1389_, v_info_1390_, v_depTrace_1391_, v_depHash_1392_, v_oldTrace_1393_, v_a_1394_, v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec_ref(v_oldTrace_1393_);
lean_dec_ref(v_depTrace_1391_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate(lean_object* v_00_u03b9_1398_, lean_object* v_inst_1399_, lean_object* v_inst_1400_, lean_object* v_info_1401_, lean_object* v_depTrace_1402_, lean_object* v_depHash_1403_, lean_object* v_oldTrace_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v___x_1412_; lean_object* v_a_1413_; lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1432_; 
v___x_1412_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1399_, v_inst_1400_, v_info_1401_, v_depTrace_1402_, v_depHash_1403_, v_oldTrace_1404_, v_a_1409_, v_a_1410_);
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
v_a_1414_ = lean_ctor_get(v___x_1412_, 1);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1416_ = v___x_1412_;
v_isShared_1417_ = v_isSharedCheck_1432_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_inc(v_a_1413_);
lean_dec(v___x_1412_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1432_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
uint8_t v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; 
v___x_1418_ = lean_unbox(v_a_1413_);
lean_dec(v_a_1413_);
v___x_1419_ = l_Lake_OutputStatus_ctorIdx(v___x_1418_);
v___x_1420_ = lean_obj_once(&l_Lake_OutputStatus_isUpToDate___closed__0, &l_Lake_OutputStatus_isUpToDate___closed__0_once, _init_l_Lake_OutputStatus_isUpToDate___closed__0);
v___x_1421_ = lean_nat_dec_eq(v___x_1419_, v___x_1420_);
lean_dec(v___x_1419_);
if (v___x_1421_ == 0)
{
uint8_t v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1422_ = 1;
v___x_1423_ = lean_box(v___x_1422_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v___x_1423_);
v___x_1425_ = v___x_1416_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1423_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_a_1414_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
else
{
uint8_t v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1427_ = 0;
v___x_1428_ = lean_box(v___x_1427_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v___x_1428_);
v___x_1430_ = v___x_1416_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_a_1414_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___boxed(lean_object* v_00_u03b9_1433_, lean_object* v_inst_1434_, lean_object* v_inst_1435_, lean_object* v_info_1436_, lean_object* v_depTrace_1437_, lean_object* v_depHash_1438_, lean_object* v_oldTrace_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lake_checkHashUpToDate(v_00_u03b9_1433_, v_inst_1434_, v_inst_1435_, v_info_1436_, v_depTrace_1437_, v_depHash_1438_, v_oldTrace_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_);
lean_dec_ref(v_a_1444_);
lean_dec(v_a_1443_);
lean_dec(v_a_1442_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec_ref(v_oldTrace_1439_);
lean_dec_ref(v_depTrace_1437_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(lean_object* v_as_1448_, size_t v_i_1449_, size_t v_stop_1450_, lean_object* v_b_1451_, lean_object* v___y_1452_){
_start:
{
uint8_t v___x_1454_; 
v___x_1454_ = lean_usize_dec_eq(v_i_1449_, v_stop_1450_);
if (v___x_1454_ == 0)
{
lean_object* v_log_1455_; uint8_t v_action_1456_; uint8_t v_wantsRebuild_1457_; lean_object* v_trace_1458_; lean_object* v_buildTime_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1472_; 
v_log_1455_ = lean_ctor_get(v___y_1452_, 0);
v_action_1456_ = lean_ctor_get_uint8(v___y_1452_, sizeof(void*)*3);
v_wantsRebuild_1457_ = lean_ctor_get_uint8(v___y_1452_, sizeof(void*)*3 + 1);
v_trace_1458_ = lean_ctor_get(v___y_1452_, 1);
v_buildTime_1459_ = lean_ctor_get(v___y_1452_, 2);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___y_1452_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1461_ = v___y_1452_;
v_isShared_1462_ = v_isSharedCheck_1472_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_buildTime_1459_);
lean_inc(v_trace_1458_);
lean_inc(v_log_1455_);
lean_dec(v___y_1452_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1472_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1467_; 
v___x_1463_ = lean_array_uget_borrowed(v_as_1448_, v_i_1449_);
v___x_1464_ = lean_box(0);
lean_inc(v___x_1463_);
v___x_1465_ = lean_array_push(v_log_1455_, v___x_1463_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v___x_1465_);
v___x_1467_ = v___x_1461_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1465_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_trace_1458_);
lean_ctor_set(v_reuseFailAlloc_1471_, 2, v_buildTime_1459_);
lean_ctor_set_uint8(v_reuseFailAlloc_1471_, sizeof(void*)*3, v_action_1456_);
lean_ctor_set_uint8(v_reuseFailAlloc_1471_, sizeof(void*)*3 + 1, v_wantsRebuild_1457_);
v___x_1467_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
size_t v___x_1468_; size_t v___x_1469_; 
v___x_1468_ = ((size_t)1ULL);
v___x_1469_ = lean_usize_add(v_i_1449_, v___x_1468_);
v_i_1449_ = v___x_1469_;
v_b_1451_ = v___x_1464_;
v___y_1452_ = v___x_1467_;
goto _start;
}
}
}
else
{
lean_object* v___x_1473_; 
v___x_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1473_, 0, v_b_1451_);
lean_ctor_set(v___x_1473_, 1, v___y_1452_);
return v___x_1473_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg___boxed(lean_object* v_as_1474_, lean_object* v_i_1475_, lean_object* v_stop_1476_, lean_object* v_b_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
size_t v_i_boxed_1480_; size_t v_stop_boxed_1481_; lean_object* v_res_1482_; 
v_i_boxed_1480_ = lean_unbox_usize(v_i_1475_);
lean_dec(v_i_1475_);
v_stop_boxed_1481_ = lean_unbox_usize(v_stop_1476_);
lean_dec(v_stop_1476_);
v_res_1482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_as_1474_, v_i_boxed_1480_, v_stop_boxed_1481_, v_b_1477_, v___y_1478_);
lean_dec_ref(v_as_1474_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(lean_object* v_log_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1491_ = lean_unsigned_to_nat(0u);
v___x_1492_ = lean_array_get_size(v_log_1483_);
v___x_1493_ = lean_box(0);
v___x_1494_ = lean_nat_dec_lt(v___x_1491_, v___x_1492_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; 
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1493_);
lean_ctor_set(v___x_1495_, 1, v_a_1489_);
return v___x_1495_;
}
else
{
size_t v___x_1496_; size_t v___x_1497_; lean_object* v___x_1498_; 
v___x_1496_ = ((size_t)0ULL);
v___x_1497_ = lean_usize_of_nat(v___x_1492_);
v___x_1498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1483_, v___x_1496_, v___x_1497_, v___x_1493_, v_a_1489_);
return v___x_1498_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay___boxed(lean_object* v_log_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
lean_dec_ref(v_a_1504_);
lean_dec(v_a_1503_);
lean_dec(v_a_1502_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec_ref(v_log_1499_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(lean_object* v_as_1508_, size_t v_i_1509_, size_t v_stop_1510_, lean_object* v_b_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_as_1508_, v_i_1509_, v_stop_1510_, v_b_1511_, v___y_1517_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___boxed(lean_object* v_as_1520_, lean_object* v_i_1521_, lean_object* v_stop_1522_, lean_object* v_b_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
size_t v_i_boxed_1531_; size_t v_stop_boxed_1532_; lean_object* v_res_1533_; 
v_i_boxed_1531_ = lean_unbox_usize(v_i_1521_);
lean_dec(v_i_1521_);
v_stop_boxed_1532_ = lean_unbox_usize(v_stop_1522_);
lean_dec(v_stop_1522_);
v_res_1533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(v_as_1520_, v_i_boxed_1531_, v_stop_boxed_1532_, v_b_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec_ref(v_as_1520_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(lean_object* v_inst_1534_, lean_object* v_inst_1535_, lean_object* v_info_1536_, lean_object* v_depTrace_1537_, lean_object* v_savedTrace_1538_, lean_object* v_oldTrace_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_){
_start:
{
if (lean_obj_tag(v_savedTrace_1538_) == 2)
{
lean_object* v_data_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1598_; 
v_data_1547_ = lean_ctor_get(v_savedTrace_1538_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v_savedTrace_1538_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1549_ = v_savedTrace_1538_;
v_isShared_1550_ = v_isSharedCheck_1598_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_data_1547_);
lean_dec(v_savedTrace_1538_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1598_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
uint64_t v_depHash_1551_; lean_object* v_log_1552_; lean_object* v___x_1553_; lean_object* v___x_1555_; 
v_depHash_1551_ = lean_ctor_get_uint64(v_data_1547_, sizeof(void*)*3);
v_log_1552_ = lean_ctor_get(v_data_1547_, 2);
lean_inc_ref(v_log_1552_);
lean_dec_ref(v_data_1547_);
v___x_1553_ = lean_box_uint64(v_depHash_1551_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set_tag(v___x_1549_, 1);
lean_ctor_set(v___x_1549_, 0, v___x_1553_);
v___x_1555_ = v___x_1549_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1553_);
v___x_1555_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1556_; lean_object* v_a_1557_; lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1596_; 
v___x_1556_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(v_inst_1534_, v_inst_1535_, v_info_1536_, v_depTrace_1537_, v___x_1555_, v_oldTrace_1539_, v_a_1544_, v_a_1545_);
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
v_a_1558_ = lean_ctor_get(v___x_1556_, 1);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1560_ = v___x_1556_;
v_isShared_1561_ = v_isSharedCheck_1596_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_inc(v_a_1557_);
lean_dec(v___x_1556_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1596_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___y_1563_; uint8_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
v___x_1567_ = lean_unbox(v_a_1557_);
v___x_1568_ = l_Lake_OutputStatus_ctorIdx(v___x_1567_);
v___x_1569_ = lean_obj_once(&l_Lake_OutputStatus_isUpToDate___closed__0, &l_Lake_OutputStatus_isUpToDate___closed__0_once, _init_l_Lake_OutputStatus_isUpToDate___closed__0);
v___x_1570_ = lean_nat_dec_eq(v___x_1568_, v___x_1569_);
lean_dec(v___x_1568_);
if (v___x_1570_ == 0)
{
lean_object* v_log_1571_; uint8_t v_action_1572_; uint8_t v_wantsRebuild_1573_; lean_object* v_trace_1574_; lean_object* v_buildTime_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1595_; 
v_log_1571_ = lean_ctor_get(v_a_1558_, 0);
v_action_1572_ = lean_ctor_get_uint8(v_a_1558_, sizeof(void*)*3);
v_wantsRebuild_1573_ = lean_ctor_get_uint8(v_a_1558_, sizeof(void*)*3 + 1);
v_trace_1574_ = lean_ctor_get(v_a_1558_, 1);
v_buildTime_1575_ = lean_ctor_get(v_a_1558_, 2);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_a_1558_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1577_ = v_a_1558_;
v_isShared_1578_ = v_isSharedCheck_1595_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_buildTime_1575_);
lean_inc(v_trace_1574_);
lean_inc(v_log_1571_);
lean_dec(v_a_1558_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1595_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
uint8_t v___x_1579_; uint8_t v___x_1580_; lean_object* v___x_1582_; 
v___x_1579_ = 2;
v___x_1580_ = l_Lake_JobAction_merge(v_action_1572_, v___x_1579_);
if (v_isShared_1578_ == 0)
{
v___x_1582_ = v___x_1577_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_log_1571_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_trace_1574_);
lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_buildTime_1575_);
lean_ctor_set_uint8(v_reuseFailAlloc_1594_, sizeof(void*)*3 + 1, v_wantsRebuild_1573_);
v___x_1582_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1583_; 
lean_ctor_set_uint8(v___x_1582_, sizeof(void*)*3, v___x_1580_);
v___x_1583_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_1552_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v___x_1582_);
lean_dec_ref(v_log_1552_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 1);
lean_inc(v_a_1584_);
lean_dec_ref_known(v___x_1583_, 2);
v___y_1563_ = v_a_1584_;
goto v___jp_1562_;
}
else
{
lean_object* v_a_1585_; lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_del_object(v___x_1560_);
lean_dec(v_a_1557_);
v_a_1585_ = lean_ctor_get(v___x_1583_, 0);
v_a_1586_ = lean_ctor_get(v___x_1583_, 1);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1583_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_inc(v_a_1585_);
lean_dec(v___x_1583_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1585_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_log_1552_);
v___y_1563_ = v_a_1558_;
goto v___jp_1562_;
}
v___jp_1562_:
{
lean_object* v___x_1565_; 
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 1, v___y_1563_);
v___x_1565_ = v___x_1560_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1557_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v___y_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
}
else
{
lean_object* v_toBuildConfig_1599_; uint8_t v_oldMode_1600_; 
lean_dec(v_savedTrace_1538_);
lean_dec_ref(v_inst_1534_);
v_toBuildConfig_1599_ = lean_ctor_get(v_a_1544_, 0);
v_oldMode_1600_ = lean_ctor_get_uint8(v_toBuildConfig_1599_, sizeof(void*)*4);
if (v_oldMode_1600_ == 0)
{
uint8_t v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_dec(v_info_1536_);
lean_dec_ref(v_inst_1535_);
v___x_1601_ = 0;
v___x_1602_ = lean_box(v___x_1601_);
v___x_1603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
lean_ctor_set(v___x_1603_, 1, v_a_1545_);
return v___x_1603_;
}
else
{
uint8_t v___x_1604_; 
v___x_1604_ = l_Lake_MTime_checkUpToDate___redArg(v_inst_1535_, v_info_1536_, v_oldTrace_1539_);
if (v___x_1604_ == 0)
{
uint8_t v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1605_ = 0;
v___x_1606_ = lean_box(v___x_1605_);
v___x_1607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1606_);
lean_ctor_set(v___x_1607_, 1, v_a_1545_);
return v___x_1607_;
}
else
{
uint8_t v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1608_ = 1;
v___x_1609_ = lean_box(v___x_1608_);
v___x_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v_a_1545_);
return v___x_1610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg___boxed(lean_object* v_inst_1611_, lean_object* v_inst_1612_, lean_object* v_info_1613_, lean_object* v_depTrace_1614_, lean_object* v_savedTrace_1615_, lean_object* v_oldTrace_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1611_, v_inst_1612_, v_info_1613_, v_depTrace_1614_, v_savedTrace_1615_, v_oldTrace_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_);
lean_dec_ref(v_a_1621_);
lean_dec(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
lean_dec_ref(v_oldTrace_1616_);
lean_dec_ref(v_depTrace_1614_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27(lean_object* v_00_u03b9_1625_, lean_object* v_inst_1626_, lean_object* v_inst_1627_, lean_object* v_info_1628_, lean_object* v_depTrace_1629_, lean_object* v_savedTrace_1630_, lean_object* v_oldTrace_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1626_, v_inst_1627_, v_info_1628_, v_depTrace_1629_, v_savedTrace_1630_, v_oldTrace_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___boxed(lean_object* v_00_u03b9_1640_, lean_object* v_inst_1641_, lean_object* v_inst_1642_, lean_object* v_info_1643_, lean_object* v_depTrace_1644_, lean_object* v_savedTrace_1645_, lean_object* v_oldTrace_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Lake_SavedTrace_replayIfUpToDate_x27(v_00_u03b9_1640_, v_inst_1641_, v_inst_1642_, v_info_1643_, v_depTrace_1644_, v_savedTrace_1645_, v_oldTrace_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
lean_dec_ref(v_oldTrace_1646_);
lean_dec_ref(v_depTrace_1644_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg(lean_object* v_inst_1655_, lean_object* v_inst_1656_, lean_object* v_info_1657_, lean_object* v_depTrace_1658_, lean_object* v_savedTrace_1659_, lean_object* v_oldTrace_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_1655_, v_inst_1656_, v_info_1657_, v_depTrace_1658_, v_savedTrace_1659_, v_oldTrace_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1688_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
v_a_1670_ = lean_ctor_get(v___x_1668_, 1);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1672_ = v___x_1668_;
v_isShared_1673_ = v_isSharedCheck_1688_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_inc(v_a_1669_);
lean_dec(v___x_1668_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1688_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
uint8_t v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; uint8_t v___x_1677_; 
v___x_1674_ = lean_unbox(v_a_1669_);
lean_dec(v_a_1669_);
v___x_1675_ = l_Lake_OutputStatus_ctorIdx(v___x_1674_);
v___x_1676_ = lean_obj_once(&l_Lake_OutputStatus_isUpToDate___closed__0, &l_Lake_OutputStatus_isUpToDate___closed__0_once, _init_l_Lake_OutputStatus_isUpToDate___closed__0);
v___x_1677_ = lean_nat_dec_eq(v___x_1675_, v___x_1676_);
lean_dec(v___x_1675_);
if (v___x_1677_ == 0)
{
uint8_t v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1678_ = 1;
v___x_1679_ = lean_box(v___x_1678_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1679_);
v___x_1681_ = v___x_1672_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_a_1670_);
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
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1684_);
v___x_1686_ = v___x_1672_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_a_1670_);
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
v_a_1689_ = lean_ctor_get(v___x_1668_, 0);
v_a_1690_ = lean_ctor_get(v___x_1668_, 1);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1668_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_inc(v_a_1689_);
lean_dec(v___x_1668_);
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
lean_object* v_a_1727_; lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1746_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
v_a_1728_ = lean_ctor_get(v___x_1726_, 1);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1730_ = v___x_1726_;
v_isShared_1731_ = v_isSharedCheck_1746_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_inc(v_a_1727_);
lean_dec(v___x_1726_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1746_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
uint8_t v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; uint8_t v___x_1735_; 
v___x_1732_ = lean_unbox(v_a_1727_);
lean_dec(v_a_1727_);
v___x_1733_ = l_Lake_OutputStatus_ctorIdx(v___x_1732_);
v___x_1734_ = lean_obj_once(&l_Lake_OutputStatus_isUpToDate___closed__0, &l_Lake_OutputStatus_isUpToDate___closed__0_once, _init_l_Lake_OutputStatus_isUpToDate___closed__0);
v___x_1735_ = lean_nat_dec_eq(v___x_1733_, v___x_1734_);
lean_dec(v___x_1733_);
if (v___x_1735_ == 0)
{
uint8_t v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1739_; 
v___x_1736_ = 1;
v___x_1737_ = lean_box(v___x_1736_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1737_);
v___x_1739_ = v___x_1730_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_a_1728_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
else
{
uint8_t v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1744_; 
v___x_1741_ = 0;
v___x_1742_ = lean_box(v___x_1741_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1742_);
v___x_1744_ = v___x_1730_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_a_1728_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
v_a_1747_ = lean_ctor_get(v___x_1726_, 0);
v_a_1748_ = lean_ctor_get(v___x_1726_, 1);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1726_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_inc(v_a_1747_);
lean_dec(v___x_1726_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1747_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___boxed(lean_object* v_00_u03b9_1756_, lean_object* v_inst_1757_, lean_object* v_inst_1758_, lean_object* v_info_1759_, lean_object* v_depTrace_1760_, lean_object* v_savedTrace_1761_, lean_object* v_oldTrace_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lake_SavedTrace_replayIfUpToDate(v_00_u03b9_1756_, v_inst_1757_, v_inst_1758_, v_info_1759_, v_depTrace_1760_, v_savedTrace_1761_, v_oldTrace_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_);
lean_dec_ref(v_a_1767_);
lean_dec(v_a_1766_);
lean_dec(v_a_1765_);
lean_dec(v_a_1764_);
lean_dec_ref(v_a_1763_);
lean_dec_ref(v_oldTrace_1762_);
lean_dec_ref(v_depTrace_1760_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(uint64_t v_inputHash_1771_, lean_object* v_self_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v___y_1776_; 
if (lean_obj_tag(v_self_1772_) == 2)
{
lean_object* v_data_1794_; uint64_t v_depHash_1795_; lean_object* v_log_1796_; uint8_t v_synthetic_1797_; uint8_t v___x_1798_; lean_object* v___y_1800_; 
v_data_1794_ = lean_ctor_get(v_self_1772_, 0);
v_depHash_1795_ = lean_ctor_get_uint64(v_data_1794_, sizeof(void*)*3);
v_log_1796_ = lean_ctor_get(v_data_1794_, 2);
v_synthetic_1797_ = lean_ctor_get_uint8(v_data_1794_, sizeof(void*)*3 + 8);
v___x_1798_ = lean_uint64_dec_eq(v_depHash_1795_, v_inputHash_1771_);
if (v___x_1798_ == 0)
{
v___y_1776_ = v_a_1773_;
goto v___jp_1775_;
}
else
{
if (v_synthetic_1797_ == 0)
{
goto v___jp_1803_;
}
else
{
lean_object* v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v___x_1835_ = lean_array_get_size(v_log_1796_);
v___x_1836_ = lean_unsigned_to_nat(0u);
v___x_1837_ = lean_nat_dec_eq(v___x_1835_, v___x_1836_);
if (v___x_1837_ == 0)
{
goto v___jp_1803_;
}
else
{
lean_object* v_log_1838_; uint8_t v_action_1839_; uint8_t v_wantsRebuild_1840_; lean_object* v_trace_1841_; lean_object* v_buildTime_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1851_; 
v_log_1838_ = lean_ctor_get(v_a_1773_, 0);
v_action_1839_ = lean_ctor_get_uint8(v_a_1773_, sizeof(void*)*3);
v_wantsRebuild_1840_ = lean_ctor_get_uint8(v_a_1773_, sizeof(void*)*3 + 1);
v_trace_1841_ = lean_ctor_get(v_a_1773_, 1);
v_buildTime_1842_ = lean_ctor_get(v_a_1773_, 2);
v_isSharedCheck_1851_ = !lean_is_exclusive(v_a_1773_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1844_ = v_a_1773_;
v_isShared_1845_ = v_isSharedCheck_1851_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_buildTime_1842_);
lean_inc(v_trace_1841_);
lean_inc(v_log_1838_);
lean_dec(v_a_1773_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1851_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
uint8_t v___x_1846_; uint8_t v___x_1847_; lean_object* v___x_1849_; 
v___x_1846_ = 1;
v___x_1847_ = l_Lake_JobAction_merge(v_action_1839_, v___x_1846_);
if (v_isShared_1845_ == 0)
{
v___x_1849_ = v___x_1844_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_log_1838_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_trace_1841_);
lean_ctor_set(v_reuseFailAlloc_1850_, 2, v_buildTime_1842_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, sizeof(void*)*3 + 1, v_wantsRebuild_1840_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_ctor_set_uint8(v___x_1849_, sizeof(void*)*3, v___x_1847_);
v___y_1800_ = v___x_1849_;
goto v___jp_1799_;
}
}
}
}
}
v___jp_1799_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = lean_box(v___x_1798_);
v___x_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1801_);
lean_ctor_set(v___x_1802_, 1, v___y_1800_);
return v___x_1802_;
}
v___jp_1803_:
{
lean_object* v_log_1804_; uint8_t v_action_1805_; uint8_t v_wantsRebuild_1806_; lean_object* v_trace_1807_; lean_object* v_buildTime_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1834_; 
v_log_1804_ = lean_ctor_get(v_a_1773_, 0);
v_action_1805_ = lean_ctor_get_uint8(v_a_1773_, sizeof(void*)*3);
v_wantsRebuild_1806_ = lean_ctor_get_uint8(v_a_1773_, sizeof(void*)*3 + 1);
v_trace_1807_ = lean_ctor_get(v_a_1773_, 1);
v_buildTime_1808_ = lean_ctor_get(v_a_1773_, 2);
v_isSharedCheck_1834_ = !lean_is_exclusive(v_a_1773_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1810_ = v_a_1773_;
v_isShared_1811_ = v_isSharedCheck_1834_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_buildTime_1808_);
lean_inc(v_trace_1807_);
lean_inc(v_log_1804_);
lean_dec(v_a_1773_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1834_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
uint8_t v___x_1812_; uint8_t v___x_1813_; lean_object* v___x_1815_; 
v___x_1812_ = 2;
v___x_1813_ = l_Lake_JobAction_merge(v_action_1805_, v___x_1812_);
if (v_isShared_1811_ == 0)
{
v___x_1815_ = v___x_1810_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_log_1804_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v_trace_1807_);
lean_ctor_set(v_reuseFailAlloc_1833_, 2, v_buildTime_1808_);
lean_ctor_set_uint8(v_reuseFailAlloc_1833_, sizeof(void*)*3 + 1, v_wantsRebuild_1806_);
v___x_1815_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
lean_ctor_set_uint8(v___x_1815_, sizeof(void*)*3, v___x_1813_);
v___x_1816_ = lean_unsigned_to_nat(0u);
v___x_1817_ = lean_array_get_size(v_log_1796_);
v___x_1818_ = lean_nat_dec_lt(v___x_1816_, v___x_1817_);
if (v___x_1818_ == 0)
{
v___y_1800_ = v___x_1815_;
goto v___jp_1799_;
}
else
{
lean_object* v___x_1819_; size_t v___x_1820_; size_t v___x_1821_; lean_object* v___x_1822_; 
v___x_1819_ = lean_box(0);
v___x_1820_ = ((size_t)0ULL);
v___x_1821_ = lean_usize_of_nat(v___x_1817_);
v___x_1822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(v_log_1796_, v___x_1820_, v___x_1821_, v___x_1819_, v___x_1815_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 1);
lean_inc(v_a_1823_);
lean_dec_ref_known(v___x_1822_, 2);
v___y_1800_ = v_a_1823_;
goto v___jp_1799_;
}
else
{
lean_object* v_a_1824_; lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
v_a_1824_ = lean_ctor_get(v___x_1822_, 0);
v_a_1825_ = lean_ctor_get(v___x_1822_, 1);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1822_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_inc(v_a_1824_);
lean_dec(v___x_1822_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1824_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
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
v___y_1776_ = v_a_1773_;
goto v___jp_1775_;
}
v___jp_1775_:
{
lean_object* v_log_1777_; uint8_t v_action_1778_; uint8_t v_wantsRebuild_1779_; lean_object* v_trace_1780_; lean_object* v_buildTime_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1793_; 
v_log_1777_ = lean_ctor_get(v___y_1776_, 0);
v_action_1778_ = lean_ctor_get_uint8(v___y_1776_, sizeof(void*)*3);
v_wantsRebuild_1779_ = lean_ctor_get_uint8(v___y_1776_, sizeof(void*)*3 + 1);
v_trace_1780_ = lean_ctor_get(v___y_1776_, 1);
v_buildTime_1781_ = lean_ctor_get(v___y_1776_, 2);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___y_1776_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1783_ = v___y_1776_;
v_isShared_1784_ = v_isSharedCheck_1793_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_buildTime_1781_);
lean_inc(v_trace_1780_);
lean_inc(v_log_1777_);
lean_dec(v___y_1776_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1793_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
uint8_t v___x_1785_; uint8_t v___x_1786_; lean_object* v___x_1788_; 
v___x_1785_ = 1;
v___x_1786_ = l_Lake_JobAction_merge(v_action_1778_, v___x_1785_);
if (v_isShared_1784_ == 0)
{
v___x_1788_ = v___x_1783_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_log_1777_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_trace_1780_);
lean_ctor_set(v_reuseFailAlloc_1792_, 2, v_buildTime_1781_);
lean_ctor_set_uint8(v_reuseFailAlloc_1792_, sizeof(void*)*3 + 1, v_wantsRebuild_1779_);
v___x_1788_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
uint8_t v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
lean_ctor_set_uint8(v___x_1788_, sizeof(void*)*3, v___x_1786_);
v___x_1789_ = 0;
v___x_1790_ = lean_box(v___x_1789_);
v___x_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
lean_ctor_set(v___x_1791_, 1, v___x_1788_);
return v___x_1791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate___redArg___boxed(lean_object* v_inputHash_1852_, lean_object* v_self_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_){
_start:
{
uint64_t v_inputHash_boxed_1856_; lean_object* v_res_1857_; 
v_inputHash_boxed_1856_ = lean_unbox_uint64(v_inputHash_1852_);
lean_dec_ref(v_inputHash_1852_);
v_res_1857_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_inputHash_boxed_1856_, v_self_1853_, v_a_1854_);
lean_dec(v_self_1853_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate(uint64_t v_inputHash_1858_, lean_object* v_self_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_inputHash_1858_, v_self_1859_, v_a_1865_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayCachedIfUpToDate___boxed(lean_object* v_inputHash_1868_, lean_object* v_self_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
uint64_t v_inputHash_boxed_1877_; lean_object* v_res_1878_; 
v_inputHash_boxed_1877_ = lean_unbox_uint64(v_inputHash_1868_);
lean_dec_ref(v_inputHash_1868_);
v_res_1878_ = l_Lake_SavedTrace_replayCachedIfUpToDate(v_inputHash_boxed_1877_, v_self_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_);
lean_dec_ref(v_a_1874_);
lean_dec(v_a_1873_);
lean_dec(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_self_1869_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(uint64_t v_inputHash_1879_, lean_object* v_self_1880_, lean_object* v_a_1881_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_inputHash_1879_, v_self_1880_, v_a_1881_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg___boxed(lean_object* v_inputHash_1884_, lean_object* v_self_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
uint64_t v_inputHash_boxed_1888_; lean_object* v_res_1889_; 
v_inputHash_boxed_1888_ = lean_unbox_uint64(v_inputHash_1884_);
lean_dec_ref(v_inputHash_1884_);
v_res_1889_ = l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(v_inputHash_boxed_1888_, v_self_1885_, v_a_1886_);
lean_dec(v_self_1885_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate(uint64_t v_inputHash_1890_, lean_object* v_self_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_inputHash_1890_, v_self_1891_, v_a_1897_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___boxed(lean_object* v_inputHash_1900_, lean_object* v_self_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
uint64_t v_inputHash_boxed_1909_; lean_object* v_res_1910_; 
v_inputHash_boxed_1909_ = lean_unbox_uint64(v_inputHash_1900_);
lean_dec_ref(v_inputHash_1900_);
v_res_1910_ = l_Lake_SavedTrace_replayOrFetchIfUpToDate(v_inputHash_boxed_1909_, v_self_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
lean_dec_ref(v_a_1906_);
lean_dec(v_a_1905_);
lean_dec(v_a_1904_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_self_1901_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonPUnit___lam__0(lean_object* v_x_1911_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = lean_box(0);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0(lean_object* v_x_1916_){
_start:
{
lean_object* v_descr_1917_; uint64_t v_hash_1918_; lean_object* v_ext_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; 
v_descr_1917_ = lean_ctor_get(v_x_1916_, 0);
v_hash_1918_ = lean_ctor_get_uint64(v_descr_1917_, sizeof(void*)*1);
v_ext_1919_ = lean_ctor_get(v_descr_1917_, 0);
v___x_1920_ = lean_string_utf8_byte_size(v_ext_1919_);
v___x_1921_ = lean_unsigned_to_nat(0u);
v___x_1922_ = lean_nat_dec_eq(v___x_1920_, v___x_1921_);
if (v___x_1922_ == 0)
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1923_ = l_Lake_lowerHexUInt64(v_hash_1918_);
v___x_1924_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_1925_ = lean_string_append(v___x_1923_, v___x_1924_);
v___x_1926_ = lean_string_append(v___x_1925_, v_ext_1919_);
v___x_1927_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
return v___x_1927_;
}
else
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = l_Lake_lowerHexUInt64(v_hash_1918_);
v___x_1929_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
return v___x_1929_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0___boxed(lean_object* v_x_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lake_instToOutputJsonArtifact___lam__0(v_x_1930_);
lean_dec_ref(v_x_1930_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0(lean_object* v_val_1934_, lean_object* v_a_x3f_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v_log_1938_; uint8_t v_action_1939_; uint8_t v_wantsRebuild_1940_; lean_object* v_trace_1941_; lean_object* v_buildTime_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1954_; 
v_log_1938_ = lean_ctor_get(v___y_1936_, 0);
v_action_1939_ = lean_ctor_get_uint8(v___y_1936_, sizeof(void*)*3);
v_wantsRebuild_1940_ = lean_ctor_get_uint8(v___y_1936_, sizeof(void*)*3 + 1);
v_trace_1941_ = lean_ctor_get(v___y_1936_, 1);
v_buildTime_1942_ = lean_ctor_get(v___y_1936_, 2);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___y_1936_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1944_ = v___y_1936_;
v_isShared_1945_ = v_isSharedCheck_1954_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_buildTime_1942_);
lean_inc(v_trace_1941_);
lean_inc(v_log_1938_);
lean_dec(v___y_1936_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1954_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1951_; 
v___x_1946_ = lean_io_mono_ms_now();
v___x_1947_ = lean_nat_sub(v___x_1946_, v_val_1934_);
lean_dec(v___x_1946_);
v___x_1948_ = lean_box(0);
v___x_1949_ = lean_nat_add(v_buildTime_1942_, v___x_1947_);
lean_dec(v___x_1947_);
lean_dec(v_buildTime_1942_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 2, v___x_1949_);
v___x_1951_ = v___x_1944_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_log_1938_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v_trace_1941_);
lean_ctor_set(v_reuseFailAlloc_1953_, 2, v___x_1949_);
lean_ctor_set_uint8(v_reuseFailAlloc_1953_, sizeof(void*)*3, v_action_1939_);
lean_ctor_set_uint8(v_reuseFailAlloc_1953_, sizeof(void*)*3 + 1, v_wantsRebuild_1940_);
v___x_1951_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
lean_object* v___x_1952_; 
v___x_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1948_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
return v___x_1952_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0___boxed(lean_object* v_val_1955_, lean_object* v_a_x3f_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lake_buildAction___redArg___lam__0(v_val_1955_, v_a_x3f_1956_, v___y_1957_);
lean_dec(v_a_x3f_1956_);
lean_dec(v_val_1955_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg(lean_object* v_inst_1965_, lean_object* v_depTrace_1966_, lean_object* v_traceFile_1967_, lean_object* v_build_1968_, uint8_t v_action_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v_a_1978_; lean_object* v_a_1979_; lean_object* v_log_1982_; uint8_t v_action_1983_; uint8_t v_wantsRebuild_1984_; lean_object* v_trace_1985_; lean_object* v_buildTime_1986_; lean_object* v_toBuildConfig_1992_; lean_object* v_log_1993_; uint8_t v_action_1994_; uint8_t v_wantsRebuild_1995_; lean_object* v_trace_1996_; lean_object* v_buildTime_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2103_; 
v_toBuildConfig_1992_ = lean_ctor_get(v_a_1974_, 0);
v_log_1993_ = lean_ctor_get(v_a_1975_, 0);
v_action_1994_ = lean_ctor_get_uint8(v_a_1975_, sizeof(void*)*3);
v_wantsRebuild_1995_ = lean_ctor_get_uint8(v_a_1975_, sizeof(void*)*3 + 1);
v_trace_1996_ = lean_ctor_get(v_a_1975_, 1);
v_buildTime_1997_ = lean_ctor_get(v_a_1975_, 2);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_a_1975_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_1999_ = v_a_1975_;
v_isShared_2000_ = v_isSharedCheck_2103_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_buildTime_1997_);
lean_inc(v_trace_1996_);
lean_inc(v_log_1993_);
lean_dec(v_a_1975_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2103_;
goto v_resetjp_1998_;
}
v___jp_1977_:
{
lean_object* v___x_1980_; 
v___x_1980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1980_, 0, v_a_1978_);
lean_ctor_set(v___x_1980_, 1, v_a_1979_);
return v___x_1980_;
}
v___jp_1981_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1987_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_1988_ = lean_array_get_size(v_log_1982_);
v___x_1989_ = lean_array_push(v_log_1982_, v___x_1987_);
v___x_1990_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
lean_ctor_set(v___x_1990_, 1, v_trace_1985_);
lean_ctor_set(v___x_1990_, 2, v_buildTime_1986_);
lean_ctor_set_uint8(v___x_1990_, sizeof(void*)*3, v_action_1983_);
lean_ctor_set_uint8(v___x_1990_, sizeof(void*)*3 + 1, v_wantsRebuild_1984_);
v___x_1991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1988_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
return v___x_1991_;
}
v_resetjp_1998_:
{
uint8_t v_noBuild_2001_; uint8_t v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v_noBuild_2001_ = lean_ctor_get_uint8(v_toBuildConfig_1992_, sizeof(void*)*4 + 2);
v___x_2002_ = l_Lake_JobAction_merge(v_action_1994_, v_action_1969_);
v___x_2003_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_1967_);
v___x_2004_ = l_System_FilePath_addExtension(v_traceFile_1967_, v___x_2003_);
if (v_noBuild_2001_ == 0)
{
lean_object* v___x_2005_; lean_object* v_a_2007_; lean_object* v_a_2008_; lean_object* v___x_2013_; 
v___x_2005_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_1993_);
if (v_isShared_2000_ == 0)
{
v___x_2013_ = v___x_1999_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_log_1993_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_trace_1996_);
lean_ctor_set(v_reuseFailAlloc_2087_, 2, v_buildTime_1997_);
lean_ctor_set_uint8(v_reuseFailAlloc_2087_, sizeof(void*)*3 + 1, v_wantsRebuild_1995_);
v___x_2013_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2012_;
}
v___jp_2006_:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v_a_2011_; 
v___x_2009_ = lean_box(0);
v___x_2010_ = l_Lake_buildAction___redArg___lam__0(v___x_2005_, v___x_2009_, v_a_2008_);
lean_dec(v___x_2005_);
v_a_2011_ = lean_ctor_get(v___x_2010_, 1);
lean_inc(v_a_2011_);
lean_dec_ref(v___x_2010_);
v_a_1978_ = v_a_2007_;
v_a_1979_ = v_a_2011_;
goto v___jp_1977_;
}
v_reusejp_2012_:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
lean_ctor_set_uint8(v___x_2013_, sizeof(void*)*3, v___x_2002_);
v___x_2014_ = lean_array_get_size(v_log_1993_);
lean_dec_ref(v_log_1993_);
lean_inc_ref(v_a_1974_);
lean_inc(v_a_1973_);
lean_inc(v_a_1972_);
lean_inc(v_a_1971_);
v___x_2015_ = lean_apply_7(v_build_1968_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v___x_2013_, lean_box(0));
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v_a_2017_; lean_object* v_log_2018_; uint8_t v_action_2019_; uint8_t v_wantsRebuild_2020_; lean_object* v_trace_2021_; lean_object* v_buildTime_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 1);
lean_inc(v_a_2016_);
v_a_2017_ = lean_ctor_get(v___x_2015_, 0);
lean_inc_n(v_a_2017_, 2);
lean_dec_ref_known(v___x_2015_, 2);
v_log_2018_ = lean_ctor_get(v_a_2016_, 0);
v_action_2019_ = lean_ctor_get_uint8(v_a_2016_, sizeof(void*)*3);
v_wantsRebuild_2020_ = lean_ctor_get_uint8(v_a_2016_, sizeof(void*)*3 + 1);
v_trace_2021_ = lean_ctor_get(v_a_2016_, 1);
v_buildTime_2022_ = lean_ctor_get(v_a_2016_, 2);
v___x_2023_ = lean_array_get_size(v_log_2018_);
v___x_2024_ = l_Array_extract___redArg(v_log_2018_, v___x_2014_, v___x_2023_);
v___x_2025_ = lean_apply_1(v_inst_1965_, v_a_2017_);
v___x_2026_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1966_, v___x_2025_, v___x_2024_);
v___x_2027_ = l_Lake_BuildMetadata_writeFile(v_traceFile_1967_, v___x_2026_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2068_; 
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2068_ == 0)
{
lean_object* v_unused_2069_; 
v_unused_2069_ = lean_ctor_get(v___x_2027_, 0);
lean_dec(v_unused_2069_);
v___x_2029_ = v___x_2027_;
v_isShared_2030_ = v_isSharedCheck_2068_;
goto v_resetjp_2028_;
}
else
{
lean_dec(v___x_2027_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2068_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2031_; 
v___x_2031_ = l_Lake_removeFileIfExists(v___x_2004_);
lean_dec_ref(v___x_2004_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2051_; 
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; 
v_unused_2052_ = lean_ctor_get(v___x_2031_, 0);
lean_dec(v_unused_2052_);
v___x_2033_ = v___x_2031_;
v_isShared_2034_ = v_isSharedCheck_2051_;
goto v_resetjp_2032_;
}
else
{
lean_dec(v___x_2031_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2051_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
lean_inc(v_a_2017_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 0, v_a_2017_);
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2017_);
v___x_2036_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
lean_object* v___x_2038_; 
if (v_isShared_2030_ == 0)
{
lean_ctor_set_tag(v___x_2029_, 1);
lean_ctor_set(v___x_2029_, 0, v___x_2036_);
v___x_2038_ = v___x_2029_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2039_; lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
v___x_2039_ = l_Lake_buildAction___redArg___lam__0(v___x_2005_, v___x_2038_, v_a_2016_);
lean_dec_ref(v___x_2038_);
lean_dec(v___x_2005_);
v_a_2040_ = lean_ctor_get(v___x_2039_, 1);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2047_ == 0)
{
lean_object* v_unused_2048_; 
v_unused_2048_ = lean_ctor_get(v___x_2039_, 0);
lean_dec(v_unused_2048_);
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v_a_2017_);
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2017_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
}
}
else
{
lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2064_; 
lean_inc(v_buildTime_2022_);
lean_inc_ref(v_trace_2021_);
lean_inc_ref(v_log_2018_);
lean_del_object(v___x_2029_);
lean_dec(v_a_2017_);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_a_2016_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; lean_object* v_unused_2066_; lean_object* v_unused_2067_; 
v_unused_2065_ = lean_ctor_get(v_a_2016_, 2);
lean_dec(v_unused_2065_);
v_unused_2066_ = lean_ctor_get(v_a_2016_, 1);
lean_dec(v_unused_2066_);
v_unused_2067_ = lean_ctor_get(v_a_2016_, 0);
lean_dec(v_unused_2067_);
v___x_2054_ = v_a_2016_;
v_isShared_2055_ = v_isSharedCheck_2064_;
goto v_resetjp_2053_;
}
else
{
lean_dec(v_a_2016_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2064_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v_a_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2062_; 
v_a_2056_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___x_2031_, 1);
v___x_2057_ = lean_io_error_to_string(v_a_2056_);
v___x_2058_ = 3;
v___x_2059_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2059_, 0, v___x_2057_);
lean_ctor_set_uint8(v___x_2059_, sizeof(void*)*1, v___x_2058_);
v___x_2060_ = lean_array_push(v_log_2018_, v___x_2059_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2060_);
v___x_2062_ = v___x_2054_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_trace_2021_);
lean_ctor_set(v_reuseFailAlloc_2063_, 2, v_buildTime_2022_);
lean_ctor_set_uint8(v_reuseFailAlloc_2063_, sizeof(void*)*3, v_action_2019_);
lean_ctor_set_uint8(v_reuseFailAlloc_2063_, sizeof(void*)*3 + 1, v_wantsRebuild_2020_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
v_a_2007_ = v___x_2023_;
v_a_2008_ = v___x_2062_;
goto v___jp_2006_;
}
}
}
}
}
else
{
lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2081_; 
lean_inc(v_buildTime_2022_);
lean_inc_ref(v_trace_2021_);
lean_inc_ref(v_log_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v___x_2004_);
v_isSharedCheck_2081_ = !lean_is_exclusive(v_a_2016_);
if (v_isSharedCheck_2081_ == 0)
{
lean_object* v_unused_2082_; lean_object* v_unused_2083_; lean_object* v_unused_2084_; 
v_unused_2082_ = lean_ctor_get(v_a_2016_, 2);
lean_dec(v_unused_2082_);
v_unused_2083_ = lean_ctor_get(v_a_2016_, 1);
lean_dec(v_unused_2083_);
v_unused_2084_ = lean_ctor_get(v_a_2016_, 0);
lean_dec(v_unused_2084_);
v___x_2071_ = v_a_2016_;
v_isShared_2072_ = v_isSharedCheck_2081_;
goto v_resetjp_2070_;
}
else
{
lean_dec(v_a_2016_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2081_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v_a_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2079_; 
v_a_2073_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2073_);
lean_dec_ref_known(v___x_2027_, 1);
v___x_2074_ = lean_io_error_to_string(v_a_2073_);
v___x_2075_ = 3;
v___x_2076_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2076_, 0, v___x_2074_);
lean_ctor_set_uint8(v___x_2076_, sizeof(void*)*1, v___x_2075_);
v___x_2077_ = lean_array_push(v_log_2018_, v___x_2076_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 0, v___x_2077_);
v___x_2079_ = v___x_2071_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v___x_2077_);
lean_ctor_set(v_reuseFailAlloc_2080_, 1, v_trace_2021_);
lean_ctor_set(v_reuseFailAlloc_2080_, 2, v_buildTime_2022_);
lean_ctor_set_uint8(v_reuseFailAlloc_2080_, sizeof(void*)*3, v_action_2019_);
lean_ctor_set_uint8(v_reuseFailAlloc_2080_, sizeof(void*)*3 + 1, v_wantsRebuild_2020_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
v_a_2007_ = v___x_2023_;
v_a_2008_ = v___x_2079_;
goto v___jp_2006_;
}
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v_a_2086_; 
lean_dec_ref(v___x_2004_);
lean_dec_ref(v_traceFile_1967_);
lean_dec_ref(v_inst_1965_);
v_a_2085_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2085_);
v_a_2086_ = lean_ctor_get(v___x_2015_, 1);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2015_, 2);
v_a_2007_ = v_a_2085_;
v_a_2008_ = v_a_2086_;
goto v___jp_2006_;
}
}
}
else
{
uint8_t v___x_2088_; 
lean_dec_ref(v_a_1970_);
lean_dec_ref(v_build_1968_);
lean_dec_ref(v_inst_1965_);
v___x_2088_ = l_System_FilePath_pathExists(v_traceFile_1967_);
lean_dec_ref(v_traceFile_1967_);
if (v___x_2088_ == 0)
{
lean_dec_ref(v___x_2004_);
lean_del_object(v___x_1999_);
v_log_1982_ = v_log_1993_;
v_action_1983_ = v___x_2002_;
v_wantsRebuild_1984_ = v_noBuild_2001_;
v_trace_1985_ = v_trace_1996_;
v_buildTime_1986_ = v_buildTime_1997_;
goto v___jp_1981_;
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2089_ = lean_box(0);
v___x_2090_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_2091_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1966_, v___x_2089_, v___x_2090_);
v___x_2092_ = l_Lake_BuildMetadata_writeFile(v___x_2004_, v___x_2091_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_dec_ref_known(v___x_2092_, 1);
lean_del_object(v___x_1999_);
v_log_1982_ = v_log_1993_;
v_action_1983_ = v___x_2002_;
v_wantsRebuild_1984_ = v_noBuild_2001_;
v_trace_1985_ = v_trace_1996_;
v_buildTime_1986_ = v_buildTime_1997_;
goto v___jp_1981_;
}
else
{
lean_object* v_a_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2100_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2092_, 1);
v___x_2094_ = lean_io_error_to_string(v_a_2093_);
v___x_2095_ = 3;
v___x_2096_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2096_, 0, v___x_2094_);
lean_ctor_set_uint8(v___x_2096_, sizeof(void*)*1, v___x_2095_);
v___x_2097_ = lean_array_get_size(v_log_1993_);
v___x_2098_ = lean_array_push(v_log_1993_, v___x_2096_);
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 0, v___x_2098_);
v___x_2100_ = v___x_1999_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_trace_1996_);
lean_ctor_set(v_reuseFailAlloc_2102_, 2, v_buildTime_1997_);
v___x_2100_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2101_; 
lean_ctor_set_uint8(v___x_2100_, sizeof(void*)*3, v___x_2002_);
lean_ctor_set_uint8(v___x_2100_, sizeof(void*)*3 + 1, v_noBuild_2001_);
v___x_2101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2097_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
return v___x_2101_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___boxed(lean_object* v_inst_2104_, lean_object* v_depTrace_2105_, lean_object* v_traceFile_2106_, lean_object* v_build_2107_, lean_object* v_action_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_){
_start:
{
uint8_t v_action_boxed_2116_; lean_object* v_res_2117_; 
v_action_boxed_2116_ = lean_unbox(v_action_2108_);
v_res_2117_ = l_Lake_buildAction___redArg(v_inst_2104_, v_depTrace_2105_, v_traceFile_2106_, v_build_2107_, v_action_boxed_2116_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
lean_dec_ref(v_a_2113_);
lean_dec(v_a_2112_);
lean_dec(v_a_2111_);
lean_dec(v_a_2110_);
lean_dec_ref(v_depTrace_2105_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction(lean_object* v_00_u03b1_2118_, lean_object* v_inst_2119_, lean_object* v_depTrace_2120_, lean_object* v_traceFile_2121_, lean_object* v_build_2122_, uint8_t v_action_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
lean_object* v___x_2131_; 
v___x_2131_ = l_Lake_buildAction___redArg(v_inst_2119_, v_depTrace_2120_, v_traceFile_2121_, v_build_2122_, v_action_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___boxed(lean_object* v_00_u03b1_2132_, lean_object* v_inst_2133_, lean_object* v_depTrace_2134_, lean_object* v_traceFile_2135_, lean_object* v_build_2136_, lean_object* v_action_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_){
_start:
{
uint8_t v_action_boxed_2145_; lean_object* v_res_2146_; 
v_action_boxed_2145_ = lean_unbox(v_action_2137_);
v_res_2146_ = l_Lake_buildAction(v_00_u03b1_2132_, v_inst_2133_, v_depTrace_2134_, v_traceFile_2135_, v_build_2136_, v_action_boxed_2145_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
lean_dec_ref(v_a_2142_);
lean_dec(v_a_2141_);
lean_dec(v_a_2140_);
lean_dec(v_a_2139_);
lean_dec_ref(v_depTrace_2134_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg(lean_object* v_inst_2147_, lean_object* v_inst_2148_, lean_object* v_info_2149_, lean_object* v_depTrace_2150_, lean_object* v_traceFile_2151_, lean_object* v_build_2152_, uint8_t v_action_2153_, lean_object* v_oldTrace_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_){
_start:
{
lean_object* v_log_2162_; uint8_t v_action_2163_; uint8_t v_wantsRebuild_2164_; lean_object* v_trace_2165_; lean_object* v_buildTime_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2235_; 
v_log_2162_ = lean_ctor_get(v_a_2160_, 0);
v_action_2163_ = lean_ctor_get_uint8(v_a_2160_, sizeof(void*)*3);
v_wantsRebuild_2164_ = lean_ctor_get_uint8(v_a_2160_, sizeof(void*)*3 + 1);
v_trace_2165_ = lean_ctor_get(v_a_2160_, 1);
v_buildTime_2166_ = lean_ctor_get(v_a_2160_, 2);
v_isSharedCheck_2235_ = !lean_is_exclusive(v_a_2160_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2168_ = v_a_2160_;
v_isShared_2169_ = v_isSharedCheck_2235_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_buildTime_2166_);
lean_inc(v_trace_2165_);
lean_inc(v_log_2162_);
lean_dec(v_a_2160_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2235_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___f_2170_; lean_object* v___x_2171_; 
v___f_2170_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
lean_inc_ref(v_traceFile_2151_);
v___x_2171_ = l_Lake_readTraceFile(v_traceFile_2151_, v_log_2162_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v_a_2173_; lean_object* v___x_2175_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2172_);
v_a_2173_ = lean_ctor_get(v___x_2171_, 1);
lean_inc(v_a_2173_);
lean_dec_ref_known(v___x_2171_, 2);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 0, v_a_2173_);
v___x_2175_ = v___x_2168_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2173_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_trace_2165_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v_buildTime_2166_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*3, v_action_2163_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*3 + 1, v_wantsRebuild_2164_);
v___x_2175_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2147_, v_inst_2148_, v_info_2149_, v_depTrace_2150_, v_a_2172_, v_oldTrace_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v___x_2175_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2212_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
v_a_2178_ = lean_ctor_get(v___x_2176_, 1);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2180_ = v___x_2176_;
v_isShared_2181_ = v_isSharedCheck_2212_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_inc(v_a_2177_);
lean_dec(v___x_2176_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2212_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
uint8_t v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; 
v___x_2182_ = lean_unbox(v_a_2177_);
lean_dec(v_a_2177_);
v___x_2183_ = l_Lake_OutputStatus_ctorIdx(v___x_2182_);
v___x_2184_ = lean_obj_once(&l_Lake_OutputStatus_isUpToDate___closed__0, &l_Lake_OutputStatus_isUpToDate___closed__0_once, _init_l_Lake_OutputStatus_isUpToDate___closed__0);
v___x_2185_ = lean_nat_dec_eq(v___x_2183_, v___x_2184_);
lean_dec(v___x_2183_);
if (v___x_2185_ == 0)
{
uint8_t v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2189_; 
lean_dec_ref(v_a_2155_);
lean_dec_ref(v_build_2152_);
lean_dec_ref(v_traceFile_2151_);
v___x_2186_ = 1;
v___x_2187_ = lean_box(v___x_2186_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 0, v___x_2187_);
v___x_2189_ = v___x_2180_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2187_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v_a_2178_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
else
{
uint8_t v___x_2191_; lean_object* v___x_2192_; 
lean_del_object(v___x_2180_);
v___x_2191_ = 0;
v___x_2192_ = l_Lake_buildAction___redArg(v___f_2170_, v_depTrace_2150_, v_traceFile_2151_, v_build_2152_, v_action_2153_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2178_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2201_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 1);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2201_ == 0)
{
lean_object* v_unused_2202_; 
v_unused_2202_ = lean_ctor_get(v___x_2192_, 0);
lean_dec(v_unused_2202_);
v___x_2195_ = v___x_2192_;
v_isShared_2196_ = v_isSharedCheck_2201_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2192_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2201_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2197_; lean_object* v___x_2199_; 
v___x_2197_ = lean_box(v___x_2191_);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 0, v___x_2197_);
v___x_2199_ = v___x_2195_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_a_2193_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
else
{
lean_object* v_a_2203_; lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
v_a_2203_ = lean_ctor_get(v___x_2192_, 0);
v_a_2204_ = lean_ctor_get(v___x_2192_, 1);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2192_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_inc(v_a_2203_);
lean_dec(v___x_2192_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2203_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec_ref(v_a_2155_);
lean_dec_ref(v_build_2152_);
lean_dec_ref(v_traceFile_2151_);
v_a_2213_ = lean_ctor_get(v___x_2176_, 0);
v_a_2214_ = lean_ctor_get(v___x_2176_, 1);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2176_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_inc(v_a_2213_);
lean_dec(v___x_2176_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2213_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v_a_2214_);
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
else
{
lean_object* v_a_2223_; lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2234_; 
lean_dec_ref(v_a_2155_);
lean_dec_ref(v_build_2152_);
lean_dec_ref(v_traceFile_2151_);
lean_dec(v_info_2149_);
lean_dec_ref(v_inst_2148_);
lean_dec_ref(v_inst_2147_);
v_a_2223_ = lean_ctor_get(v___x_2171_, 0);
v_a_2224_ = lean_ctor_get(v___x_2171_, 1);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2226_ = v___x_2171_;
v_isShared_2227_ = v_isSharedCheck_2234_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_inc(v_a_2223_);
lean_dec(v___x_2171_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2234_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 0, v_a_2224_);
v___x_2229_ = v___x_2168_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2224_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v_trace_2165_);
lean_ctor_set(v_reuseFailAlloc_2233_, 2, v_buildTime_2166_);
lean_ctor_set_uint8(v_reuseFailAlloc_2233_, sizeof(void*)*3, v_action_2163_);
lean_ctor_set_uint8(v_reuseFailAlloc_2233_, sizeof(void*)*3 + 1, v_wantsRebuild_2164_);
v___x_2229_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
lean_object* v___x_2231_; 
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 1, v___x_2229_);
v___x_2231_ = v___x_2226_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2223_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v___x_2229_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg___boxed(lean_object* v_inst_2236_, lean_object* v_inst_2237_, lean_object* v_info_2238_, lean_object* v_depTrace_2239_, lean_object* v_traceFile_2240_, lean_object* v_build_2241_, lean_object* v_action_2242_, lean_object* v_oldTrace_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_){
_start:
{
uint8_t v_action_boxed_2251_; lean_object* v_res_2252_; 
v_action_boxed_2251_ = lean_unbox(v_action_2242_);
v_res_2252_ = l_Lake_buildUnlessUpToDate_x3f___redArg(v_inst_2236_, v_inst_2237_, v_info_2238_, v_depTrace_2239_, v_traceFile_2240_, v_build_2241_, v_action_boxed_2251_, v_oldTrace_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
lean_dec_ref(v_a_2248_);
lean_dec(v_a_2247_);
lean_dec(v_a_2246_);
lean_dec(v_a_2245_);
lean_dec_ref(v_oldTrace_2243_);
lean_dec_ref(v_depTrace_2239_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f(lean_object* v_00_u03b9_2253_, lean_object* v_inst_2254_, lean_object* v_inst_2255_, lean_object* v_info_2256_, lean_object* v_depTrace_2257_, lean_object* v_traceFile_2258_, lean_object* v_build_2259_, uint8_t v_action_2260_, lean_object* v_oldTrace_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_){
_start:
{
lean_object* v_log_2269_; uint8_t v_action_2270_; uint8_t v_wantsRebuild_2271_; lean_object* v_trace_2272_; lean_object* v_buildTime_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2342_; 
v_log_2269_ = lean_ctor_get(v_a_2267_, 0);
v_action_2270_ = lean_ctor_get_uint8(v_a_2267_, sizeof(void*)*3);
v_wantsRebuild_2271_ = lean_ctor_get_uint8(v_a_2267_, sizeof(void*)*3 + 1);
v_trace_2272_ = lean_ctor_get(v_a_2267_, 1);
v_buildTime_2273_ = lean_ctor_get(v_a_2267_, 2);
v_isSharedCheck_2342_ = !lean_is_exclusive(v_a_2267_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2275_ = v_a_2267_;
v_isShared_2276_ = v_isSharedCheck_2342_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_buildTime_2273_);
lean_inc(v_trace_2272_);
lean_inc(v_log_2269_);
lean_dec(v_a_2267_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2342_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___f_2277_; lean_object* v___x_2278_; 
v___f_2277_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
lean_inc_ref(v_traceFile_2258_);
v___x_2278_ = l_Lake_readTraceFile(v_traceFile_2258_, v_log_2269_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v_a_2280_; lean_object* v___x_2282_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2279_);
v_a_2280_ = lean_ctor_get(v___x_2278_, 1);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___x_2278_, 2);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 0, v_a_2280_);
v___x_2282_ = v___x_2275_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2280_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v_trace_2272_);
lean_ctor_set(v_reuseFailAlloc_2329_, 2, v_buildTime_2273_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*3, v_action_2270_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*3 + 1, v_wantsRebuild_2271_);
v___x_2282_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2254_, v_inst_2255_, v_info_2256_, v_depTrace_2257_, v_a_2279_, v_oldTrace_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v___x_2282_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2319_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
v_a_2285_ = lean_ctor_get(v___x_2283_, 1);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2287_ = v___x_2283_;
v_isShared_2288_ = v_isSharedCheck_2319_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_inc(v_a_2284_);
lean_dec(v___x_2283_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2319_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
uint8_t v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; uint8_t v___x_2292_; 
v___x_2289_ = lean_unbox(v_a_2284_);
lean_dec(v_a_2284_);
v___x_2290_ = l_Lake_OutputStatus_ctorIdx(v___x_2289_);
v___x_2291_ = lean_obj_once(&l_Lake_OutputStatus_isUpToDate___closed__0, &l_Lake_OutputStatus_isUpToDate___closed__0_once, _init_l_Lake_OutputStatus_isUpToDate___closed__0);
v___x_2292_ = lean_nat_dec_eq(v___x_2290_, v___x_2291_);
lean_dec(v___x_2290_);
if (v___x_2292_ == 0)
{
uint8_t v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2296_; 
lean_dec_ref(v_a_2262_);
lean_dec_ref(v_build_2259_);
lean_dec_ref(v_traceFile_2258_);
v___x_2293_ = 1;
v___x_2294_ = lean_box(v___x_2293_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v___x_2294_);
v___x_2296_ = v___x_2287_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2294_);
lean_ctor_set(v_reuseFailAlloc_2297_, 1, v_a_2285_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
else
{
uint8_t v___x_2298_; lean_object* v___x_2299_; 
lean_del_object(v___x_2287_);
v___x_2298_ = 0;
v___x_2299_ = l_Lake_buildAction___redArg(v___f_2277_, v_depTrace_2257_, v_traceFile_2258_, v_build_2259_, v_action_2260_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2285_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2308_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 1);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2308_ == 0)
{
lean_object* v_unused_2309_; 
v_unused_2309_ = lean_ctor_get(v___x_2299_, 0);
lean_dec(v_unused_2309_);
v___x_2302_ = v___x_2299_;
v_isShared_2303_ = v_isSharedCheck_2308_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2299_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2308_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2304_; lean_object* v___x_2306_; 
v___x_2304_ = lean_box(v___x_2298_);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v___x_2304_);
v___x_2306_ = v___x_2302_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_a_2300_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
v_a_2310_ = lean_ctor_get(v___x_2299_, 0);
v_a_2311_ = lean_ctor_get(v___x_2299_, 1);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2299_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_inc(v_a_2310_);
lean_dec(v___x_2299_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2310_);
lean_ctor_set(v_reuseFailAlloc_2317_, 1, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
}
}
else
{
lean_object* v_a_2320_; lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec_ref(v_a_2262_);
lean_dec_ref(v_build_2259_);
lean_dec_ref(v_traceFile_2258_);
v_a_2320_ = lean_ctor_get(v___x_2283_, 0);
v_a_2321_ = lean_ctor_get(v___x_2283_, 1);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2283_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_inc(v_a_2320_);
lean_dec(v___x_2283_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2320_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_a_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
}
else
{
lean_object* v_a_2330_; lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2341_; 
lean_dec_ref(v_a_2262_);
lean_dec_ref(v_build_2259_);
lean_dec_ref(v_traceFile_2258_);
lean_dec(v_info_2256_);
lean_dec_ref(v_inst_2255_);
lean_dec_ref(v_inst_2254_);
v_a_2330_ = lean_ctor_get(v___x_2278_, 0);
v_a_2331_ = lean_ctor_get(v___x_2278_, 1);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2333_ = v___x_2278_;
v_isShared_2334_ = v_isSharedCheck_2341_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_inc(v_a_2330_);
lean_dec(v___x_2278_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2341_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 0, v_a_2331_);
v___x_2336_ = v___x_2275_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2331_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_trace_2272_);
lean_ctor_set(v_reuseFailAlloc_2340_, 2, v_buildTime_2273_);
lean_ctor_set_uint8(v_reuseFailAlloc_2340_, sizeof(void*)*3, v_action_2270_);
lean_ctor_set_uint8(v_reuseFailAlloc_2340_, sizeof(void*)*3 + 1, v_wantsRebuild_2271_);
v___x_2336_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
lean_object* v___x_2338_; 
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 1, v___x_2336_);
v___x_2338_ = v___x_2333_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2330_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v___x_2336_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___boxed(lean_object* v_00_u03b9_2343_, lean_object* v_inst_2344_, lean_object* v_inst_2345_, lean_object* v_info_2346_, lean_object* v_depTrace_2347_, lean_object* v_traceFile_2348_, lean_object* v_build_2349_, lean_object* v_action_2350_, lean_object* v_oldTrace_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_){
_start:
{
uint8_t v_action_boxed_2359_; lean_object* v_res_2360_; 
v_action_boxed_2359_ = lean_unbox(v_action_2350_);
v_res_2360_ = l_Lake_buildUnlessUpToDate_x3f(v_00_u03b9_2343_, v_inst_2344_, v_inst_2345_, v_info_2346_, v_depTrace_2347_, v_traceFile_2348_, v_build_2349_, v_action_boxed_2359_, v_oldTrace_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
lean_dec_ref(v_a_2356_);
lean_dec(v_a_2355_);
lean_dec(v_a_2354_);
lean_dec(v_a_2353_);
lean_dec_ref(v_oldTrace_2351_);
lean_dec_ref(v_depTrace_2347_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg(lean_object* v_inst_2361_, lean_object* v_inst_2362_, lean_object* v_info_2363_, lean_object* v_depTrace_2364_, lean_object* v_traceFile_2365_, lean_object* v_build_2366_, uint8_t v_action_2367_, lean_object* v_oldTrace_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_){
_start:
{
lean_object* v_a_2377_; lean_object* v_a_2378_; lean_object* v_log_2380_; uint8_t v_action_2381_; uint8_t v_wantsRebuild_2382_; lean_object* v_trace_2383_; lean_object* v_buildTime_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2417_; 
v_log_2380_ = lean_ctor_get(v_a_2374_, 0);
v_action_2381_ = lean_ctor_get_uint8(v_a_2374_, sizeof(void*)*3);
v_wantsRebuild_2382_ = lean_ctor_get_uint8(v_a_2374_, sizeof(void*)*3 + 1);
v_trace_2383_ = lean_ctor_get(v_a_2374_, 1);
v_buildTime_2384_ = lean_ctor_get(v_a_2374_, 2);
v_isSharedCheck_2417_ = !lean_is_exclusive(v_a_2374_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2386_ = v_a_2374_;
v_isShared_2387_ = v_isSharedCheck_2417_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_buildTime_2384_);
lean_inc(v_trace_2383_);
lean_inc(v_log_2380_);
lean_dec(v_a_2374_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2417_;
goto v_resetjp_2385_;
}
v___jp_2376_:
{
lean_object* v___x_2379_; 
v___x_2379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2379_, 0, v_a_2377_);
lean_ctor_set(v___x_2379_, 1, v_a_2378_);
return v___x_2379_;
}
v_resetjp_2385_:
{
lean_object* v___x_2388_; lean_object* v_a_2390_; lean_object* v___f_2392_; lean_object* v___x_2393_; 
v___x_2388_ = lean_box(0);
v___f_2392_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
lean_inc_ref(v_traceFile_2365_);
v___x_2393_ = l_Lake_readTraceFile(v_traceFile_2365_, v_log_2380_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v_a_2395_; lean_object* v___x_2397_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
v_a_2395_ = lean_ctor_get(v___x_2393_, 1);
lean_inc(v_a_2395_);
lean_dec_ref_known(v___x_2393_, 2);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 0, v_a_2395_);
v___x_2397_ = v___x_2386_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2395_);
lean_ctor_set(v_reuseFailAlloc_2411_, 1, v_trace_2383_);
lean_ctor_set(v_reuseFailAlloc_2411_, 2, v_buildTime_2384_);
lean_ctor_set_uint8(v_reuseFailAlloc_2411_, sizeof(void*)*3, v_action_2381_);
lean_ctor_set_uint8(v_reuseFailAlloc_2411_, sizeof(void*)*3 + 1, v_wantsRebuild_2382_);
v___x_2397_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
lean_object* v___x_2398_; 
v___x_2398_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2361_, v_inst_2362_, v_info_2363_, v_depTrace_2364_, v_a_2394_, v_oldTrace_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v___x_2397_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; lean_object* v_a_2400_; uint8_t v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; uint8_t v___x_2404_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_a_2399_);
v_a_2400_ = lean_ctor_get(v___x_2398_, 1);
lean_inc(v_a_2400_);
lean_dec_ref_known(v___x_2398_, 2);
v___x_2401_ = lean_unbox(v_a_2399_);
lean_dec(v_a_2399_);
v___x_2402_ = l_Lake_OutputStatus_ctorIdx(v___x_2401_);
v___x_2403_ = lean_obj_once(&l_Lake_OutputStatus_isUpToDate___closed__0, &l_Lake_OutputStatus_isUpToDate___closed__0_once, _init_l_Lake_OutputStatus_isUpToDate___closed__0);
v___x_2404_ = lean_nat_dec_eq(v___x_2402_, v___x_2403_);
lean_dec(v___x_2402_);
if (v___x_2404_ == 0)
{
lean_dec_ref(v_a_2369_);
lean_dec_ref(v_build_2366_);
lean_dec_ref(v_traceFile_2365_);
v_a_2390_ = v_a_2400_;
goto v___jp_2389_;
}
else
{
lean_object* v___x_2405_; 
v___x_2405_ = l_Lake_buildAction___redArg(v___f_2392_, v_depTrace_2364_, v_traceFile_2365_, v_build_2366_, v_action_2367_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2400_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 1);
lean_inc(v_a_2406_);
lean_dec_ref_known(v___x_2405_, 2);
v_a_2390_ = v_a_2406_;
goto v___jp_2389_;
}
else
{
lean_object* v_a_2407_; lean_object* v_a_2408_; 
v_a_2407_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2407_);
v_a_2408_ = lean_ctor_get(v___x_2405_, 1);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2405_, 2);
v_a_2377_ = v_a_2407_;
v_a_2378_ = v_a_2408_;
goto v___jp_2376_;
}
}
}
else
{
lean_object* v_a_2409_; lean_object* v_a_2410_; 
lean_dec_ref(v_a_2369_);
lean_dec_ref(v_build_2366_);
lean_dec_ref(v_traceFile_2365_);
v_a_2409_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_a_2409_);
v_a_2410_ = lean_ctor_get(v___x_2398_, 1);
lean_inc(v_a_2410_);
lean_dec_ref_known(v___x_2398_, 2);
v_a_2377_ = v_a_2409_;
v_a_2378_ = v_a_2410_;
goto v___jp_2376_;
}
}
}
else
{
lean_object* v_a_2412_; lean_object* v_a_2413_; lean_object* v___x_2415_; 
lean_dec_ref(v_a_2369_);
lean_dec_ref(v_build_2366_);
lean_dec_ref(v_traceFile_2365_);
lean_dec(v_info_2363_);
lean_dec_ref(v_inst_2362_);
lean_dec_ref(v_inst_2361_);
v_a_2412_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2412_);
v_a_2413_ = lean_ctor_get(v___x_2393_, 1);
lean_inc(v_a_2413_);
lean_dec_ref_known(v___x_2393_, 2);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 0, v_a_2413_);
v___x_2415_ = v___x_2386_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2413_);
lean_ctor_set(v_reuseFailAlloc_2416_, 1, v_trace_2383_);
lean_ctor_set(v_reuseFailAlloc_2416_, 2, v_buildTime_2384_);
lean_ctor_set_uint8(v_reuseFailAlloc_2416_, sizeof(void*)*3, v_action_2381_);
lean_ctor_set_uint8(v_reuseFailAlloc_2416_, sizeof(void*)*3 + 1, v_wantsRebuild_2382_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
v_a_2377_ = v_a_2412_;
v_a_2378_ = v___x_2415_;
goto v___jp_2376_;
}
}
v___jp_2389_:
{
lean_object* v___x_2391_; 
v___x_2391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2388_);
lean_ctor_set(v___x_2391_, 1, v_a_2390_);
return v___x_2391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg___boxed(lean_object* v_inst_2418_, lean_object* v_inst_2419_, lean_object* v_info_2420_, lean_object* v_depTrace_2421_, lean_object* v_traceFile_2422_, lean_object* v_build_2423_, lean_object* v_action_2424_, lean_object* v_oldTrace_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_){
_start:
{
uint8_t v_action_boxed_2433_; lean_object* v_res_2434_; 
v_action_boxed_2433_ = lean_unbox(v_action_2424_);
v_res_2434_ = l_Lake_buildUnlessUpToDate___redArg(v_inst_2418_, v_inst_2419_, v_info_2420_, v_depTrace_2421_, v_traceFile_2422_, v_build_2423_, v_action_boxed_2433_, v_oldTrace_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_);
lean_dec_ref(v_a_2430_);
lean_dec(v_a_2429_);
lean_dec(v_a_2428_);
lean_dec(v_a_2427_);
lean_dec_ref(v_oldTrace_2425_);
lean_dec_ref(v_depTrace_2421_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate(lean_object* v_00_u03b9_2435_, lean_object* v_inst_2436_, lean_object* v_inst_2437_, lean_object* v_info_2438_, lean_object* v_depTrace_2439_, lean_object* v_traceFile_2440_, lean_object* v_build_2441_, uint8_t v_action_2442_, lean_object* v_oldTrace_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v_a_2452_; lean_object* v_a_2453_; lean_object* v_log_2455_; uint8_t v_action_2456_; uint8_t v_wantsRebuild_2457_; lean_object* v_trace_2458_; lean_object* v_buildTime_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2492_; 
v_log_2455_ = lean_ctor_get(v_a_2449_, 0);
v_action_2456_ = lean_ctor_get_uint8(v_a_2449_, sizeof(void*)*3);
v_wantsRebuild_2457_ = lean_ctor_get_uint8(v_a_2449_, sizeof(void*)*3 + 1);
v_trace_2458_ = lean_ctor_get(v_a_2449_, 1);
v_buildTime_2459_ = lean_ctor_get(v_a_2449_, 2);
v_isSharedCheck_2492_ = !lean_is_exclusive(v_a_2449_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2461_ = v_a_2449_;
v_isShared_2462_ = v_isSharedCheck_2492_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_buildTime_2459_);
lean_inc(v_trace_2458_);
lean_inc(v_log_2455_);
lean_dec(v_a_2449_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2492_;
goto v_resetjp_2460_;
}
v___jp_2451_:
{
lean_object* v___x_2454_; 
v___x_2454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2454_, 0, v_a_2452_);
lean_ctor_set(v___x_2454_, 1, v_a_2453_);
return v___x_2454_;
}
v_resetjp_2460_:
{
lean_object* v___x_2463_; lean_object* v_a_2465_; lean_object* v___f_2467_; lean_object* v___x_2468_; 
v___x_2463_ = lean_box(0);
v___f_2467_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
lean_inc_ref(v_traceFile_2440_);
v___x_2468_ = l_Lake_readTraceFile(v_traceFile_2440_, v_log_2455_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; lean_object* v_a_2470_; lean_object* v___x_2472_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_a_2469_);
v_a_2470_ = lean_ctor_get(v___x_2468_, 1);
lean_inc(v_a_2470_);
lean_dec_ref_known(v___x_2468_, 2);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v_a_2470_);
v___x_2472_ = v___x_2461_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2470_);
lean_ctor_set(v_reuseFailAlloc_2486_, 1, v_trace_2458_);
lean_ctor_set(v_reuseFailAlloc_2486_, 2, v_buildTime_2459_);
lean_ctor_set_uint8(v_reuseFailAlloc_2486_, sizeof(void*)*3, v_action_2456_);
lean_ctor_set_uint8(v_reuseFailAlloc_2486_, sizeof(void*)*3 + 1, v_wantsRebuild_2457_);
v___x_2472_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
lean_object* v___x_2473_; 
v___x_2473_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2436_, v_inst_2437_, v_info_2438_, v_depTrace_2439_, v_a_2469_, v_oldTrace_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v___x_2472_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; lean_object* v_a_2475_; uint8_t v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; uint8_t v___x_2479_; 
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_a_2474_);
v_a_2475_ = lean_ctor_get(v___x_2473_, 1);
lean_inc(v_a_2475_);
lean_dec_ref_known(v___x_2473_, 2);
v___x_2476_ = lean_unbox(v_a_2474_);
lean_dec(v_a_2474_);
v___x_2477_ = l_Lake_OutputStatus_ctorIdx(v___x_2476_);
v___x_2478_ = lean_obj_once(&l_Lake_OutputStatus_isUpToDate___closed__0, &l_Lake_OutputStatus_isUpToDate___closed__0_once, _init_l_Lake_OutputStatus_isUpToDate___closed__0);
v___x_2479_ = lean_nat_dec_eq(v___x_2477_, v___x_2478_);
lean_dec(v___x_2477_);
if (v___x_2479_ == 0)
{
lean_dec_ref(v_a_2444_);
lean_dec_ref(v_build_2441_);
lean_dec_ref(v_traceFile_2440_);
v_a_2465_ = v_a_2475_;
goto v___jp_2464_;
}
else
{
lean_object* v___x_2480_; 
v___x_2480_ = l_Lake_buildAction___redArg(v___f_2467_, v_depTrace_2439_, v_traceFile_2440_, v_build_2441_, v_action_2442_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2475_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v_a_2481_; 
v_a_2481_ = lean_ctor_get(v___x_2480_, 1);
lean_inc(v_a_2481_);
lean_dec_ref_known(v___x_2480_, 2);
v_a_2465_ = v_a_2481_;
goto v___jp_2464_;
}
else
{
lean_object* v_a_2482_; lean_object* v_a_2483_; 
v_a_2482_ = lean_ctor_get(v___x_2480_, 0);
lean_inc(v_a_2482_);
v_a_2483_ = lean_ctor_get(v___x_2480_, 1);
lean_inc(v_a_2483_);
lean_dec_ref_known(v___x_2480_, 2);
v_a_2452_ = v_a_2482_;
v_a_2453_ = v_a_2483_;
goto v___jp_2451_;
}
}
}
else
{
lean_object* v_a_2484_; lean_object* v_a_2485_; 
lean_dec_ref(v_a_2444_);
lean_dec_ref(v_build_2441_);
lean_dec_ref(v_traceFile_2440_);
v_a_2484_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_a_2484_);
v_a_2485_ = lean_ctor_get(v___x_2473_, 1);
lean_inc(v_a_2485_);
lean_dec_ref_known(v___x_2473_, 2);
v_a_2452_ = v_a_2484_;
v_a_2453_ = v_a_2485_;
goto v___jp_2451_;
}
}
}
else
{
lean_object* v_a_2487_; lean_object* v_a_2488_; lean_object* v___x_2490_; 
lean_dec_ref(v_a_2444_);
lean_dec_ref(v_build_2441_);
lean_dec_ref(v_traceFile_2440_);
lean_dec(v_info_2438_);
lean_dec_ref(v_inst_2437_);
lean_dec_ref(v_inst_2436_);
v_a_2487_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_a_2487_);
v_a_2488_ = lean_ctor_get(v___x_2468_, 1);
lean_inc(v_a_2488_);
lean_dec_ref_known(v___x_2468_, 2);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v_a_2488_);
v___x_2490_ = v___x_2461_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2488_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v_trace_2458_);
lean_ctor_set(v_reuseFailAlloc_2491_, 2, v_buildTime_2459_);
lean_ctor_set_uint8(v_reuseFailAlloc_2491_, sizeof(void*)*3, v_action_2456_);
lean_ctor_set_uint8(v_reuseFailAlloc_2491_, sizeof(void*)*3 + 1, v_wantsRebuild_2457_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
v_a_2452_ = v_a_2487_;
v_a_2453_ = v___x_2490_;
goto v___jp_2451_;
}
}
v___jp_2464_:
{
lean_object* v___x_2466_; 
v___x_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2463_);
lean_ctor_set(v___x_2466_, 1, v_a_2465_);
return v___x_2466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___boxed(lean_object* v_00_u03b9_2493_, lean_object* v_inst_2494_, lean_object* v_inst_2495_, lean_object* v_info_2496_, lean_object* v_depTrace_2497_, lean_object* v_traceFile_2498_, lean_object* v_build_2499_, lean_object* v_action_2500_, lean_object* v_oldTrace_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_){
_start:
{
uint8_t v_action_boxed_2509_; lean_object* v_res_2510_; 
v_action_boxed_2509_ = lean_unbox(v_action_2500_);
v_res_2510_ = l_Lake_buildUnlessUpToDate(v_00_u03b9_2493_, v_inst_2494_, v_inst_2495_, v_info_2496_, v_depTrace_2497_, v_traceFile_2498_, v_build_2499_, v_action_boxed_2509_, v_oldTrace_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_);
lean_dec_ref(v_a_2506_);
lean_dec(v_a_2505_);
lean_dec(v_a_2504_);
lean_dec(v_a_2503_);
lean_dec_ref(v_oldTrace_2501_);
lean_dec_ref(v_depTrace_2497_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFileHash(lean_object* v_file_2512_, uint64_t v_hash_2513_){
_start:
{
lean_object* v___x_2515_; lean_object* v_hashFile_2516_; lean_object* v___x_2517_; 
v___x_2515_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
v_hashFile_2516_ = lean_string_append(v_file_2512_, v___x_2515_);
lean_inc_ref(v_hashFile_2516_);
v___x_2517_ = l_Lake_createParentDirs(v_hashFile_2516_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
lean_dec_ref_known(v___x_2517_, 1);
v___x_2518_ = l_Lake_lowerHexUInt64(v_hash_2513_);
v___x_2519_ = l_IO_FS_writeFile(v_hashFile_2516_, v___x_2518_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v_hashFile_2516_);
return v___x_2519_;
}
else
{
lean_dec_ref(v_hashFile_2516_);
return v___x_2517_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_writeFileHash___boxed(lean_object* v_file_2520_, lean_object* v_hash_2521_, lean_object* v_a_2522_){
_start:
{
uint64_t v_hash_boxed_2523_; lean_object* v_res_2524_; 
v_hash_boxed_2523_ = lean_unbox_uint64(v_hash_2521_);
lean_dec_ref(v_hash_2521_);
v_res_2524_ = l_Lake_writeFileHash(v_file_2520_, v_hash_boxed_2523_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object* v_file_2525_, uint8_t v_text_2526_){
_start:
{
lean_object* v___y_2529_; 
if (v_text_2526_ == 0)
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Lake_computeBinFileHash(v_file_2525_);
v___y_2529_ = v___x_2541_;
goto v___jp_2528_;
}
else
{
lean_object* v___x_2542_; 
v___x_2542_ = l_Lake_computeTextFileHash(v_file_2525_);
v___y_2529_ = v___x_2542_;
goto v___jp_2528_;
}
v___jp_2528_:
{
if (lean_obj_tag(v___y_2529_) == 0)
{
lean_object* v_a_2530_; uint64_t v___x_2531_; lean_object* v___x_2532_; 
v_a_2530_ = lean_ctor_get(v___y_2529_, 0);
lean_inc(v_a_2530_);
lean_dec_ref_known(v___y_2529_, 1);
v___x_2531_ = lean_unbox_uint64(v_a_2530_);
lean_dec(v_a_2530_);
v___x_2532_ = l_Lake_writeFileHash(v_file_2525_, v___x_2531_);
return v___x_2532_;
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec_ref(v_file_2525_);
v_a_2533_ = lean_ctor_get(v___y_2529_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___y_2529_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___y_2529_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___y_2529_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash___boxed(lean_object* v_file_2543_, lean_object* v_text_2544_, lean_object* v_a_2545_){
_start:
{
uint8_t v_text_boxed_2546_; lean_object* v_res_2547_; 
v_text_boxed_2546_ = lean_unbox(v_text_2544_);
v_res_2547_ = l_Lake_cacheFileHash(v_file_2543_, v_text_boxed_2546_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Lake_clearFileHash(lean_object* v_file_2548_){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2550_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
v___x_2551_ = lean_string_append(v_file_2548_, v___x_2550_);
v___x_2552_ = l_Lake_removeFileIfExists(v___x_2551_);
lean_dec_ref(v___x_2551_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l_Lake_clearFileHash___boxed(lean_object* v_file_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Lake_clearFileHash(v_file_2553_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg(lean_object* v_file_2556_, uint8_t v_text_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v_toBuildConfig_2561_; uint8_t v_trustHash_2562_; lean_object* v___x_2563_; lean_object* v_hashFile_2564_; uint8_t v___y_2566_; uint8_t v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2604_; 
v_toBuildConfig_2561_ = lean_ctor_get(v_a_2558_, 0);
v_trustHash_2562_ = lean_ctor_get_uint8(v_toBuildConfig_2561_, sizeof(void*)*4 + 1);
v___x_2563_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
lean_inc_ref(v_file_2556_);
v_hashFile_2564_ = lean_string_append(v_file_2556_, v___x_2563_);
if (v_trustHash_2562_ == 0)
{
v___y_2604_ = v_a_2559_;
goto v___jp_2603_;
}
else
{
lean_object* v___x_2617_; 
v___x_2617_ = l_Lake_Hash_load_x3f(v_hashFile_2564_);
if (lean_obj_tag(v___x_2617_) == 1)
{
lean_object* v_val_2618_; lean_object* v___x_2619_; 
lean_dec_ref(v_hashFile_2564_);
lean_dec_ref(v_file_2556_);
v_val_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_val_2618_);
lean_dec_ref_known(v___x_2617_, 1);
v___x_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2619_, 0, v_val_2618_);
lean_ctor_set(v___x_2619_, 1, v_a_2559_);
return v___x_2619_;
}
else
{
lean_dec(v___x_2617_);
v___y_2604_ = v_a_2559_;
goto v___jp_2603_;
}
}
v___jp_2565_:
{
if (lean_obj_tag(v___y_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v___x_2573_; 
v_a_2572_ = lean_ctor_get(v___y_2571_, 0);
lean_inc(v_a_2572_);
lean_dec_ref_known(v___y_2571_, 1);
lean_inc_ref(v_hashFile_2564_);
v___x_2573_ = l_Lake_createParentDirs(v_hashFile_2564_);
if (lean_obj_tag(v___x_2573_) == 0)
{
uint64_t v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
lean_dec_ref_known(v___x_2573_, 1);
v___x_2574_ = lean_unbox_uint64(v_a_2572_);
v___x_2575_ = l_Lake_lowerHexUInt64(v___x_2574_);
v___x_2576_ = l_IO_FS_writeFile(v_hashFile_2564_, v___x_2575_);
lean_dec_ref(v___x_2575_);
lean_dec_ref(v_hashFile_2564_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v___x_2577_; lean_object* v___x_2578_; 
lean_dec_ref_known(v___x_2576_, 1);
v___x_2577_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2577_, 0, v___y_2569_);
lean_ctor_set(v___x_2577_, 1, v___y_2570_);
lean_ctor_set(v___x_2577_, 2, v___y_2568_);
lean_ctor_set_uint8(v___x_2577_, sizeof(void*)*3, v___y_2566_);
lean_ctor_set_uint8(v___x_2577_, sizeof(void*)*3 + 1, v___y_2567_);
v___x_2578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2578_, 0, v_a_2572_);
lean_ctor_set(v___x_2578_, 1, v___x_2577_);
return v___x_2578_;
}
else
{
lean_object* v_a_2579_; lean_object* v___x_2580_; uint8_t v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
lean_dec(v_a_2572_);
v_a_2579_ = lean_ctor_get(v___x_2576_, 0);
lean_inc(v_a_2579_);
lean_dec_ref_known(v___x_2576_, 1);
v___x_2580_ = lean_io_error_to_string(v_a_2579_);
v___x_2581_ = 3;
v___x_2582_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2582_, 0, v___x_2580_);
lean_ctor_set_uint8(v___x_2582_, sizeof(void*)*1, v___x_2581_);
v___x_2583_ = lean_array_get_size(v___y_2569_);
v___x_2584_ = lean_array_push(v___y_2569_, v___x_2582_);
v___x_2585_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
lean_ctor_set(v___x_2585_, 1, v___y_2570_);
lean_ctor_set(v___x_2585_, 2, v___y_2568_);
lean_ctor_set_uint8(v___x_2585_, sizeof(void*)*3, v___y_2566_);
lean_ctor_set_uint8(v___x_2585_, sizeof(void*)*3 + 1, v___y_2567_);
v___x_2586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2583_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
return v___x_2586_;
}
}
else
{
lean_object* v_a_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
lean_dec(v_a_2572_);
lean_dec_ref(v_hashFile_2564_);
v_a_2587_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2587_);
lean_dec_ref_known(v___x_2573_, 1);
v___x_2588_ = lean_io_error_to_string(v_a_2587_);
v___x_2589_ = 3;
v___x_2590_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2590_, 0, v___x_2588_);
lean_ctor_set_uint8(v___x_2590_, sizeof(void*)*1, v___x_2589_);
v___x_2591_ = lean_array_get_size(v___y_2569_);
v___x_2592_ = lean_array_push(v___y_2569_, v___x_2590_);
v___x_2593_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
lean_ctor_set(v___x_2593_, 1, v___y_2570_);
lean_ctor_set(v___x_2593_, 2, v___y_2568_);
lean_ctor_set_uint8(v___x_2593_, sizeof(void*)*3, v___y_2566_);
lean_ctor_set_uint8(v___x_2593_, sizeof(void*)*3 + 1, v___y_2567_);
v___x_2594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2591_);
lean_ctor_set(v___x_2594_, 1, v___x_2593_);
return v___x_2594_;
}
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2596_; uint8_t v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
lean_dec_ref(v_hashFile_2564_);
v_a_2595_ = lean_ctor_get(v___y_2571_, 0);
lean_inc(v_a_2595_);
lean_dec_ref_known(v___y_2571_, 1);
v___x_2596_ = lean_io_error_to_string(v_a_2595_);
v___x_2597_ = 3;
v___x_2598_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2598_, 0, v___x_2596_);
lean_ctor_set_uint8(v___x_2598_, sizeof(void*)*1, v___x_2597_);
v___x_2599_ = lean_array_get_size(v___y_2569_);
v___x_2600_ = lean_array_push(v___y_2569_, v___x_2598_);
v___x_2601_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
lean_ctor_set(v___x_2601_, 1, v___y_2570_);
lean_ctor_set(v___x_2601_, 2, v___y_2568_);
lean_ctor_set_uint8(v___x_2601_, sizeof(void*)*3, v___y_2566_);
lean_ctor_set_uint8(v___x_2601_, sizeof(void*)*3 + 1, v___y_2567_);
v___x_2602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2599_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
return v___x_2602_;
}
}
v___jp_2603_:
{
if (v_text_2557_ == 0)
{
lean_object* v_log_2605_; uint8_t v_action_2606_; uint8_t v_wantsRebuild_2607_; lean_object* v_trace_2608_; lean_object* v_buildTime_2609_; lean_object* v___x_2610_; 
v_log_2605_ = lean_ctor_get(v___y_2604_, 0);
lean_inc_ref(v_log_2605_);
v_action_2606_ = lean_ctor_get_uint8(v___y_2604_, sizeof(void*)*3);
v_wantsRebuild_2607_ = lean_ctor_get_uint8(v___y_2604_, sizeof(void*)*3 + 1);
v_trace_2608_ = lean_ctor_get(v___y_2604_, 1);
lean_inc_ref(v_trace_2608_);
v_buildTime_2609_ = lean_ctor_get(v___y_2604_, 2);
lean_inc(v_buildTime_2609_);
lean_dec_ref(v___y_2604_);
v___x_2610_ = l_Lake_computeBinFileHash(v_file_2556_);
lean_dec_ref(v_file_2556_);
v___y_2566_ = v_action_2606_;
v___y_2567_ = v_wantsRebuild_2607_;
v___y_2568_ = v_buildTime_2609_;
v___y_2569_ = v_log_2605_;
v___y_2570_ = v_trace_2608_;
v___y_2571_ = v___x_2610_;
goto v___jp_2565_;
}
else
{
lean_object* v_log_2611_; uint8_t v_action_2612_; uint8_t v_wantsRebuild_2613_; lean_object* v_trace_2614_; lean_object* v_buildTime_2615_; lean_object* v___x_2616_; 
v_log_2611_ = lean_ctor_get(v___y_2604_, 0);
lean_inc_ref(v_log_2611_);
v_action_2612_ = lean_ctor_get_uint8(v___y_2604_, sizeof(void*)*3);
v_wantsRebuild_2613_ = lean_ctor_get_uint8(v___y_2604_, sizeof(void*)*3 + 1);
v_trace_2614_ = lean_ctor_get(v___y_2604_, 1);
lean_inc_ref(v_trace_2614_);
v_buildTime_2615_ = lean_ctor_get(v___y_2604_, 2);
lean_inc(v_buildTime_2615_);
lean_dec_ref(v___y_2604_);
v___x_2616_ = l_Lake_computeTextFileHash(v_file_2556_);
lean_dec_ref(v_file_2556_);
v___y_2566_ = v_action_2612_;
v___y_2567_ = v_wantsRebuild_2613_;
v___y_2568_ = v_buildTime_2615_;
v___y_2569_ = v_log_2611_;
v___y_2570_ = v_trace_2614_;
v___y_2571_ = v___x_2616_;
goto v___jp_2565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg___boxed(lean_object* v_file_2620_, lean_object* v_text_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_){
_start:
{
uint8_t v_text_boxed_2625_; lean_object* v_res_2626_; 
v_text_boxed_2625_ = lean_unbox(v_text_2621_);
v_res_2626_ = l_Lake_fetchFileHash___redArg(v_file_2620_, v_text_boxed_2625_, v_a_2622_, v_a_2623_);
lean_dec_ref(v_a_2622_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash(lean_object* v_file_2627_, uint8_t v_text_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = l_Lake_fetchFileHash___redArg(v_file_2627_, v_text_2628_, v_a_2633_, v_a_2634_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___boxed(lean_object* v_file_2637_, lean_object* v_text_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_){
_start:
{
uint8_t v_text_boxed_2646_; lean_object* v_res_2647_; 
v_text_boxed_2646_ = lean_unbox(v_text_2638_);
v_res_2647_ = l_Lake_fetchFileHash(v_file_2637_, v_text_boxed_2646_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_);
lean_dec_ref(v_a_2643_);
lean_dec(v_a_2642_);
lean_dec(v_a_2641_);
lean_dec(v_a_2640_);
lean_dec_ref(v_a_2639_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg(lean_object* v_file_2648_, uint8_t v_text_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_){
_start:
{
lean_object* v___x_2653_; 
lean_inc_ref(v_file_2648_);
v___x_2653_ = l_Lake_fetchFileHash___redArg(v_file_2648_, v_text_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2692_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 1);
v_a_2655_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2657_ = v___x_2653_;
v_isShared_2658_ = v_isSharedCheck_2692_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2654_);
lean_inc(v_a_2655_);
lean_dec(v___x_2653_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2692_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v_log_2659_; uint8_t v_action_2660_; uint8_t v_wantsRebuild_2661_; lean_object* v_trace_2662_; lean_object* v_buildTime_2663_; lean_object* v___x_2664_; 
v_log_2659_ = lean_ctor_get(v_a_2654_, 0);
v_action_2660_ = lean_ctor_get_uint8(v_a_2654_, sizeof(void*)*3);
v_wantsRebuild_2661_ = lean_ctor_get_uint8(v_a_2654_, sizeof(void*)*3 + 1);
v_trace_2662_ = lean_ctor_get(v_a_2654_, 1);
v_buildTime_2663_ = lean_ctor_get(v_a_2654_, 2);
v___x_2664_ = lean_io_metadata(v_file_2648_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v_modified_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; uint64_t v___x_2669_; lean_object* v___x_2671_; 
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2665_);
lean_dec_ref_known(v___x_2664_, 1);
v_modified_2666_ = lean_ctor_get(v_a_2665_, 1);
lean_inc_ref(v_modified_2666_);
lean_dec(v_a_2665_);
v___x_2667_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_2668_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_2668_, 0, v_file_2648_);
lean_ctor_set(v___x_2668_, 1, v___x_2667_);
lean_ctor_set(v___x_2668_, 2, v_modified_2666_);
v___x_2669_ = lean_unbox_uint64(v_a_2655_);
lean_dec(v_a_2655_);
lean_ctor_set_uint64(v___x_2668_, sizeof(void*)*3, v___x_2669_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 0, v___x_2668_);
v___x_2671_ = v___x_2657_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v_a_2654_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
else
{
lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2688_; 
lean_inc(v_buildTime_2663_);
lean_inc_ref(v_trace_2662_);
lean_inc_ref(v_log_2659_);
lean_dec(v_a_2655_);
lean_dec_ref(v_file_2648_);
v_isSharedCheck_2688_ = !lean_is_exclusive(v_a_2654_);
if (v_isSharedCheck_2688_ == 0)
{
lean_object* v_unused_2689_; lean_object* v_unused_2690_; lean_object* v_unused_2691_; 
v_unused_2689_ = lean_ctor_get(v_a_2654_, 2);
lean_dec(v_unused_2689_);
v_unused_2690_ = lean_ctor_get(v_a_2654_, 1);
lean_dec(v_unused_2690_);
v_unused_2691_ = lean_ctor_get(v_a_2654_, 0);
lean_dec(v_unused_2691_);
v___x_2674_ = v_a_2654_;
v_isShared_2675_ = v_isSharedCheck_2688_;
goto v_resetjp_2673_;
}
else
{
lean_dec(v_a_2654_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2688_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v_a_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2683_; 
v_a_2676_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v___x_2664_, 1);
v___x_2677_ = lean_io_error_to_string(v_a_2676_);
v___x_2678_ = 3;
v___x_2679_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2679_, 0, v___x_2677_);
lean_ctor_set_uint8(v___x_2679_, sizeof(void*)*1, v___x_2678_);
v___x_2680_ = lean_array_get_size(v_log_2659_);
v___x_2681_ = lean_array_push(v_log_2659_, v___x_2679_);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v___x_2681_);
v___x_2683_ = v___x_2674_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2681_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v_trace_2662_);
lean_ctor_set(v_reuseFailAlloc_2687_, 2, v_buildTime_2663_);
lean_ctor_set_uint8(v_reuseFailAlloc_2687_, sizeof(void*)*3, v_action_2660_);
lean_ctor_set_uint8(v_reuseFailAlloc_2687_, sizeof(void*)*3 + 1, v_wantsRebuild_2661_);
v___x_2683_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
lean_object* v___x_2685_; 
if (v_isShared_2658_ == 0)
{
lean_ctor_set_tag(v___x_2657_, 1);
lean_ctor_set(v___x_2657_, 1, v___x_2683_);
lean_ctor_set(v___x_2657_, 0, v___x_2680_);
v___x_2685_ = v___x_2657_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2680_);
lean_ctor_set(v_reuseFailAlloc_2686_, 1, v___x_2683_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
}
}
else
{
lean_object* v_a_2693_; lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
lean_dec_ref(v_file_2648_);
v_a_2693_ = lean_ctor_get(v___x_2653_, 0);
v_a_2694_ = lean_ctor_get(v___x_2653_, 1);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2653_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_inc(v_a_2693_);
lean_dec(v___x_2653_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2693_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg___boxed(lean_object* v_file_2702_, lean_object* v_text_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_){
_start:
{
uint8_t v_text_boxed_2707_; lean_object* v_res_2708_; 
v_text_boxed_2707_ = lean_unbox(v_text_2703_);
v_res_2708_ = l_Lake_fetchFileTrace___redArg(v_file_2702_, v_text_boxed_2707_, v_a_2704_, v_a_2705_);
lean_dec_ref(v_a_2704_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object* v_file_2709_, uint8_t v_text_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l_Lake_fetchFileTrace___redArg(v_file_2709_, v_text_2710_, v_a_2715_, v_a_2716_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object* v_file_2719_, lean_object* v_text_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_){
_start:
{
uint8_t v_text_boxed_2728_; lean_object* v_res_2729_; 
v_text_boxed_2728_ = lean_unbox(v_text_2720_);
v_res_2729_ = l_Lake_fetchFileTrace(v_file_2719_, v_text_boxed_2728_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
lean_dec_ref(v_a_2725_);
lean_dec(v_a_2724_);
lean_dec(v_a_2723_);
lean_dec(v_a_2722_);
lean_dec_ref(v_a_2721_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(lean_object* v_val_2730_, lean_object* v_a_x3f_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v_log_2734_; uint8_t v_action_2735_; uint8_t v_wantsRebuild_2736_; lean_object* v_trace_2737_; lean_object* v_buildTime_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2750_; 
v_log_2734_ = lean_ctor_get(v___y_2732_, 0);
v_action_2735_ = lean_ctor_get_uint8(v___y_2732_, sizeof(void*)*3);
v_wantsRebuild_2736_ = lean_ctor_get_uint8(v___y_2732_, sizeof(void*)*3 + 1);
v_trace_2737_ = lean_ctor_get(v___y_2732_, 1);
v_buildTime_2738_ = lean_ctor_get(v___y_2732_, 2);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___y_2732_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2740_ = v___y_2732_;
v_isShared_2741_ = v_isSharedCheck_2750_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_buildTime_2738_);
lean_inc(v_trace_2737_);
lean_inc(v_log_2734_);
lean_dec(v___y_2732_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2750_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2747_; 
v___x_2742_ = lean_io_mono_ms_now();
v___x_2743_ = lean_nat_sub(v___x_2742_, v_val_2730_);
lean_dec(v___x_2742_);
v___x_2744_ = lean_box(0);
v___x_2745_ = lean_nat_add(v_buildTime_2738_, v___x_2743_);
lean_dec(v___x_2743_);
lean_dec(v_buildTime_2738_);
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 2, v___x_2745_);
v___x_2747_ = v___x_2740_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_log_2734_);
lean_ctor_set(v_reuseFailAlloc_2749_, 1, v_trace_2737_);
lean_ctor_set(v_reuseFailAlloc_2749_, 2, v___x_2745_);
lean_ctor_set_uint8(v_reuseFailAlloc_2749_, sizeof(void*)*3, v_action_2735_);
lean_ctor_set_uint8(v_reuseFailAlloc_2749_, sizeof(void*)*3 + 1, v_wantsRebuild_2736_);
v___x_2747_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
lean_object* v___x_2748_; 
v___x_2748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2744_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
return v___x_2748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0___boxed(lean_object* v_val_2751_, lean_object* v_a_x3f_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v_val_2751_, v_a_x3f_2752_, v___y_2753_);
lean_dec(v_a_x3f_2752_);
lean_dec(v_val_2751_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(lean_object* v_build_2756_, lean_object* v_file_2757_, lean_object* v_a_2758_, lean_object* v_depTrace_2759_, lean_object* v_traceFile_2760_, uint8_t v_action_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_){
_start:
{
lean_object* v_a_2769_; lean_object* v_a_2770_; lean_object* v_log_2773_; uint8_t v_action_2774_; uint8_t v_wantsRebuild_2775_; lean_object* v_trace_2776_; lean_object* v_buildTime_2777_; lean_object* v_toBuildConfig_2783_; lean_object* v_log_2784_; uint8_t v_action_2785_; uint8_t v_wantsRebuild_2786_; lean_object* v_trace_2787_; lean_object* v_buildTime_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2911_; 
v_toBuildConfig_2783_ = lean_ctor_get(v_a_2765_, 0);
v_log_2784_ = lean_ctor_get(v_a_2766_, 0);
v_action_2785_ = lean_ctor_get_uint8(v_a_2766_, sizeof(void*)*3);
v_wantsRebuild_2786_ = lean_ctor_get_uint8(v_a_2766_, sizeof(void*)*3 + 1);
v_trace_2787_ = lean_ctor_get(v_a_2766_, 1);
v_buildTime_2788_ = lean_ctor_get(v_a_2766_, 2);
v_isSharedCheck_2911_ = !lean_is_exclusive(v_a_2766_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2790_ = v_a_2766_;
v_isShared_2791_ = v_isSharedCheck_2911_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_buildTime_2788_);
lean_inc(v_trace_2787_);
lean_inc(v_log_2784_);
lean_dec(v_a_2766_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2911_;
goto v_resetjp_2789_;
}
v___jp_2768_:
{
lean_object* v___x_2771_; 
v___x_2771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2771_, 0, v_a_2769_);
lean_ctor_set(v___x_2771_, 1, v_a_2770_);
return v___x_2771_;
}
v___jp_2772_:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2778_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_2779_ = lean_array_get_size(v_log_2773_);
v___x_2780_ = lean_array_push(v_log_2773_, v___x_2778_);
v___x_2781_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2781_, 0, v___x_2780_);
lean_ctor_set(v___x_2781_, 1, v_trace_2776_);
lean_ctor_set(v___x_2781_, 2, v_buildTime_2777_);
lean_ctor_set_uint8(v___x_2781_, sizeof(void*)*3, v_action_2774_);
lean_ctor_set_uint8(v___x_2781_, sizeof(void*)*3 + 1, v_wantsRebuild_2775_);
v___x_2782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2779_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
return v___x_2782_;
}
v_resetjp_2789_:
{
uint8_t v_noBuild_2792_; uint8_t v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v_noBuild_2792_ = lean_ctor_get_uint8(v_toBuildConfig_2783_, sizeof(void*)*4 + 2);
v___x_2793_ = l_Lake_JobAction_merge(v_action_2785_, v_action_2761_);
v___x_2794_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_2760_);
v___x_2795_ = l_System_FilePath_addExtension(v_traceFile_2760_, v___x_2794_);
if (v_noBuild_2792_ == 0)
{
lean_object* v___x_2796_; lean_object* v_a_2798_; lean_object* v_a_2799_; lean_object* v___x_2804_; 
v___x_2796_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_2784_);
if (v_isShared_2791_ == 0)
{
v___x_2804_ = v___x_2790_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_log_2784_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_trace_2787_);
lean_ctor_set(v_reuseFailAlloc_2895_, 2, v_buildTime_2788_);
lean_ctor_set_uint8(v_reuseFailAlloc_2895_, sizeof(void*)*3 + 1, v_wantsRebuild_2786_);
v___x_2804_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2803_;
}
v___jp_2797_:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v_a_2802_; 
v___x_2800_ = lean_box(0);
v___x_2801_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v___x_2796_, v___x_2800_, v_a_2799_);
lean_dec(v___x_2796_);
v_a_2802_ = lean_ctor_get(v___x_2801_, 1);
lean_inc(v_a_2802_);
lean_dec_ref(v___x_2801_);
v_a_2769_ = v_a_2798_;
v_a_2770_ = v_a_2802_;
goto v___jp_2768_;
}
v_reusejp_2803_:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
lean_ctor_set_uint8(v___x_2804_, sizeof(void*)*3, v___x_2793_);
v___x_2805_ = lean_array_get_size(v_log_2784_);
lean_dec_ref(v_log_2784_);
lean_inc_ref(v_a_2765_);
lean_inc(v_a_2764_);
lean_inc(v_a_2763_);
lean_inc(v_a_2762_);
v___x_2806_ = lean_apply_7(v_build_2756_, v_a_2758_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v___x_2804_, lean_box(0));
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v_log_2808_; uint8_t v_action_2809_; uint8_t v_wantsRebuild_2810_; lean_object* v_trace_2811_; lean_object* v_buildTime_2812_; lean_object* v___x_2813_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 1);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2806_, 2);
v_log_2808_ = lean_ctor_get(v_a_2807_, 0);
v_action_2809_ = lean_ctor_get_uint8(v_a_2807_, sizeof(void*)*3);
v_wantsRebuild_2810_ = lean_ctor_get_uint8(v_a_2807_, sizeof(void*)*3 + 1);
v_trace_2811_ = lean_ctor_get(v_a_2807_, 1);
v_buildTime_2812_ = lean_ctor_get(v_a_2807_, 2);
v___x_2813_ = l_Lake_clearFileHash(v_file_2757_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2814_);
lean_dec_ref_known(v___x_2813_, 1);
v___x_2815_ = lean_array_get_size(v_log_2808_);
v___x_2816_ = l_Array_extract___redArg(v_log_2808_, v___x_2805_, v___x_2815_);
v___x_2817_ = lean_box(0);
v___x_2818_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_2759_, v___x_2817_, v___x_2816_);
v___x_2819_ = l_Lake_BuildMetadata_writeFile(v_traceFile_2760_, v___x_2818_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2860_; 
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2860_ == 0)
{
lean_object* v_unused_2861_; 
v_unused_2861_ = lean_ctor_get(v___x_2819_, 0);
lean_dec(v_unused_2861_);
v___x_2821_ = v___x_2819_;
v_isShared_2822_ = v_isSharedCheck_2860_;
goto v_resetjp_2820_;
}
else
{
lean_dec(v___x_2819_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2860_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2823_; 
v___x_2823_ = l_Lake_removeFileIfExists(v___x_2795_);
lean_dec_ref(v___x_2795_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2843_; 
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2843_ == 0)
{
lean_object* v_unused_2844_; 
v_unused_2844_ = lean_ctor_get(v___x_2823_, 0);
lean_dec(v_unused_2844_);
v___x_2825_ = v___x_2823_;
v_isShared_2826_ = v_isSharedCheck_2843_;
goto v_resetjp_2824_;
}
else
{
lean_dec(v___x_2823_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2843_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
lean_inc(v_a_2814_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 0, v_a_2814_);
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2814_);
v___x_2828_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
lean_object* v___x_2830_; 
if (v_isShared_2822_ == 0)
{
lean_ctor_set_tag(v___x_2821_, 1);
lean_ctor_set(v___x_2821_, 0, v___x_2828_);
v___x_2830_ = v___x_2821_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2828_);
v___x_2830_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
lean_object* v___x_2831_; lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
v___x_2831_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v___x_2796_, v___x_2830_, v_a_2807_);
lean_dec_ref(v___x_2830_);
lean_dec(v___x_2796_);
v_a_2832_ = lean_ctor_get(v___x_2831_, 1);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2839_ == 0)
{
lean_object* v_unused_2840_; 
v_unused_2840_ = lean_ctor_get(v___x_2831_, 0);
lean_dec(v_unused_2840_);
v___x_2834_ = v___x_2831_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2831_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v_a_2814_);
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2814_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
}
}
else
{
lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2856_; 
lean_inc(v_buildTime_2812_);
lean_inc_ref(v_trace_2811_);
lean_inc_ref(v_log_2808_);
lean_del_object(v___x_2821_);
lean_dec(v_a_2814_);
v_isSharedCheck_2856_ = !lean_is_exclusive(v_a_2807_);
if (v_isSharedCheck_2856_ == 0)
{
lean_object* v_unused_2857_; lean_object* v_unused_2858_; lean_object* v_unused_2859_; 
v_unused_2857_ = lean_ctor_get(v_a_2807_, 2);
lean_dec(v_unused_2857_);
v_unused_2858_ = lean_ctor_get(v_a_2807_, 1);
lean_dec(v_unused_2858_);
v_unused_2859_ = lean_ctor_get(v_a_2807_, 0);
lean_dec(v_unused_2859_);
v___x_2846_ = v_a_2807_;
v_isShared_2847_ = v_isSharedCheck_2856_;
goto v_resetjp_2845_;
}
else
{
lean_dec(v_a_2807_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2856_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v_a_2848_; lean_object* v___x_2849_; uint8_t v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2854_; 
v_a_2848_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2848_);
lean_dec_ref_known(v___x_2823_, 1);
v___x_2849_ = lean_io_error_to_string(v_a_2848_);
v___x_2850_ = 3;
v___x_2851_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2851_, 0, v___x_2849_);
lean_ctor_set_uint8(v___x_2851_, sizeof(void*)*1, v___x_2850_);
v___x_2852_ = lean_array_push(v_log_2808_, v___x_2851_);
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 0, v___x_2852_);
v___x_2854_ = v___x_2846_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v___x_2852_);
lean_ctor_set(v_reuseFailAlloc_2855_, 1, v_trace_2811_);
lean_ctor_set(v_reuseFailAlloc_2855_, 2, v_buildTime_2812_);
lean_ctor_set_uint8(v_reuseFailAlloc_2855_, sizeof(void*)*3, v_action_2809_);
lean_ctor_set_uint8(v_reuseFailAlloc_2855_, sizeof(void*)*3 + 1, v_wantsRebuild_2810_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
v_a_2798_ = v___x_2815_;
v_a_2799_ = v___x_2854_;
goto v___jp_2797_;
}
}
}
}
}
else
{
lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2873_; 
lean_inc(v_buildTime_2812_);
lean_inc_ref(v_trace_2811_);
lean_inc_ref(v_log_2808_);
lean_dec(v_a_2814_);
lean_dec_ref(v___x_2795_);
v_isSharedCheck_2873_ = !lean_is_exclusive(v_a_2807_);
if (v_isSharedCheck_2873_ == 0)
{
lean_object* v_unused_2874_; lean_object* v_unused_2875_; lean_object* v_unused_2876_; 
v_unused_2874_ = lean_ctor_get(v_a_2807_, 2);
lean_dec(v_unused_2874_);
v_unused_2875_ = lean_ctor_get(v_a_2807_, 1);
lean_dec(v_unused_2875_);
v_unused_2876_ = lean_ctor_get(v_a_2807_, 0);
lean_dec(v_unused_2876_);
v___x_2863_ = v_a_2807_;
v_isShared_2864_ = v_isSharedCheck_2873_;
goto v_resetjp_2862_;
}
else
{
lean_dec(v_a_2807_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2873_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v_a_2865_; lean_object* v___x_2866_; uint8_t v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2871_; 
v_a_2865_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2865_);
lean_dec_ref_known(v___x_2819_, 1);
v___x_2866_ = lean_io_error_to_string(v_a_2865_);
v___x_2867_ = 3;
v___x_2868_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2868_, 0, v___x_2866_);
lean_ctor_set_uint8(v___x_2868_, sizeof(void*)*1, v___x_2867_);
v___x_2869_ = lean_array_push(v_log_2808_, v___x_2868_);
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 0, v___x_2869_);
v___x_2871_ = v___x_2863_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v___x_2869_);
lean_ctor_set(v_reuseFailAlloc_2872_, 1, v_trace_2811_);
lean_ctor_set(v_reuseFailAlloc_2872_, 2, v_buildTime_2812_);
lean_ctor_set_uint8(v_reuseFailAlloc_2872_, sizeof(void*)*3, v_action_2809_);
lean_ctor_set_uint8(v_reuseFailAlloc_2872_, sizeof(void*)*3 + 1, v_wantsRebuild_2810_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
v_a_2798_ = v___x_2815_;
v_a_2799_ = v___x_2871_;
goto v___jp_2797_;
}
}
}
}
else
{
lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2889_; 
lean_inc(v_buildTime_2812_);
lean_inc_ref(v_trace_2811_);
lean_inc_ref(v_log_2808_);
lean_dec_ref(v___x_2795_);
lean_dec_ref(v_traceFile_2760_);
v_isSharedCheck_2889_ = !lean_is_exclusive(v_a_2807_);
if (v_isSharedCheck_2889_ == 0)
{
lean_object* v_unused_2890_; lean_object* v_unused_2891_; lean_object* v_unused_2892_; 
v_unused_2890_ = lean_ctor_get(v_a_2807_, 2);
lean_dec(v_unused_2890_);
v_unused_2891_ = lean_ctor_get(v_a_2807_, 1);
lean_dec(v_unused_2891_);
v_unused_2892_ = lean_ctor_get(v_a_2807_, 0);
lean_dec(v_unused_2892_);
v___x_2878_ = v_a_2807_;
v_isShared_2879_ = v_isSharedCheck_2889_;
goto v_resetjp_2877_;
}
else
{
lean_dec(v_a_2807_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2889_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v_a_2880_; lean_object* v___x_2881_; uint8_t v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2887_; 
v_a_2880_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2880_);
lean_dec_ref_known(v___x_2813_, 1);
v___x_2881_ = lean_io_error_to_string(v_a_2880_);
v___x_2882_ = 3;
v___x_2883_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2883_, 0, v___x_2881_);
lean_ctor_set_uint8(v___x_2883_, sizeof(void*)*1, v___x_2882_);
v___x_2884_ = lean_array_get_size(v_log_2808_);
v___x_2885_ = lean_array_push(v_log_2808_, v___x_2883_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2885_);
v___x_2887_ = v___x_2878_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v___x_2885_);
lean_ctor_set(v_reuseFailAlloc_2888_, 1, v_trace_2811_);
lean_ctor_set(v_reuseFailAlloc_2888_, 2, v_buildTime_2812_);
lean_ctor_set_uint8(v_reuseFailAlloc_2888_, sizeof(void*)*3, v_action_2809_);
lean_ctor_set_uint8(v_reuseFailAlloc_2888_, sizeof(void*)*3 + 1, v_wantsRebuild_2810_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
v_a_2798_ = v___x_2884_;
v_a_2799_ = v___x_2887_;
goto v___jp_2797_;
}
}
}
}
else
{
lean_object* v_a_2893_; lean_object* v_a_2894_; 
lean_dec_ref(v___x_2795_);
lean_dec_ref(v_traceFile_2760_);
lean_dec_ref(v_file_2757_);
v_a_2893_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2893_);
v_a_2894_ = lean_ctor_get(v___x_2806_, 1);
lean_inc(v_a_2894_);
lean_dec_ref_known(v___x_2806_, 2);
v_a_2798_ = v_a_2893_;
v_a_2799_ = v_a_2894_;
goto v___jp_2797_;
}
}
}
else
{
uint8_t v___x_2896_; 
lean_dec_ref(v_a_2758_);
lean_dec_ref(v_file_2757_);
lean_dec_ref(v_build_2756_);
v___x_2896_ = l_System_FilePath_pathExists(v_traceFile_2760_);
lean_dec_ref(v_traceFile_2760_);
if (v___x_2896_ == 0)
{
lean_dec_ref(v___x_2795_);
lean_del_object(v___x_2790_);
v_log_2773_ = v_log_2784_;
v_action_2774_ = v___x_2793_;
v_wantsRebuild_2775_ = v_noBuild_2792_;
v_trace_2776_ = v_trace_2787_;
v_buildTime_2777_ = v_buildTime_2788_;
goto v___jp_2772_;
}
else
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2897_ = lean_box(0);
v___x_2898_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_2899_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_2759_, v___x_2897_, v___x_2898_);
v___x_2900_ = l_Lake_BuildMetadata_writeFile(v___x_2795_, v___x_2899_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_dec_ref_known(v___x_2900_, 1);
lean_del_object(v___x_2790_);
v_log_2773_ = v_log_2784_;
v_action_2774_ = v___x_2793_;
v_wantsRebuild_2775_ = v_noBuild_2792_;
v_trace_2776_ = v_trace_2787_;
v_buildTime_2777_ = v_buildTime_2788_;
goto v___jp_2772_;
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2902_; uint8_t v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2908_; 
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_a_2901_);
lean_dec_ref_known(v___x_2900_, 1);
v___x_2902_ = lean_io_error_to_string(v_a_2901_);
v___x_2903_ = 3;
v___x_2904_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2904_, 0, v___x_2902_);
lean_ctor_set_uint8(v___x_2904_, sizeof(void*)*1, v___x_2903_);
v___x_2905_ = lean_array_get_size(v_log_2784_);
v___x_2906_ = lean_array_push(v_log_2784_, v___x_2904_);
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 0, v___x_2906_);
v___x_2908_ = v___x_2790_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2906_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v_trace_2787_);
lean_ctor_set(v_reuseFailAlloc_2910_, 2, v_buildTime_2788_);
v___x_2908_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
lean_object* v___x_2909_; 
lean_ctor_set_uint8(v___x_2908_, sizeof(void*)*3, v___x_2793_);
lean_ctor_set_uint8(v___x_2908_, sizeof(void*)*3 + 1, v_noBuild_2792_);
v___x_2909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2905_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
return v___x_2909_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___boxed(lean_object* v_build_2912_, lean_object* v_file_2913_, lean_object* v_a_2914_, lean_object* v_depTrace_2915_, lean_object* v_traceFile_2916_, lean_object* v_action_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_){
_start:
{
uint8_t v_action_boxed_2924_; lean_object* v_res_2925_; 
v_action_boxed_2924_ = lean_unbox(v_action_2917_);
v_res_2925_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(v_build_2912_, v_file_2913_, v_a_2914_, v_depTrace_2915_, v_traceFile_2916_, v_action_boxed_2924_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_);
lean_dec_ref(v_a_2921_);
lean_dec(v_a_2920_);
lean_dec(v_a_2919_);
lean_dec(v_a_2918_);
lean_dec_ref(v_depTrace_2915_);
return v_res_2925_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(lean_object* v_info_2926_, lean_object* v_self_2927_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = lean_io_metadata(v_info_2926_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_a_2930_; lean_object* v_modified_2931_; uint8_t v___x_2932_; 
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_a_2930_);
lean_dec_ref_known(v___x_2929_, 1);
v_modified_2931_ = lean_ctor_get(v_a_2930_, 1);
lean_inc_ref(v_modified_2931_);
lean_dec(v_a_2930_);
v___x_2932_ = l_IO_FS_instOrdSystemTime_ord(v_self_2927_, v_modified_2931_);
lean_dec_ref(v_modified_2931_);
if (v___x_2932_ == 0)
{
uint8_t v___x_2933_; 
v___x_2933_ = 1;
return v___x_2933_;
}
else
{
uint8_t v___x_2934_; 
v___x_2934_ = 0;
return v___x_2934_;
}
}
else
{
uint8_t v___x_2935_; 
lean_dec_ref_known(v___x_2929_, 1);
v___x_2935_ = 0;
return v___x_2935_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___boxed(lean_object* v_info_2936_, lean_object* v_self_2937_, lean_object* v_a_2938_){
_start:
{
uint8_t v_res_2939_; lean_object* v_r_2940_; 
v_res_2939_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_2936_, v_self_2937_);
lean_dec_ref(v_self_2937_);
lean_dec_ref(v_info_2936_);
v_r_2940_ = lean_box(v_res_2939_);
return v_r_2940_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(lean_object* v_x_2941_, lean_object* v_x_2942_){
_start:
{
if (lean_obj_tag(v_x_2941_) == 0)
{
if (lean_obj_tag(v_x_2942_) == 0)
{
uint8_t v___x_2943_; 
v___x_2943_ = 1;
return v___x_2943_;
}
else
{
uint8_t v___x_2944_; 
v___x_2944_ = 0;
return v___x_2944_;
}
}
else
{
if (lean_obj_tag(v_x_2942_) == 0)
{
uint8_t v___x_2945_; 
v___x_2945_ = 0;
return v___x_2945_;
}
else
{
lean_object* v_val_2946_; lean_object* v_val_2947_; uint64_t v___x_2948_; uint64_t v___x_2949_; uint8_t v___x_2950_; 
v_val_2946_ = lean_ctor_get(v_x_2941_, 0);
v_val_2947_ = lean_ctor_get(v_x_2942_, 0);
v___x_2948_ = lean_unbox_uint64(v_val_2946_);
v___x_2949_ = lean_unbox_uint64(v_val_2947_);
v___x_2950_ = lean_uint64_dec_eq(v___x_2948_, v___x_2949_);
return v___x_2950_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2951_, lean_object* v_x_2952_){
_start:
{
uint8_t v_res_2953_; lean_object* v_r_2954_; 
v_res_2953_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(v_x_2951_, v_x_2952_);
lean_dec(v_x_2952_);
lean_dec(v_x_2951_);
v_r_2954_ = lean_box(v_res_2953_);
return v_r_2954_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(lean_object* v_info_2955_, lean_object* v_depTrace_2956_, lean_object* v_depHash_2957_, lean_object* v_oldTrace_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_){
_start:
{
uint64_t v_hash_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; uint8_t v___x_2965_; 
v_hash_2962_ = lean_ctor_get_uint64(v_depTrace_2956_, sizeof(void*)*3);
v___x_2963_ = lean_box_uint64(v_hash_2962_);
v___x_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2963_);
v___x_2965_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(v___x_2964_, v_depHash_2957_);
lean_dec_ref_known(v___x_2964_, 1);
if (v___x_2965_ == 0)
{
lean_object* v_toBuildConfig_2966_; uint8_t v_oldMode_2967_; 
v_toBuildConfig_2966_ = lean_ctor_get(v_a_2959_, 0);
v_oldMode_2967_ = lean_ctor_get_uint8(v_toBuildConfig_2966_, sizeof(void*)*4);
if (v_oldMode_2967_ == 0)
{
uint8_t v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2968_ = 0;
v___x_2969_ = lean_box(v___x_2968_);
v___x_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
lean_ctor_set(v___x_2970_, 1, v_a_2960_);
return v___x_2970_;
}
else
{
uint8_t v___x_2971_; 
v___x_2971_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_2955_, v_oldTrace_2958_);
if (v___x_2971_ == 0)
{
uint8_t v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2972_ = 0;
v___x_2973_ = lean_box(v___x_2972_);
v___x_2974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2973_);
lean_ctor_set(v___x_2974_, 1, v_a_2960_);
return v___x_2974_;
}
else
{
uint8_t v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2975_ = 1;
v___x_2976_ = lean_box(v___x_2975_);
v___x_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
lean_ctor_set(v___x_2977_, 1, v_a_2960_);
return v___x_2977_;
}
}
}
else
{
uint8_t v___x_2978_; 
v___x_2978_ = l_System_FilePath_pathExists(v_info_2955_);
if (v___x_2978_ == 0)
{
uint8_t v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2979_ = 0;
v___x_2980_ = lean_box(v___x_2979_);
v___x_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
lean_ctor_set(v___x_2981_, 1, v_a_2960_);
return v___x_2981_;
}
else
{
uint8_t v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2982_ = 2;
v___x_2983_ = lean_box(v___x_2982_);
v___x_2984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2983_);
lean_ctor_set(v___x_2984_, 1, v_a_2960_);
return v___x_2984_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg___boxed(lean_object* v_info_2985_, lean_object* v_depTrace_2986_, lean_object* v_depHash_2987_, lean_object* v_oldTrace_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_2985_, v_depTrace_2986_, v_depHash_2987_, v_oldTrace_2988_, v_a_2989_, v_a_2990_);
lean_dec_ref(v_a_2989_);
lean_dec_ref(v_oldTrace_2988_);
lean_dec(v_depHash_2987_);
lean_dec_ref(v_depTrace_2986_);
lean_dec_ref(v_info_2985_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(lean_object* v_a_2993_, lean_object* v_info_2994_, lean_object* v_depTrace_2995_, lean_object* v_savedTrace_2996_, lean_object* v_oldTrace_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_){
_start:
{
if (lean_obj_tag(v_savedTrace_2996_) == 2)
{
lean_object* v_data_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3055_; 
v_data_3004_ = lean_ctor_get(v_savedTrace_2996_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v_savedTrace_2996_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3006_ = v_savedTrace_2996_;
v_isShared_3007_ = v_isSharedCheck_3055_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_data_3004_);
lean_dec(v_savedTrace_2996_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3055_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
uint64_t v_depHash_3008_; lean_object* v_log_3009_; lean_object* v___x_3010_; lean_object* v___x_3012_; 
v_depHash_3008_ = lean_ctor_get_uint64(v_data_3004_, sizeof(void*)*3);
v_log_3009_ = lean_ctor_get(v_data_3004_, 2);
lean_inc_ref(v_log_3009_);
lean_dec_ref(v_data_3004_);
v___x_3010_ = lean_box_uint64(v_depHash_3008_);
if (v_isShared_3007_ == 0)
{
lean_ctor_set_tag(v___x_3006_, 1);
lean_ctor_set(v___x_3006_, 0, v___x_3010_);
v___x_3012_ = v___x_3006_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3010_);
v___x_3012_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
lean_object* v___x_3013_; lean_object* v_a_3014_; lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3053_; 
v___x_3013_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_2994_, v_depTrace_2995_, v___x_3012_, v_oldTrace_2997_, v_a_3001_, v_a_3002_);
lean_dec_ref(v___x_3012_);
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
v_a_3015_ = lean_ctor_get(v___x_3013_, 1);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3017_ = v___x_3013_;
v_isShared_3018_ = v_isSharedCheck_3053_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_inc(v_a_3014_);
lean_dec(v___x_3013_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3053_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___y_3020_; uint8_t v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; uint8_t v___x_3027_; 
v___x_3024_ = lean_unbox(v_a_3014_);
v___x_3025_ = l_Lake_OutputStatus_ctorIdx(v___x_3024_);
v___x_3026_ = lean_obj_once(&l_Lake_OutputStatus_isUpToDate___closed__0, &l_Lake_OutputStatus_isUpToDate___closed__0_once, _init_l_Lake_OutputStatus_isUpToDate___closed__0);
v___x_3027_ = lean_nat_dec_eq(v___x_3025_, v___x_3026_);
lean_dec(v___x_3025_);
if (v___x_3027_ == 0)
{
lean_object* v_log_3028_; uint8_t v_action_3029_; uint8_t v_wantsRebuild_3030_; lean_object* v_trace_3031_; lean_object* v_buildTime_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3052_; 
v_log_3028_ = lean_ctor_get(v_a_3015_, 0);
v_action_3029_ = lean_ctor_get_uint8(v_a_3015_, sizeof(void*)*3);
v_wantsRebuild_3030_ = lean_ctor_get_uint8(v_a_3015_, sizeof(void*)*3 + 1);
v_trace_3031_ = lean_ctor_get(v_a_3015_, 1);
v_buildTime_3032_ = lean_ctor_get(v_a_3015_, 2);
v_isSharedCheck_3052_ = !lean_is_exclusive(v_a_3015_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3034_ = v_a_3015_;
v_isShared_3035_ = v_isSharedCheck_3052_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_buildTime_3032_);
lean_inc(v_trace_3031_);
lean_inc(v_log_3028_);
lean_dec(v_a_3015_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3052_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
uint8_t v___x_3036_; uint8_t v___x_3037_; lean_object* v___x_3039_; 
v___x_3036_ = 2;
v___x_3037_ = l_Lake_JobAction_merge(v_action_3029_, v___x_3036_);
if (v_isShared_3035_ == 0)
{
v___x_3039_ = v___x_3034_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_log_3028_);
lean_ctor_set(v_reuseFailAlloc_3051_, 1, v_trace_3031_);
lean_ctor_set(v_reuseFailAlloc_3051_, 2, v_buildTime_3032_);
lean_ctor_set_uint8(v_reuseFailAlloc_3051_, sizeof(void*)*3 + 1, v_wantsRebuild_3030_);
v___x_3039_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
lean_object* v___x_3040_; 
lean_ctor_set_uint8(v___x_3039_, sizeof(void*)*3, v___x_3037_);
v___x_3040_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_3009_, v_a_2993_, v_a_2998_, v_a_2999_, v_a_3000_, v_a_3001_, v___x_3039_);
lean_dec_ref(v_log_3009_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 1);
lean_inc(v_a_3041_);
lean_dec_ref_known(v___x_3040_, 2);
v___y_3020_ = v_a_3041_;
goto v___jp_3019_;
}
else
{
lean_object* v_a_3042_; lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
lean_del_object(v___x_3017_);
lean_dec(v_a_3014_);
v_a_3042_ = lean_ctor_get(v___x_3040_, 0);
v_a_3043_ = lean_ctor_get(v___x_3040_, 1);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_3040_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_inc(v_a_3042_);
lean_dec(v___x_3040_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3042_);
lean_ctor_set(v_reuseFailAlloc_3049_, 1, v_a_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_log_3009_);
v___y_3020_ = v_a_3015_;
goto v___jp_3019_;
}
v___jp_3019_:
{
lean_object* v___x_3022_; 
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 1, v___y_3020_);
v___x_3022_ = v___x_3017_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3014_);
lean_ctor_set(v_reuseFailAlloc_3023_, 1, v___y_3020_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
}
}
else
{
lean_object* v_toBuildConfig_3056_; uint8_t v_oldMode_3057_; 
lean_dec(v_savedTrace_2996_);
v_toBuildConfig_3056_ = lean_ctor_get(v_a_3001_, 0);
v_oldMode_3057_ = lean_ctor_get_uint8(v_toBuildConfig_3056_, sizeof(void*)*4);
if (v_oldMode_3057_ == 0)
{
uint8_t v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3058_ = 0;
v___x_3059_ = lean_box(v___x_3058_);
v___x_3060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3059_);
lean_ctor_set(v___x_3060_, 1, v_a_3002_);
return v___x_3060_;
}
else
{
uint8_t v___x_3061_; 
v___x_3061_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_2994_, v_oldTrace_2997_);
if (v___x_3061_ == 0)
{
uint8_t v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3062_ = 0;
v___x_3063_ = lean_box(v___x_3062_);
v___x_3064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3063_);
lean_ctor_set(v___x_3064_, 1, v_a_3002_);
return v___x_3064_;
}
else
{
uint8_t v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3065_ = 1;
v___x_3066_ = lean_box(v___x_3065_);
v___x_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3066_);
lean_ctor_set(v___x_3067_, 1, v_a_3002_);
return v___x_3067_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0___boxed(lean_object* v_a_3068_, lean_object* v_info_3069_, lean_object* v_depTrace_3070_, lean_object* v_savedTrace_3071_, lean_object* v_oldTrace_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_3068_, v_info_3069_, v_depTrace_3070_, v_savedTrace_3071_, v_oldTrace_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_);
lean_dec_ref(v_a_3076_);
lean_dec(v_a_3075_);
lean_dec(v_a_3074_);
lean_dec(v_a_3073_);
lean_dec_ref(v_oldTrace_3072_);
lean_dec_ref(v_depTrace_3070_);
lean_dec_ref(v_info_3069_);
lean_dec_ref(v_a_3068_);
return v_res_3079_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27(lean_object* v_file_3081_, lean_object* v_build_3082_, uint8_t v_text_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_){
_start:
{
lean_object* v_a_3092_; lean_object* v_a_3126_; lean_object* v_a_3127_; lean_object* v_trace_3129_; lean_object* v_log_3130_; uint8_t v_action_3131_; uint8_t v_wantsRebuild_3132_; lean_object* v_buildTime_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3165_; 
v_trace_3129_ = lean_ctor_get(v_a_3089_, 1);
v_log_3130_ = lean_ctor_get(v_a_3089_, 0);
v_action_3131_ = lean_ctor_get_uint8(v_a_3089_, sizeof(void*)*3);
v_wantsRebuild_3132_ = lean_ctor_get_uint8(v_a_3089_, sizeof(void*)*3 + 1);
v_buildTime_3133_ = lean_ctor_get(v_a_3089_, 2);
v_isSharedCheck_3165_ = !lean_is_exclusive(v_a_3089_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3135_ = v_a_3089_;
v_isShared_3136_ = v_isSharedCheck_3165_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_buildTime_3133_);
lean_inc(v_trace_3129_);
lean_inc(v_log_3130_);
lean_dec(v_a_3089_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3165_;
goto v_resetjp_3134_;
}
v___jp_3091_:
{
lean_object* v___x_3093_; 
v___x_3093_ = l_Lake_fetchFileTrace___redArg(v_file_3081_, v_text_3083_, v_a_3088_, v_a_3092_);
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
v___jp_3125_:
{
lean_object* v___x_3128_; 
v___x_3128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3128_, 0, v_a_3126_);
lean_ctor_set(v___x_3128_, 1, v_a_3127_);
return v___x_3128_;
}
v_resetjp_3134_:
{
lean_object* v_mtime_3137_; lean_object* v___x_3138_; lean_object* v_traceFile_3139_; uint8_t v___x_3140_; lean_object* v___x_3141_; 
v_mtime_3137_ = lean_ctor_get(v_trace_3129_, 2);
v___x_3138_ = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(v_file_3081_);
v_traceFile_3139_ = lean_string_append(v_file_3081_, v___x_3138_);
v___x_3140_ = 5;
lean_inc_ref(v_traceFile_3139_);
v___x_3141_ = l_Lake_readTraceFile(v_traceFile_3139_, v_log_3130_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; lean_object* v_a_3143_; lean_object* v___x_3145_; 
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_a_3142_);
v_a_3143_ = lean_ctor_get(v___x_3141_, 1);
lean_inc(v_a_3143_);
lean_dec_ref_known(v___x_3141_, 2);
lean_inc_ref(v_trace_3129_);
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 0, v_a_3143_);
v___x_3145_ = v___x_3135_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3143_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v_trace_3129_);
lean_ctor_set(v_reuseFailAlloc_3159_, 2, v_buildTime_3133_);
lean_ctor_set_uint8(v_reuseFailAlloc_3159_, sizeof(void*)*3, v_action_3131_);
lean_ctor_set_uint8(v_reuseFailAlloc_3159_, sizeof(void*)*3 + 1, v_wantsRebuild_3132_);
v___x_3145_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
lean_object* v___x_3146_; 
v___x_3146_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_3084_, v_file_3081_, v_trace_3129_, v_a_3142_, v_mtime_3137_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v___x_3145_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; lean_object* v_a_3148_; uint8_t v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; uint8_t v___x_3152_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_a_3147_);
v_a_3148_ = lean_ctor_get(v___x_3146_, 1);
lean_inc(v_a_3148_);
lean_dec_ref_known(v___x_3146_, 2);
v___x_3149_ = lean_unbox(v_a_3147_);
lean_dec(v_a_3147_);
v___x_3150_ = l_Lake_OutputStatus_ctorIdx(v___x_3149_);
v___x_3151_ = lean_obj_once(&l_Lake_OutputStatus_isUpToDate___closed__0, &l_Lake_OutputStatus_isUpToDate___closed__0_once, _init_l_Lake_OutputStatus_isUpToDate___closed__0);
v___x_3152_ = lean_nat_dec_eq(v___x_3150_, v___x_3151_);
lean_dec(v___x_3150_);
if (v___x_3152_ == 0)
{
lean_dec_ref(v_traceFile_3139_);
lean_dec_ref(v_trace_3129_);
lean_dec_ref(v_a_3084_);
lean_dec_ref(v_build_3082_);
v_a_3092_ = v_a_3148_;
goto v___jp_3091_;
}
else
{
lean_object* v___x_3153_; 
lean_inc_ref(v_file_3081_);
v___x_3153_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(v_build_3082_, v_file_3081_, v_a_3084_, v_trace_3129_, v_traceFile_3139_, v___x_3140_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3148_);
lean_dec_ref(v_trace_3129_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 1);
lean_inc(v_a_3154_);
lean_dec_ref_known(v___x_3153_, 2);
v_a_3092_ = v_a_3154_;
goto v___jp_3091_;
}
else
{
lean_object* v_a_3155_; lean_object* v_a_3156_; 
lean_dec_ref(v_file_3081_);
v_a_3155_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3155_);
v_a_3156_ = lean_ctor_get(v___x_3153_, 1);
lean_inc(v_a_3156_);
lean_dec_ref_known(v___x_3153_, 2);
v_a_3126_ = v_a_3155_;
v_a_3127_ = v_a_3156_;
goto v___jp_3125_;
}
}
}
else
{
lean_object* v_a_3157_; lean_object* v_a_3158_; 
lean_dec_ref(v_traceFile_3139_);
lean_dec_ref(v_trace_3129_);
lean_dec_ref(v_a_3084_);
lean_dec_ref(v_build_3082_);
lean_dec_ref(v_file_3081_);
v_a_3157_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_a_3157_);
v_a_3158_ = lean_ctor_get(v___x_3146_, 1);
lean_inc(v_a_3158_);
lean_dec_ref_known(v___x_3146_, 2);
v_a_3126_ = v_a_3157_;
v_a_3127_ = v_a_3158_;
goto v___jp_3125_;
}
}
}
else
{
lean_object* v_a_3160_; lean_object* v_a_3161_; lean_object* v___x_3163_; 
lean_dec_ref(v_traceFile_3139_);
lean_dec_ref(v_a_3084_);
lean_dec_ref(v_build_3082_);
lean_dec_ref(v_file_3081_);
v_a_3160_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_a_3160_);
v_a_3161_ = lean_ctor_get(v___x_3141_, 1);
lean_inc(v_a_3161_);
lean_dec_ref_known(v___x_3141_, 2);
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 0, v_a_3161_);
v___x_3163_ = v___x_3135_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3161_);
lean_ctor_set(v_reuseFailAlloc_3164_, 1, v_trace_3129_);
lean_ctor_set(v_reuseFailAlloc_3164_, 2, v_buildTime_3133_);
lean_ctor_set_uint8(v_reuseFailAlloc_3164_, sizeof(void*)*3, v_action_3131_);
lean_ctor_set_uint8(v_reuseFailAlloc_3164_, sizeof(void*)*3 + 1, v_wantsRebuild_3132_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
v_a_3126_ = v_a_3160_;
v_a_3127_ = v___x_3163_;
goto v___jp_3125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27___boxed(lean_object* v_file_3166_, lean_object* v_build_3167_, lean_object* v_text_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_){
_start:
{
uint8_t v_text_boxed_3176_; lean_object* v_res_3177_; 
v_text_boxed_3176_ = lean_unbox(v_text_3168_);
v_res_3177_ = l_Lake_buildFileUnlessUpToDate_x27(v_file_3166_, v_build_3167_, v_text_boxed_3176_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_);
lean_dec_ref(v_a_3173_);
lean_dec(v_a_3172_);
lean_dec(v_a_3171_);
lean_dec(v_a_3170_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(lean_object* v_a_3178_, lean_object* v_info_3179_, lean_object* v_depTrace_3180_, lean_object* v_depHash_3181_, lean_object* v_oldTrace_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_){
_start:
{
lean_object* v___x_3189_; 
v___x_3189_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_3179_, v_depTrace_3180_, v_depHash_3181_, v_oldTrace_3182_, v_a_3186_, v_a_3187_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___boxed(lean_object* v_a_3190_, lean_object* v_info_3191_, lean_object* v_depTrace_3192_, lean_object* v_depHash_3193_, lean_object* v_oldTrace_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(v_a_3190_, v_info_3191_, v_depTrace_3192_, v_depHash_3193_, v_oldTrace_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_);
lean_dec_ref(v_a_3198_);
lean_dec(v_a_3197_);
lean_dec(v_a_3196_);
lean_dec(v_a_3195_);
lean_dec_ref(v_oldTrace_3194_);
lean_dec(v_depHash_3193_);
lean_dec_ref(v_depTrace_3192_);
lean_dec_ref(v_info_3191_);
lean_dec_ref(v_a_3190_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0(lean_object* v___x_3202_, lean_object* v___x_3203_, lean_object* v_file_3204_, uint64_t v___x_3205_, lean_object* v___x_3206_, uint8_t v_useLocalFile_3207_, lean_object* v_____r_3208_){
_start:
{
lean_object* v___x_3210_; 
v___x_3210_ = l_IO_setAccessRights(v___x_3202_, v___x_3203_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v___x_3211_; 
lean_dec_ref_known(v___x_3210_, 1);
lean_inc_ref(v_file_3204_);
v___x_3211_ = l_Lake_writeFileHash(v_file_3204_, v___x_3205_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v___x_3212_; 
lean_dec_ref_known(v___x_3211_, 1);
v___x_3212_ = lean_io_metadata(v___x_3202_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3225_; 
v_a_3213_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3215_ = v___x_3212_;
v_isShared_3216_ = v_isSharedCheck_3225_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3212_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3225_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v_modified_3217_; lean_object* v___y_3219_; 
v_modified_3217_ = lean_ctor_get(v_a_3213_, 1);
lean_inc_ref(v_modified_3217_);
lean_dec(v_a_3213_);
if (v_useLocalFile_3207_ == 0)
{
v___y_3219_ = v___x_3202_;
goto v___jp_3218_;
}
else
{
lean_dec_ref(v___x_3202_);
lean_inc_ref(v_file_3204_);
v___y_3219_ = v_file_3204_;
goto v___jp_3218_;
}
v___jp_3218_:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3223_; 
v___x_3220_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3206_);
lean_ctor_set(v___x_3220_, 1, v___y_3219_);
lean_ctor_set(v___x_3220_, 2, v_file_3204_);
lean_ctor_set(v___x_3220_, 3, v_modified_3217_);
v___x_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 0, v___x_3221_);
v___x_3223_ = v___x_3215_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3221_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
lean_dec_ref(v___x_3206_);
lean_dec_ref(v_file_3204_);
lean_dec_ref(v___x_3202_);
v_a_3226_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3212_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3212_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3226_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec_ref(v___x_3206_);
lean_dec_ref(v_file_3204_);
lean_dec_ref(v___x_3202_);
v_a_3234_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3211_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3211_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
else
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
lean_dec_ref(v___x_3206_);
lean_dec_ref(v_file_3204_);
lean_dec_ref(v___x_3202_);
v_a_3242_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3210_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3210_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0___boxed(lean_object* v___x_3250_, lean_object* v___x_3251_, lean_object* v_file_3252_, lean_object* v___x_3253_, lean_object* v___x_3254_, lean_object* v_useLocalFile_3255_, lean_object* v_____r_3256_, lean_object* v___y_3257_){
_start:
{
uint64_t v___x_2111__boxed_3258_; uint8_t v_useLocalFile_boxed_3259_; lean_object* v_res_3260_; 
v___x_2111__boxed_3258_ = lean_unbox_uint64(v___x_3253_);
lean_dec_ref(v___x_3253_);
v_useLocalFile_boxed_3259_ = lean_unbox(v_useLocalFile_3255_);
v_res_3260_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3250_, v___x_3251_, v_file_3252_, v___x_2111__boxed_3258_, v___x_3254_, v_useLocalFile_boxed_3259_, v_____r_3256_);
lean_dec_ref(v___x_3251_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact(lean_object* v_cache_3268_, lean_object* v_file_3269_, lean_object* v_ext_3270_, uint8_t v_text_3271_, uint8_t v_exe_3272_, uint8_t v_useLocalFile_3273_){
_start:
{
lean_object* v_a_3276_; lean_object* v___y_3283_; uint8_t v___x_3294_; 
v___x_3294_ = 1;
if (v_text_3271_ == 0)
{
lean_object* v___x_3295_; 
v___x_3295_ = l_IO_FS_readBinFile(v_file_3269_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_object* v_a_3296_; uint64_t v___x_3297_; uint64_t v___x_3298_; uint64_t v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___y_3304_; lean_object* v___x_3325_; lean_object* v___x_3326_; uint8_t v___x_3327_; 
v_a_3296_ = lean_ctor_get(v___x_3295_, 0);
lean_inc(v_a_3296_);
lean_dec_ref_known(v___x_3295_, 1);
v___x_3297_ = l_Lake_Hash_nil;
v___x_3298_ = lean_byte_array_hash(v_a_3296_);
v___x_3299_ = lean_uint64_mix_hash(v___x_3297_, v___x_3298_);
lean_inc_ref(v_ext_3270_);
v___x_3300_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3300_, 0, v_ext_3270_);
lean_ctor_set_uint64(v___x_3300_, sizeof(void*)*1, v___x_3299_);
v___x_3301_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
v___x_3302_ = l_System_FilePath_join(v_cache_3268_, v___x_3301_);
v___x_3325_ = lean_string_utf8_byte_size(v_ext_3270_);
v___x_3326_ = lean_unsigned_to_nat(0u);
v___x_3327_ = lean_nat_dec_eq(v___x_3325_, v___x_3326_);
if (v___x_3327_ == 0)
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3328_ = l_Lake_lowerHexUInt64(v___x_3299_);
v___x_3329_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_3330_ = lean_string_append(v___x_3328_, v___x_3329_);
v___x_3331_ = lean_string_append(v___x_3330_, v_ext_3270_);
lean_dec_ref(v_ext_3270_);
v___y_3304_ = v___x_3331_;
goto v___jp_3303_;
}
else
{
lean_object* v___x_3332_; 
lean_dec_ref(v_ext_3270_);
v___x_3332_ = l_Lake_lowerHexUInt64(v___x_3299_);
v___y_3304_ = v___x_3332_;
goto v___jp_3303_;
}
v___jp_3303_:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3305_ = l_Lake_joinRelative(v___x_3302_, v___y_3304_);
v___x_3306_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_3306_, 0, v___x_3294_);
lean_ctor_set_uint8(v___x_3306_, 1, v_text_3271_);
lean_ctor_set_uint8(v___x_3306_, 2, v_exe_3272_);
lean_inc_ref_n(v___x_3306_, 2);
v___x_3307_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3306_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
lean_ctor_set(v___x_3307_, 2, v___x_3306_);
v___x_3308_ = l_IO_setAccessRights(v_file_3269_, v___x_3307_);
if (lean_obj_tag(v___x_3308_) == 0)
{
uint8_t v___x_3309_; 
lean_dec_ref_known(v___x_3308_, 1);
v___x_3309_ = l_System_FilePath_pathExists(v___x_3305_);
if (v___x_3309_ == 0)
{
lean_object* v___x_3310_; 
lean_inc_ref(v___x_3305_);
v___x_3310_ = l_Lake_createParentDirs(v___x_3305_);
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_object* v___x_3311_; 
lean_dec_ref_known(v___x_3310_, 1);
v___x_3311_ = lean_io_hard_link(v_file_3269_, v___x_3305_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
lean_dec_ref_known(v___x_3311_, 1);
lean_dec(v_a_3296_);
v___x_3312_ = lean_box(0);
v___x_3313_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3305_, v___x_3307_, v_file_3269_, v___x_3299_, v___x_3300_, v_useLocalFile_3273_, v___x_3312_);
lean_dec_ref_known(v___x_3307_, 3);
v___y_3283_ = v___x_3313_;
goto v___jp_3282_;
}
else
{
lean_object* v_a_3314_; 
v_a_3314_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_a_3314_);
lean_dec_ref_known(v___x_3311_, 1);
if (lean_obj_tag(v_a_3314_) == 0)
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
lean_dec_ref_known(v_a_3314_, 2);
lean_dec(v_a_3296_);
v___x_3315_ = lean_box(0);
v___x_3316_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3305_, v___x_3307_, v_file_3269_, v___x_3299_, v___x_3300_, v_useLocalFile_3273_, v___x_3315_);
lean_dec_ref_known(v___x_3307_, 3);
v___y_3283_ = v___x_3316_;
goto v___jp_3282_;
}
else
{
lean_object* v___x_3317_; 
lean_dec(v_a_3314_);
v___x_3317_ = l_Lake_writeBinFileIfNew(v___x_3305_, v_a_3296_);
lean_dec(v_a_3296_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v_a_3318_; lean_object* v___x_3319_; 
v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
lean_inc(v_a_3318_);
lean_dec_ref_known(v___x_3317_, 1);
v___x_3319_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3305_, v___x_3307_, v_file_3269_, v___x_3299_, v___x_3300_, v_useLocalFile_3273_, v_a_3318_);
lean_dec_ref_known(v___x_3307_, 3);
v___y_3283_ = v___x_3319_;
goto v___jp_3282_;
}
else
{
lean_object* v_a_3320_; 
lean_dec_ref_known(v___x_3307_, 3);
lean_dec_ref(v___x_3305_);
lean_dec_ref_known(v___x_3300_, 1);
lean_dec_ref(v_file_3269_);
v_a_3320_ = lean_ctor_get(v___x_3317_, 0);
lean_inc(v_a_3320_);
lean_dec_ref_known(v___x_3317_, 1);
v_a_3276_ = v_a_3320_;
goto v___jp_3275_;
}
}
}
}
else
{
lean_object* v_a_3321_; 
lean_dec_ref_known(v___x_3307_, 3);
lean_dec_ref(v___x_3305_);
lean_dec_ref_known(v___x_3300_, 1);
lean_dec(v_a_3296_);
lean_dec_ref(v_file_3269_);
v_a_3321_ = lean_ctor_get(v___x_3310_, 0);
lean_inc(v_a_3321_);
lean_dec_ref_known(v___x_3310_, 1);
v_a_3276_ = v_a_3321_;
goto v___jp_3275_;
}
}
else
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
lean_dec(v_a_3296_);
v___x_3322_ = lean_box(0);
v___x_3323_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3305_, v___x_3307_, v_file_3269_, v___x_3299_, v___x_3300_, v_useLocalFile_3273_, v___x_3322_);
lean_dec_ref_known(v___x_3307_, 3);
v___y_3283_ = v___x_3323_;
goto v___jp_3282_;
}
}
else
{
lean_object* v_a_3324_; 
lean_dec_ref_known(v___x_3307_, 3);
lean_dec_ref(v___x_3305_);
lean_dec_ref_known(v___x_3300_, 1);
lean_dec(v_a_3296_);
lean_dec_ref(v_file_3269_);
v_a_3324_ = lean_ctor_get(v___x_3308_, 0);
lean_inc(v_a_3324_);
lean_dec_ref_known(v___x_3308_, 1);
v_a_3276_ = v_a_3324_;
goto v___jp_3275_;
}
}
}
else
{
lean_object* v_a_3333_; 
lean_dec_ref(v_ext_3270_);
lean_dec_ref(v_file_3269_);
lean_dec_ref(v_cache_3268_);
v_a_3333_ = lean_ctor_get(v___x_3295_, 0);
lean_inc(v_a_3333_);
lean_dec_ref_known(v___x_3295_, 1);
v_a_3276_ = v_a_3333_;
goto v___jp_3275_;
}
}
else
{
lean_object* v___x_3334_; 
v___x_3334_ = l_IO_FS_readFile(v_file_3269_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3335_; lean_object* v___x_3336_; uint64_t v___x_3337_; uint64_t v___x_3338_; uint64_t v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___y_3344_; lean_object* v___x_3358_; lean_object* v___x_3359_; uint8_t v___x_3360_; 
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3335_);
lean_dec_ref_known(v___x_3334_, 1);
v___x_3336_ = l_String_crlfToLf(v_a_3335_);
lean_dec(v_a_3335_);
v___x_3337_ = l_Lake_Hash_nil;
v___x_3338_ = lean_string_hash(v___x_3336_);
v___x_3339_ = lean_uint64_mix_hash(v___x_3337_, v___x_3338_);
lean_inc_ref(v_ext_3270_);
v___x_3340_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3340_, 0, v_ext_3270_);
lean_ctor_set_uint64(v___x_3340_, sizeof(void*)*1, v___x_3339_);
v___x_3341_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
v___x_3342_ = l_System_FilePath_join(v_cache_3268_, v___x_3341_);
v___x_3358_ = lean_string_utf8_byte_size(v_ext_3270_);
v___x_3359_ = lean_unsigned_to_nat(0u);
v___x_3360_ = lean_nat_dec_eq(v___x_3358_, v___x_3359_);
if (v___x_3360_ == 0)
{
lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3361_ = l_Lake_lowerHexUInt64(v___x_3339_);
v___x_3362_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_3363_ = lean_string_append(v___x_3361_, v___x_3362_);
v___x_3364_ = lean_string_append(v___x_3363_, v_ext_3270_);
lean_dec_ref(v_ext_3270_);
v___y_3344_ = v___x_3364_;
goto v___jp_3343_;
}
else
{
lean_object* v___x_3365_; 
lean_dec_ref(v_ext_3270_);
v___x_3365_ = l_Lake_lowerHexUInt64(v___x_3339_);
v___y_3344_ = v___x_3365_;
goto v___jp_3343_;
}
v___jp_3343_:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3345_ = l_Lake_joinRelative(v___x_3342_, v___y_3344_);
v___x_3346_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__3));
v___x_3347_ = l_IO_setAccessRights(v_file_3269_, v___x_3346_);
if (lean_obj_tag(v___x_3347_) == 0)
{
uint8_t v___x_3348_; 
lean_dec_ref_known(v___x_3347_, 1);
v___x_3348_ = l_System_FilePath_pathExists(v___x_3345_);
if (v___x_3348_ == 0)
{
lean_object* v___x_3349_; 
lean_inc_ref(v___x_3345_);
v___x_3349_ = l_Lake_createParentDirs(v___x_3345_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v___x_3350_; 
lean_dec_ref_known(v___x_3349_, 1);
v___x_3350_ = l_Lake_writeFileIfNew(v___x_3345_, v___x_3336_);
lean_dec_ref(v___x_3336_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; lean_object* v___x_3352_; 
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_a_3351_);
lean_dec_ref_known(v___x_3350_, 1);
v___x_3352_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3345_, v___x_3346_, v_file_3269_, v___x_3339_, v___x_3340_, v_useLocalFile_3273_, v_a_3351_);
v___y_3283_ = v___x_3352_;
goto v___jp_3282_;
}
else
{
lean_object* v_a_3353_; 
lean_dec_ref(v___x_3345_);
lean_dec_ref_known(v___x_3340_, 1);
lean_dec_ref(v_file_3269_);
v_a_3353_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_a_3353_);
lean_dec_ref_known(v___x_3350_, 1);
v_a_3276_ = v_a_3353_;
goto v___jp_3275_;
}
}
else
{
lean_object* v_a_3354_; 
lean_dec_ref(v___x_3345_);
lean_dec_ref_known(v___x_3340_, 1);
lean_dec_ref(v___x_3336_);
lean_dec_ref(v_file_3269_);
v_a_3354_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_a_3354_);
lean_dec_ref_known(v___x_3349_, 1);
v_a_3276_ = v_a_3354_;
goto v___jp_3275_;
}
}
else
{
lean_object* v___x_3355_; lean_object* v___x_3356_; 
lean_dec_ref(v___x_3336_);
v___x_3355_ = lean_box(0);
v___x_3356_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3345_, v___x_3346_, v_file_3269_, v___x_3339_, v___x_3340_, v_useLocalFile_3273_, v___x_3355_);
v___y_3283_ = v___x_3356_;
goto v___jp_3282_;
}
}
else
{
lean_object* v_a_3357_; 
lean_dec_ref(v___x_3345_);
lean_dec_ref_known(v___x_3340_, 1);
lean_dec_ref(v___x_3336_);
lean_dec_ref(v_file_3269_);
v_a_3357_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3357_);
lean_dec_ref_known(v___x_3347_, 1);
v_a_3276_ = v_a_3357_;
goto v___jp_3275_;
}
}
}
else
{
lean_object* v_a_3366_; 
lean_dec_ref(v_ext_3270_);
lean_dec_ref(v_file_3269_);
lean_dec_ref(v_cache_3268_);
v_a_3366_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3366_);
lean_dec_ref_known(v___x_3334_, 1);
v_a_3276_ = v_a_3366_;
goto v___jp_3275_;
}
}
v___jp_3275_:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3277_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__0));
v___x_3278_ = lean_io_error_to_string(v_a_3276_);
v___x_3279_ = lean_string_append(v___x_3277_, v___x_3278_);
lean_dec_ref(v___x_3278_);
v___x_3280_ = lean_mk_io_user_error(v___x_3279_);
v___x_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
return v___x_3281_;
}
v___jp_3282_:
{
if (lean_obj_tag(v___y_3283_) == 0)
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3292_; 
v_a_3284_ = lean_ctor_get(v___y_3283_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___y_3283_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3286_ = v___y_3283_;
v_isShared_3287_ = v_isSharedCheck_3292_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___y_3283_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3292_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v_a_3288_; lean_object* v___x_3290_; 
v_a_3288_ = lean_ctor_get(v_a_3284_, 0);
lean_inc(v_a_3288_);
lean_dec(v_a_3284_);
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 0, v_a_3288_);
v___x_3290_ = v___x_3286_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3288_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
else
{
lean_object* v_a_3293_; 
v_a_3293_ = lean_ctor_get(v___y_3283_, 0);
lean_inc(v_a_3293_);
lean_dec_ref_known(v___y_3283_, 1);
v_a_3276_ = v_a_3293_;
goto v___jp_3275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___boxed(lean_object* v_cache_3367_, lean_object* v_file_3368_, lean_object* v_ext_3369_, lean_object* v_text_3370_, lean_object* v_exe_3371_, lean_object* v_useLocalFile_3372_, lean_object* v_a_3373_){
_start:
{
uint8_t v_text_boxed_3374_; uint8_t v_exe_boxed_3375_; uint8_t v_useLocalFile_boxed_3376_; lean_object* v_res_3377_; 
v_text_boxed_3374_ = lean_unbox(v_text_3370_);
v_exe_boxed_3375_ = lean_unbox(v_exe_3371_);
v_useLocalFile_boxed_3376_ = lean_unbox(v_useLocalFile_3372_);
v_res_3377_ = l_Lake_Cache_saveArtifact(v_cache_3367_, v_file_3368_, v_ext_3369_, v_text_boxed_3374_, v_exe_boxed_3375_, v_useLocalFile_boxed_3376_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0(lean_object* v_x_3378_){
_start:
{
lean_object* v_lakeCache_3379_; 
v_lakeCache_3379_ = lean_ctor_get(v_x_3378_, 2);
lean_inc_ref(v_lakeCache_3379_);
return v_lakeCache_3379_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0___boxed(lean_object* v_x_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_Lake_cacheArtifact___redArg___lam__0(v_x_3380_);
lean_dec_ref(v_x_3380_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1(lean_object* v_file_3382_, lean_object* v_ext_3383_, uint8_t v_text_3384_, uint8_t v_exe_3385_, uint8_t v_useLocalFile_3386_, lean_object* v_inst_3387_, lean_object* v_____do__lift_3388_){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3389_ = lean_box(v_text_3384_);
v___x_3390_ = lean_box(v_exe_3385_);
v___x_3391_ = lean_box(v_useLocalFile_3386_);
v___x_3392_ = lean_alloc_closure((void*)(l_Lake_Cache_saveArtifact___boxed), 7, 6);
lean_closure_set(v___x_3392_, 0, v_____do__lift_3388_);
lean_closure_set(v___x_3392_, 1, v_file_3382_);
lean_closure_set(v___x_3392_, 2, v_ext_3383_);
lean_closure_set(v___x_3392_, 3, v___x_3389_);
lean_closure_set(v___x_3392_, 4, v___x_3390_);
lean_closure_set(v___x_3392_, 5, v___x_3391_);
v___x_3393_ = lean_apply_2(v_inst_3387_, lean_box(0), v___x_3392_);
return v___x_3393_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1___boxed(lean_object* v_file_3394_, lean_object* v_ext_3395_, lean_object* v_text_3396_, lean_object* v_exe_3397_, lean_object* v_useLocalFile_3398_, lean_object* v_inst_3399_, lean_object* v_____do__lift_3400_){
_start:
{
uint8_t v_text_boxed_3401_; uint8_t v_exe_boxed_3402_; uint8_t v_useLocalFile_boxed_3403_; lean_object* v_res_3404_; 
v_text_boxed_3401_ = lean_unbox(v_text_3396_);
v_exe_boxed_3402_ = lean_unbox(v_exe_3397_);
v_useLocalFile_boxed_3403_ = lean_unbox(v_useLocalFile_3398_);
v_res_3404_ = l_Lake_cacheArtifact___redArg___lam__1(v_file_3394_, v_ext_3395_, v_text_boxed_3401_, v_exe_boxed_3402_, v_useLocalFile_boxed_3403_, v_inst_3399_, v_____do__lift_3400_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg(lean_object* v_inst_3406_, lean_object* v_inst_3407_, lean_object* v_inst_3408_, lean_object* v_file_3409_, lean_object* v_ext_3410_, uint8_t v_text_3411_, uint8_t v_exe_3412_, uint8_t v_useLocalFile_3413_){
_start:
{
lean_object* v_toApplicative_3414_; lean_object* v_toFunctor_3415_; lean_object* v_toBind_3416_; lean_object* v_map_3417_; lean_object* v___f_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___f_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v_toApplicative_3414_ = lean_ctor_get(v_inst_3408_, 0);
v_toFunctor_3415_ = lean_ctor_get(v_toApplicative_3414_, 0);
lean_inc_ref(v_toFunctor_3415_);
v_toBind_3416_ = lean_ctor_get(v_inst_3408_, 1);
lean_inc(v_toBind_3416_);
lean_dec_ref(v_inst_3408_);
v_map_3417_ = lean_ctor_get(v_toFunctor_3415_, 0);
lean_inc(v_map_3417_);
lean_dec_ref(v_toFunctor_3415_);
v___f_3418_ = ((lean_object*)(l_Lake_cacheArtifact___redArg___closed__0));
v___x_3419_ = lean_box(v_text_3411_);
v___x_3420_ = lean_box(v_exe_3412_);
v___x_3421_ = lean_box(v_useLocalFile_3413_);
v___f_3422_ = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_3422_, 0, v_file_3409_);
lean_closure_set(v___f_3422_, 1, v_ext_3410_);
lean_closure_set(v___f_3422_, 2, v___x_3419_);
lean_closure_set(v___f_3422_, 3, v___x_3420_);
lean_closure_set(v___f_3422_, 4, v___x_3421_);
lean_closure_set(v___f_3422_, 5, v_inst_3407_);
v___x_3423_ = lean_apply_4(v_map_3417_, lean_box(0), lean_box(0), v___f_3418_, v_inst_3406_);
v___x_3424_ = lean_apply_4(v_toBind_3416_, lean_box(0), lean_box(0), v___x_3423_, v___f_3422_);
return v___x_3424_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___boxed(lean_object* v_inst_3425_, lean_object* v_inst_3426_, lean_object* v_inst_3427_, lean_object* v_file_3428_, lean_object* v_ext_3429_, lean_object* v_text_3430_, lean_object* v_exe_3431_, lean_object* v_useLocalFile_3432_){
_start:
{
uint8_t v_text_boxed_3433_; uint8_t v_exe_boxed_3434_; uint8_t v_useLocalFile_boxed_3435_; lean_object* v_res_3436_; 
v_text_boxed_3433_ = lean_unbox(v_text_3430_);
v_exe_boxed_3434_ = lean_unbox(v_exe_3431_);
v_useLocalFile_boxed_3435_ = lean_unbox(v_useLocalFile_3432_);
v_res_3436_ = l_Lake_cacheArtifact___redArg(v_inst_3425_, v_inst_3426_, v_inst_3427_, v_file_3428_, v_ext_3429_, v_text_boxed_3433_, v_exe_boxed_3434_, v_useLocalFile_boxed_3435_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact(lean_object* v_m_3437_, lean_object* v_inst_3438_, lean_object* v_inst_3439_, lean_object* v_inst_3440_, lean_object* v_file_3441_, lean_object* v_ext_3442_, uint8_t v_text_3443_, uint8_t v_exe_3444_, uint8_t v_useLocalFile_3445_){
_start:
{
lean_object* v_toApplicative_3446_; lean_object* v_toFunctor_3447_; lean_object* v_toBind_3448_; lean_object* v_map_3449_; lean_object* v___f_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___f_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v_toApplicative_3446_ = lean_ctor_get(v_inst_3440_, 0);
v_toFunctor_3447_ = lean_ctor_get(v_toApplicative_3446_, 0);
lean_inc_ref(v_toFunctor_3447_);
v_toBind_3448_ = lean_ctor_get(v_inst_3440_, 1);
lean_inc(v_toBind_3448_);
lean_dec_ref(v_inst_3440_);
v_map_3449_ = lean_ctor_get(v_toFunctor_3447_, 0);
lean_inc(v_map_3449_);
lean_dec_ref(v_toFunctor_3447_);
v___f_3450_ = ((lean_object*)(l_Lake_cacheArtifact___redArg___closed__0));
v___x_3451_ = lean_box(v_text_3443_);
v___x_3452_ = lean_box(v_exe_3444_);
v___x_3453_ = lean_box(v_useLocalFile_3445_);
v___f_3454_ = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_3454_, 0, v_file_3441_);
lean_closure_set(v___f_3454_, 1, v_ext_3442_);
lean_closure_set(v___f_3454_, 2, v___x_3451_);
lean_closure_set(v___f_3454_, 3, v___x_3452_);
lean_closure_set(v___f_3454_, 4, v___x_3453_);
lean_closure_set(v___f_3454_, 5, v_inst_3439_);
v___x_3455_ = lean_apply_4(v_map_3449_, lean_box(0), lean_box(0), v___f_3450_, v_inst_3438_);
v___x_3456_ = lean_apply_4(v_toBind_3448_, lean_box(0), lean_box(0), v___x_3455_, v___f_3454_);
return v___x_3456_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___boxed(lean_object* v_m_3457_, lean_object* v_inst_3458_, lean_object* v_inst_3459_, lean_object* v_inst_3460_, lean_object* v_file_3461_, lean_object* v_ext_3462_, lean_object* v_text_3463_, lean_object* v_exe_3464_, lean_object* v_useLocalFile_3465_){
_start:
{
uint8_t v_text_boxed_3466_; uint8_t v_exe_boxed_3467_; uint8_t v_useLocalFile_boxed_3468_; lean_object* v_res_3469_; 
v_text_boxed_3466_ = lean_unbox(v_text_3463_);
v_exe_boxed_3467_ = lean_unbox(v_exe_3464_);
v_useLocalFile_boxed_3468_ = lean_unbox(v_useLocalFile_3465_);
v_res_3469_ = l_Lake_cacheArtifact(v_m_3457_, v_inst_3458_, v_inst_3459_, v_inst_3460_, v_file_3461_, v_ext_3462_, v_text_boxed_3466_, v_exe_boxed_3467_, v_useLocalFile_boxed_3468_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0(lean_object* v_x1_3471_, lean_object* v_x2_3472_){
_start:
{
lean_object* v_message_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
v_message_3473_ = lean_ctor_get(v_x2_3472_, 0);
v___x_3474_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0));
v___x_3475_ = lean_string_append(v_x1_3471_, v___x_3474_);
v___x_3476_ = lean_string_append(v___x_3475_, v_message_3473_);
return v___x_3476_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___boxed(lean_object* v_x1_3477_, lean_object* v_x2_3478_){
_start:
{
lean_object* v_res_3479_; 
v_res_3479_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0(v_x1_3477_, v_x2_3478_);
lean_dec_ref(v_x2_3478_);
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(lean_object* v_inst_3483_, uint64_t v_inputHash_3484_, lean_object* v_pkg_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_){
_start:
{
lean_object* v_r_3494_; lean_object* v___y_3495_; uint8_t v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; uint8_t v___y_3502_; lean_object* v___y_3503_; lean_object* v_toContext_3509_; lean_object* v_log_3510_; uint8_t v_action_3511_; uint8_t v_wantsRebuild_3512_; lean_object* v_trace_3513_; lean_object* v_buildTime_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3580_; 
v_toContext_3509_ = lean_ctor_get(v_a_3490_, 1);
v_log_3510_ = lean_ctor_get(v_a_3491_, 0);
v_action_3511_ = lean_ctor_get_uint8(v_a_3491_, sizeof(void*)*3);
v_wantsRebuild_3512_ = lean_ctor_get_uint8(v_a_3491_, sizeof(void*)*3 + 1);
v_trace_3513_ = lean_ctor_get(v_a_3491_, 1);
v_buildTime_3514_ = lean_ctor_get(v_a_3491_, 2);
v_isSharedCheck_3580_ = !lean_is_exclusive(v_a_3491_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3516_ = v_a_3491_;
v_isShared_3517_ = v_isSharedCheck_3580_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_buildTime_3514_);
lean_inc(v_trace_3513_);
lean_inc(v_log_3510_);
lean_dec(v_a_3491_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3580_;
goto v_resetjp_3515_;
}
v___jp_3493_:
{
lean_object* v___x_3496_; 
v___x_3496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3496_, 0, v_r_3494_);
lean_ctor_set(v___x_3496_, 1, v___y_3495_);
return v___x_3496_;
}
v___jp_3497_:
{
uint8_t v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3504_ = 0;
v___x_3505_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3505_, 0, v___y_3503_);
lean_ctor_set_uint8(v___x_3505_, sizeof(void*)*1, v___x_3504_);
v___x_3506_ = lean_array_push(v___y_3500_, v___x_3505_);
v___x_3507_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3507_, 0, v___x_3506_);
lean_ctor_set(v___x_3507_, 1, v___y_3499_);
lean_ctor_set(v___x_3507_, 2, v___y_3501_);
lean_ctor_set_uint8(v___x_3507_, sizeof(void*)*3, v___y_3502_);
lean_ctor_set_uint8(v___x_3507_, sizeof(void*)*3 + 1, v___y_3498_);
v___x_3508_ = lean_box(0);
v_r_3494_ = v___x_3508_;
v___y_3495_ = v___x_3507_;
goto v___jp_3493_;
}
v_resetjp_3515_:
{
lean_object* v_lakeCache_3518_; lean_object* v___f_3519_; lean_object* v_a_3521_; lean_object* v_log_3522_; uint8_t v_action_3523_; uint8_t v_wantsRebuild_3524_; lean_object* v_trace_3525_; lean_object* v_buildTime_3526_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v_lakeCache_3518_ = lean_ctor_get(v_toContext_3509_, 2);
v___f_3519_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0));
v___x_3552_ = l_Lake_Package_cacheScope(v_pkg_3485_);
lean_inc_ref(v_lakeCache_3518_);
v___x_3553_ = l_Lake_Cache_readOutputs_x3f(v_lakeCache_3518_, v___x_3552_, v_inputHash_3484_, v_log_3510_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; lean_object* v_a_3555_; lean_object* v___x_3557_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3554_);
v_a_3555_ = lean_ctor_get(v___x_3553_, 1);
lean_inc(v_a_3555_);
lean_dec_ref_known(v___x_3553_, 2);
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 0, v_a_3555_);
v___x_3557_ = v___x_3516_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_a_3555_);
lean_ctor_set(v_reuseFailAlloc_3577_, 1, v_trace_3513_);
lean_ctor_set(v_reuseFailAlloc_3577_, 2, v_buildTime_3514_);
lean_ctor_set_uint8(v_reuseFailAlloc_3577_, sizeof(void*)*3, v_action_3511_);
lean_ctor_set_uint8(v_reuseFailAlloc_3577_, sizeof(void*)*3 + 1, v_wantsRebuild_3512_);
v___x_3557_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
if (lean_obj_tag(v_a_3554_) == 0)
{
lean_object* v___x_3558_; 
lean_dec_ref(v_a_3486_);
lean_dec_ref(v_inst_3483_);
v___x_3558_ = lean_box(0);
v_r_3494_ = v___x_3558_;
v___y_3495_ = v___x_3557_;
goto v___jp_3493_;
}
else
{
lean_object* v_val_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3576_; 
v_val_3559_ = lean_ctor_get(v_a_3554_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v_a_3554_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3561_ = v_a_3554_;
v_isShared_3562_ = v_isSharedCheck_3576_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_val_3559_);
lean_dec(v_a_3554_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3576_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3563_; 
lean_inc_ref(v_a_3490_);
lean_inc(v_a_3489_);
lean_inc(v_a_3488_);
lean_inc(v_a_3487_);
v___x_3563_ = lean_apply_8(v_inst_3483_, v_val_3559_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v___x_3557_, lean_box(0));
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_a_3564_; lean_object* v_a_3565_; lean_object* v___x_3567_; 
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_a_3564_);
v_a_3565_ = lean_ctor_get(v___x_3563_, 1);
lean_inc(v_a_3565_);
lean_dec_ref_known(v___x_3563_, 2);
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 0, v_a_3564_);
v___x_3567_ = v___x_3561_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3564_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
v_r_3494_ = v___x_3567_;
v___y_3495_ = v_a_3565_;
goto v___jp_3493_;
}
}
else
{
lean_object* v_a_3569_; lean_object* v_a_3570_; lean_object* v_log_3571_; uint8_t v_action_3572_; uint8_t v_wantsRebuild_3573_; lean_object* v_trace_3574_; lean_object* v_buildTime_3575_; 
lean_del_object(v___x_3561_);
v_a_3569_ = lean_ctor_get(v___x_3563_, 1);
lean_inc(v_a_3569_);
v_a_3570_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_a_3570_);
lean_dec_ref_known(v___x_3563_, 2);
v_log_3571_ = lean_ctor_get(v_a_3569_, 0);
lean_inc_ref(v_log_3571_);
v_action_3572_ = lean_ctor_get_uint8(v_a_3569_, sizeof(void*)*3);
v_wantsRebuild_3573_ = lean_ctor_get_uint8(v_a_3569_, sizeof(void*)*3 + 1);
v_trace_3574_ = lean_ctor_get(v_a_3569_, 1);
lean_inc_ref(v_trace_3574_);
v_buildTime_3575_ = lean_ctor_get(v_a_3569_, 2);
lean_inc(v_buildTime_3575_);
lean_dec(v_a_3569_);
v_a_3521_ = v_a_3570_;
v_log_3522_ = v_log_3571_;
v_action_3523_ = v_action_3572_;
v_wantsRebuild_3524_ = v_wantsRebuild_3573_;
v_trace_3525_ = v_trace_3574_;
v_buildTime_3526_ = v_buildTime_3575_;
goto v___jp_3520_;
}
}
}
}
}
else
{
lean_object* v_a_3578_; lean_object* v_a_3579_; 
lean_del_object(v___x_3516_);
lean_dec_ref(v_a_3486_);
lean_dec_ref(v_inst_3483_);
v_a_3578_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3578_);
v_a_3579_ = lean_ctor_get(v___x_3553_, 1);
lean_inc(v_a_3579_);
lean_dec_ref_known(v___x_3553_, 2);
v_a_3521_ = v_a_3578_;
v_log_3522_ = v_a_3579_;
v_action_3523_ = v_action_3511_;
v_wantsRebuild_3524_ = v_wantsRebuild_3512_;
v_trace_3525_ = v_trace_3513_;
v_buildTime_3526_ = v_buildTime_3514_;
goto v___jp_3520_;
}
v___jp_3520_:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; uint8_t v___x_3544_; 
v___x_3527_ = lean_array_get_size(v_log_3522_);
lean_inc(v_a_3521_);
v___x_3528_ = l_Array_extract___redArg(v_log_3522_, v_a_3521_, v___x_3527_);
v___x_3529_ = l_Array_shrink___redArg(v_log_3522_, v_a_3521_);
lean_dec(v_a_3521_);
v___x_3530_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1));
v___x_3531_ = l_Lake_lowerHexUInt64(v_inputHash_3484_);
v___x_3532_ = lean_unsigned_to_nat(7u);
v___x_3533_ = lean_unsigned_to_nat(0u);
v___x_3534_ = lean_string_utf8_byte_size(v___x_3531_);
lean_inc_ref(v___x_3531_);
v___x_3535_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3531_);
lean_ctor_set(v___x_3535_, 1, v___x_3533_);
lean_ctor_set(v___x_3535_, 2, v___x_3534_);
v___x_3536_ = l_String_Slice_Pos_nextn(v___x_3535_, v___x_3533_, v___x_3532_);
lean_dec_ref_known(v___x_3535_, 3);
v___x_3537_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3531_);
lean_ctor_set(v___x_3537_, 1, v___x_3533_);
lean_ctor_set(v___x_3537_, 2, v___x_3536_);
v___x_3538_ = l_String_Slice_toString(v___x_3537_);
lean_dec_ref_known(v___x_3537_, 3);
v___x_3539_ = lean_string_append(v___x_3530_, v___x_3538_);
lean_dec_ref(v___x_3538_);
v___x_3540_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__2));
v___x_3541_ = lean_string_append(v___x_3539_, v___x_3540_);
v___x_3542_ = lean_array_get_size(v___x_3528_);
v___x_3543_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__9));
v___x_3544_ = lean_nat_dec_lt(v___x_3533_, v___x_3542_);
if (v___x_3544_ == 0)
{
lean_dec_ref(v___x_3528_);
v___y_3498_ = v_wantsRebuild_3524_;
v___y_3499_ = v_trace_3525_;
v___y_3500_ = v___x_3529_;
v___y_3501_ = v_buildTime_3526_;
v___y_3502_ = v_action_3523_;
v___y_3503_ = v___x_3541_;
goto v___jp_3497_;
}
else
{
uint8_t v___x_3545_; 
v___x_3545_ = lean_nat_dec_le(v___x_3542_, v___x_3542_);
if (v___x_3545_ == 0)
{
if (v___x_3544_ == 0)
{
lean_dec_ref(v___x_3528_);
v___y_3498_ = v_wantsRebuild_3524_;
v___y_3499_ = v_trace_3525_;
v___y_3500_ = v___x_3529_;
v___y_3501_ = v_buildTime_3526_;
v___y_3502_ = v_action_3523_;
v___y_3503_ = v___x_3541_;
goto v___jp_3497_;
}
else
{
size_t v___x_3546_; size_t v___x_3547_; lean_object* v___x_3548_; 
v___x_3546_ = ((size_t)0ULL);
v___x_3547_ = lean_usize_of_nat(v___x_3542_);
v___x_3548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3543_, v___f_3519_, v___x_3528_, v___x_3546_, v___x_3547_, v___x_3541_);
v___y_3498_ = v_wantsRebuild_3524_;
v___y_3499_ = v_trace_3525_;
v___y_3500_ = v___x_3529_;
v___y_3501_ = v_buildTime_3526_;
v___y_3502_ = v_action_3523_;
v___y_3503_ = v___x_3548_;
goto v___jp_3497_;
}
}
else
{
size_t v___x_3549_; size_t v___x_3550_; lean_object* v___x_3551_; 
v___x_3549_ = ((size_t)0ULL);
v___x_3550_ = lean_usize_of_nat(v___x_3542_);
v___x_3551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3543_, v___f_3519_, v___x_3528_, v___x_3549_, v___x_3550_, v___x_3541_);
v___y_3498_ = v_wantsRebuild_3524_;
v___y_3499_ = v_trace_3525_;
v___y_3500_ = v___x_3529_;
v___y_3501_ = v_buildTime_3526_;
v___y_3502_ = v_action_3523_;
v___y_3503_ = v___x_3551_;
goto v___jp_3497_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___boxed(lean_object* v_inst_3581_, lean_object* v_inputHash_3582_, lean_object* v_pkg_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_){
_start:
{
uint64_t v_inputHash_boxed_3591_; lean_object* v_res_3592_; 
v_inputHash_boxed_3591_ = lean_unbox_uint64(v_inputHash_3582_);
lean_dec_ref(v_inputHash_3582_);
v_res_3592_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3581_, v_inputHash_boxed_3591_, v_pkg_3583_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_);
lean_dec_ref(v_a_3588_);
lean_dec(v_a_3587_);
lean_dec(v_a_3586_);
lean_dec(v_a_3585_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f(lean_object* v_00_u03b1_3593_, lean_object* v_inst_3594_, uint64_t v_inputHash_3595_, lean_object* v_pkg_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_){
_start:
{
lean_object* v___x_3604_; 
v___x_3604_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3594_, v_inputHash_3595_, v_pkg_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___boxed(lean_object* v_00_u03b1_3605_, lean_object* v_inst_3606_, lean_object* v_inputHash_3607_, lean_object* v_pkg_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_){
_start:
{
uint64_t v_inputHash_boxed_3616_; lean_object* v_res_3617_; 
v_inputHash_boxed_3616_ = lean_unbox_uint64(v_inputHash_3607_);
lean_dec_ref(v_inputHash_3607_);
v_res_3617_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f(v_00_u03b1_3605_, v_inst_3606_, v_inputHash_boxed_3616_, v_pkg_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_);
lean_dec_ref(v_a_3613_);
lean_dec(v_a_3612_);
lean_dec(v_a_3611_);
lean_dec(v_a_3610_);
return v_res_3617_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(lean_object* v_a_3618_, lean_object* v_____r_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3627_, 0, v_a_3618_);
v___x_3628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3627_);
v___x_3629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3628_);
lean_ctor_set(v___x_3629_, 1, v___y_3625_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0___boxed(lean_object* v_a_3630_, lean_object* v_____r_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
lean_object* v_res_3639_; 
v_res_3639_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3630_, v_____r_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg(lean_object* v_inst_3641_, uint64_t v_inputHash_3642_, lean_object* v_savedTrace_3643_, lean_object* v_pkg_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_){
_start:
{
lean_object* v___y_3653_; lean_object* v_a_3657_; lean_object* v_a_3658_; lean_object* v___y_3673_; 
if (lean_obj_tag(v_savedTrace_3643_) == 2)
{
lean_object* v_data_3688_; uint64_t v_depHash_3689_; lean_object* v_outputs_x3f_3690_; uint8_t v___x_3691_; 
v_data_3688_ = lean_ctor_get(v_savedTrace_3643_, 0);
lean_inc_ref(v_data_3688_);
lean_dec_ref_known(v_savedTrace_3643_, 1);
v_depHash_3689_ = lean_ctor_get_uint64(v_data_3688_, sizeof(void*)*3);
v_outputs_x3f_3690_ = lean_ctor_get(v_data_3688_, 1);
lean_inc(v_outputs_x3f_3690_);
lean_dec_ref(v_data_3688_);
v___x_3691_ = lean_uint64_dec_eq(v_depHash_3689_, v_inputHash_3642_);
if (v___x_3691_ == 0)
{
lean_dec(v_outputs_x3f_3690_);
lean_dec_ref(v_a_3645_);
lean_dec_ref(v_pkg_3644_);
lean_dec_ref(v_inst_3641_);
v___y_3653_ = v_a_3650_;
goto v___jp_3652_;
}
else
{
if (lean_obj_tag(v_outputs_x3f_3690_) == 1)
{
lean_object* v_val_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v_val_3692_ = lean_ctor_get(v_outputs_x3f_3690_, 0);
lean_inc_n(v_val_3692_, 2);
lean_dec_ref_known(v_outputs_x3f_3690_, 1);
v___x_3693_ = lean_box(0);
v___x_3694_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3694_, 0, v_val_3692_);
lean_ctor_set(v___x_3694_, 1, v___x_3693_);
lean_ctor_set(v___x_3694_, 2, v___x_3693_);
lean_inc_ref(v_a_3649_);
lean_inc(v_a_3648_);
lean_inc(v_a_3647_);
lean_inc(v_a_3646_);
lean_inc_ref(v_a_3645_);
v___x_3695_ = lean_apply_8(v_inst_3641_, v___x_3694_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_, lean_box(0));
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_config_3696_; lean_object* v_a_3697_; lean_object* v_a_3698_; lean_object* v_enableArtifactCache_x3f_3699_; lean_object* v_a_3701_; uint8_t v_a_3705_; lean_object* v_a_3706_; 
v_config_3696_ = lean_ctor_get(v_pkg_3644_, 6);
v_a_3697_ = lean_ctor_get(v___x_3695_, 0);
lean_inc(v_a_3697_);
v_a_3698_ = lean_ctor_get(v___x_3695_, 1);
lean_inc(v_a_3698_);
lean_dec_ref_known(v___x_3695_, 2);
v_enableArtifactCache_x3f_3699_ = lean_ctor_get(v_config_3696_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_3699_) == 0)
{
lean_object* v_toContext_3738_; lean_object* v_lakeEnv_3739_; lean_object* v_enableArtifactCache_x3f_3740_; 
v_toContext_3738_ = lean_ctor_get(v_a_3649_, 1);
v_lakeEnv_3739_ = lean_ctor_get(v_toContext_3738_, 0);
v_enableArtifactCache_x3f_3740_ = lean_ctor_get(v_lakeEnv_3739_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_3740_) == 0)
{
lean_object* v_packages_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v_config_3744_; lean_object* v_enableArtifactCache_x3f_3745_; 
v_packages_3741_ = lean_ctor_get(v_toContext_3738_, 4);
v___x_3742_ = lean_unsigned_to_nat(0u);
v___x_3743_ = lean_array_fget_borrowed(v_packages_3741_, v___x_3742_);
v_config_3744_ = lean_ctor_get(v___x_3743_, 6);
v_enableArtifactCache_x3f_3745_ = lean_ctor_get(v_config_3744_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_3745_) == 0)
{
lean_dec(v_val_3692_);
lean_dec_ref(v_pkg_3644_);
v_a_3701_ = v_a_3698_;
goto v___jp_3700_;
}
else
{
lean_object* v_val_3746_; uint8_t v___x_3747_; 
v_val_3746_ = lean_ctor_get(v_enableArtifactCache_x3f_3745_, 0);
v___x_3747_ = lean_unbox(v_val_3746_);
v_a_3705_ = v___x_3747_;
v_a_3706_ = v_a_3698_;
goto v___jp_3704_;
}
}
else
{
lean_object* v_val_3748_; uint8_t v___x_3749_; 
v_val_3748_ = lean_ctor_get(v_enableArtifactCache_x3f_3740_, 0);
v___x_3749_ = lean_unbox(v_val_3748_);
v_a_3705_ = v___x_3749_;
v_a_3706_ = v_a_3698_;
goto v___jp_3704_;
}
}
else
{
lean_object* v_val_3750_; uint8_t v___x_3751_; 
v_val_3750_ = lean_ctor_get(v_enableArtifactCache_x3f_3699_, 0);
v___x_3751_ = lean_unbox(v_val_3750_);
v_a_3705_ = v___x_3751_;
v_a_3706_ = v_a_3698_;
goto v___jp_3704_;
}
v___jp_3700_:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; 
v___x_3702_ = lean_box(0);
v___x_3703_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3697_, v___x_3702_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3701_);
lean_dec_ref(v_a_3645_);
v___y_3673_ = v___x_3703_;
goto v___jp_3672_;
}
v___jp_3704_:
{
if (v_a_3705_ == 0)
{
lean_dec(v_val_3692_);
lean_dec_ref(v_pkg_3644_);
v_a_3701_ = v_a_3706_;
goto v___jp_3700_;
}
else
{
lean_object* v_toContext_3707_; lean_object* v_log_3708_; uint8_t v_action_3709_; uint8_t v_wantsRebuild_3710_; lean_object* v_trace_3711_; lean_object* v_buildTime_3712_; lean_object* v_lakeCache_3713_; lean_object* v___x_3714_; uint8_t v___x_3715_; lean_object* v___x_3716_; 
v_toContext_3707_ = lean_ctor_get(v_a_3649_, 1);
v_log_3708_ = lean_ctor_get(v_a_3706_, 0);
v_action_3709_ = lean_ctor_get_uint8(v_a_3706_, sizeof(void*)*3);
v_wantsRebuild_3710_ = lean_ctor_get_uint8(v_a_3706_, sizeof(void*)*3 + 1);
v_trace_3711_ = lean_ctor_get(v_a_3706_, 1);
v_buildTime_3712_ = lean_ctor_get(v_a_3706_, 2);
v_lakeCache_3713_ = lean_ctor_get(v_toContext_3707_, 2);
v___x_3714_ = l_Lake_Package_cacheScope(v_pkg_3644_);
v___x_3715_ = 0;
lean_inc_ref(v_lakeCache_3713_);
v___x_3716_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_3713_, v___x_3714_, v_inputHash_3642_, v_val_3692_, v___x_3693_, v___x_3693_, v___x_3715_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_object* v___x_3717_; lean_object* v___x_3718_; 
lean_dec_ref_known(v___x_3716_, 1);
v___x_3717_ = lean_box(0);
v___x_3718_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3697_, v___x_3717_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3706_);
lean_dec_ref(v_a_3645_);
v___y_3673_ = v___x_3718_;
goto v___jp_3672_;
}
else
{
lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3734_; 
lean_inc(v_buildTime_3712_);
lean_inc_ref(v_trace_3711_);
lean_inc_ref(v_log_3708_);
v_isSharedCheck_3734_ = !lean_is_exclusive(v_a_3706_);
if (v_isSharedCheck_3734_ == 0)
{
lean_object* v_unused_3735_; lean_object* v_unused_3736_; lean_object* v_unused_3737_; 
v_unused_3735_ = lean_ctor_get(v_a_3706_, 2);
lean_dec(v_unused_3735_);
v_unused_3736_ = lean_ctor_get(v_a_3706_, 1);
lean_dec(v_unused_3736_);
v_unused_3737_ = lean_ctor_get(v_a_3706_, 0);
lean_dec(v_unused_3737_);
v___x_3720_ = v_a_3706_;
v_isShared_3721_ = v_isSharedCheck_3734_;
goto v_resetjp_3719_;
}
else
{
lean_dec(v_a_3706_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3734_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v_a_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; uint8_t v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3731_; 
v_a_3722_ = lean_ctor_get(v___x_3716_, 0);
lean_inc(v_a_3722_);
lean_dec_ref_known(v___x_3716_, 1);
v___x_3723_ = ((lean_object*)(l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0));
v___x_3724_ = lean_io_error_to_string(v_a_3722_);
v___x_3725_ = lean_string_append(v___x_3723_, v___x_3724_);
lean_dec_ref(v___x_3724_);
v___x_3726_ = 2;
v___x_3727_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3727_, 0, v___x_3725_);
lean_ctor_set_uint8(v___x_3727_, sizeof(void*)*1, v___x_3726_);
v___x_3728_ = lean_box(0);
v___x_3729_ = lean_array_push(v_log_3708_, v___x_3727_);
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 0, v___x_3729_);
v___x_3731_ = v___x_3720_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3729_);
lean_ctor_set(v_reuseFailAlloc_3733_, 1, v_trace_3711_);
lean_ctor_set(v_reuseFailAlloc_3733_, 2, v_buildTime_3712_);
lean_ctor_set_uint8(v_reuseFailAlloc_3733_, sizeof(void*)*3, v_action_3709_);
lean_ctor_set_uint8(v_reuseFailAlloc_3733_, sizeof(void*)*3 + 1, v_wantsRebuild_3710_);
v___x_3731_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
lean_object* v___x_3732_; 
v___x_3732_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3697_, v___x_3728_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, v___x_3731_);
lean_dec_ref(v_a_3645_);
v___y_3673_ = v___x_3732_;
goto v___jp_3672_;
}
}
}
}
}
}
else
{
lean_object* v_a_3752_; lean_object* v_a_3753_; 
lean_dec(v_val_3692_);
lean_dec_ref(v_a_3645_);
lean_dec_ref(v_pkg_3644_);
v_a_3752_ = lean_ctor_get(v___x_3695_, 0);
lean_inc(v_a_3752_);
v_a_3753_ = lean_ctor_get(v___x_3695_, 1);
lean_inc(v_a_3753_);
lean_dec_ref_known(v___x_3695_, 2);
v_a_3657_ = v_a_3752_;
v_a_3658_ = v_a_3753_;
goto v___jp_3656_;
}
}
else
{
lean_dec(v_outputs_x3f_3690_);
lean_dec_ref(v_a_3645_);
lean_dec_ref(v_pkg_3644_);
lean_dec_ref(v_inst_3641_);
v___y_3653_ = v_a_3650_;
goto v___jp_3652_;
}
}
}
else
{
lean_dec_ref(v_a_3645_);
lean_dec_ref(v_pkg_3644_);
lean_dec(v_savedTrace_3643_);
lean_dec_ref(v_inst_3641_);
v___y_3653_ = v_a_3650_;
goto v___jp_3652_;
}
v___jp_3652_:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = lean_box(0);
v___x_3655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3654_);
lean_ctor_set(v___x_3655_, 1, v___y_3653_);
return v___x_3655_;
}
v___jp_3656_:
{
lean_object* v_log_3659_; uint8_t v_action_3660_; uint8_t v_wantsRebuild_3661_; lean_object* v_trace_3662_; lean_object* v_buildTime_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3671_; 
v_log_3659_ = lean_ctor_get(v_a_3658_, 0);
v_action_3660_ = lean_ctor_get_uint8(v_a_3658_, sizeof(void*)*3);
v_wantsRebuild_3661_ = lean_ctor_get_uint8(v_a_3658_, sizeof(void*)*3 + 1);
v_trace_3662_ = lean_ctor_get(v_a_3658_, 1);
v_buildTime_3663_ = lean_ctor_get(v_a_3658_, 2);
v_isSharedCheck_3671_ = !lean_is_exclusive(v_a_3658_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3665_ = v_a_3658_;
v_isShared_3666_ = v_isSharedCheck_3671_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_buildTime_3663_);
lean_inc(v_trace_3662_);
lean_inc(v_log_3659_);
lean_dec(v_a_3658_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3671_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3667_; lean_object* v___x_3669_; 
v___x_3667_ = l_Array_shrink___redArg(v_log_3659_, v_a_3657_);
lean_dec(v_a_3657_);
if (v_isShared_3666_ == 0)
{
lean_ctor_set(v___x_3665_, 0, v___x_3667_);
v___x_3669_ = v___x_3665_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3670_, 1, v_trace_3662_);
lean_ctor_set(v_reuseFailAlloc_3670_, 2, v_buildTime_3663_);
lean_ctor_set_uint8(v_reuseFailAlloc_3670_, sizeof(void*)*3, v_action_3660_);
lean_ctor_set_uint8(v_reuseFailAlloc_3670_, sizeof(void*)*3 + 1, v_wantsRebuild_3661_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
v___y_3653_ = v___x_3669_;
goto v___jp_3652_;
}
}
}
v___jp_3672_:
{
if (lean_obj_tag(v___y_3673_) == 0)
{
lean_object* v_a_3674_; 
v_a_3674_ = lean_ctor_get(v___y_3673_, 0);
if (lean_obj_tag(v_a_3674_) == 0)
{
lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3683_; 
lean_inc_ref(v_a_3674_);
v_a_3675_ = lean_ctor_get(v___y_3673_, 1);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___y_3673_);
if (v_isSharedCheck_3683_ == 0)
{
lean_object* v_unused_3684_; 
v_unused_3684_ = lean_ctor_get(v___y_3673_, 0);
lean_dec(v_unused_3684_);
v___x_3677_ = v___y_3673_;
v_isShared_3678_ = v_isSharedCheck_3683_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___y_3673_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3683_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v_a_3679_; lean_object* v___x_3681_; 
v_a_3679_ = lean_ctor_get(v_a_3674_, 0);
lean_inc(v_a_3679_);
lean_dec_ref_known(v_a_3674_, 1);
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 0, v_a_3679_);
v___x_3681_ = v___x_3677_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3679_);
lean_ctor_set(v_reuseFailAlloc_3682_, 1, v_a_3675_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
else
{
lean_object* v_a_3685_; 
v_a_3685_ = lean_ctor_get(v___y_3673_, 1);
lean_inc(v_a_3685_);
lean_dec_ref_known(v___y_3673_, 2);
v___y_3653_ = v_a_3685_;
goto v___jp_3652_;
}
}
else
{
lean_object* v_a_3686_; lean_object* v_a_3687_; 
v_a_3686_ = lean_ctor_get(v___y_3673_, 0);
lean_inc(v_a_3686_);
v_a_3687_ = lean_ctor_get(v___y_3673_, 1);
lean_inc(v_a_3687_);
lean_dec_ref_known(v___y_3673_, 2);
v_a_3657_ = v_a_3686_;
v_a_3658_ = v_a_3687_;
goto v___jp_3656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___boxed(lean_object* v_inst_3754_, lean_object* v_inputHash_3755_, lean_object* v_savedTrace_3756_, lean_object* v_pkg_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_){
_start:
{
uint64_t v_inputHash_boxed_3765_; lean_object* v_res_3766_; 
v_inputHash_boxed_3765_ = lean_unbox_uint64(v_inputHash_3755_);
lean_dec_ref(v_inputHash_3755_);
v_res_3766_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3754_, v_inputHash_boxed_3765_, v_savedTrace_3756_, v_pkg_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_);
lean_dec_ref(v_a_3762_);
lean_dec(v_a_3761_);
lean_dec(v_a_3760_);
lean_dec(v_a_3759_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f(lean_object* v_00_u03b1_3767_, lean_object* v_inst_3768_, uint64_t v_inputHash_3769_, lean_object* v_savedTrace_3770_, lean_object* v_pkg_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_){
_start:
{
lean_object* v___x_3779_; 
v___x_3779_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3768_, v_inputHash_3769_, v_savedTrace_3770_, v_pkg_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___boxed(lean_object* v_00_u03b1_3780_, lean_object* v_inst_3781_, lean_object* v_inputHash_3782_, lean_object* v_savedTrace_3783_, lean_object* v_pkg_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_){
_start:
{
uint64_t v_inputHash_boxed_3792_; lean_object* v_res_3793_; 
v_inputHash_boxed_3792_ = lean_unbox_uint64(v_inputHash_3782_);
lean_dec_ref(v_inputHash_3782_);
v_res_3793_ = l_Lake_getArtifactsUsingTrace_x3f(v_00_u03b1_3780_, v_inst_3781_, v_inputHash_boxed_3792_, v_savedTrace_3783_, v_pkg_3784_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_);
lean_dec_ref(v_a_3789_);
lean_dec(v_a_3788_);
lean_dec(v_a_3787_);
lean_dec(v_a_3786_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg(lean_object* v_inst_3794_, uint64_t v_inputHash_3795_, lean_object* v_savedTrace_3796_, lean_object* v_pkg_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_){
_start:
{
lean_object* v_a_3806_; lean_object* v___y_3807_; lean_object* v___x_3810_; lean_object* v_a_3811_; 
lean_inc_ref(v_a_3798_);
lean_inc_ref(v_pkg_3797_);
lean_inc_ref(v_inst_3794_);
v___x_3810_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3794_, v_inputHash_3795_, v_savedTrace_3796_, v_pkg_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
v_a_3811_ = lean_ctor_get(v___x_3810_, 0);
lean_inc(v_a_3811_);
if (lean_obj_tag(v_a_3811_) == 1)
{
lean_object* v_a_3812_; lean_object* v_val_3813_; 
lean_dec_ref(v_a_3798_);
lean_dec_ref(v_pkg_3797_);
lean_dec_ref(v_inst_3794_);
v_a_3812_ = lean_ctor_get(v___x_3810_, 1);
lean_inc(v_a_3812_);
lean_dec_ref(v___x_3810_);
v_val_3813_ = lean_ctor_get(v_a_3811_, 0);
lean_inc(v_val_3813_);
lean_dec_ref_known(v_a_3811_, 1);
v_a_3806_ = v_val_3813_;
v___y_3807_ = v_a_3812_;
goto v___jp_3805_;
}
else
{
lean_object* v_a_3814_; lean_object* v___x_3815_; lean_object* v_a_3816_; 
lean_dec(v_a_3811_);
v_a_3814_ = lean_ctor_get(v___x_3810_, 1);
lean_inc(v_a_3814_);
lean_dec_ref(v___x_3810_);
v___x_3815_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3794_, v_inputHash_3795_, v_pkg_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3814_);
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_a_3816_);
if (lean_obj_tag(v_a_3816_) == 1)
{
lean_object* v_a_3817_; lean_object* v_val_3818_; 
v_a_3817_ = lean_ctor_get(v___x_3815_, 1);
lean_inc(v_a_3817_);
lean_dec_ref(v___x_3815_);
v_val_3818_ = lean_ctor_get(v_a_3816_, 0);
lean_inc(v_val_3818_);
lean_dec_ref_known(v_a_3816_, 1);
v_a_3806_ = v_val_3818_;
v___y_3807_ = v_a_3817_;
goto v___jp_3805_;
}
else
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3827_; 
lean_dec(v_a_3816_);
v_a_3819_ = lean_ctor_get(v___x_3815_, 1);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3827_ == 0)
{
lean_object* v_unused_3828_; 
v_unused_3828_ = lean_ctor_get(v___x_3815_, 0);
lean_dec(v_unused_3828_);
v___x_3821_ = v___x_3815_;
v_isShared_3822_ = v_isSharedCheck_3827_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3815_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3827_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3823_; lean_object* v___x_3825_; 
v___x_3823_ = lean_box(0);
if (v_isShared_3822_ == 0)
{
lean_ctor_set(v___x_3821_, 0, v___x_3823_);
v___x_3825_ = v___x_3821_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3823_);
lean_ctor_set(v_reuseFailAlloc_3826_, 1, v_a_3819_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
v___jp_3805_:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3808_, 0, v_a_3806_);
v___x_3809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3808_);
lean_ctor_set(v___x_3809_, 1, v___y_3807_);
return v___x_3809_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___boxed(lean_object* v_inst_3829_, lean_object* v_inputHash_3830_, lean_object* v_savedTrace_3831_, lean_object* v_pkg_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_){
_start:
{
uint64_t v_inputHash_boxed_3840_; lean_object* v_res_3841_; 
v_inputHash_boxed_3840_ = lean_unbox_uint64(v_inputHash_3830_);
lean_dec_ref(v_inputHash_3830_);
v_res_3841_ = l_Lake_getArtifacts_x3f___redArg(v_inst_3829_, v_inputHash_boxed_3840_, v_savedTrace_3831_, v_pkg_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_);
lean_dec_ref(v_a_3837_);
lean_dec(v_a_3836_);
lean_dec(v_a_3835_);
lean_dec(v_a_3834_);
return v_res_3841_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f(lean_object* v_00_u03b1_3842_, lean_object* v_inst_3843_, uint64_t v_inputHash_3844_, lean_object* v_savedTrace_3845_, lean_object* v_pkg_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_){
_start:
{
lean_object* v_a_3855_; lean_object* v___y_3856_; lean_object* v___x_3859_; lean_object* v_a_3860_; 
lean_inc_ref(v_a_3847_);
lean_inc_ref(v_pkg_3846_);
lean_inc_ref(v_inst_3843_);
v___x_3859_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3843_, v_inputHash_3844_, v_savedTrace_3845_, v_pkg_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_);
v_a_3860_ = lean_ctor_get(v___x_3859_, 0);
lean_inc(v_a_3860_);
if (lean_obj_tag(v_a_3860_) == 1)
{
lean_object* v_a_3861_; lean_object* v_val_3862_; 
lean_dec_ref(v_a_3847_);
lean_dec_ref(v_pkg_3846_);
lean_dec_ref(v_inst_3843_);
v_a_3861_ = lean_ctor_get(v___x_3859_, 1);
lean_inc(v_a_3861_);
lean_dec_ref(v___x_3859_);
v_val_3862_ = lean_ctor_get(v_a_3860_, 0);
lean_inc(v_val_3862_);
lean_dec_ref_known(v_a_3860_, 1);
v_a_3855_ = v_val_3862_;
v___y_3856_ = v_a_3861_;
goto v___jp_3854_;
}
else
{
lean_object* v_a_3863_; lean_object* v___x_3864_; lean_object* v_a_3865_; 
lean_dec(v_a_3860_);
v_a_3863_ = lean_ctor_get(v___x_3859_, 1);
lean_inc(v_a_3863_);
lean_dec_ref(v___x_3859_);
v___x_3864_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3843_, v_inputHash_3844_, v_pkg_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3863_);
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_a_3865_);
if (lean_obj_tag(v_a_3865_) == 1)
{
lean_object* v_a_3866_; lean_object* v_val_3867_; 
v_a_3866_ = lean_ctor_get(v___x_3864_, 1);
lean_inc(v_a_3866_);
lean_dec_ref(v___x_3864_);
v_val_3867_ = lean_ctor_get(v_a_3865_, 0);
lean_inc(v_val_3867_);
lean_dec_ref_known(v_a_3865_, 1);
v_a_3855_ = v_val_3867_;
v___y_3856_ = v_a_3866_;
goto v___jp_3854_;
}
else
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3876_; 
lean_dec(v_a_3865_);
v_a_3868_ = lean_ctor_get(v___x_3864_, 1);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3876_ == 0)
{
lean_object* v_unused_3877_; 
v_unused_3877_ = lean_ctor_get(v___x_3864_, 0);
lean_dec(v_unused_3877_);
v___x_3870_ = v___x_3864_;
v_isShared_3871_ = v_isSharedCheck_3876_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3864_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3876_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3872_; lean_object* v___x_3874_; 
v___x_3872_ = lean_box(0);
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 0, v___x_3872_);
v___x_3874_ = v___x_3870_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v___x_3872_);
lean_ctor_set(v_reuseFailAlloc_3875_, 1, v_a_3868_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
}
v___jp_3854_:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3857_, 0, v_a_3855_);
v___x_3858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3857_);
lean_ctor_set(v___x_3858_, 1, v___y_3856_);
return v___x_3858_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___boxed(lean_object* v_00_u03b1_3878_, lean_object* v_inst_3879_, lean_object* v_inputHash_3880_, lean_object* v_savedTrace_3881_, lean_object* v_pkg_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_){
_start:
{
uint64_t v_inputHash_boxed_3890_; lean_object* v_res_3891_; 
v_inputHash_boxed_3890_ = lean_unbox_uint64(v_inputHash_3880_);
lean_dec_ref(v_inputHash_3880_);
v_res_3891_ = l_Lake_getArtifacts_x3f(v_00_u03b1_3878_, v_inst_3879_, v_inputHash_boxed_3890_, v_savedTrace_3881_, v_pkg_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_);
lean_dec_ref(v_a_3887_);
lean_dec(v_a_3886_);
lean_dec(v_a_3885_);
lean_dec(v_a_3884_);
return v_res_3891_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__0(lean_object* v_descr_3892_, lean_object* v___x_3893_, lean_object* v_mtime_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; 
lean_inc_ref(v___x_3893_);
v___x_3902_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3902_, 0, v_descr_3892_);
lean_ctor_set(v___x_3902_, 1, v___x_3893_);
lean_ctor_set(v___x_3902_, 2, v___x_3893_);
lean_ctor_set(v___x_3902_, 3, v_mtime_3894_);
v___x_3903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3902_);
lean_ctor_set(v___x_3903_, 1, v___y_3900_);
return v___x_3903_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__0___boxed(lean_object* v_descr_3904_, lean_object* v___x_3905_, lean_object* v_mtime_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_){
_start:
{
lean_object* v_res_3914_; 
v_res_3914_ = l_Lake_resolveArtifact___lam__0(v_descr_3904_, v___x_3905_, v_mtime_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_);
lean_dec_ref(v___y_3911_);
lean_dec(v___y_3910_);
lean_dec(v___y_3909_);
lean_dec(v___y_3908_);
lean_dec_ref(v___y_3907_);
return v_res_3914_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__1(lean_object* v___x_3916_, lean_object* v___f_3917_, lean_object* v_____r_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
lean_object* v_log_3926_; uint8_t v_action_3927_; uint8_t v_wantsRebuild_3928_; lean_object* v_trace_3929_; lean_object* v_buildTime_3930_; lean_object* v___x_3931_; 
v_log_3926_ = lean_ctor_get(v___y_3924_, 0);
v_action_3927_ = lean_ctor_get_uint8(v___y_3924_, sizeof(void*)*3);
v_wantsRebuild_3928_ = lean_ctor_get_uint8(v___y_3924_, sizeof(void*)*3 + 1);
v_trace_3929_ = lean_ctor_get(v___y_3924_, 1);
v_buildTime_3930_ = lean_ctor_get(v___y_3924_, 2);
v___x_3931_ = lean_io_metadata(v___x_3916_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3932_; lean_object* v_modified_3933_; lean_object* v___x_3934_; 
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3932_);
lean_dec_ref_known(v___x_3931_, 1);
v_modified_3933_ = lean_ctor_get(v_a_3932_, 1);
lean_inc_ref(v_modified_3933_);
lean_dec(v_a_3932_);
lean_inc_ref(v___y_3923_);
lean_inc(v___y_3922_);
lean_inc(v___y_3921_);
lean_inc(v___y_3920_);
v___x_3934_ = lean_apply_8(v___f_3917_, v_modified_3933_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, lean_box(0));
return v___x_3934_;
}
else
{
lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3950_; 
lean_inc(v_buildTime_3930_);
lean_inc_ref(v_trace_3929_);
lean_inc_ref(v_log_3926_);
lean_dec_ref(v___y_3919_);
lean_dec_ref(v___f_3917_);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___y_3924_);
if (v_isSharedCheck_3950_ == 0)
{
lean_object* v_unused_3951_; lean_object* v_unused_3952_; lean_object* v_unused_3953_; 
v_unused_3951_ = lean_ctor_get(v___y_3924_, 2);
lean_dec(v_unused_3951_);
v_unused_3952_ = lean_ctor_get(v___y_3924_, 1);
lean_dec(v_unused_3952_);
v_unused_3953_ = lean_ctor_get(v___y_3924_, 0);
lean_dec(v_unused_3953_);
v___x_3936_ = v___y_3924_;
v_isShared_3937_ = v_isSharedCheck_3950_;
goto v_resetjp_3935_;
}
else
{
lean_dec(v___y_3924_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3950_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v_a_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; uint8_t v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3947_; 
v_a_3938_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3938_);
lean_dec_ref_known(v___x_3931_, 1);
v___x_3939_ = ((lean_object*)(l_Lake_resolveArtifact___lam__1___closed__0));
v___x_3940_ = lean_io_error_to_string(v_a_3938_);
v___x_3941_ = lean_string_append(v___x_3939_, v___x_3940_);
lean_dec_ref(v___x_3940_);
v___x_3942_ = 3;
v___x_3943_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3943_, 0, v___x_3941_);
lean_ctor_set_uint8(v___x_3943_, sizeof(void*)*1, v___x_3942_);
v___x_3944_ = lean_array_get_size(v_log_3926_);
v___x_3945_ = lean_array_push(v_log_3926_, v___x_3943_);
if (v_isShared_3937_ == 0)
{
lean_ctor_set(v___x_3936_, 0, v___x_3945_);
v___x_3947_ = v___x_3936_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v___x_3945_);
lean_ctor_set(v_reuseFailAlloc_3949_, 1, v_trace_3929_);
lean_ctor_set(v_reuseFailAlloc_3949_, 2, v_buildTime_3930_);
lean_ctor_set_uint8(v_reuseFailAlloc_3949_, sizeof(void*)*3, v_action_3927_);
lean_ctor_set_uint8(v_reuseFailAlloc_3949_, sizeof(void*)*3 + 1, v_wantsRebuild_3928_);
v___x_3947_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
lean_object* v___x_3948_; 
v___x_3948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3948_, 0, v___x_3944_);
lean_ctor_set(v___x_3948_, 1, v___x_3947_);
return v___x_3948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__1___boxed(lean_object* v___x_3954_, lean_object* v___f_3955_, lean_object* v_____r_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v_res_3964_; 
v_res_3964_ = l_Lake_resolveArtifact___lam__1(v___x_3954_, v___f_3955_, v_____r_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
lean_dec_ref(v___y_3961_);
lean_dec(v___y_3960_);
lean_dec(v___y_3959_);
lean_dec(v___y_3958_);
lean_dec_ref(v___x_3954_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact(lean_object* v_descr_3976_, lean_object* v_service_x3f_3977_, lean_object* v_scope_x3f_3978_, uint8_t v_exe_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_){
_start:
{
lean_object* v___y_3988_; lean_object* v_a_3989_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v_toContext_3995_; lean_object* v_log_3996_; uint8_t v_action_3997_; uint8_t v_wantsRebuild_3998_; lean_object* v_trace_3999_; lean_object* v_buildTime_4000_; lean_object* v_lakeConfig_4001_; lean_object* v_lakeCache_4002_; uint64_t v_hash_4003_; lean_object* v_ext_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___y_4008_; lean_object* v___x_4106_; lean_object* v___x_4107_; uint8_t v___x_4108_; 
v_toContext_3995_ = lean_ctor_get(v_a_3984_, 1);
v_log_3996_ = lean_ctor_get(v_a_3985_, 0);
v_action_3997_ = lean_ctor_get_uint8(v_a_3985_, sizeof(void*)*3);
v_wantsRebuild_3998_ = lean_ctor_get_uint8(v_a_3985_, sizeof(void*)*3 + 1);
v_trace_3999_ = lean_ctor_get(v_a_3985_, 1);
v_buildTime_4000_ = lean_ctor_get(v_a_3985_, 2);
v_lakeConfig_4001_ = lean_ctor_get(v_toContext_3995_, 1);
v_lakeCache_4002_ = lean_ctor_get(v_toContext_3995_, 2);
v_hash_4003_ = lean_ctor_get_uint64(v_descr_3976_, sizeof(void*)*1);
v_ext_4004_ = lean_ctor_get(v_descr_3976_, 0);
v___x_4005_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
lean_inc_ref(v_lakeCache_4002_);
v___x_4006_ = l_System_FilePath_join(v_lakeCache_4002_, v___x_4005_);
v___x_4106_ = lean_string_utf8_byte_size(v_ext_4004_);
v___x_4107_ = lean_unsigned_to_nat(0u);
v___x_4108_ = lean_nat_dec_eq(v___x_4106_, v___x_4107_);
if (v___x_4108_ == 0)
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4109_ = l_Lake_lowerHexUInt64(v_hash_4003_);
v___x_4110_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_4111_ = lean_string_append(v___x_4109_, v___x_4110_);
v___x_4112_ = lean_string_append(v___x_4111_, v_ext_4004_);
v___y_4008_ = v___x_4112_;
goto v___jp_4007_;
}
else
{
lean_object* v___x_4113_; 
v___x_4113_ = l_Lake_lowerHexUInt64(v_hash_4003_);
v___y_4008_ = v___x_4113_;
goto v___jp_4007_;
}
v___jp_3987_:
{
lean_object* v___x_3990_; 
v___x_3990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3990_, 0, v___y_3988_);
lean_ctor_set(v___x_3990_, 1, v_a_3989_);
return v___x_3990_;
}
v___jp_3991_:
{
if (lean_obj_tag(v___y_3993_) == 0)
{
lean_dec(v___y_3992_);
return v___y_3993_;
}
else
{
lean_object* v_a_3994_; 
v_a_3994_ = lean_ctor_get(v___y_3993_, 1);
lean_inc(v_a_3994_);
lean_dec_ref_known(v___y_3993_, 2);
v___y_3988_ = v___y_3992_;
v_a_3989_ = v_a_3994_;
goto v___jp_3987_;
}
}
v___jp_4007_:
{
lean_object* v___x_4009_; lean_object* v___f_4010_; lean_object* v___x_4011_; 
v___x_4009_ = l_Lake_joinRelative(v___x_4006_, v___y_4008_);
lean_inc_ref(v___x_4009_);
lean_inc_ref(v_descr_3976_);
v___f_4010_ = lean_alloc_closure((void*)(l_Lake_resolveArtifact___lam__0___boxed), 10, 2);
lean_closure_set(v___f_4010_, 0, v_descr_3976_);
lean_closure_set(v___f_4010_, 1, v___x_4009_);
v___x_4011_ = lean_io_metadata(v___x_4009_);
if (lean_obj_tag(v___x_4011_) == 0)
{
lean_object* v_a_4012_; lean_object* v_modified_4013_; lean_object* v___x_4014_; 
lean_dec_ref(v___f_4010_);
lean_dec(v_scope_x3f_3978_);
lean_dec(v_service_x3f_3977_);
v_a_4012_ = lean_ctor_get(v___x_4011_, 0);
lean_inc(v_a_4012_);
lean_dec_ref_known(v___x_4011_, 1);
v_modified_4013_ = lean_ctor_get(v_a_4012_, 1);
lean_inc_ref(v_modified_4013_);
lean_dec(v_a_4012_);
v___x_4014_ = l_Lake_resolveArtifact___lam__0(v_descr_3976_, v___x_4009_, v_modified_4013_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
lean_dec_ref(v_a_3980_);
return v___x_4014_;
}
else
{
lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4102_; 
lean_inc(v_buildTime_4000_);
lean_inc_ref(v_trace_3999_);
lean_inc_ref(v_log_3996_);
lean_dec_ref(v_descr_3976_);
v_isSharedCheck_4102_ = !lean_is_exclusive(v_a_3985_);
if (v_isSharedCheck_4102_ == 0)
{
lean_object* v_unused_4103_; lean_object* v_unused_4104_; lean_object* v_unused_4105_; 
v_unused_4103_ = lean_ctor_get(v_a_3985_, 2);
lean_dec(v_unused_4103_);
v_unused_4104_ = lean_ctor_get(v_a_3985_, 1);
lean_dec(v_unused_4104_);
v_unused_4105_ = lean_ctor_get(v_a_3985_, 0);
lean_dec(v_unused_4105_);
v___x_4016_ = v_a_3985_;
v_isShared_4017_ = v_isSharedCheck_4102_;
goto v_resetjp_4015_;
}
else
{
lean_dec(v_a_3985_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4102_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v_a_4018_; 
v_a_4018_ = lean_ctor_get(v___x_4011_, 0);
lean_inc(v_a_4018_);
lean_dec_ref_known(v___x_4011_, 1);
if (lean_obj_tag(v_a_4018_) == 11)
{
lean_object* v___x_4019_; 
lean_dec_ref_known(v_a_4018_, 2);
v___x_4019_ = lean_array_get_size(v_log_3996_);
if (lean_obj_tag(v_service_x3f_3977_) == 1)
{
lean_object* v_val_4020_; lean_object* v_cacheServices_4021_; uint8_t v___x_4022_; uint8_t v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v_val_4020_ = lean_ctor_get(v_service_x3f_3977_, 0);
lean_inc_n(v_val_4020_, 2);
lean_dec_ref_known(v_service_x3f_3977_, 1);
v_cacheServices_4021_ = lean_ctor_get(v_lakeConfig_4001_, 3);
v___x_4022_ = 4;
v___x_4023_ = l_Lake_JobAction_merge(v_action_3997_, v___x_4022_);
v___x_4024_ = lean_box(0);
v___x_4025_ = l_Lean_Name_str___override(v___x_4024_, v_val_4020_);
v___x_4026_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_cacheServices_4021_, v___x_4025_);
lean_dec(v___x_4025_);
if (lean_obj_tag(v___x_4026_) == 1)
{
lean_dec(v_val_4020_);
if (lean_obj_tag(v_scope_x3f_3978_) == 1)
{
lean_object* v_val_4027_; lean_object* v_val_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; uint8_t v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v_val_4027_ = lean_ctor_get(v___x_4026_, 0);
lean_inc(v_val_4027_);
lean_dec_ref_known(v___x_4026_, 1);
v_val_4028_ = lean_ctor_get(v_scope_x3f_3978_, 0);
lean_inc(v_val_4028_);
lean_dec_ref_known(v_scope_x3f_3978_, 1);
v___x_4029_ = l_Lake_CacheService_artifactUrl(v_hash_4003_, v_val_4027_, v_val_4028_);
v___x_4030_ = ((lean_object*)(l_Lake_resolveArtifact___closed__0));
v___x_4031_ = l_Lake_lowerHexUInt64(v_hash_4003_);
v___x_4032_ = lean_string_append(v___x_4030_, v___x_4031_);
lean_dec_ref(v___x_4031_);
v___x_4033_ = ((lean_object*)(l_Lake_resolveArtifact___closed__1));
v___x_4034_ = lean_string_append(v___x_4032_, v___x_4033_);
v___x_4035_ = lean_string_append(v___x_4034_, v___x_4009_);
v___x_4036_ = ((lean_object*)(l_Lake_resolveArtifact___closed__2));
v___x_4037_ = lean_string_append(v___x_4035_, v___x_4036_);
v___x_4038_ = lean_string_append(v___x_4037_, v___x_4029_);
v___x_4039_ = 0;
v___x_4040_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4040_, 0, v___x_4038_);
lean_ctor_set_uint8(v___x_4040_, sizeof(void*)*1, v___x_4039_);
v___x_4041_ = lean_array_push(v_log_3996_, v___x_4040_);
lean_inc_ref(v___x_4009_);
v___x_4042_ = l_Lake_downloadArtifactCore(v_hash_4003_, v___x_4029_, v___x_4009_, v___x_4041_);
if (lean_obj_tag(v___x_4042_) == 0)
{
lean_object* v_a_4043_; uint8_t v___x_4044_; uint8_t v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; 
v_a_4043_ = lean_ctor_get(v___x_4042_, 1);
lean_inc(v_a_4043_);
lean_dec_ref_known(v___x_4042_, 2);
v___x_4044_ = 1;
v___x_4045_ = 0;
v___x_4046_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4046_, 0, v___x_4044_);
lean_ctor_set_uint8(v___x_4046_, 1, v___x_4045_);
lean_ctor_set_uint8(v___x_4046_, 2, v_exe_3979_);
lean_inc_ref_n(v___x_4046_, 2);
v___x_4047_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4046_);
lean_ctor_set(v___x_4047_, 1, v___x_4046_);
lean_ctor_set(v___x_4047_, 2, v___x_4046_);
v___x_4048_ = l_IO_setAccessRights(v___x_4009_, v___x_4047_);
lean_dec_ref_known(v___x_4047_, 3);
if (lean_obj_tag(v___x_4048_) == 0)
{
lean_object* v___x_4050_; 
lean_dec_ref_known(v___x_4048_, 1);
if (v_isShared_4017_ == 0)
{
lean_ctor_set(v___x_4016_, 0, v_a_4043_);
v___x_4050_ = v___x_4016_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_a_4043_);
lean_ctor_set(v_reuseFailAlloc_4053_, 1, v_trace_3999_);
lean_ctor_set(v_reuseFailAlloc_4053_, 2, v_buildTime_4000_);
lean_ctor_set_uint8(v_reuseFailAlloc_4053_, sizeof(void*)*3 + 1, v_wantsRebuild_3998_);
v___x_4050_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; 
lean_ctor_set_uint8(v___x_4050_, sizeof(void*)*3, v___x_4023_);
v___x_4051_ = lean_box(0);
v___x_4052_ = l_Lake_resolveArtifact___lam__1(v___x_4009_, v___f_4010_, v___x_4051_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v___x_4050_);
lean_dec_ref(v___x_4009_);
v___y_3992_ = v___x_4019_;
v___y_3993_ = v___x_4052_;
goto v___jp_3991_;
}
}
else
{
lean_object* v_a_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; uint8_t v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4063_; 
v_a_4054_ = lean_ctor_get(v___x_4048_, 0);
lean_inc(v_a_4054_);
lean_dec_ref_known(v___x_4048_, 1);
v___x_4055_ = ((lean_object*)(l_Lake_resolveArtifact___closed__3));
v___x_4056_ = lean_io_error_to_string(v_a_4054_);
v___x_4057_ = lean_string_append(v___x_4055_, v___x_4056_);
lean_dec_ref(v___x_4056_);
v___x_4058_ = 2;
v___x_4059_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4059_, 0, v___x_4057_);
lean_ctor_set_uint8(v___x_4059_, sizeof(void*)*1, v___x_4058_);
v___x_4060_ = lean_box(0);
v___x_4061_ = lean_array_push(v_a_4043_, v___x_4059_);
if (v_isShared_4017_ == 0)
{
lean_ctor_set(v___x_4016_, 0, v___x_4061_);
v___x_4063_ = v___x_4016_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v___x_4061_);
lean_ctor_set(v_reuseFailAlloc_4065_, 1, v_trace_3999_);
lean_ctor_set(v_reuseFailAlloc_4065_, 2, v_buildTime_4000_);
lean_ctor_set_uint8(v_reuseFailAlloc_4065_, sizeof(void*)*3 + 1, v_wantsRebuild_3998_);
v___x_4063_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
lean_object* v___x_4064_; 
lean_ctor_set_uint8(v___x_4063_, sizeof(void*)*3, v___x_4023_);
v___x_4064_ = l_Lake_resolveArtifact___lam__1(v___x_4009_, v___f_4010_, v___x_4060_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v___x_4063_);
lean_dec_ref(v___x_4009_);
v___y_3992_ = v___x_4019_;
v___y_3993_ = v___x_4064_;
goto v___jp_3991_;
}
}
}
else
{
lean_object* v_a_4066_; lean_object* v___x_4068_; 
lean_dec_ref(v___f_4010_);
lean_dec_ref(v___x_4009_);
lean_dec_ref(v_a_3980_);
v_a_4066_ = lean_ctor_get(v___x_4042_, 1);
lean_inc(v_a_4066_);
lean_dec_ref_known(v___x_4042_, 2);
if (v_isShared_4017_ == 0)
{
lean_ctor_set(v___x_4016_, 0, v_a_4066_);
v___x_4068_ = v___x_4016_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_a_4066_);
lean_ctor_set(v_reuseFailAlloc_4069_, 1, v_trace_3999_);
lean_ctor_set(v_reuseFailAlloc_4069_, 2, v_buildTime_4000_);
lean_ctor_set_uint8(v_reuseFailAlloc_4069_, sizeof(void*)*3 + 1, v_wantsRebuild_3998_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
lean_ctor_set_uint8(v___x_4068_, sizeof(void*)*3, v___x_4023_);
v___y_3988_ = v___x_4019_;
v_a_3989_ = v___x_4068_;
goto v___jp_3987_;
}
}
}
else
{
lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4073_; 
lean_dec_ref_known(v___x_4026_, 1);
lean_dec_ref(v___f_4010_);
lean_dec_ref(v___x_4009_);
lean_dec_ref(v_a_3980_);
lean_dec(v_scope_x3f_3978_);
v___x_4070_ = ((lean_object*)(l_Lake_resolveArtifact___closed__5));
v___x_4071_ = lean_array_push(v_log_3996_, v___x_4070_);
if (v_isShared_4017_ == 0)
{
lean_ctor_set(v___x_4016_, 0, v___x_4071_);
v___x_4073_ = v___x_4016_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v___x_4071_);
lean_ctor_set(v_reuseFailAlloc_4074_, 1, v_trace_3999_);
lean_ctor_set(v_reuseFailAlloc_4074_, 2, v_buildTime_4000_);
lean_ctor_set_uint8(v_reuseFailAlloc_4074_, sizeof(void*)*3 + 1, v_wantsRebuild_3998_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
lean_ctor_set_uint8(v___x_4073_, sizeof(void*)*3, v___x_4023_);
v___y_3988_ = v___x_4019_;
v_a_3989_ = v___x_4073_;
goto v___jp_3987_;
}
}
}
else
{
lean_object* v___x_4075_; lean_object* v___x_4076_; uint8_t v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4081_; 
lean_dec(v___x_4026_);
lean_dec_ref(v___f_4010_);
lean_dec_ref(v___x_4009_);
lean_dec_ref(v_a_3980_);
lean_dec(v_scope_x3f_3978_);
v___x_4075_ = ((lean_object*)(l_Lake_resolveArtifact___closed__6));
v___x_4076_ = lean_string_append(v___x_4075_, v_val_4020_);
lean_dec(v_val_4020_);
v___x_4077_ = 3;
v___x_4078_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4078_, 0, v___x_4076_);
lean_ctor_set_uint8(v___x_4078_, sizeof(void*)*1, v___x_4077_);
v___x_4079_ = lean_array_push(v_log_3996_, v___x_4078_);
if (v_isShared_4017_ == 0)
{
lean_ctor_set(v___x_4016_, 0, v___x_4079_);
v___x_4081_ = v___x_4016_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v___x_4079_);
lean_ctor_set(v_reuseFailAlloc_4082_, 1, v_trace_3999_);
lean_ctor_set(v_reuseFailAlloc_4082_, 2, v_buildTime_4000_);
lean_ctor_set_uint8(v_reuseFailAlloc_4082_, sizeof(void*)*3 + 1, v_wantsRebuild_3998_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
lean_ctor_set_uint8(v___x_4081_, sizeof(void*)*3, v___x_4023_);
v___y_3988_ = v___x_4019_;
v_a_3989_ = v___x_4081_;
goto v___jp_3987_;
}
}
}
else
{
lean_object* v___x_4083_; lean_object* v___x_4084_; uint8_t v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4089_; 
lean_dec_ref(v___f_4010_);
lean_dec_ref(v_a_3980_);
lean_dec(v_scope_x3f_3978_);
lean_dec(v_service_x3f_3977_);
v___x_4083_ = ((lean_object*)(l_Lake_resolveArtifact___closed__7));
v___x_4084_ = lean_string_append(v___x_4083_, v___x_4009_);
lean_dec_ref(v___x_4009_);
v___x_4085_ = 3;
v___x_4086_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4086_, 0, v___x_4084_);
lean_ctor_set_uint8(v___x_4086_, sizeof(void*)*1, v___x_4085_);
v___x_4087_ = lean_array_push(v_log_3996_, v___x_4086_);
if (v_isShared_4017_ == 0)
{
lean_ctor_set(v___x_4016_, 0, v___x_4087_);
v___x_4089_ = v___x_4016_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v___x_4087_);
lean_ctor_set(v_reuseFailAlloc_4090_, 1, v_trace_3999_);
lean_ctor_set(v_reuseFailAlloc_4090_, 2, v_buildTime_4000_);
lean_ctor_set_uint8(v_reuseFailAlloc_4090_, sizeof(void*)*3, v_action_3997_);
lean_ctor_set_uint8(v_reuseFailAlloc_4090_, sizeof(void*)*3 + 1, v_wantsRebuild_3998_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
v___y_3988_ = v___x_4019_;
v_a_3989_ = v___x_4089_;
goto v___jp_3987_;
}
}
}
else
{
lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; uint8_t v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4099_; 
lean_dec_ref(v___f_4010_);
lean_dec_ref(v___x_4009_);
lean_dec_ref(v_a_3980_);
lean_dec(v_scope_x3f_3978_);
lean_dec(v_service_x3f_3977_);
v___x_4091_ = ((lean_object*)(l_Lake_resolveArtifact___closed__8));
v___x_4092_ = lean_io_error_to_string(v_a_4018_);
v___x_4093_ = lean_string_append(v___x_4091_, v___x_4092_);
lean_dec_ref(v___x_4092_);
v___x_4094_ = 3;
v___x_4095_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4095_, 0, v___x_4093_);
lean_ctor_set_uint8(v___x_4095_, sizeof(void*)*1, v___x_4094_);
v___x_4096_ = lean_array_get_size(v_log_3996_);
v___x_4097_ = lean_array_push(v_log_3996_, v___x_4095_);
if (v_isShared_4017_ == 0)
{
lean_ctor_set(v___x_4016_, 0, v___x_4097_);
v___x_4099_ = v___x_4016_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v___x_4097_);
lean_ctor_set(v_reuseFailAlloc_4101_, 1, v_trace_3999_);
lean_ctor_set(v_reuseFailAlloc_4101_, 2, v_buildTime_4000_);
lean_ctor_set_uint8(v_reuseFailAlloc_4101_, sizeof(void*)*3, v_action_3997_);
lean_ctor_set_uint8(v_reuseFailAlloc_4101_, sizeof(void*)*3 + 1, v_wantsRebuild_3998_);
v___x_4099_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
lean_object* v___x_4100_; 
v___x_4100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4096_);
lean_ctor_set(v___x_4100_, 1, v___x_4099_);
return v___x_4100_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___boxed(lean_object* v_descr_4114_, lean_object* v_service_x3f_4115_, lean_object* v_scope_x3f_4116_, lean_object* v_exe_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_){
_start:
{
uint8_t v_exe_boxed_4125_; lean_object* v_res_4126_; 
v_exe_boxed_4125_ = lean_unbox(v_exe_4117_);
v_res_4126_ = l_Lake_resolveArtifact(v_descr_4114_, v_service_x3f_4115_, v_scope_x3f_4116_, v_exe_boxed_4125_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_);
lean_dec_ref(v_a_4122_);
lean_dec(v_a_4121_);
lean_dec(v_a_4120_);
lean_dec(v_a_4119_);
return v_res_4126_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput(lean_object* v_out_4129_, uint8_t v_exe_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_){
_start:
{
lean_object* v_data_4138_; lean_object* v_service_x3f_4139_; lean_object* v_scope_x3f_4140_; lean_object* v___x_4141_; 
v_data_4138_ = lean_ctor_get(v_out_4129_, 0);
lean_inc_n(v_data_4138_, 2);
v_service_x3f_4139_ = lean_ctor_get(v_out_4129_, 1);
lean_inc(v_service_x3f_4139_);
v_scope_x3f_4140_ = lean_ctor_get(v_out_4129_, 2);
lean_inc(v_scope_x3f_4140_);
lean_dec_ref(v_out_4129_);
v___x_4141_ = l_Lake_ArtifactDescr_fromJson_x3f(v_data_4138_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v_a_4142_; lean_object* v_log_4143_; uint8_t v_action_4144_; uint8_t v_wantsRebuild_4145_; lean_object* v_trace_4146_; lean_object* v_buildTime_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4169_; 
lean_dec(v_scope_x3f_4140_);
lean_dec(v_service_x3f_4139_);
lean_dec_ref(v_a_4131_);
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_a_4142_);
lean_dec_ref_known(v___x_4141_, 1);
v_log_4143_ = lean_ctor_get(v_a_4136_, 0);
v_action_4144_ = lean_ctor_get_uint8(v_a_4136_, sizeof(void*)*3);
v_wantsRebuild_4145_ = lean_ctor_get_uint8(v_a_4136_, sizeof(void*)*3 + 1);
v_trace_4146_ = lean_ctor_get(v_a_4136_, 1);
v_buildTime_4147_ = lean_ctor_get(v_a_4136_, 2);
v_isSharedCheck_4169_ = !lean_is_exclusive(v_a_4136_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_4149_ = v_a_4136_;
v_isShared_4150_ = v_isSharedCheck_4169_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_buildTime_4147_);
lean_inc(v_trace_4146_);
lean_inc(v_log_4143_);
lean_dec(v_a_4136_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4169_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; uint8_t v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4166_; 
v___x_4151_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__0));
v___x_4152_ = l_Lean_Json_render(v_data_4138_);
v___x_4153_ = lean_unsigned_to_nat(80u);
v___x_4154_ = lean_unsigned_to_nat(2u);
v___x_4155_ = lean_unsigned_to_nat(0u);
v___x_4156_ = l_Std_Format_pretty(v___x_4152_, v___x_4153_, v___x_4154_, v___x_4155_);
v___x_4157_ = lean_string_append(v___x_4151_, v___x_4156_);
lean_dec_ref(v___x_4156_);
v___x_4158_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__1));
v___x_4159_ = lean_string_append(v___x_4157_, v___x_4158_);
v___x_4160_ = lean_string_append(v___x_4159_, v_a_4142_);
lean_dec(v_a_4142_);
v___x_4161_ = 3;
v___x_4162_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4162_, 0, v___x_4160_);
lean_ctor_set_uint8(v___x_4162_, sizeof(void*)*1, v___x_4161_);
v___x_4163_ = lean_array_get_size(v_log_4143_);
v___x_4164_ = lean_array_push(v_log_4143_, v___x_4162_);
if (v_isShared_4150_ == 0)
{
lean_ctor_set(v___x_4149_, 0, v___x_4164_);
v___x_4166_ = v___x_4149_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v___x_4164_);
lean_ctor_set(v_reuseFailAlloc_4168_, 1, v_trace_4146_);
lean_ctor_set(v_reuseFailAlloc_4168_, 2, v_buildTime_4147_);
lean_ctor_set_uint8(v_reuseFailAlloc_4168_, sizeof(void*)*3, v_action_4144_);
lean_ctor_set_uint8(v_reuseFailAlloc_4168_, sizeof(void*)*3 + 1, v_wantsRebuild_4145_);
v___x_4166_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
lean_object* v___x_4167_; 
v___x_4167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4163_);
lean_ctor_set(v___x_4167_, 1, v___x_4166_);
return v___x_4167_;
}
}
}
else
{
lean_object* v_a_4170_; lean_object* v___x_4171_; 
lean_dec(v_data_4138_);
v_a_4170_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_a_4170_);
lean_dec_ref_known(v___x_4141_, 1);
v___x_4171_ = l_Lake_resolveArtifact(v_a_4170_, v_service_x3f_4139_, v_scope_x3f_4140_, v_exe_4130_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_);
return v___x_4171_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput___boxed(lean_object* v_out_4172_, lean_object* v_exe_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_){
_start:
{
uint8_t v_exe_boxed_4181_; lean_object* v_res_4182_; 
v_exe_boxed_4181_ = lean_unbox(v_exe_4173_);
v_res_4182_ = l_Lake_resolveArtifactOutput(v_out_4172_, v_exe_boxed_4181_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_);
lean_dec_ref(v_a_4178_);
lean_dec(v_a_4177_);
lean_dec(v_a_4176_);
lean_dec(v_a_4175_);
return v_res_4182_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(uint8_t v_exe_4183_, lean_object* v_out_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
lean_object* v___x_4192_; 
v___x_4192_ = l_Lake_resolveArtifactOutput(v_out_4184_, v_exe_4183_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed(lean_object* v_exe_4193_, lean_object* v_out_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_){
_start:
{
uint8_t v_exe_boxed_4202_; lean_object* v_res_4203_; 
v_exe_boxed_4202_ = lean_unbox(v_exe_4193_);
v_res_4203_ = l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(v_exe_boxed_4202_, v_out_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
lean_dec_ref(v___y_4199_);
lean_dec(v___y_4198_);
lean_dec(v___y_4197_);
lean_dec(v___y_4196_);
return v_res_4203_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(uint8_t v_exe_4204_){
_start:
{
lean_object* v___x_4205_; lean_object* v___f_4206_; 
v___x_4205_ = lean_box(v_exe_4204_);
v___f_4206_ = lean_alloc_closure((void*)(l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4206_, 0, v___x_4205_);
return v___f_4206_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___boxed(lean_object* v_exe_4207_){
_start:
{
uint8_t v_exe_boxed_4208_; lean_object* v_res_4209_; 
v_exe_boxed_4208_ = lean_unbox(v_exe_4207_);
v_res_4209_ = l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(v_exe_boxed_4208_);
return v_res_4209_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg(lean_object* v_path_4210_, lean_object* v_ext_4211_, uint8_t v_text_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_){
_start:
{
lean_object* v___x_4216_; 
lean_inc_ref(v_path_4210_);
v___x_4216_ = l_Lake_fetchFileHash___redArg(v_path_4210_, v_text_4212_, v_a_4213_, v_a_4214_);
if (lean_obj_tag(v___x_4216_) == 0)
{
lean_object* v_a_4217_; lean_object* v_a_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4235_; 
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
v_a_4218_ = lean_ctor_get(v___x_4216_, 1);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4220_ = v___x_4216_;
v_isShared_4221_ = v_isSharedCheck_4235_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_a_4218_);
lean_inc(v_a_4217_);
lean_dec(v___x_4216_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4235_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___x_4231_; 
v___x_4231_ = lean_io_metadata(v_path_4210_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v_a_4232_; lean_object* v_modified_4233_; 
v_a_4232_ = lean_ctor_get(v___x_4231_, 0);
lean_inc(v_a_4232_);
lean_dec_ref_known(v___x_4231_, 1);
v_modified_4233_ = lean_ctor_get(v_a_4232_, 1);
lean_inc_ref(v_modified_4233_);
lean_dec(v_a_4232_);
v___y_4223_ = v_a_4218_;
v___y_4224_ = v_modified_4233_;
goto v___jp_4222_;
}
else
{
lean_object* v___x_4234_; 
lean_dec_ref_known(v___x_4231_, 1);
v___x_4234_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___y_4223_ = v_a_4218_;
v___y_4224_ = v___x_4234_;
goto v___jp_4222_;
}
v___jp_4222_:
{
lean_object* v___x_4225_; uint64_t v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4229_; 
v___x_4225_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4225_, 0, v_ext_4211_);
v___x_4226_ = lean_unbox_uint64(v_a_4217_);
lean_dec(v_a_4217_);
lean_ctor_set_uint64(v___x_4225_, sizeof(void*)*1, v___x_4226_);
lean_inc_ref(v_path_4210_);
v___x_4227_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4227_, 0, v___x_4225_);
lean_ctor_set(v___x_4227_, 1, v_path_4210_);
lean_ctor_set(v___x_4227_, 2, v_path_4210_);
lean_ctor_set(v___x_4227_, 3, v___y_4224_);
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 1, v___y_4223_);
lean_ctor_set(v___x_4220_, 0, v___x_4227_);
v___x_4229_ = v___x_4220_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v___x_4227_);
lean_ctor_set(v_reuseFailAlloc_4230_, 1, v___y_4223_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
}
else
{
lean_object* v_a_4236_; lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4244_; 
lean_dec_ref(v_ext_4211_);
lean_dec_ref(v_path_4210_);
v_a_4236_ = lean_ctor_get(v___x_4216_, 0);
v_a_4237_ = lean_ctor_get(v___x_4216_, 1);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4239_ = v___x_4216_;
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_inc(v_a_4236_);
lean_dec(v___x_4216_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4242_; 
if (v_isShared_4240_ == 0)
{
v___x_4242_ = v___x_4239_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_a_4236_);
lean_ctor_set(v_reuseFailAlloc_4243_, 1, v_a_4237_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg___boxed(lean_object* v_path_4245_, lean_object* v_ext_4246_, lean_object* v_text_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_){
_start:
{
uint8_t v_text_boxed_4251_; lean_object* v_res_4252_; 
v_text_boxed_4251_ = lean_unbox(v_text_4247_);
v_res_4252_ = l_Lake_computeArtifact___redArg(v_path_4245_, v_ext_4246_, v_text_boxed_4251_, v_a_4248_, v_a_4249_);
lean_dec_ref(v_a_4248_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact(lean_object* v_path_4253_, lean_object* v_ext_4254_, uint8_t v_text_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_){
_start:
{
lean_object* v___x_4263_; 
v___x_4263_ = l_Lake_computeArtifact___redArg(v_path_4253_, v_ext_4254_, v_text_4255_, v_a_4260_, v_a_4261_);
return v___x_4263_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___boxed(lean_object* v_path_4264_, lean_object* v_ext_4265_, lean_object* v_text_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_){
_start:
{
uint8_t v_text_boxed_4274_; lean_object* v_res_4275_; 
v_text_boxed_4274_ = lean_unbox(v_text_4266_);
v_res_4275_ = l_Lake_computeArtifact(v_path_4264_, v_ext_4265_, v_text_boxed_4274_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
lean_dec_ref(v_a_4271_);
lean_dec(v_a_4270_);
lean_dec(v_a_4269_);
lean_dec(v_a_4268_);
lean_dec_ref(v_a_4267_);
return v_res_4275_;
}
}
LEAN_EXPORT lean_object* l_Lake_restoreArtifact(lean_object* v_file_4279_, lean_object* v_art_4280_, uint8_t v_exe_4281_, lean_object* v_a_4282_){
_start:
{
lean_object* v___y_4285_; lean_object* v___y_4299_; uint8_t v___x_4315_; 
v___x_4315_ = l_System_FilePath_pathExists(v_file_4279_);
if (v___x_4315_ == 0)
{
lean_object* v_path_4316_; uint8_t v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; uint8_t v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; 
v_path_4316_ = lean_ctor_get(v_art_4280_, 1);
v___x_4317_ = 1;
v___x_4318_ = ((lean_object*)(l_Lake_restoreArtifact___closed__1));
v___x_4319_ = lean_string_append(v___x_4318_, v_path_4316_);
v___x_4320_ = 0;
v___x_4321_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4321_, 0, v___x_4319_);
lean_ctor_set_uint8(v___x_4321_, sizeof(void*)*1, v___x_4320_);
v___x_4322_ = lean_array_push(v_a_4282_, v___x_4321_);
lean_inc_ref(v_file_4279_);
v___x_4323_ = l_Lake_createParentDirs(v_file_4279_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v___x_4324_; 
lean_dec_ref_known(v___x_4323_, 1);
v___x_4324_ = lean_io_hard_link(v_path_4316_, v_file_4279_);
if (lean_obj_tag(v___x_4324_) == 0)
{
lean_dec_ref_known(v___x_4324_, 1);
if (v_exe_4281_ == 0)
{
v___y_4299_ = v___x_4322_;
goto v___jp_4298_;
}
else
{
lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; 
v___x_4325_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4325_, 0, v___x_4317_);
lean_ctor_set_uint8(v___x_4325_, 1, v___x_4315_);
lean_ctor_set_uint8(v___x_4325_, 2, v_exe_4281_);
lean_inc_ref_n(v___x_4325_, 2);
v___x_4326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4326_, 0, v___x_4325_);
lean_ctor_set(v___x_4326_, 1, v___x_4325_);
lean_ctor_set(v___x_4326_, 2, v___x_4325_);
v___x_4327_ = l_IO_setAccessRights(v_file_4279_, v___x_4326_);
lean_dec_ref_known(v___x_4326_, 3);
if (lean_obj_tag(v___x_4327_) == 0)
{
lean_dec_ref_known(v___x_4327_, 1);
v___y_4299_ = v___x_4322_;
goto v___jp_4298_;
}
else
{
lean_object* v_a_4328_; lean_object* v___x_4329_; uint8_t v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; 
lean_dec_ref(v_art_4280_);
lean_dec_ref(v_file_4279_);
v_a_4328_ = lean_ctor_get(v___x_4327_, 0);
lean_inc(v_a_4328_);
lean_dec_ref_known(v___x_4327_, 1);
v___x_4329_ = lean_io_error_to_string(v_a_4328_);
v___x_4330_ = 3;
v___x_4331_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4331_, 0, v___x_4329_);
lean_ctor_set_uint8(v___x_4331_, sizeof(void*)*1, v___x_4330_);
v___x_4332_ = lean_array_get_size(v___x_4322_);
v___x_4333_ = lean_array_push(v___x_4322_, v___x_4331_);
v___x_4334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4332_);
lean_ctor_set(v___x_4334_, 1, v___x_4333_);
return v___x_4334_;
}
}
}
else
{
lean_object* v_a_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; 
v_a_4335_ = lean_ctor_get(v___x_4324_, 0);
lean_inc(v_a_4335_);
lean_dec_ref_known(v___x_4324_, 1);
v___x_4336_ = ((lean_object*)(l_Lake_restoreArtifact___closed__2));
v___x_4337_ = lean_io_error_to_string(v_a_4335_);
v___x_4338_ = lean_string_append(v___x_4336_, v___x_4337_);
lean_dec_ref(v___x_4337_);
v___x_4339_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4339_, 0, v___x_4338_);
lean_ctor_set_uint8(v___x_4339_, sizeof(void*)*1, v___x_4320_);
v___x_4340_ = lean_array_push(v___x_4322_, v___x_4339_);
v___x_4341_ = l_Lake_copyFile(v_path_4316_, v_file_4279_);
if (lean_obj_tag(v___x_4341_) == 0)
{
lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; 
lean_dec_ref_known(v___x_4341_, 1);
v___x_4342_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4342_, 0, v___x_4317_);
lean_ctor_set_uint8(v___x_4342_, 1, v___x_4315_);
lean_ctor_set_uint8(v___x_4342_, 2, v_exe_4281_);
lean_inc_ref_n(v___x_4342_, 2);
v___x_4343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4343_, 0, v___x_4342_);
lean_ctor_set(v___x_4343_, 1, v___x_4342_);
lean_ctor_set(v___x_4343_, 2, v___x_4342_);
v___x_4344_ = l_IO_setAccessRights(v_file_4279_, v___x_4343_);
lean_dec_ref_known(v___x_4343_, 3);
if (lean_obj_tag(v___x_4344_) == 0)
{
lean_dec_ref_known(v___x_4344_, 1);
v___y_4299_ = v___x_4340_;
goto v___jp_4298_;
}
else
{
lean_object* v_a_4345_; lean_object* v___x_4346_; uint8_t v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; 
lean_dec_ref(v_art_4280_);
lean_dec_ref(v_file_4279_);
v_a_4345_ = lean_ctor_get(v___x_4344_, 0);
lean_inc(v_a_4345_);
lean_dec_ref_known(v___x_4344_, 1);
v___x_4346_ = lean_io_error_to_string(v_a_4345_);
v___x_4347_ = 3;
v___x_4348_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4348_, 0, v___x_4346_);
lean_ctor_set_uint8(v___x_4348_, sizeof(void*)*1, v___x_4347_);
v___x_4349_ = lean_array_get_size(v___x_4340_);
v___x_4350_ = lean_array_push(v___x_4340_, v___x_4348_);
v___x_4351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4351_, 0, v___x_4349_);
lean_ctor_set(v___x_4351_, 1, v___x_4350_);
return v___x_4351_;
}
}
else
{
lean_object* v_a_4352_; lean_object* v___x_4353_; uint8_t v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; 
lean_dec_ref(v_art_4280_);
lean_dec_ref(v_file_4279_);
v_a_4352_ = lean_ctor_get(v___x_4341_, 0);
lean_inc(v_a_4352_);
lean_dec_ref_known(v___x_4341_, 1);
v___x_4353_ = lean_io_error_to_string(v_a_4352_);
v___x_4354_ = 3;
v___x_4355_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4355_, 0, v___x_4353_);
lean_ctor_set_uint8(v___x_4355_, sizeof(void*)*1, v___x_4354_);
v___x_4356_ = lean_array_get_size(v___x_4340_);
v___x_4357_ = lean_array_push(v___x_4340_, v___x_4355_);
v___x_4358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4358_, 0, v___x_4356_);
lean_ctor_set(v___x_4358_, 1, v___x_4357_);
return v___x_4358_;
}
}
}
else
{
lean_object* v_a_4359_; lean_object* v___x_4360_; uint8_t v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
lean_dec_ref(v_art_4280_);
lean_dec_ref(v_file_4279_);
v_a_4359_ = lean_ctor_get(v___x_4323_, 0);
lean_inc(v_a_4359_);
lean_dec_ref_known(v___x_4323_, 1);
v___x_4360_ = lean_io_error_to_string(v_a_4359_);
v___x_4361_ = 3;
v___x_4362_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4362_, 0, v___x_4360_);
lean_ctor_set_uint8(v___x_4362_, sizeof(void*)*1, v___x_4361_);
v___x_4363_ = lean_array_get_size(v___x_4322_);
v___x_4364_ = lean_array_push(v___x_4322_, v___x_4362_);
v___x_4365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4365_, 0, v___x_4363_);
lean_ctor_set(v___x_4365_, 1, v___x_4364_);
return v___x_4365_;
}
}
else
{
v___y_4285_ = v_a_4282_;
goto v___jp_4284_;
}
v___jp_4284_:
{
lean_object* v_descr_4286_; lean_object* v_mtime_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4295_; 
v_descr_4286_ = lean_ctor_get(v_art_4280_, 0);
v_mtime_4287_ = lean_ctor_get(v_art_4280_, 3);
v_isSharedCheck_4295_ = !lean_is_exclusive(v_art_4280_);
if (v_isSharedCheck_4295_ == 0)
{
lean_object* v_unused_4296_; lean_object* v_unused_4297_; 
v_unused_4296_ = lean_ctor_get(v_art_4280_, 2);
lean_dec(v_unused_4296_);
v_unused_4297_ = lean_ctor_get(v_art_4280_, 1);
lean_dec(v_unused_4297_);
v___x_4289_ = v_art_4280_;
v_isShared_4290_ = v_isSharedCheck_4295_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_mtime_4287_);
lean_inc(v_descr_4286_);
lean_dec(v_art_4280_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4295_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v___x_4292_; 
lean_inc_ref(v_file_4279_);
if (v_isShared_4290_ == 0)
{
lean_ctor_set(v___x_4289_, 2, v_file_4279_);
lean_ctor_set(v___x_4289_, 1, v_file_4279_);
v___x_4292_ = v___x_4289_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v_descr_4286_);
lean_ctor_set(v_reuseFailAlloc_4294_, 1, v_file_4279_);
lean_ctor_set(v_reuseFailAlloc_4294_, 2, v_file_4279_);
lean_ctor_set(v_reuseFailAlloc_4294_, 3, v_mtime_4287_);
v___x_4292_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
lean_object* v___x_4293_; 
v___x_4293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4293_, 0, v___x_4292_);
lean_ctor_set(v___x_4293_, 1, v___y_4285_);
return v___x_4293_;
}
}
}
v___jp_4298_:
{
lean_object* v_descr_4300_; uint64_t v_hash_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; uint8_t v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; 
v_descr_4300_ = lean_ctor_get(v_art_4280_, 0);
v_hash_4301_ = lean_ctor_get_uint64(v_descr_4300_, sizeof(void*)*1);
v___x_4302_ = ((lean_object*)(l_Lake_restoreArtifact___closed__0));
v___x_4303_ = lean_string_append(v___x_4302_, v_file_4279_);
v___x_4304_ = 0;
v___x_4305_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4305_, 0, v___x_4303_);
lean_ctor_set_uint8(v___x_4305_, sizeof(void*)*1, v___x_4304_);
v___x_4306_ = lean_array_push(v___y_4299_, v___x_4305_);
lean_inc_ref(v_file_4279_);
v___x_4307_ = l_Lake_writeFileHash(v_file_4279_, v_hash_4301_);
if (lean_obj_tag(v___x_4307_) == 0)
{
lean_dec_ref_known(v___x_4307_, 1);
v___y_4285_ = v___x_4306_;
goto v___jp_4284_;
}
else
{
lean_object* v_a_4308_; lean_object* v___x_4309_; uint8_t v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
lean_dec_ref(v_art_4280_);
lean_dec_ref(v_file_4279_);
v_a_4308_ = lean_ctor_get(v___x_4307_, 0);
lean_inc(v_a_4308_);
lean_dec_ref_known(v___x_4307_, 1);
v___x_4309_ = lean_io_error_to_string(v_a_4308_);
v___x_4310_ = 3;
v___x_4311_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4311_, 0, v___x_4309_);
lean_ctor_set_uint8(v___x_4311_, sizeof(void*)*1, v___x_4310_);
v___x_4312_ = lean_array_get_size(v___x_4306_);
v___x_4313_ = lean_array_push(v___x_4306_, v___x_4311_);
v___x_4314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4312_);
lean_ctor_set(v___x_4314_, 1, v___x_4313_);
return v___x_4314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_restoreArtifact___boxed(lean_object* v_file_4366_, lean_object* v_art_4367_, lean_object* v_exe_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_){
_start:
{
uint8_t v_exe_boxed_4371_; lean_object* v_res_4372_; 
v_exe_boxed_4371_ = lean_unbox(v_exe_4368_);
v_res_4372_ = l_Lake_restoreArtifact(v_file_4366_, v_art_4367_, v_exe_boxed_4371_, v_a_4369_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(lean_object* v_val_4373_, lean_object* v_a_x3f_4374_, lean_object* v___y_4375_){
_start:
{
lean_object* v_log_4377_; uint8_t v_action_4378_; uint8_t v_wantsRebuild_4379_; lean_object* v_trace_4380_; lean_object* v_buildTime_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4393_; 
v_log_4377_ = lean_ctor_get(v___y_4375_, 0);
v_action_4378_ = lean_ctor_get_uint8(v___y_4375_, sizeof(void*)*3);
v_wantsRebuild_4379_ = lean_ctor_get_uint8(v___y_4375_, sizeof(void*)*3 + 1);
v_trace_4380_ = lean_ctor_get(v___y_4375_, 1);
v_buildTime_4381_ = lean_ctor_get(v___y_4375_, 2);
v_isSharedCheck_4393_ = !lean_is_exclusive(v___y_4375_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4383_ = v___y_4375_;
v_isShared_4384_ = v_isSharedCheck_4393_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_buildTime_4381_);
lean_inc(v_trace_4380_);
lean_inc(v_log_4377_);
lean_dec(v___y_4375_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4393_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4390_; 
v___x_4385_ = lean_io_mono_ms_now();
v___x_4386_ = lean_nat_sub(v___x_4385_, v_val_4373_);
lean_dec(v___x_4385_);
v___x_4387_ = lean_box(0);
v___x_4388_ = lean_nat_add(v_buildTime_4381_, v___x_4386_);
lean_dec(v___x_4386_);
lean_dec(v_buildTime_4381_);
if (v_isShared_4384_ == 0)
{
lean_ctor_set(v___x_4383_, 2, v___x_4388_);
v___x_4390_ = v___x_4383_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_log_4377_);
lean_ctor_set(v_reuseFailAlloc_4392_, 1, v_trace_4380_);
lean_ctor_set(v_reuseFailAlloc_4392_, 2, v___x_4388_);
lean_ctor_set_uint8(v_reuseFailAlloc_4392_, sizeof(void*)*3, v_action_4378_);
lean_ctor_set_uint8(v_reuseFailAlloc_4392_, sizeof(void*)*3 + 1, v_wantsRebuild_4379_);
v___x_4390_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
lean_object* v___x_4391_; 
v___x_4391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4387_);
lean_ctor_set(v___x_4391_, 1, v___x_4390_);
return v___x_4391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0___boxed(lean_object* v_val_4394_, lean_object* v_a_x3f_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
lean_object* v_res_4398_; 
v_res_4398_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v_val_4394_, v_a_x3f_4395_, v___y_4396_);
lean_dec(v_a_x3f_4395_);
lean_dec(v_val_4394_);
return v_res_4398_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(lean_object* v_file_4399_, lean_object* v_build_4400_, lean_object* v_traceFile_4401_, lean_object* v_ext_4402_, uint8_t v_text_4403_, lean_object* v_a_4404_, lean_object* v_depTrace_4405_, lean_object* v_traceFile_4406_, uint8_t v_action_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_){
_start:
{
lean_object* v_a_4415_; lean_object* v_a_4416_; lean_object* v_log_4419_; uint8_t v_action_4420_; uint8_t v_wantsRebuild_4421_; lean_object* v_trace_4422_; lean_object* v_buildTime_4423_; lean_object* v_toBuildConfig_4429_; lean_object* v_log_4430_; uint8_t v_action_4431_; uint8_t v_wantsRebuild_4432_; lean_object* v_trace_4433_; lean_object* v_buildTime_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4612_; 
v_toBuildConfig_4429_ = lean_ctor_get(v_a_4411_, 0);
v_log_4430_ = lean_ctor_get(v_a_4412_, 0);
v_action_4431_ = lean_ctor_get_uint8(v_a_4412_, sizeof(void*)*3);
v_wantsRebuild_4432_ = lean_ctor_get_uint8(v_a_4412_, sizeof(void*)*3 + 1);
v_trace_4433_ = lean_ctor_get(v_a_4412_, 1);
v_buildTime_4434_ = lean_ctor_get(v_a_4412_, 2);
v_isSharedCheck_4612_ = !lean_is_exclusive(v_a_4412_);
if (v_isSharedCheck_4612_ == 0)
{
v___x_4436_ = v_a_4412_;
v_isShared_4437_ = v_isSharedCheck_4612_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_buildTime_4434_);
lean_inc(v_trace_4433_);
lean_inc(v_log_4430_);
lean_dec(v_a_4412_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4612_;
goto v_resetjp_4435_;
}
v___jp_4414_:
{
lean_object* v___x_4417_; 
v___x_4417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4417_, 0, v_a_4415_);
lean_ctor_set(v___x_4417_, 1, v_a_4416_);
return v___x_4417_;
}
v___jp_4418_:
{
lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; 
v___x_4424_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_4425_ = lean_array_get_size(v_log_4419_);
v___x_4426_ = lean_array_push(v_log_4419_, v___x_4424_);
v___x_4427_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4427_, 0, v___x_4426_);
lean_ctor_set(v___x_4427_, 1, v_trace_4422_);
lean_ctor_set(v___x_4427_, 2, v_buildTime_4423_);
lean_ctor_set_uint8(v___x_4427_, sizeof(void*)*3, v_action_4420_);
lean_ctor_set_uint8(v___x_4427_, sizeof(void*)*3 + 1, v_wantsRebuild_4421_);
v___x_4428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4428_, 0, v___x_4425_);
lean_ctor_set(v___x_4428_, 1, v___x_4427_);
return v___x_4428_;
}
v_resetjp_4435_:
{
uint8_t v_noBuild_4438_; uint8_t v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; 
v_noBuild_4438_ = lean_ctor_get_uint8(v_toBuildConfig_4429_, sizeof(void*)*4 + 2);
v___x_4439_ = l_Lake_JobAction_merge(v_action_4431_, v_action_4407_);
v___x_4440_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_4406_);
v___x_4441_ = l_System_FilePath_addExtension(v_traceFile_4406_, v___x_4440_);
if (v_noBuild_4438_ == 0)
{
lean_object* v___x_4442_; lean_object* v_a_4444_; lean_object* v_a_4445_; lean_object* v___x_4449_; lean_object* v___x_4450_; 
v___x_4442_ = lean_io_mono_ms_now();
v___x_4449_ = lean_array_get_size(v_log_4430_);
v___x_4450_ = l_Lake_removeFileIfExists(v_file_4399_);
if (lean_obj_tag(v___x_4450_) == 0)
{
lean_object* v___x_4452_; 
lean_dec_ref_known(v___x_4450_, 1);
if (v_isShared_4437_ == 0)
{
v___x_4452_ = v___x_4436_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4588_; 
v_reuseFailAlloc_4588_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4588_, 0, v_log_4430_);
lean_ctor_set(v_reuseFailAlloc_4588_, 1, v_trace_4433_);
lean_ctor_set(v_reuseFailAlloc_4588_, 2, v_buildTime_4434_);
lean_ctor_set_uint8(v_reuseFailAlloc_4588_, sizeof(void*)*3 + 1, v_wantsRebuild_4432_);
v___x_4452_ = v_reuseFailAlloc_4588_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
lean_object* v___x_4453_; 
lean_ctor_set_uint8(v___x_4452_, sizeof(void*)*3, v___x_4439_);
lean_inc_ref(v_a_4411_);
lean_inc(v_a_4410_);
lean_inc(v_a_4409_);
lean_inc(v_a_4408_);
v___x_4453_ = lean_apply_7(v_build_4400_, v_a_4404_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v___x_4452_, lean_box(0));
if (lean_obj_tag(v___x_4453_) == 0)
{
lean_object* v_a_4454_; lean_object* v_log_4455_; uint8_t v_action_4456_; uint8_t v_wantsRebuild_4457_; lean_object* v_trace_4458_; lean_object* v_buildTime_4459_; lean_object* v___x_4460_; 
v_a_4454_ = lean_ctor_get(v___x_4453_, 1);
lean_inc(v_a_4454_);
lean_dec_ref_known(v___x_4453_, 2);
v_log_4455_ = lean_ctor_get(v_a_4454_, 0);
v_action_4456_ = lean_ctor_get_uint8(v_a_4454_, sizeof(void*)*3);
v_wantsRebuild_4457_ = lean_ctor_get_uint8(v_a_4454_, sizeof(void*)*3 + 1);
v_trace_4458_ = lean_ctor_get(v_a_4454_, 1);
v_buildTime_4459_ = lean_ctor_get(v_a_4454_, 2);
lean_inc_ref(v_file_4399_);
v___x_4460_ = l_Lake_clearFileHash(v_file_4399_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v___x_4461_; 
lean_dec_ref_known(v___x_4460_, 1);
v___x_4461_ = l_Lake_removeFileIfExists(v_traceFile_4401_);
if (lean_obj_tag(v___x_4461_) == 0)
{
lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4552_; 
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4461_);
if (v_isSharedCheck_4552_ == 0)
{
lean_object* v_unused_4553_; 
v_unused_4553_ = lean_ctor_get(v___x_4461_, 0);
lean_dec(v_unused_4553_);
v___x_4463_ = v___x_4461_;
v_isShared_4464_ = v_isSharedCheck_4552_;
goto v_resetjp_4462_;
}
else
{
lean_dec(v___x_4461_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4552_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4465_; 
v___x_4465_ = l_Lake_computeArtifact___redArg(v_file_4399_, v_ext_4402_, v_text_4403_, v_a_4411_, v_a_4454_);
if (lean_obj_tag(v___x_4465_) == 0)
{
lean_object* v_a_4466_; lean_object* v_a_4467_; lean_object* v_descr_4468_; lean_object* v_log_4469_; uint8_t v_action_4470_; uint8_t v_wantsRebuild_4471_; lean_object* v_trace_4472_; lean_object* v_buildTime_4473_; uint64_t v_hash_4474_; lean_object* v_ext_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___y_4479_; lean_object* v___x_4542_; lean_object* v___x_4543_; uint8_t v___x_4544_; 
v_a_4466_ = lean_ctor_get(v___x_4465_, 1);
lean_inc(v_a_4466_);
v_a_4467_ = lean_ctor_get(v___x_4465_, 0);
lean_inc(v_a_4467_);
lean_dec_ref_known(v___x_4465_, 2);
v_descr_4468_ = lean_ctor_get(v_a_4467_, 0);
v_log_4469_ = lean_ctor_get(v_a_4466_, 0);
v_action_4470_ = lean_ctor_get_uint8(v_a_4466_, sizeof(void*)*3);
v_wantsRebuild_4471_ = lean_ctor_get_uint8(v_a_4466_, sizeof(void*)*3 + 1);
v_trace_4472_ = lean_ctor_get(v_a_4466_, 1);
v_buildTime_4473_ = lean_ctor_get(v_a_4466_, 2);
v_hash_4474_ = lean_ctor_get_uint64(v_descr_4468_, sizeof(void*)*1);
v_ext_4475_ = lean_ctor_get(v_descr_4468_, 0);
v___x_4476_ = lean_array_get_size(v_log_4469_);
v___x_4477_ = l_Array_extract___redArg(v_log_4469_, v___x_4449_, v___x_4476_);
v___x_4542_ = lean_string_utf8_byte_size(v_ext_4475_);
v___x_4543_ = lean_unsigned_to_nat(0u);
v___x_4544_ = lean_nat_dec_eq(v___x_4542_, v___x_4543_);
if (v___x_4544_ == 0)
{
lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; 
v___x_4545_ = l_Lake_lowerHexUInt64(v_hash_4474_);
v___x_4546_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_4547_ = lean_string_append(v___x_4545_, v___x_4546_);
v___x_4548_ = lean_string_append(v___x_4547_, v_ext_4475_);
v___y_4479_ = v___x_4548_;
goto v___jp_4478_;
}
else
{
lean_object* v___x_4549_; 
v___x_4549_ = l_Lake_lowerHexUInt64(v_hash_4474_);
v___y_4479_ = v___x_4549_;
goto v___jp_4478_;
}
v___jp_4478_:
{
lean_object* v___x_4481_; 
if (v_isShared_4464_ == 0)
{
lean_ctor_set_tag(v___x_4463_, 3);
lean_ctor_set(v___x_4463_, 0, v___y_4479_);
v___x_4481_ = v___x_4463_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v___y_4479_);
v___x_4481_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
lean_object* v___x_4482_; lean_object* v___x_4483_; 
v___x_4482_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_4405_, v___x_4481_, v___x_4477_);
v___x_4483_ = l_Lake_BuildMetadata_writeFile(v_traceFile_4406_, v___x_4482_);
if (lean_obj_tag(v___x_4483_) == 0)
{
lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4524_; 
v_isSharedCheck_4524_ = !lean_is_exclusive(v___x_4483_);
if (v_isSharedCheck_4524_ == 0)
{
lean_object* v_unused_4525_; 
v_unused_4525_ = lean_ctor_get(v___x_4483_, 0);
lean_dec(v_unused_4525_);
v___x_4485_ = v___x_4483_;
v_isShared_4486_ = v_isSharedCheck_4524_;
goto v_resetjp_4484_;
}
else
{
lean_dec(v___x_4483_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4524_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v___x_4487_; 
v___x_4487_ = l_Lake_removeFileIfExists(v___x_4441_);
lean_dec_ref(v___x_4441_);
if (lean_obj_tag(v___x_4487_) == 0)
{
lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4507_; 
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4487_);
if (v_isSharedCheck_4507_ == 0)
{
lean_object* v_unused_4508_; 
v_unused_4508_ = lean_ctor_get(v___x_4487_, 0);
lean_dec(v_unused_4508_);
v___x_4489_ = v___x_4487_;
v_isShared_4490_ = v_isSharedCheck_4507_;
goto v_resetjp_4488_;
}
else
{
lean_dec(v___x_4487_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4507_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4492_; 
lean_inc(v_a_4467_);
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 0, v_a_4467_);
v___x_4492_ = v___x_4489_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_a_4467_);
v___x_4492_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
lean_object* v___x_4494_; 
if (v_isShared_4486_ == 0)
{
lean_ctor_set_tag(v___x_4485_, 1);
lean_ctor_set(v___x_4485_, 0, v___x_4492_);
v___x_4494_ = v___x_4485_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v___x_4492_);
v___x_4494_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
lean_object* v___x_4495_; lean_object* v_a_4496_; lean_object* v___x_4498_; uint8_t v_isShared_4499_; uint8_t v_isSharedCheck_4503_; 
v___x_4495_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v___x_4442_, v___x_4494_, v_a_4466_);
lean_dec_ref(v___x_4494_);
lean_dec(v___x_4442_);
v_a_4496_ = lean_ctor_get(v___x_4495_, 1);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4495_);
if (v_isSharedCheck_4503_ == 0)
{
lean_object* v_unused_4504_; 
v_unused_4504_ = lean_ctor_get(v___x_4495_, 0);
lean_dec(v_unused_4504_);
v___x_4498_ = v___x_4495_;
v_isShared_4499_ = v_isSharedCheck_4503_;
goto v_resetjp_4497_;
}
else
{
lean_inc(v_a_4496_);
lean_dec(v___x_4495_);
v___x_4498_ = lean_box(0);
v_isShared_4499_ = v_isSharedCheck_4503_;
goto v_resetjp_4497_;
}
v_resetjp_4497_:
{
lean_object* v___x_4501_; 
if (v_isShared_4499_ == 0)
{
lean_ctor_set(v___x_4498_, 0, v_a_4467_);
v___x_4501_ = v___x_4498_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_a_4467_);
lean_ctor_set(v_reuseFailAlloc_4502_, 1, v_a_4496_);
v___x_4501_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
return v___x_4501_;
}
}
}
}
}
}
else
{
lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4520_; 
lean_inc(v_buildTime_4473_);
lean_inc_ref(v_trace_4472_);
lean_inc_ref(v_log_4469_);
lean_del_object(v___x_4485_);
lean_dec(v_a_4467_);
v_isSharedCheck_4520_ = !lean_is_exclusive(v_a_4466_);
if (v_isSharedCheck_4520_ == 0)
{
lean_object* v_unused_4521_; lean_object* v_unused_4522_; lean_object* v_unused_4523_; 
v_unused_4521_ = lean_ctor_get(v_a_4466_, 2);
lean_dec(v_unused_4521_);
v_unused_4522_ = lean_ctor_get(v_a_4466_, 1);
lean_dec(v_unused_4522_);
v_unused_4523_ = lean_ctor_get(v_a_4466_, 0);
lean_dec(v_unused_4523_);
v___x_4510_ = v_a_4466_;
v_isShared_4511_ = v_isSharedCheck_4520_;
goto v_resetjp_4509_;
}
else
{
lean_dec(v_a_4466_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4520_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v_a_4512_; lean_object* v___x_4513_; uint8_t v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4518_; 
v_a_4512_ = lean_ctor_get(v___x_4487_, 0);
lean_inc(v_a_4512_);
lean_dec_ref_known(v___x_4487_, 1);
v___x_4513_ = lean_io_error_to_string(v_a_4512_);
v___x_4514_ = 3;
v___x_4515_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4515_, 0, v___x_4513_);
lean_ctor_set_uint8(v___x_4515_, sizeof(void*)*1, v___x_4514_);
v___x_4516_ = lean_array_push(v_log_4469_, v___x_4515_);
if (v_isShared_4511_ == 0)
{
lean_ctor_set(v___x_4510_, 0, v___x_4516_);
v___x_4518_ = v___x_4510_;
goto v_reusejp_4517_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v___x_4516_);
lean_ctor_set(v_reuseFailAlloc_4519_, 1, v_trace_4472_);
lean_ctor_set(v_reuseFailAlloc_4519_, 2, v_buildTime_4473_);
lean_ctor_set_uint8(v_reuseFailAlloc_4519_, sizeof(void*)*3, v_action_4470_);
lean_ctor_set_uint8(v_reuseFailAlloc_4519_, sizeof(void*)*3 + 1, v_wantsRebuild_4471_);
v___x_4518_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4517_;
}
v_reusejp_4517_:
{
v_a_4444_ = v___x_4476_;
v_a_4445_ = v___x_4518_;
goto v___jp_4443_;
}
}
}
}
}
else
{
lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4537_; 
lean_inc(v_buildTime_4473_);
lean_inc_ref(v_trace_4472_);
lean_inc_ref(v_log_4469_);
lean_dec(v_a_4467_);
lean_dec_ref(v___x_4441_);
v_isSharedCheck_4537_ = !lean_is_exclusive(v_a_4466_);
if (v_isSharedCheck_4537_ == 0)
{
lean_object* v_unused_4538_; lean_object* v_unused_4539_; lean_object* v_unused_4540_; 
v_unused_4538_ = lean_ctor_get(v_a_4466_, 2);
lean_dec(v_unused_4538_);
v_unused_4539_ = lean_ctor_get(v_a_4466_, 1);
lean_dec(v_unused_4539_);
v_unused_4540_ = lean_ctor_get(v_a_4466_, 0);
lean_dec(v_unused_4540_);
v___x_4527_ = v_a_4466_;
v_isShared_4528_ = v_isSharedCheck_4537_;
goto v_resetjp_4526_;
}
else
{
lean_dec(v_a_4466_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4537_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v_a_4529_; lean_object* v___x_4530_; uint8_t v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4535_; 
v_a_4529_ = lean_ctor_get(v___x_4483_, 0);
lean_inc(v_a_4529_);
lean_dec_ref_known(v___x_4483_, 1);
v___x_4530_ = lean_io_error_to_string(v_a_4529_);
v___x_4531_ = 3;
v___x_4532_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4532_, 0, v___x_4530_);
lean_ctor_set_uint8(v___x_4532_, sizeof(void*)*1, v___x_4531_);
v___x_4533_ = lean_array_push(v_log_4469_, v___x_4532_);
if (v_isShared_4528_ == 0)
{
lean_ctor_set(v___x_4527_, 0, v___x_4533_);
v___x_4535_ = v___x_4527_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v___x_4533_);
lean_ctor_set(v_reuseFailAlloc_4536_, 1, v_trace_4472_);
lean_ctor_set(v_reuseFailAlloc_4536_, 2, v_buildTime_4473_);
lean_ctor_set_uint8(v_reuseFailAlloc_4536_, sizeof(void*)*3, v_action_4470_);
lean_ctor_set_uint8(v_reuseFailAlloc_4536_, sizeof(void*)*3 + 1, v_wantsRebuild_4471_);
v___x_4535_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
v_a_4444_ = v___x_4476_;
v_a_4445_ = v___x_4535_;
goto v___jp_4443_;
}
}
}
}
}
}
else
{
lean_object* v_a_4550_; lean_object* v_a_4551_; 
lean_del_object(v___x_4463_);
lean_dec_ref(v___x_4441_);
lean_dec_ref(v_traceFile_4406_);
v_a_4550_ = lean_ctor_get(v___x_4465_, 0);
lean_inc(v_a_4550_);
v_a_4551_ = lean_ctor_get(v___x_4465_, 1);
lean_inc(v_a_4551_);
lean_dec_ref_known(v___x_4465_, 2);
v_a_4444_ = v_a_4550_;
v_a_4445_ = v_a_4551_;
goto v___jp_4443_;
}
}
}
else
{
lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4566_; 
lean_inc(v_buildTime_4459_);
lean_inc_ref(v_trace_4458_);
lean_inc_ref(v_log_4455_);
lean_dec_ref(v___x_4441_);
lean_dec_ref(v_traceFile_4406_);
lean_dec_ref(v_ext_4402_);
lean_dec_ref(v_file_4399_);
v_isSharedCheck_4566_ = !lean_is_exclusive(v_a_4454_);
if (v_isSharedCheck_4566_ == 0)
{
lean_object* v_unused_4567_; lean_object* v_unused_4568_; lean_object* v_unused_4569_; 
v_unused_4567_ = lean_ctor_get(v_a_4454_, 2);
lean_dec(v_unused_4567_);
v_unused_4568_ = lean_ctor_get(v_a_4454_, 1);
lean_dec(v_unused_4568_);
v_unused_4569_ = lean_ctor_get(v_a_4454_, 0);
lean_dec(v_unused_4569_);
v___x_4555_ = v_a_4454_;
v_isShared_4556_ = v_isSharedCheck_4566_;
goto v_resetjp_4554_;
}
else
{
lean_dec(v_a_4454_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4566_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
lean_object* v_a_4557_; lean_object* v___x_4558_; uint8_t v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4564_; 
v_a_4557_ = lean_ctor_get(v___x_4461_, 0);
lean_inc(v_a_4557_);
lean_dec_ref_known(v___x_4461_, 1);
v___x_4558_ = lean_io_error_to_string(v_a_4557_);
v___x_4559_ = 3;
v___x_4560_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4560_, 0, v___x_4558_);
lean_ctor_set_uint8(v___x_4560_, sizeof(void*)*1, v___x_4559_);
v___x_4561_ = lean_array_get_size(v_log_4455_);
v___x_4562_ = lean_array_push(v_log_4455_, v___x_4560_);
if (v_isShared_4556_ == 0)
{
lean_ctor_set(v___x_4555_, 0, v___x_4562_);
v___x_4564_ = v___x_4555_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v___x_4562_);
lean_ctor_set(v_reuseFailAlloc_4565_, 1, v_trace_4458_);
lean_ctor_set(v_reuseFailAlloc_4565_, 2, v_buildTime_4459_);
lean_ctor_set_uint8(v_reuseFailAlloc_4565_, sizeof(void*)*3, v_action_4456_);
lean_ctor_set_uint8(v_reuseFailAlloc_4565_, sizeof(void*)*3 + 1, v_wantsRebuild_4457_);
v___x_4564_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
v_a_4444_ = v___x_4561_;
v_a_4445_ = v___x_4564_;
goto v___jp_4443_;
}
}
}
}
else
{
lean_object* v___x_4571_; uint8_t v_isShared_4572_; uint8_t v_isSharedCheck_4582_; 
lean_inc(v_buildTime_4459_);
lean_inc_ref(v_trace_4458_);
lean_inc_ref(v_log_4455_);
lean_dec_ref(v___x_4441_);
lean_dec_ref(v_traceFile_4406_);
lean_dec_ref(v_ext_4402_);
lean_dec_ref(v_file_4399_);
v_isSharedCheck_4582_ = !lean_is_exclusive(v_a_4454_);
if (v_isSharedCheck_4582_ == 0)
{
lean_object* v_unused_4583_; lean_object* v_unused_4584_; lean_object* v_unused_4585_; 
v_unused_4583_ = lean_ctor_get(v_a_4454_, 2);
lean_dec(v_unused_4583_);
v_unused_4584_ = lean_ctor_get(v_a_4454_, 1);
lean_dec(v_unused_4584_);
v_unused_4585_ = lean_ctor_get(v_a_4454_, 0);
lean_dec(v_unused_4585_);
v___x_4571_ = v_a_4454_;
v_isShared_4572_ = v_isSharedCheck_4582_;
goto v_resetjp_4570_;
}
else
{
lean_dec(v_a_4454_);
v___x_4571_ = lean_box(0);
v_isShared_4572_ = v_isSharedCheck_4582_;
goto v_resetjp_4570_;
}
v_resetjp_4570_:
{
lean_object* v_a_4573_; lean_object* v___x_4574_; uint8_t v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4580_; 
v_a_4573_ = lean_ctor_get(v___x_4460_, 0);
lean_inc(v_a_4573_);
lean_dec_ref_known(v___x_4460_, 1);
v___x_4574_ = lean_io_error_to_string(v_a_4573_);
v___x_4575_ = 3;
v___x_4576_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4576_, 0, v___x_4574_);
lean_ctor_set_uint8(v___x_4576_, sizeof(void*)*1, v___x_4575_);
v___x_4577_ = lean_array_get_size(v_log_4455_);
v___x_4578_ = lean_array_push(v_log_4455_, v___x_4576_);
if (v_isShared_4572_ == 0)
{
lean_ctor_set(v___x_4571_, 0, v___x_4578_);
v___x_4580_ = v___x_4571_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v___x_4578_);
lean_ctor_set(v_reuseFailAlloc_4581_, 1, v_trace_4458_);
lean_ctor_set(v_reuseFailAlloc_4581_, 2, v_buildTime_4459_);
lean_ctor_set_uint8(v_reuseFailAlloc_4581_, sizeof(void*)*3, v_action_4456_);
lean_ctor_set_uint8(v_reuseFailAlloc_4581_, sizeof(void*)*3 + 1, v_wantsRebuild_4457_);
v___x_4580_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
v_a_4444_ = v___x_4577_;
v_a_4445_ = v___x_4580_;
goto v___jp_4443_;
}
}
}
}
else
{
lean_object* v_a_4586_; lean_object* v_a_4587_; 
lean_dec_ref(v___x_4441_);
lean_dec_ref(v_traceFile_4406_);
lean_dec_ref(v_ext_4402_);
lean_dec_ref(v_file_4399_);
v_a_4586_ = lean_ctor_get(v___x_4453_, 0);
lean_inc(v_a_4586_);
v_a_4587_ = lean_ctor_get(v___x_4453_, 1);
lean_inc(v_a_4587_);
lean_dec_ref_known(v___x_4453_, 2);
v_a_4444_ = v_a_4586_;
v_a_4445_ = v_a_4587_;
goto v___jp_4443_;
}
}
}
else
{
lean_object* v_a_4589_; lean_object* v___x_4590_; uint8_t v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4595_; 
lean_dec_ref(v___x_4441_);
lean_dec_ref(v_traceFile_4406_);
lean_dec_ref(v_a_4404_);
lean_dec_ref(v_ext_4402_);
lean_dec_ref(v_build_4400_);
lean_dec_ref(v_file_4399_);
v_a_4589_ = lean_ctor_get(v___x_4450_, 0);
lean_inc(v_a_4589_);
lean_dec_ref_known(v___x_4450_, 1);
v___x_4590_ = lean_io_error_to_string(v_a_4589_);
v___x_4591_ = 3;
v___x_4592_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4592_, 0, v___x_4590_);
lean_ctor_set_uint8(v___x_4592_, sizeof(void*)*1, v___x_4591_);
v___x_4593_ = lean_array_push(v_log_4430_, v___x_4592_);
if (v_isShared_4437_ == 0)
{
lean_ctor_set(v___x_4436_, 0, v___x_4593_);
v___x_4595_ = v___x_4436_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v___x_4593_);
lean_ctor_set(v_reuseFailAlloc_4596_, 1, v_trace_4433_);
lean_ctor_set(v_reuseFailAlloc_4596_, 2, v_buildTime_4434_);
lean_ctor_set_uint8(v_reuseFailAlloc_4596_, sizeof(void*)*3 + 1, v_wantsRebuild_4432_);
v___x_4595_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
lean_ctor_set_uint8(v___x_4595_, sizeof(void*)*3, v___x_4439_);
v_a_4444_ = v___x_4449_;
v_a_4445_ = v___x_4595_;
goto v___jp_4443_;
}
}
v___jp_4443_:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v_a_4448_; 
v___x_4446_ = lean_box(0);
v___x_4447_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v___x_4442_, v___x_4446_, v_a_4445_);
lean_dec(v___x_4442_);
v_a_4448_ = lean_ctor_get(v___x_4447_, 1);
lean_inc(v_a_4448_);
lean_dec_ref(v___x_4447_);
v_a_4415_ = v_a_4444_;
v_a_4416_ = v_a_4448_;
goto v___jp_4414_;
}
}
else
{
uint8_t v___x_4597_; 
lean_dec_ref(v_a_4404_);
lean_dec_ref(v_ext_4402_);
lean_dec_ref(v_build_4400_);
lean_dec_ref(v_file_4399_);
v___x_4597_ = l_System_FilePath_pathExists(v_traceFile_4406_);
lean_dec_ref(v_traceFile_4406_);
if (v___x_4597_ == 0)
{
lean_dec_ref(v___x_4441_);
lean_del_object(v___x_4436_);
v_log_4419_ = v_log_4430_;
v_action_4420_ = v___x_4439_;
v_wantsRebuild_4421_ = v_noBuild_4438_;
v_trace_4422_ = v_trace_4433_;
v_buildTime_4423_ = v_buildTime_4434_;
goto v___jp_4418_;
}
else
{
lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; 
v___x_4598_ = lean_box(0);
v___x_4599_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_4600_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_4405_, v___x_4598_, v___x_4599_);
v___x_4601_ = l_Lake_BuildMetadata_writeFile(v___x_4441_, v___x_4600_);
if (lean_obj_tag(v___x_4601_) == 0)
{
lean_dec_ref_known(v___x_4601_, 1);
lean_del_object(v___x_4436_);
v_log_4419_ = v_log_4430_;
v_action_4420_ = v___x_4439_;
v_wantsRebuild_4421_ = v_noBuild_4438_;
v_trace_4422_ = v_trace_4433_;
v_buildTime_4423_ = v_buildTime_4434_;
goto v___jp_4418_;
}
else
{
lean_object* v_a_4602_; lean_object* v___x_4603_; uint8_t v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4609_; 
v_a_4602_ = lean_ctor_get(v___x_4601_, 0);
lean_inc(v_a_4602_);
lean_dec_ref_known(v___x_4601_, 1);
v___x_4603_ = lean_io_error_to_string(v_a_4602_);
v___x_4604_ = 3;
v___x_4605_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4605_, 0, v___x_4603_);
lean_ctor_set_uint8(v___x_4605_, sizeof(void*)*1, v___x_4604_);
v___x_4606_ = lean_array_get_size(v_log_4430_);
v___x_4607_ = lean_array_push(v_log_4430_, v___x_4605_);
if (v_isShared_4437_ == 0)
{
lean_ctor_set(v___x_4436_, 0, v___x_4607_);
v___x_4609_ = v___x_4436_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v___x_4607_);
lean_ctor_set(v_reuseFailAlloc_4611_, 1, v_trace_4433_);
lean_ctor_set(v_reuseFailAlloc_4611_, 2, v_buildTime_4434_);
v___x_4609_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
lean_object* v___x_4610_; 
lean_ctor_set_uint8(v___x_4609_, sizeof(void*)*3, v___x_4439_);
lean_ctor_set_uint8(v___x_4609_, sizeof(void*)*3 + 1, v_noBuild_4438_);
v___x_4610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4610_, 0, v___x_4606_);
lean_ctor_set(v___x_4610_, 1, v___x_4609_);
return v___x_4610_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___boxed(lean_object* v_file_4613_, lean_object* v_build_4614_, lean_object* v_traceFile_4615_, lean_object* v_ext_4616_, lean_object* v_text_4617_, lean_object* v_a_4618_, lean_object* v_depTrace_4619_, lean_object* v_traceFile_4620_, lean_object* v_action_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_){
_start:
{
uint8_t v_text_boxed_4628_; uint8_t v_action_boxed_4629_; lean_object* v_res_4630_; 
v_text_boxed_4628_ = lean_unbox(v_text_4617_);
v_action_boxed_4629_ = lean_unbox(v_action_4621_);
v_res_4630_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(v_file_4613_, v_build_4614_, v_traceFile_4615_, v_ext_4616_, v_text_boxed_4628_, v_a_4618_, v_depTrace_4619_, v_traceFile_4620_, v_action_boxed_4629_, v_a_4622_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_);
lean_dec_ref(v_a_4625_);
lean_dec(v_a_4624_);
lean_dec(v_a_4623_);
lean_dec(v_a_4622_);
lean_dec_ref(v_depTrace_4619_);
lean_dec_ref(v_traceFile_4615_);
return v_res_4630_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(lean_object* v_file_4631_, lean_object* v_build_4632_, uint8_t v_text_4633_, lean_object* v_ext_4634_, lean_object* v_depTrace_4635_, lean_object* v_traceFile_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_){
_start:
{
uint8_t v___x_4644_; lean_object* v___x_4645_; 
v___x_4644_ = 5;
lean_inc_ref(v_traceFile_4636_);
v___x_4645_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(v_file_4631_, v_build_4632_, v_traceFile_4636_, v_ext_4634_, v_text_4633_, v_a_4637_, v_depTrace_4635_, v_traceFile_4636_, v___x_4644_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_);
lean_dec_ref(v_traceFile_4636_);
return v___x_4645_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild___boxed(lean_object* v_file_4646_, lean_object* v_build_4647_, lean_object* v_text_4648_, lean_object* v_ext_4649_, lean_object* v_depTrace_4650_, lean_object* v_traceFile_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_){
_start:
{
uint8_t v_text_boxed_4659_; lean_object* v_res_4660_; 
v_text_boxed_4659_ = lean_unbox(v_text_4648_);
v_res_4660_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_4646_, v_build_4647_, v_text_boxed_4659_, v_ext_4649_, v_depTrace_4650_, v_traceFile_4651_, v_a_4652_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_);
lean_dec_ref(v_a_4656_);
lean_dec(v_a_4655_);
lean_dec(v_a_4654_);
lean_dec(v_a_4653_);
lean_dec_ref(v_depTrace_4650_);
return v_res_4660_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(lean_object* v_art_4662_, lean_object* v_traceFile_4663_, lean_object* v_a_4664_){
_start:
{
lean_object* v_log_4666_; uint8_t v_action_4667_; uint8_t v_wantsRebuild_4668_; lean_object* v_trace_4669_; lean_object* v_buildTime_4670_; lean_object* v___x_4671_; 
v_log_4666_ = lean_ctor_get(v_a_4664_, 0);
v_action_4667_ = lean_ctor_get_uint8(v_a_4664_, sizeof(void*)*3);
v_wantsRebuild_4668_ = lean_ctor_get_uint8(v_a_4664_, sizeof(void*)*3 + 1);
v_trace_4669_ = lean_ctor_get(v_a_4664_, 1);
v_buildTime_4670_ = lean_ctor_get(v_a_4664_, 2);
v___x_4671_ = lean_io_metadata(v_traceFile_4663_);
if (lean_obj_tag(v___x_4671_) == 0)
{
lean_object* v_a_4672_; lean_object* v_modified_4673_; lean_object* v_descr_4674_; lean_object* v_path_4675_; lean_object* v_name_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4684_; 
v_a_4672_ = lean_ctor_get(v___x_4671_, 0);
lean_inc(v_a_4672_);
lean_dec_ref_known(v___x_4671_, 1);
v_modified_4673_ = lean_ctor_get(v_a_4672_, 1);
lean_inc_ref(v_modified_4673_);
lean_dec(v_a_4672_);
v_descr_4674_ = lean_ctor_get(v_art_4662_, 0);
v_path_4675_ = lean_ctor_get(v_art_4662_, 1);
v_name_4676_ = lean_ctor_get(v_art_4662_, 2);
v_isSharedCheck_4684_ = !lean_is_exclusive(v_art_4662_);
if (v_isSharedCheck_4684_ == 0)
{
lean_object* v_unused_4685_; 
v_unused_4685_ = lean_ctor_get(v_art_4662_, 3);
lean_dec(v_unused_4685_);
v___x_4678_ = v_art_4662_;
v_isShared_4679_ = v_isSharedCheck_4684_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_name_4676_);
lean_inc(v_path_4675_);
lean_inc(v_descr_4674_);
lean_dec(v_art_4662_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4684_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v___x_4681_; 
if (v_isShared_4679_ == 0)
{
lean_ctor_set(v___x_4678_, 3, v_modified_4673_);
v___x_4681_ = v___x_4678_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v_descr_4674_);
lean_ctor_set(v_reuseFailAlloc_4683_, 1, v_path_4675_);
lean_ctor_set(v_reuseFailAlloc_4683_, 2, v_name_4676_);
lean_ctor_set(v_reuseFailAlloc_4683_, 3, v_modified_4673_);
v___x_4681_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
lean_object* v___x_4682_; 
v___x_4682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4682_, 0, v___x_4681_);
lean_ctor_set(v___x_4682_, 1, v_a_4664_);
return v___x_4682_;
}
}
}
else
{
lean_object* v_a_4686_; 
v_a_4686_ = lean_ctor_get(v___x_4671_, 0);
lean_inc(v_a_4686_);
lean_dec_ref_known(v___x_4671_, 1);
if (lean_obj_tag(v_a_4686_) == 11)
{
lean_object* v___x_4687_; 
lean_dec_ref_known(v_a_4686_, 2);
v___x_4687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4687_, 0, v_art_4662_);
lean_ctor_set(v___x_4687_, 1, v_a_4664_);
return v___x_4687_;
}
else
{
lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4702_; 
lean_inc(v_buildTime_4670_);
lean_inc_ref(v_trace_4669_);
lean_inc_ref(v_log_4666_);
lean_dec_ref(v_art_4662_);
v_isSharedCheck_4702_ = !lean_is_exclusive(v_a_4664_);
if (v_isSharedCheck_4702_ == 0)
{
lean_object* v_unused_4703_; lean_object* v_unused_4704_; lean_object* v_unused_4705_; 
v_unused_4703_ = lean_ctor_get(v_a_4664_, 2);
lean_dec(v_unused_4703_);
v_unused_4704_ = lean_ctor_get(v_a_4664_, 1);
lean_dec(v_unused_4704_);
v_unused_4705_ = lean_ctor_get(v_a_4664_, 0);
lean_dec(v_unused_4705_);
v___x_4689_ = v_a_4664_;
v_isShared_4690_ = v_isSharedCheck_4702_;
goto v_resetjp_4688_;
}
else
{
lean_dec(v_a_4664_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4702_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; uint8_t v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4699_; 
v___x_4691_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___closed__0));
v___x_4692_ = lean_io_error_to_string(v_a_4686_);
v___x_4693_ = lean_string_append(v___x_4691_, v___x_4692_);
lean_dec_ref(v___x_4692_);
v___x_4694_ = 3;
v___x_4695_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4695_, 0, v___x_4693_);
lean_ctor_set_uint8(v___x_4695_, sizeof(void*)*1, v___x_4694_);
v___x_4696_ = lean_array_get_size(v_log_4666_);
v___x_4697_ = lean_array_push(v_log_4666_, v___x_4695_);
if (v_isShared_4690_ == 0)
{
lean_ctor_set(v___x_4689_, 0, v___x_4697_);
v___x_4699_ = v___x_4689_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4701_; 
v_reuseFailAlloc_4701_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4701_, 0, v___x_4697_);
lean_ctor_set(v_reuseFailAlloc_4701_, 1, v_trace_4669_);
lean_ctor_set(v_reuseFailAlloc_4701_, 2, v_buildTime_4670_);
lean_ctor_set_uint8(v_reuseFailAlloc_4701_, sizeof(void*)*3, v_action_4667_);
lean_ctor_set_uint8(v_reuseFailAlloc_4701_, sizeof(void*)*3 + 1, v_wantsRebuild_4668_);
v___x_4699_ = v_reuseFailAlloc_4701_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
lean_object* v___x_4700_; 
v___x_4700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4700_, 0, v___x_4696_);
lean_ctor_set(v___x_4700_, 1, v___x_4699_);
return v___x_4700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___boxed(lean_object* v_art_4706_, lean_object* v_traceFile_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_){
_start:
{
lean_object* v_res_4710_; 
v_res_4710_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_4706_, v_traceFile_4707_, v_a_4708_);
lean_dec_ref(v_traceFile_4707_);
return v_res_4710_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(lean_object* v_art_4711_, lean_object* v_traceFile_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_){
_start:
{
lean_object* v___x_4720_; 
v___x_4720_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_4711_, v_traceFile_4712_, v_a_4718_);
return v___x_4720_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___boxed(lean_object* v_art_4721_, lean_object* v_traceFile_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_){
_start:
{
lean_object* v_res_4730_; 
v_res_4730_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(v_art_4721_, v_traceFile_4722_, v_a_4723_, v_a_4724_, v_a_4725_, v_a_4726_, v_a_4727_, v_a_4728_);
lean_dec_ref(v_a_4727_);
lean_dec(v_a_4726_);
lean_dec(v_a_4725_);
lean_dec(v_a_4724_);
lean_dec_ref(v_a_4723_);
lean_dec_ref(v_traceFile_4722_);
return v_res_4730_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(lean_object* v_a_4731_, lean_object* v_____r_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_){
_start:
{
lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; 
v___x_4740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4740_, 0, v_a_4731_);
v___x_4741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4741_, 0, v___x_4740_);
v___x_4742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4742_, 0, v___x_4741_);
lean_ctor_set(v___x_4742_, 1, v___y_4738_);
return v___x_4742_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0___boxed(lean_object* v_a_4743_, lean_object* v_____r_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_){
_start:
{
lean_object* v_res_4752_; 
v_res_4752_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4743_, v_____r_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_);
lean_dec_ref(v___y_4749_);
lean_dec(v___y_4748_);
lean_dec(v___y_4747_);
lean_dec(v___y_4746_);
lean_dec_ref(v___y_4745_);
return v_res_4752_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(uint8_t v_exe_4753_, lean_object* v___y_4754_, uint64_t v_inputHash_4755_, lean_object* v_savedTrace_4756_, lean_object* v_pkg_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_){
_start:
{
lean_object* v___y_4765_; lean_object* v_a_4769_; lean_object* v_a_4770_; lean_object* v___y_4785_; 
if (lean_obj_tag(v_savedTrace_4756_) == 2)
{
lean_object* v_data_4800_; uint64_t v_depHash_4801_; lean_object* v_outputs_x3f_4802_; uint8_t v___x_4803_; 
v_data_4800_ = lean_ctor_get(v_savedTrace_4756_, 0);
lean_inc_ref(v_data_4800_);
lean_dec_ref_known(v_savedTrace_4756_, 1);
v_depHash_4801_ = lean_ctor_get_uint64(v_data_4800_, sizeof(void*)*3);
v_outputs_x3f_4802_ = lean_ctor_get(v_data_4800_, 1);
lean_inc(v_outputs_x3f_4802_);
lean_dec_ref(v_data_4800_);
v___x_4803_ = lean_uint64_dec_eq(v_depHash_4801_, v_inputHash_4755_);
if (v___x_4803_ == 0)
{
lean_dec(v_outputs_x3f_4802_);
lean_dec_ref(v_pkg_4757_);
lean_dec_ref(v___y_4754_);
v___y_4765_ = v_a_4762_;
goto v___jp_4764_;
}
else
{
if (lean_obj_tag(v_outputs_x3f_4802_) == 1)
{
lean_object* v_val_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; 
v_val_4804_ = lean_ctor_get(v_outputs_x3f_4802_, 0);
lean_inc_n(v_val_4804_, 2);
lean_dec_ref_known(v_outputs_x3f_4802_, 1);
v___x_4805_ = lean_box(0);
v___x_4806_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4806_, 0, v_val_4804_);
lean_ctor_set(v___x_4806_, 1, v___x_4805_);
lean_ctor_set(v___x_4806_, 2, v___x_4805_);
lean_inc_ref(v___y_4754_);
v___x_4807_ = l_Lake_resolveArtifactOutput(v___x_4806_, v_exe_4753_, v___y_4754_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_, v_a_4762_);
if (lean_obj_tag(v___x_4807_) == 0)
{
lean_object* v_config_4808_; lean_object* v_a_4809_; lean_object* v_a_4810_; lean_object* v_enableArtifactCache_x3f_4811_; lean_object* v_a_4813_; uint8_t v_a_4817_; lean_object* v_a_4818_; 
v_config_4808_ = lean_ctor_get(v_pkg_4757_, 6);
v_a_4809_ = lean_ctor_get(v___x_4807_, 0);
lean_inc(v_a_4809_);
v_a_4810_ = lean_ctor_get(v___x_4807_, 1);
lean_inc(v_a_4810_);
lean_dec_ref_known(v___x_4807_, 2);
v_enableArtifactCache_x3f_4811_ = lean_ctor_get(v_config_4808_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_4811_) == 0)
{
lean_object* v_toContext_4850_; lean_object* v_lakeEnv_4851_; lean_object* v_enableArtifactCache_x3f_4852_; 
v_toContext_4850_ = lean_ctor_get(v_a_4761_, 1);
v_lakeEnv_4851_ = lean_ctor_get(v_toContext_4850_, 0);
v_enableArtifactCache_x3f_4852_ = lean_ctor_get(v_lakeEnv_4851_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_4852_) == 0)
{
lean_object* v_packages_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v_config_4856_; lean_object* v_enableArtifactCache_x3f_4857_; 
v_packages_4853_ = lean_ctor_get(v_toContext_4850_, 4);
v___x_4854_ = lean_unsigned_to_nat(0u);
v___x_4855_ = lean_array_fget_borrowed(v_packages_4853_, v___x_4854_);
v_config_4856_ = lean_ctor_get(v___x_4855_, 6);
v_enableArtifactCache_x3f_4857_ = lean_ctor_get(v_config_4856_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_4857_) == 0)
{
lean_dec(v_val_4804_);
lean_dec_ref(v_pkg_4757_);
v_a_4813_ = v_a_4810_;
goto v___jp_4812_;
}
else
{
lean_object* v_val_4858_; uint8_t v___x_4859_; 
v_val_4858_ = lean_ctor_get(v_enableArtifactCache_x3f_4857_, 0);
v___x_4859_ = lean_unbox(v_val_4858_);
v_a_4817_ = v___x_4859_;
v_a_4818_ = v_a_4810_;
goto v___jp_4816_;
}
}
else
{
lean_object* v_val_4860_; uint8_t v___x_4861_; 
v_val_4860_ = lean_ctor_get(v_enableArtifactCache_x3f_4852_, 0);
v___x_4861_ = lean_unbox(v_val_4860_);
v_a_4817_ = v___x_4861_;
v_a_4818_ = v_a_4810_;
goto v___jp_4816_;
}
}
else
{
lean_object* v_val_4862_; uint8_t v___x_4863_; 
v_val_4862_ = lean_ctor_get(v_enableArtifactCache_x3f_4811_, 0);
v___x_4863_ = lean_unbox(v_val_4862_);
v_a_4817_ = v___x_4863_;
v_a_4818_ = v_a_4810_;
goto v___jp_4816_;
}
v___jp_4812_:
{
lean_object* v___x_4814_; lean_object* v___x_4815_; 
v___x_4814_ = lean_box(0);
v___x_4815_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4809_, v___x_4814_, v___y_4754_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_, v_a_4813_);
lean_dec_ref(v___y_4754_);
v___y_4785_ = v___x_4815_;
goto v___jp_4784_;
}
v___jp_4816_:
{
if (v_a_4817_ == 0)
{
lean_dec(v_val_4804_);
lean_dec_ref(v_pkg_4757_);
v_a_4813_ = v_a_4818_;
goto v___jp_4812_;
}
else
{
lean_object* v_toContext_4819_; lean_object* v_log_4820_; uint8_t v_action_4821_; uint8_t v_wantsRebuild_4822_; lean_object* v_trace_4823_; lean_object* v_buildTime_4824_; lean_object* v_lakeCache_4825_; lean_object* v___x_4826_; uint8_t v___x_4827_; lean_object* v___x_4828_; 
v_toContext_4819_ = lean_ctor_get(v_a_4761_, 1);
v_log_4820_ = lean_ctor_get(v_a_4818_, 0);
v_action_4821_ = lean_ctor_get_uint8(v_a_4818_, sizeof(void*)*3);
v_wantsRebuild_4822_ = lean_ctor_get_uint8(v_a_4818_, sizeof(void*)*3 + 1);
v_trace_4823_ = lean_ctor_get(v_a_4818_, 1);
v_buildTime_4824_ = lean_ctor_get(v_a_4818_, 2);
v_lakeCache_4825_ = lean_ctor_get(v_toContext_4819_, 2);
v___x_4826_ = l_Lake_Package_cacheScope(v_pkg_4757_);
v___x_4827_ = 0;
lean_inc_ref(v_lakeCache_4825_);
v___x_4828_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_4825_, v___x_4826_, v_inputHash_4755_, v_val_4804_, v___x_4805_, v___x_4805_, v___x_4827_);
if (lean_obj_tag(v___x_4828_) == 0)
{
lean_object* v___x_4829_; lean_object* v___x_4830_; 
lean_dec_ref_known(v___x_4828_, 1);
v___x_4829_ = lean_box(0);
v___x_4830_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4809_, v___x_4829_, v___y_4754_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_, v_a_4818_);
lean_dec_ref(v___y_4754_);
v___y_4785_ = v___x_4830_;
goto v___jp_4784_;
}
else
{
lean_object* v___x_4832_; uint8_t v_isShared_4833_; uint8_t v_isSharedCheck_4846_; 
lean_inc(v_buildTime_4824_);
lean_inc_ref(v_trace_4823_);
lean_inc_ref(v_log_4820_);
v_isSharedCheck_4846_ = !lean_is_exclusive(v_a_4818_);
if (v_isSharedCheck_4846_ == 0)
{
lean_object* v_unused_4847_; lean_object* v_unused_4848_; lean_object* v_unused_4849_; 
v_unused_4847_ = lean_ctor_get(v_a_4818_, 2);
lean_dec(v_unused_4847_);
v_unused_4848_ = lean_ctor_get(v_a_4818_, 1);
lean_dec(v_unused_4848_);
v_unused_4849_ = lean_ctor_get(v_a_4818_, 0);
lean_dec(v_unused_4849_);
v___x_4832_ = v_a_4818_;
v_isShared_4833_ = v_isSharedCheck_4846_;
goto v_resetjp_4831_;
}
else
{
lean_dec(v_a_4818_);
v___x_4832_ = lean_box(0);
v_isShared_4833_ = v_isSharedCheck_4846_;
goto v_resetjp_4831_;
}
v_resetjp_4831_:
{
lean_object* v_a_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; uint8_t v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4843_; 
v_a_4834_ = lean_ctor_get(v___x_4828_, 0);
lean_inc(v_a_4834_);
lean_dec_ref_known(v___x_4828_, 1);
v___x_4835_ = ((lean_object*)(l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0));
v___x_4836_ = lean_io_error_to_string(v_a_4834_);
v___x_4837_ = lean_string_append(v___x_4835_, v___x_4836_);
lean_dec_ref(v___x_4836_);
v___x_4838_ = 2;
v___x_4839_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4839_, 0, v___x_4837_);
lean_ctor_set_uint8(v___x_4839_, sizeof(void*)*1, v___x_4838_);
v___x_4840_ = lean_box(0);
v___x_4841_ = lean_array_push(v_log_4820_, v___x_4839_);
if (v_isShared_4833_ == 0)
{
lean_ctor_set(v___x_4832_, 0, v___x_4841_);
v___x_4843_ = v___x_4832_;
goto v_reusejp_4842_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v___x_4841_);
lean_ctor_set(v_reuseFailAlloc_4845_, 1, v_trace_4823_);
lean_ctor_set(v_reuseFailAlloc_4845_, 2, v_buildTime_4824_);
lean_ctor_set_uint8(v_reuseFailAlloc_4845_, sizeof(void*)*3, v_action_4821_);
lean_ctor_set_uint8(v_reuseFailAlloc_4845_, sizeof(void*)*3 + 1, v_wantsRebuild_4822_);
v___x_4843_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4842_;
}
v_reusejp_4842_:
{
lean_object* v___x_4844_; 
v___x_4844_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4809_, v___x_4840_, v___y_4754_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_, v___x_4843_);
lean_dec_ref(v___y_4754_);
v___y_4785_ = v___x_4844_;
goto v___jp_4784_;
}
}
}
}
}
}
else
{
lean_object* v_a_4864_; lean_object* v_a_4865_; 
lean_dec(v_val_4804_);
lean_dec_ref(v_pkg_4757_);
lean_dec_ref(v___y_4754_);
v_a_4864_ = lean_ctor_get(v___x_4807_, 0);
lean_inc(v_a_4864_);
v_a_4865_ = lean_ctor_get(v___x_4807_, 1);
lean_inc(v_a_4865_);
lean_dec_ref_known(v___x_4807_, 2);
v_a_4769_ = v_a_4864_;
v_a_4770_ = v_a_4865_;
goto v___jp_4768_;
}
}
else
{
lean_dec(v_outputs_x3f_4802_);
lean_dec_ref(v_pkg_4757_);
lean_dec_ref(v___y_4754_);
v___y_4765_ = v_a_4762_;
goto v___jp_4764_;
}
}
}
else
{
lean_dec_ref(v_pkg_4757_);
lean_dec(v_savedTrace_4756_);
lean_dec_ref(v___y_4754_);
v___y_4765_ = v_a_4762_;
goto v___jp_4764_;
}
v___jp_4764_:
{
lean_object* v___x_4766_; lean_object* v___x_4767_; 
v___x_4766_ = lean_box(0);
v___x_4767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4767_, 0, v___x_4766_);
lean_ctor_set(v___x_4767_, 1, v___y_4765_);
return v___x_4767_;
}
v___jp_4768_:
{
lean_object* v_log_4771_; uint8_t v_action_4772_; uint8_t v_wantsRebuild_4773_; lean_object* v_trace_4774_; lean_object* v_buildTime_4775_; lean_object* v___x_4777_; uint8_t v_isShared_4778_; uint8_t v_isSharedCheck_4783_; 
v_log_4771_ = lean_ctor_get(v_a_4770_, 0);
v_action_4772_ = lean_ctor_get_uint8(v_a_4770_, sizeof(void*)*3);
v_wantsRebuild_4773_ = lean_ctor_get_uint8(v_a_4770_, sizeof(void*)*3 + 1);
v_trace_4774_ = lean_ctor_get(v_a_4770_, 1);
v_buildTime_4775_ = lean_ctor_get(v_a_4770_, 2);
v_isSharedCheck_4783_ = !lean_is_exclusive(v_a_4770_);
if (v_isSharedCheck_4783_ == 0)
{
v___x_4777_ = v_a_4770_;
v_isShared_4778_ = v_isSharedCheck_4783_;
goto v_resetjp_4776_;
}
else
{
lean_inc(v_buildTime_4775_);
lean_inc(v_trace_4774_);
lean_inc(v_log_4771_);
lean_dec(v_a_4770_);
v___x_4777_ = lean_box(0);
v_isShared_4778_ = v_isSharedCheck_4783_;
goto v_resetjp_4776_;
}
v_resetjp_4776_:
{
lean_object* v___x_4779_; lean_object* v___x_4781_; 
v___x_4779_ = l_Array_shrink___redArg(v_log_4771_, v_a_4769_);
lean_dec(v_a_4769_);
if (v_isShared_4778_ == 0)
{
lean_ctor_set(v___x_4777_, 0, v___x_4779_);
v___x_4781_ = v___x_4777_;
goto v_reusejp_4780_;
}
else
{
lean_object* v_reuseFailAlloc_4782_; 
v_reuseFailAlloc_4782_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4782_, 0, v___x_4779_);
lean_ctor_set(v_reuseFailAlloc_4782_, 1, v_trace_4774_);
lean_ctor_set(v_reuseFailAlloc_4782_, 2, v_buildTime_4775_);
lean_ctor_set_uint8(v_reuseFailAlloc_4782_, sizeof(void*)*3, v_action_4772_);
lean_ctor_set_uint8(v_reuseFailAlloc_4782_, sizeof(void*)*3 + 1, v_wantsRebuild_4773_);
v___x_4781_ = v_reuseFailAlloc_4782_;
goto v_reusejp_4780_;
}
v_reusejp_4780_:
{
v___y_4765_ = v___x_4781_;
goto v___jp_4764_;
}
}
}
v___jp_4784_:
{
if (lean_obj_tag(v___y_4785_) == 0)
{
lean_object* v_a_4786_; 
v_a_4786_ = lean_ctor_get(v___y_4785_, 0);
if (lean_obj_tag(v_a_4786_) == 0)
{
lean_object* v_a_4787_; lean_object* v___x_4789_; uint8_t v_isShared_4790_; uint8_t v_isSharedCheck_4795_; 
lean_inc_ref(v_a_4786_);
v_a_4787_ = lean_ctor_get(v___y_4785_, 1);
v_isSharedCheck_4795_ = !lean_is_exclusive(v___y_4785_);
if (v_isSharedCheck_4795_ == 0)
{
lean_object* v_unused_4796_; 
v_unused_4796_ = lean_ctor_get(v___y_4785_, 0);
lean_dec(v_unused_4796_);
v___x_4789_ = v___y_4785_;
v_isShared_4790_ = v_isSharedCheck_4795_;
goto v_resetjp_4788_;
}
else
{
lean_inc(v_a_4787_);
lean_dec(v___y_4785_);
v___x_4789_ = lean_box(0);
v_isShared_4790_ = v_isSharedCheck_4795_;
goto v_resetjp_4788_;
}
v_resetjp_4788_:
{
lean_object* v_a_4791_; lean_object* v___x_4793_; 
v_a_4791_ = lean_ctor_get(v_a_4786_, 0);
lean_inc(v_a_4791_);
lean_dec_ref_known(v_a_4786_, 1);
if (v_isShared_4790_ == 0)
{
lean_ctor_set(v___x_4789_, 0, v_a_4791_);
v___x_4793_ = v___x_4789_;
goto v_reusejp_4792_;
}
else
{
lean_object* v_reuseFailAlloc_4794_; 
v_reuseFailAlloc_4794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4794_, 0, v_a_4791_);
lean_ctor_set(v_reuseFailAlloc_4794_, 1, v_a_4787_);
v___x_4793_ = v_reuseFailAlloc_4794_;
goto v_reusejp_4792_;
}
v_reusejp_4792_:
{
return v___x_4793_;
}
}
}
else
{
lean_object* v_a_4797_; 
v_a_4797_ = lean_ctor_get(v___y_4785_, 1);
lean_inc(v_a_4797_);
lean_dec_ref_known(v___y_4785_, 2);
v___y_4765_ = v_a_4797_;
goto v___jp_4764_;
}
}
else
{
lean_object* v_a_4798_; lean_object* v_a_4799_; 
v_a_4798_ = lean_ctor_get(v___y_4785_, 0);
lean_inc(v_a_4798_);
v_a_4799_ = lean_ctor_get(v___y_4785_, 1);
lean_inc(v_a_4799_);
lean_dec_ref_known(v___y_4785_, 2);
v_a_4769_ = v_a_4798_;
v_a_4770_ = v_a_4799_;
goto v___jp_4768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object* v_exe_4866_, lean_object* v___y_4867_, lean_object* v_inputHash_4868_, lean_object* v_savedTrace_4869_, lean_object* v_pkg_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_){
_start:
{
uint8_t v_exe_boxed_4877_; uint64_t v_inputHash_boxed_4878_; lean_object* v_res_4879_; 
v_exe_boxed_4877_ = lean_unbox(v_exe_4866_);
v_inputHash_boxed_4878_ = lean_unbox_uint64(v_inputHash_4868_);
lean_dec_ref(v_inputHash_4868_);
v_res_4879_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(v_exe_boxed_4877_, v___y_4867_, v_inputHash_boxed_4878_, v_savedTrace_4869_, v_pkg_4870_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_);
lean_dec_ref(v_a_4874_);
lean_dec(v_a_4873_);
lean_dec(v_a_4872_);
lean_dec(v_a_4871_);
return v_res_4879_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1(lean_object* v_as_4880_, size_t v_i_4881_, size_t v_stop_4882_, lean_object* v_b_4883_){
_start:
{
uint8_t v___x_4884_; 
v___x_4884_ = lean_usize_dec_eq(v_i_4881_, v_stop_4882_);
if (v___x_4884_ == 0)
{
lean_object* v___x_4885_; lean_object* v_message_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; size_t v___x_4890_; size_t v___x_4891_; 
v___x_4885_ = lean_array_uget_borrowed(v_as_4880_, v_i_4881_);
v_message_4886_ = lean_ctor_get(v___x_4885_, 0);
v___x_4887_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0));
v___x_4888_ = lean_string_append(v_b_4883_, v___x_4887_);
v___x_4889_ = lean_string_append(v___x_4888_, v_message_4886_);
v___x_4890_ = ((size_t)1ULL);
v___x_4891_ = lean_usize_add(v_i_4881_, v___x_4890_);
v_i_4881_ = v___x_4891_;
v_b_4883_ = v___x_4889_;
goto _start;
}
else
{
return v_b_4883_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1___boxed(lean_object* v_as_4893_, lean_object* v_i_4894_, lean_object* v_stop_4895_, lean_object* v_b_4896_){
_start:
{
size_t v_i_boxed_4897_; size_t v_stop_boxed_4898_; lean_object* v_res_4899_; 
v_i_boxed_4897_ = lean_unbox_usize(v_i_4894_);
lean_dec(v_i_4894_);
v_stop_boxed_4898_ = lean_unbox_usize(v_stop_4895_);
lean_dec(v_stop_4895_);
v_res_4899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1(v_as_4893_, v_i_boxed_4897_, v_stop_boxed_4898_, v_b_4896_);
lean_dec_ref(v_as_4893_);
return v_res_4899_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(uint8_t v_exe_4900_, lean_object* v___y_4901_, uint64_t v_inputHash_4902_, lean_object* v_pkg_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_){
_start:
{
lean_object* v_r_4911_; lean_object* v___y_4912_; lean_object* v___y_4915_; uint8_t v___y_4916_; lean_object* v___y_4917_; uint8_t v___y_4918_; lean_object* v___y_4919_; lean_object* v___y_4920_; lean_object* v_a_4927_; lean_object* v_log_4928_; uint8_t v_action_4929_; uint8_t v_wantsRebuild_4930_; lean_object* v_trace_4931_; lean_object* v_buildTime_4932_; lean_object* v_toContext_4953_; lean_object* v_log_4954_; uint8_t v_action_4955_; uint8_t v_wantsRebuild_4956_; lean_object* v_trace_4957_; lean_object* v_buildTime_4958_; lean_object* v___x_4960_; uint8_t v_isShared_4961_; uint8_t v_isSharedCheck_4991_; 
v_toContext_4953_ = lean_ctor_get(v_a_4907_, 1);
v_log_4954_ = lean_ctor_get(v_a_4908_, 0);
v_action_4955_ = lean_ctor_get_uint8(v_a_4908_, sizeof(void*)*3);
v_wantsRebuild_4956_ = lean_ctor_get_uint8(v_a_4908_, sizeof(void*)*3 + 1);
v_trace_4957_ = lean_ctor_get(v_a_4908_, 1);
v_buildTime_4958_ = lean_ctor_get(v_a_4908_, 2);
v_isSharedCheck_4991_ = !lean_is_exclusive(v_a_4908_);
if (v_isSharedCheck_4991_ == 0)
{
v___x_4960_ = v_a_4908_;
v_isShared_4961_ = v_isSharedCheck_4991_;
goto v_resetjp_4959_;
}
else
{
lean_inc(v_buildTime_4958_);
lean_inc(v_trace_4957_);
lean_inc(v_log_4954_);
lean_dec(v_a_4908_);
v___x_4960_ = lean_box(0);
v_isShared_4961_ = v_isSharedCheck_4991_;
goto v_resetjp_4959_;
}
v___jp_4910_:
{
lean_object* v___x_4913_; 
v___x_4913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4913_, 0, v_r_4911_);
lean_ctor_set(v___x_4913_, 1, v___y_4912_);
return v___x_4913_;
}
v___jp_4914_:
{
uint8_t v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; 
v___x_4921_ = 0;
v___x_4922_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4922_, 0, v___y_4920_);
lean_ctor_set_uint8(v___x_4922_, sizeof(void*)*1, v___x_4921_);
v___x_4923_ = lean_array_push(v___y_4919_, v___x_4922_);
v___x_4924_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4924_, 0, v___x_4923_);
lean_ctor_set(v___x_4924_, 1, v___y_4917_);
lean_ctor_set(v___x_4924_, 2, v___y_4915_);
lean_ctor_set_uint8(v___x_4924_, sizeof(void*)*3, v___y_4918_);
lean_ctor_set_uint8(v___x_4924_, sizeof(void*)*3 + 1, v___y_4916_);
v___x_4925_ = lean_box(0);
v_r_4911_ = v___x_4925_;
v___y_4912_ = v___x_4924_;
goto v___jp_4910_;
}
v___jp_4926_:
{
lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; uint8_t v___x_4949_; 
v___x_4933_ = lean_array_get_size(v_log_4928_);
lean_inc(v_a_4927_);
v___x_4934_ = l_Array_extract___redArg(v_log_4928_, v_a_4927_, v___x_4933_);
v___x_4935_ = l_Array_shrink___redArg(v_log_4928_, v_a_4927_);
lean_dec(v_a_4927_);
v___x_4936_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1));
v___x_4937_ = l_Lake_lowerHexUInt64(v_inputHash_4902_);
v___x_4938_ = lean_unsigned_to_nat(7u);
v___x_4939_ = lean_unsigned_to_nat(0u);
v___x_4940_ = lean_string_utf8_byte_size(v___x_4937_);
lean_inc_ref(v___x_4937_);
v___x_4941_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4941_, 0, v___x_4937_);
lean_ctor_set(v___x_4941_, 1, v___x_4939_);
lean_ctor_set(v___x_4941_, 2, v___x_4940_);
v___x_4942_ = l_String_Slice_Pos_nextn(v___x_4941_, v___x_4939_, v___x_4938_);
lean_dec_ref_known(v___x_4941_, 3);
v___x_4943_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4943_, 0, v___x_4937_);
lean_ctor_set(v___x_4943_, 1, v___x_4939_);
lean_ctor_set(v___x_4943_, 2, v___x_4942_);
v___x_4944_ = l_String_Slice_toString(v___x_4943_);
lean_dec_ref_known(v___x_4943_, 3);
v___x_4945_ = lean_string_append(v___x_4936_, v___x_4944_);
lean_dec_ref(v___x_4944_);
v___x_4946_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__2));
v___x_4947_ = lean_string_append(v___x_4945_, v___x_4946_);
v___x_4948_ = lean_array_get_size(v___x_4934_);
v___x_4949_ = lean_nat_dec_lt(v___x_4939_, v___x_4948_);
if (v___x_4949_ == 0)
{
lean_dec_ref(v___x_4934_);
v___y_4915_ = v_buildTime_4932_;
v___y_4916_ = v_wantsRebuild_4930_;
v___y_4917_ = v_trace_4931_;
v___y_4918_ = v_action_4929_;
v___y_4919_ = v___x_4935_;
v___y_4920_ = v___x_4947_;
goto v___jp_4914_;
}
else
{
size_t v___x_4950_; size_t v___x_4951_; lean_object* v___x_4952_; 
v___x_4950_ = ((size_t)0ULL);
v___x_4951_ = lean_usize_of_nat(v___x_4948_);
v___x_4952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1(v___x_4934_, v___x_4950_, v___x_4951_, v___x_4947_);
lean_dec_ref(v___x_4934_);
v___y_4915_ = v_buildTime_4932_;
v___y_4916_ = v_wantsRebuild_4930_;
v___y_4917_ = v_trace_4931_;
v___y_4918_ = v_action_4929_;
v___y_4919_ = v___x_4935_;
v___y_4920_ = v___x_4952_;
goto v___jp_4914_;
}
}
v_resetjp_4959_:
{
lean_object* v_lakeCache_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; 
v_lakeCache_4962_ = lean_ctor_get(v_toContext_4953_, 2);
v___x_4963_ = l_Lake_Package_cacheScope(v_pkg_4903_);
lean_inc_ref(v_lakeCache_4962_);
v___x_4964_ = l_Lake_Cache_readOutputs_x3f(v_lakeCache_4962_, v___x_4963_, v_inputHash_4902_, v_log_4954_);
if (lean_obj_tag(v___x_4964_) == 0)
{
lean_object* v_a_4965_; lean_object* v_a_4966_; lean_object* v___x_4968_; 
v_a_4965_ = lean_ctor_get(v___x_4964_, 0);
lean_inc(v_a_4965_);
v_a_4966_ = lean_ctor_get(v___x_4964_, 1);
lean_inc(v_a_4966_);
lean_dec_ref_known(v___x_4964_, 2);
if (v_isShared_4961_ == 0)
{
lean_ctor_set(v___x_4960_, 0, v_a_4966_);
v___x_4968_ = v___x_4960_;
goto v_reusejp_4967_;
}
else
{
lean_object* v_reuseFailAlloc_4988_; 
v_reuseFailAlloc_4988_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4988_, 0, v_a_4966_);
lean_ctor_set(v_reuseFailAlloc_4988_, 1, v_trace_4957_);
lean_ctor_set(v_reuseFailAlloc_4988_, 2, v_buildTime_4958_);
lean_ctor_set_uint8(v_reuseFailAlloc_4988_, sizeof(void*)*3, v_action_4955_);
lean_ctor_set_uint8(v_reuseFailAlloc_4988_, sizeof(void*)*3 + 1, v_wantsRebuild_4956_);
v___x_4968_ = v_reuseFailAlloc_4988_;
goto v_reusejp_4967_;
}
v_reusejp_4967_:
{
if (lean_obj_tag(v_a_4965_) == 0)
{
lean_object* v___x_4969_; 
lean_dec_ref(v___y_4901_);
v___x_4969_ = lean_box(0);
v_r_4911_ = v___x_4969_;
v___y_4912_ = v___x_4968_;
goto v___jp_4910_;
}
else
{
lean_object* v_val_4970_; lean_object* v___x_4972_; uint8_t v_isShared_4973_; uint8_t v_isSharedCheck_4987_; 
v_val_4970_ = lean_ctor_get(v_a_4965_, 0);
v_isSharedCheck_4987_ = !lean_is_exclusive(v_a_4965_);
if (v_isSharedCheck_4987_ == 0)
{
v___x_4972_ = v_a_4965_;
v_isShared_4973_ = v_isSharedCheck_4987_;
goto v_resetjp_4971_;
}
else
{
lean_inc(v_val_4970_);
lean_dec(v_a_4965_);
v___x_4972_ = lean_box(0);
v_isShared_4973_ = v_isSharedCheck_4987_;
goto v_resetjp_4971_;
}
v_resetjp_4971_:
{
lean_object* v___x_4974_; 
v___x_4974_ = l_Lake_resolveArtifactOutput(v_val_4970_, v_exe_4900_, v___y_4901_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v___x_4968_);
if (lean_obj_tag(v___x_4974_) == 0)
{
lean_object* v_a_4975_; lean_object* v_a_4976_; lean_object* v___x_4978_; 
v_a_4975_ = lean_ctor_get(v___x_4974_, 0);
lean_inc(v_a_4975_);
v_a_4976_ = lean_ctor_get(v___x_4974_, 1);
lean_inc(v_a_4976_);
lean_dec_ref_known(v___x_4974_, 2);
if (v_isShared_4973_ == 0)
{
lean_ctor_set(v___x_4972_, 0, v_a_4975_);
v___x_4978_ = v___x_4972_;
goto v_reusejp_4977_;
}
else
{
lean_object* v_reuseFailAlloc_4979_; 
v_reuseFailAlloc_4979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_a_4975_);
v___x_4978_ = v_reuseFailAlloc_4979_;
goto v_reusejp_4977_;
}
v_reusejp_4977_:
{
v_r_4911_ = v___x_4978_;
v___y_4912_ = v_a_4976_;
goto v___jp_4910_;
}
}
else
{
lean_object* v_a_4980_; lean_object* v_a_4981_; lean_object* v_log_4982_; uint8_t v_action_4983_; uint8_t v_wantsRebuild_4984_; lean_object* v_trace_4985_; lean_object* v_buildTime_4986_; 
lean_del_object(v___x_4972_);
v_a_4980_ = lean_ctor_get(v___x_4974_, 1);
lean_inc(v_a_4980_);
v_a_4981_ = lean_ctor_get(v___x_4974_, 0);
lean_inc(v_a_4981_);
lean_dec_ref_known(v___x_4974_, 2);
v_log_4982_ = lean_ctor_get(v_a_4980_, 0);
lean_inc_ref(v_log_4982_);
v_action_4983_ = lean_ctor_get_uint8(v_a_4980_, sizeof(void*)*3);
v_wantsRebuild_4984_ = lean_ctor_get_uint8(v_a_4980_, sizeof(void*)*3 + 1);
v_trace_4985_ = lean_ctor_get(v_a_4980_, 1);
lean_inc_ref(v_trace_4985_);
v_buildTime_4986_ = lean_ctor_get(v_a_4980_, 2);
lean_inc(v_buildTime_4986_);
lean_dec(v_a_4980_);
v_a_4927_ = v_a_4981_;
v_log_4928_ = v_log_4982_;
v_action_4929_ = v_action_4983_;
v_wantsRebuild_4930_ = v_wantsRebuild_4984_;
v_trace_4931_ = v_trace_4985_;
v_buildTime_4932_ = v_buildTime_4986_;
goto v___jp_4926_;
}
}
}
}
}
else
{
lean_object* v_a_4989_; lean_object* v_a_4990_; 
lean_del_object(v___x_4960_);
lean_dec_ref(v___y_4901_);
v_a_4989_ = lean_ctor_get(v___x_4964_, 0);
lean_inc(v_a_4989_);
v_a_4990_ = lean_ctor_get(v___x_4964_, 1);
lean_inc(v_a_4990_);
lean_dec_ref_known(v___x_4964_, 2);
v_a_4927_ = v_a_4989_;
v_log_4928_ = v_a_4990_;
v_action_4929_ = v_action_4955_;
v_wantsRebuild_4930_ = v_wantsRebuild_4956_;
v_trace_4931_ = v_trace_4957_;
v_buildTime_4932_ = v_buildTime_4958_;
goto v___jp_4926_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___boxed(lean_object* v_exe_4992_, lean_object* v___y_4993_, lean_object* v_inputHash_4994_, lean_object* v_pkg_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_){
_start:
{
uint8_t v_exe_boxed_5002_; uint64_t v_inputHash_boxed_5003_; lean_object* v_res_5004_; 
v_exe_boxed_5002_ = lean_unbox(v_exe_4992_);
v_inputHash_boxed_5003_ = lean_unbox_uint64(v_inputHash_4994_);
lean_dec_ref(v_inputHash_4994_);
v_res_5004_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(v_exe_boxed_5002_, v___y_4993_, v_inputHash_boxed_5003_, v_pkg_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_);
lean_dec_ref(v_a_4999_);
lean_dec(v_a_4998_);
lean_dec(v_a_4997_);
lean_dec(v_a_4996_);
return v_res_5004_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(lean_object* v_file_5005_, uint8_t v_exe_5006_, uint64_t v_hash_5007_, lean_object* v___x_5008_, lean_object* v_a_5009_, lean_object* v_val_5010_, uint8_t v_restore_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_){
_start:
{
lean_object* v_a_5020_; lean_object* v___y_5024_; lean_object* v___y_5025_; lean_object* v___y_5026_; uint8_t v___y_5064_; lean_object* v___y_5065_; lean_object* v___y_5066_; lean_object* v___y_5067_; lean_object* v___y_5068_; lean_object* v___y_5069_; uint8_t v___y_5070_; lean_object* v___y_5071_; lean_object* v_a_5085_; lean_object* v_val_5086_; lean_object* v_a_5087_; lean_object* v_a_5141_; lean_object* v___y_5142_; lean_object* v___x_5144_; lean_object* v_a_5145_; 
lean_inc_ref(v_val_5010_);
lean_inc(v_a_5009_);
lean_inc_ref(v___y_5012_);
v___x_5144_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(v_exe_5006_, v___y_5012_, v_hash_5007_, v_a_5009_, v_val_5010_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_);
v_a_5145_ = lean_ctor_get(v___x_5144_, 0);
lean_inc(v_a_5145_);
if (lean_obj_tag(v_a_5145_) == 1)
{
lean_object* v_a_5146_; lean_object* v_val_5147_; 
lean_dec_ref(v___y_5012_);
lean_dec_ref(v_val_5010_);
v_a_5146_ = lean_ctor_get(v___x_5144_, 1);
lean_inc(v_a_5146_);
lean_dec_ref(v___x_5144_);
v_val_5147_ = lean_ctor_get(v_a_5145_, 0);
lean_inc(v_val_5147_);
lean_dec_ref_known(v_a_5145_, 1);
v_a_5141_ = v_val_5147_;
v___y_5142_ = v_a_5146_;
goto v___jp_5140_;
}
else
{
lean_object* v_a_5148_; lean_object* v___x_5149_; lean_object* v_a_5150_; 
lean_dec(v_a_5145_);
v_a_5148_ = lean_ctor_get(v___x_5144_, 1);
lean_inc(v_a_5148_);
lean_dec_ref(v___x_5144_);
v___x_5149_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(v_exe_5006_, v___y_5012_, v_hash_5007_, v_val_5010_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v_a_5148_);
v_a_5150_ = lean_ctor_get(v___x_5149_, 0);
lean_inc(v_a_5150_);
if (lean_obj_tag(v_a_5150_) == 1)
{
lean_object* v_a_5151_; lean_object* v_val_5152_; 
v_a_5151_ = lean_ctor_get(v___x_5149_, 1);
lean_inc(v_a_5151_);
lean_dec_ref(v___x_5149_);
v_val_5152_ = lean_ctor_get(v_a_5150_, 0);
lean_inc(v_val_5152_);
lean_dec_ref_known(v_a_5150_, 1);
v_a_5141_ = v_val_5152_;
v___y_5142_ = v_a_5151_;
goto v___jp_5140_;
}
else
{
lean_object* v_a_5153_; 
lean_dec(v_a_5150_);
lean_dec(v_a_5009_);
lean_dec_ref(v___x_5008_);
lean_dec_ref(v_file_5005_);
v_a_5153_ = lean_ctor_get(v___x_5149_, 1);
lean_inc(v_a_5153_);
lean_dec_ref(v___x_5149_);
v_a_5020_ = v_a_5153_;
goto v___jp_5019_;
}
}
v___jp_5019_:
{
lean_object* v___x_5021_; lean_object* v___x_5022_; 
v___x_5021_ = lean_box(0);
v___x_5022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5022_, 0, v___x_5021_);
lean_ctor_set(v___x_5022_, 1, v_a_5020_);
return v___x_5022_;
}
v___jp_5023_:
{
if (v_restore_5011_ == 0)
{
lean_object* v___x_5027_; 
lean_dec_ref(v___y_5024_);
lean_dec_ref(v_file_5005_);
v___x_5027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5027_, 0, v___y_5025_);
lean_ctor_set(v___x_5027_, 1, v___y_5026_);
return v___x_5027_;
}
else
{
lean_object* v_log_5028_; uint8_t v_action_5029_; uint8_t v_wantsRebuild_5030_; lean_object* v_trace_5031_; lean_object* v_buildTime_5032_; lean_object* v___x_5034_; uint8_t v_isShared_5035_; uint8_t v_isSharedCheck_5062_; 
lean_dec(v___y_5025_);
v_log_5028_ = lean_ctor_get(v___y_5026_, 0);
v_action_5029_ = lean_ctor_get_uint8(v___y_5026_, sizeof(void*)*3);
v_wantsRebuild_5030_ = lean_ctor_get_uint8(v___y_5026_, sizeof(void*)*3 + 1);
v_trace_5031_ = lean_ctor_get(v___y_5026_, 1);
v_buildTime_5032_ = lean_ctor_get(v___y_5026_, 2);
v_isSharedCheck_5062_ = !lean_is_exclusive(v___y_5026_);
if (v_isSharedCheck_5062_ == 0)
{
v___x_5034_ = v___y_5026_;
v_isShared_5035_ = v_isSharedCheck_5062_;
goto v_resetjp_5033_;
}
else
{
lean_inc(v_buildTime_5032_);
lean_inc(v_trace_5031_);
lean_inc(v_log_5028_);
lean_dec(v___y_5026_);
v___x_5034_ = lean_box(0);
v_isShared_5035_ = v_isSharedCheck_5062_;
goto v_resetjp_5033_;
}
v_resetjp_5033_:
{
lean_object* v___x_5036_; 
v___x_5036_ = l_Lake_restoreArtifact(v_file_5005_, v___y_5024_, v_exe_5006_, v_log_5028_);
if (lean_obj_tag(v___x_5036_) == 0)
{
lean_object* v_a_5037_; lean_object* v_a_5038_; lean_object* v___x_5040_; uint8_t v_isShared_5041_; uint8_t v_isSharedCheck_5049_; 
v_a_5037_ = lean_ctor_get(v___x_5036_, 0);
v_a_5038_ = lean_ctor_get(v___x_5036_, 1);
v_isSharedCheck_5049_ = !lean_is_exclusive(v___x_5036_);
if (v_isSharedCheck_5049_ == 0)
{
v___x_5040_ = v___x_5036_;
v_isShared_5041_ = v_isSharedCheck_5049_;
goto v_resetjp_5039_;
}
else
{
lean_inc(v_a_5038_);
lean_inc(v_a_5037_);
lean_dec(v___x_5036_);
v___x_5040_ = lean_box(0);
v_isShared_5041_ = v_isSharedCheck_5049_;
goto v_resetjp_5039_;
}
v_resetjp_5039_:
{
lean_object* v___x_5043_; 
if (v_isShared_5035_ == 0)
{
lean_ctor_set(v___x_5034_, 0, v_a_5038_);
v___x_5043_ = v___x_5034_;
goto v_reusejp_5042_;
}
else
{
lean_object* v_reuseFailAlloc_5048_; 
v_reuseFailAlloc_5048_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5048_, 0, v_a_5038_);
lean_ctor_set(v_reuseFailAlloc_5048_, 1, v_trace_5031_);
lean_ctor_set(v_reuseFailAlloc_5048_, 2, v_buildTime_5032_);
lean_ctor_set_uint8(v_reuseFailAlloc_5048_, sizeof(void*)*3, v_action_5029_);
lean_ctor_set_uint8(v_reuseFailAlloc_5048_, sizeof(void*)*3 + 1, v_wantsRebuild_5030_);
v___x_5043_ = v_reuseFailAlloc_5048_;
goto v_reusejp_5042_;
}
v_reusejp_5042_:
{
lean_object* v___x_5044_; lean_object* v___x_5046_; 
v___x_5044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5044_, 0, v_a_5037_);
if (v_isShared_5041_ == 0)
{
lean_ctor_set(v___x_5040_, 1, v___x_5043_);
lean_ctor_set(v___x_5040_, 0, v___x_5044_);
v___x_5046_ = v___x_5040_;
goto v_reusejp_5045_;
}
else
{
lean_object* v_reuseFailAlloc_5047_; 
v_reuseFailAlloc_5047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5047_, 0, v___x_5044_);
lean_ctor_set(v_reuseFailAlloc_5047_, 1, v___x_5043_);
v___x_5046_ = v_reuseFailAlloc_5047_;
goto v_reusejp_5045_;
}
v_reusejp_5045_:
{
return v___x_5046_;
}
}
}
}
else
{
lean_object* v_a_5050_; lean_object* v_a_5051_; lean_object* v___x_5053_; uint8_t v_isShared_5054_; uint8_t v_isSharedCheck_5061_; 
v_a_5050_ = lean_ctor_get(v___x_5036_, 0);
v_a_5051_ = lean_ctor_get(v___x_5036_, 1);
v_isSharedCheck_5061_ = !lean_is_exclusive(v___x_5036_);
if (v_isSharedCheck_5061_ == 0)
{
v___x_5053_ = v___x_5036_;
v_isShared_5054_ = v_isSharedCheck_5061_;
goto v_resetjp_5052_;
}
else
{
lean_inc(v_a_5051_);
lean_inc(v_a_5050_);
lean_dec(v___x_5036_);
v___x_5053_ = lean_box(0);
v_isShared_5054_ = v_isSharedCheck_5061_;
goto v_resetjp_5052_;
}
v_resetjp_5052_:
{
lean_object* v___x_5056_; 
if (v_isShared_5035_ == 0)
{
lean_ctor_set(v___x_5034_, 0, v_a_5051_);
v___x_5056_ = v___x_5034_;
goto v_reusejp_5055_;
}
else
{
lean_object* v_reuseFailAlloc_5060_; 
v_reuseFailAlloc_5060_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5060_, 0, v_a_5051_);
lean_ctor_set(v_reuseFailAlloc_5060_, 1, v_trace_5031_);
lean_ctor_set(v_reuseFailAlloc_5060_, 2, v_buildTime_5032_);
lean_ctor_set_uint8(v_reuseFailAlloc_5060_, sizeof(void*)*3, v_action_5029_);
lean_ctor_set_uint8(v_reuseFailAlloc_5060_, sizeof(void*)*3 + 1, v_wantsRebuild_5030_);
v___x_5056_ = v_reuseFailAlloc_5060_;
goto v_reusejp_5055_;
}
v_reusejp_5055_:
{
lean_object* v___x_5058_; 
if (v_isShared_5054_ == 0)
{
lean_ctor_set(v___x_5053_, 1, v___x_5056_);
v___x_5058_ = v___x_5053_;
goto v_reusejp_5057_;
}
else
{
lean_object* v_reuseFailAlloc_5059_; 
v_reuseFailAlloc_5059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5059_, 0, v_a_5050_);
lean_ctor_set(v_reuseFailAlloc_5059_, 1, v___x_5056_);
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
}
}
}
v___jp_5063_:
{
lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; 
v___x_5072_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5072_, 0, v___y_5071_);
v___x_5073_ = l_Lake_BuildMetadata_ofFetch(v_hash_5007_, v___x_5072_);
v___x_5074_ = l_Lake_BuildMetadata_writeFile(v___x_5008_, v___x_5073_);
if (lean_obj_tag(v___x_5074_) == 0)
{
lean_object* v___x_5075_; 
lean_dec_ref_known(v___x_5074_, 1);
v___x_5075_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5075_, 0, v___y_5068_);
lean_ctor_set(v___x_5075_, 1, v___y_5069_);
lean_ctor_set(v___x_5075_, 2, v___y_5067_);
lean_ctor_set_uint8(v___x_5075_, sizeof(void*)*3, v___y_5064_);
lean_ctor_set_uint8(v___x_5075_, sizeof(void*)*3 + 1, v___y_5070_);
v___y_5024_ = v___y_5065_;
v___y_5025_ = v___y_5066_;
v___y_5026_ = v___x_5075_;
goto v___jp_5023_;
}
else
{
lean_object* v_a_5076_; lean_object* v___x_5077_; uint8_t v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; 
lean_dec(v___y_5066_);
lean_dec_ref(v___y_5065_);
lean_dec_ref(v_file_5005_);
v_a_5076_ = lean_ctor_get(v___x_5074_, 0);
lean_inc(v_a_5076_);
lean_dec_ref_known(v___x_5074_, 1);
v___x_5077_ = lean_io_error_to_string(v_a_5076_);
v___x_5078_ = 3;
v___x_5079_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5079_, 0, v___x_5077_);
lean_ctor_set_uint8(v___x_5079_, sizeof(void*)*1, v___x_5078_);
v___x_5080_ = lean_array_get_size(v___y_5068_);
v___x_5081_ = lean_array_push(v___y_5068_, v___x_5079_);
v___x_5082_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5082_, 0, v___x_5081_);
lean_ctor_set(v___x_5082_, 1, v___y_5069_);
lean_ctor_set(v___x_5082_, 2, v___y_5067_);
lean_ctor_set_uint8(v___x_5082_, sizeof(void*)*3, v___y_5064_);
lean_ctor_set_uint8(v___x_5082_, sizeof(void*)*3 + 1, v___y_5070_);
v___x_5083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5083_, 0, v___x_5080_);
lean_ctor_set(v___x_5083_, 1, v___x_5082_);
return v___x_5083_;
}
}
v___jp_5084_:
{
lean_object* v___x_5088_; 
v___x_5088_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_hash_5007_, v_a_5009_, v_a_5087_);
lean_dec(v_a_5009_);
if (lean_obj_tag(v___x_5088_) == 0)
{
lean_object* v_a_5089_; uint8_t v___x_5090_; 
v_a_5089_ = lean_ctor_get(v___x_5088_, 0);
lean_inc(v_a_5089_);
v___x_5090_ = lean_unbox(v_a_5089_);
lean_dec(v_a_5089_);
if (v___x_5090_ == 0)
{
lean_object* v_a_5091_; lean_object* v___x_5093_; uint8_t v_isShared_5094_; uint8_t v_isSharedCheck_5128_; 
v_a_5091_ = lean_ctor_get(v___x_5088_, 1);
v_isSharedCheck_5128_ = !lean_is_exclusive(v___x_5088_);
if (v_isSharedCheck_5128_ == 0)
{
lean_object* v_unused_5129_; 
v_unused_5129_ = lean_ctor_get(v___x_5088_, 0);
lean_dec(v_unused_5129_);
v___x_5093_ = v___x_5088_;
v_isShared_5094_ = v_isSharedCheck_5128_;
goto v_resetjp_5092_;
}
else
{
lean_inc(v_a_5091_);
lean_dec(v___x_5088_);
v___x_5093_ = lean_box(0);
v_isShared_5094_ = v_isSharedCheck_5128_;
goto v_resetjp_5092_;
}
v_resetjp_5092_:
{
lean_object* v_log_5095_; uint8_t v_action_5096_; uint8_t v_wantsRebuild_5097_; lean_object* v_trace_5098_; lean_object* v_buildTime_5099_; lean_object* v___x_5101_; uint8_t v_isShared_5102_; uint8_t v_isSharedCheck_5127_; 
v_log_5095_ = lean_ctor_get(v_a_5091_, 0);
v_action_5096_ = lean_ctor_get_uint8(v_a_5091_, sizeof(void*)*3);
v_wantsRebuild_5097_ = lean_ctor_get_uint8(v_a_5091_, sizeof(void*)*3 + 1);
v_trace_5098_ = lean_ctor_get(v_a_5091_, 1);
v_buildTime_5099_ = lean_ctor_get(v_a_5091_, 2);
v_isSharedCheck_5127_ = !lean_is_exclusive(v_a_5091_);
if (v_isSharedCheck_5127_ == 0)
{
v___x_5101_ = v_a_5091_;
v_isShared_5102_ = v_isSharedCheck_5127_;
goto v_resetjp_5100_;
}
else
{
lean_inc(v_buildTime_5099_);
lean_inc(v_trace_5098_);
lean_inc(v_log_5095_);
lean_dec(v_a_5091_);
v___x_5101_ = lean_box(0);
v_isShared_5102_ = v_isSharedCheck_5127_;
goto v_resetjp_5100_;
}
v_resetjp_5100_:
{
lean_object* v___x_5103_; 
v___x_5103_ = l_Lake_removeFileIfExists(v_file_5005_);
if (lean_obj_tag(v___x_5103_) == 0)
{
lean_object* v_descr_5104_; uint64_t v_hash_5105_; lean_object* v_ext_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; uint8_t v___x_5109_; 
lean_dec_ref_known(v___x_5103_, 1);
lean_del_object(v___x_5101_);
lean_del_object(v___x_5093_);
v_descr_5104_ = lean_ctor_get(v_val_5086_, 0);
v_hash_5105_ = lean_ctor_get_uint64(v_descr_5104_, sizeof(void*)*1);
v_ext_5106_ = lean_ctor_get(v_descr_5104_, 0);
v___x_5107_ = lean_string_utf8_byte_size(v_ext_5106_);
v___x_5108_ = lean_unsigned_to_nat(0u);
v___x_5109_ = lean_nat_dec_eq(v___x_5107_, v___x_5108_);
if (v___x_5109_ == 0)
{
lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; 
v___x_5110_ = l_Lake_lowerHexUInt64(v_hash_5105_);
v___x_5111_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5112_ = lean_string_append(v___x_5110_, v___x_5111_);
v___x_5113_ = lean_string_append(v___x_5112_, v_ext_5106_);
v___y_5064_ = v_action_5096_;
v___y_5065_ = v_val_5086_;
v___y_5066_ = v_a_5085_;
v___y_5067_ = v_buildTime_5099_;
v___y_5068_ = v_log_5095_;
v___y_5069_ = v_trace_5098_;
v___y_5070_ = v_wantsRebuild_5097_;
v___y_5071_ = v___x_5113_;
goto v___jp_5063_;
}
else
{
lean_object* v___x_5114_; 
v___x_5114_ = l_Lake_lowerHexUInt64(v_hash_5105_);
v___y_5064_ = v_action_5096_;
v___y_5065_ = v_val_5086_;
v___y_5066_ = v_a_5085_;
v___y_5067_ = v_buildTime_5099_;
v___y_5068_ = v_log_5095_;
v___y_5069_ = v_trace_5098_;
v___y_5070_ = v_wantsRebuild_5097_;
v___y_5071_ = v___x_5114_;
goto v___jp_5063_;
}
}
else
{
lean_object* v_a_5115_; lean_object* v___x_5116_; uint8_t v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5122_; 
lean_dec_ref(v_val_5086_);
lean_dec(v_a_5085_);
lean_dec_ref(v___x_5008_);
lean_dec_ref(v_file_5005_);
v_a_5115_ = lean_ctor_get(v___x_5103_, 0);
lean_inc(v_a_5115_);
lean_dec_ref_known(v___x_5103_, 1);
v___x_5116_ = lean_io_error_to_string(v_a_5115_);
v___x_5117_ = 3;
v___x_5118_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5118_, 0, v___x_5116_);
lean_ctor_set_uint8(v___x_5118_, sizeof(void*)*1, v___x_5117_);
v___x_5119_ = lean_array_get_size(v_log_5095_);
v___x_5120_ = lean_array_push(v_log_5095_, v___x_5118_);
if (v_isShared_5102_ == 0)
{
lean_ctor_set(v___x_5101_, 0, v___x_5120_);
v___x_5122_ = v___x_5101_;
goto v_reusejp_5121_;
}
else
{
lean_object* v_reuseFailAlloc_5126_; 
v_reuseFailAlloc_5126_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5126_, 0, v___x_5120_);
lean_ctor_set(v_reuseFailAlloc_5126_, 1, v_trace_5098_);
lean_ctor_set(v_reuseFailAlloc_5126_, 2, v_buildTime_5099_);
lean_ctor_set_uint8(v_reuseFailAlloc_5126_, sizeof(void*)*3, v_action_5096_);
lean_ctor_set_uint8(v_reuseFailAlloc_5126_, sizeof(void*)*3 + 1, v_wantsRebuild_5097_);
v___x_5122_ = v_reuseFailAlloc_5126_;
goto v_reusejp_5121_;
}
v_reusejp_5121_:
{
lean_object* v___x_5124_; 
if (v_isShared_5094_ == 0)
{
lean_ctor_set_tag(v___x_5093_, 1);
lean_ctor_set(v___x_5093_, 1, v___x_5122_);
lean_ctor_set(v___x_5093_, 0, v___x_5119_);
v___x_5124_ = v___x_5093_;
goto v_reusejp_5123_;
}
else
{
lean_object* v_reuseFailAlloc_5125_; 
v_reuseFailAlloc_5125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5125_, 0, v___x_5119_);
lean_ctor_set(v_reuseFailAlloc_5125_, 1, v___x_5122_);
v___x_5124_ = v_reuseFailAlloc_5125_;
goto v_reusejp_5123_;
}
v_reusejp_5123_:
{
return v___x_5124_;
}
}
}
}
}
}
else
{
lean_object* v_a_5130_; 
lean_dec_ref(v___x_5008_);
v_a_5130_ = lean_ctor_get(v___x_5088_, 1);
lean_inc(v_a_5130_);
lean_dec_ref_known(v___x_5088_, 2);
v___y_5024_ = v_val_5086_;
v___y_5025_ = v_a_5085_;
v___y_5026_ = v_a_5130_;
goto v___jp_5023_;
}
}
else
{
lean_object* v_a_5131_; lean_object* v_a_5132_; lean_object* v___x_5134_; uint8_t v_isShared_5135_; uint8_t v_isSharedCheck_5139_; 
lean_dec_ref(v_val_5086_);
lean_dec(v_a_5085_);
lean_dec_ref(v___x_5008_);
lean_dec_ref(v_file_5005_);
v_a_5131_ = lean_ctor_get(v___x_5088_, 0);
v_a_5132_ = lean_ctor_get(v___x_5088_, 1);
v_isSharedCheck_5139_ = !lean_is_exclusive(v___x_5088_);
if (v_isSharedCheck_5139_ == 0)
{
v___x_5134_ = v___x_5088_;
v_isShared_5135_ = v_isSharedCheck_5139_;
goto v_resetjp_5133_;
}
else
{
lean_inc(v_a_5132_);
lean_inc(v_a_5131_);
lean_dec(v___x_5088_);
v___x_5134_ = lean_box(0);
v_isShared_5135_ = v_isSharedCheck_5139_;
goto v_resetjp_5133_;
}
v_resetjp_5133_:
{
lean_object* v___x_5137_; 
if (v_isShared_5135_ == 0)
{
v___x_5137_ = v___x_5134_;
goto v_reusejp_5136_;
}
else
{
lean_object* v_reuseFailAlloc_5138_; 
v_reuseFailAlloc_5138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5138_, 0, v_a_5131_);
lean_ctor_set(v_reuseFailAlloc_5138_, 1, v_a_5132_);
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
v___jp_5140_:
{
lean_object* v___x_5143_; 
lean_inc_ref(v_a_5141_);
v___x_5143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5143_, 0, v_a_5141_);
v_a_5085_ = v___x_5143_;
v_val_5086_ = v_a_5141_;
v_a_5087_ = v___y_5142_;
goto v___jp_5084_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object* v_file_5154_, lean_object* v_exe_5155_, lean_object* v_hash_5156_, lean_object* v___x_5157_, lean_object* v_a_5158_, lean_object* v_val_5159_, lean_object* v_restore_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_){
_start:
{
uint8_t v_exe_boxed_5168_; uint64_t v_hash_boxed_5169_; uint8_t v_restore_boxed_5170_; lean_object* v_res_5171_; 
v_exe_boxed_5168_ = lean_unbox(v_exe_5155_);
v_hash_boxed_5169_ = lean_unbox_uint64(v_hash_5156_);
lean_dec_ref(v_hash_5156_);
v_restore_boxed_5170_ = lean_unbox(v_restore_5160_);
v_res_5171_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_file_5154_, v_exe_boxed_5168_, v_hash_boxed_5169_, v___x_5157_, v_a_5158_, v_val_5159_, v_restore_boxed_5170_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_, v___y_5166_);
lean_dec_ref(v___y_5165_);
lean_dec(v___y_5164_);
lean_dec(v___y_5163_);
lean_dec(v___y_5162_);
return v_res_5171_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1(uint8_t v_a_5172_, lean_object* v_file_5173_, lean_object* v_ext_5174_, uint8_t v_text_5175_, uint8_t v_exe_5176_, uint8_t v___y_5177_, lean_object* v_val_5178_, uint64_t v_hash_5179_, uint8_t v_a_5180_, lean_object* v_____r_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_){
_start:
{
lean_object* v___x_5189_; lean_object* v___x_5190_; uint8_t v___x_5191_; 
v___x_5189_ = l_Lake_OutputStatus_ctorIdx(v_a_5172_);
v___x_5190_ = lean_obj_once(&l_Lake_OutputStatus_isCacheable___closed__0, &l_Lake_OutputStatus_isCacheable___closed__0_once, _init_l_Lake_OutputStatus_isCacheable___closed__0);
v___x_5191_ = lean_nat_dec_eq(v___x_5189_, v___x_5190_);
lean_dec(v___x_5189_);
if (v___x_5191_ == 0)
{
lean_object* v_toContext_5192_; lean_object* v_log_5193_; uint8_t v_action_5194_; uint8_t v_wantsRebuild_5195_; lean_object* v_trace_5196_; lean_object* v_buildTime_5197_; lean_object* v_lakeCache_5198_; lean_object* v___x_5199_; 
v_toContext_5192_ = lean_ctor_get(v___y_5186_, 1);
v_log_5193_ = lean_ctor_get(v___y_5187_, 0);
v_action_5194_ = lean_ctor_get_uint8(v___y_5187_, sizeof(void*)*3);
v_wantsRebuild_5195_ = lean_ctor_get_uint8(v___y_5187_, sizeof(void*)*3 + 1);
v_trace_5196_ = lean_ctor_get(v___y_5187_, 1);
v_buildTime_5197_ = lean_ctor_get(v___y_5187_, 2);
v_lakeCache_5198_ = lean_ctor_get(v_toContext_5192_, 2);
lean_inc_ref(v_lakeCache_5198_);
v___x_5199_ = l_Lake_Cache_saveArtifact(v_lakeCache_5198_, v_file_5173_, v_ext_5174_, v_text_5175_, v_exe_5176_, v___y_5177_);
if (lean_obj_tag(v___x_5199_) == 0)
{
lean_object* v_a_5200_; lean_object* v___x_5202_; uint8_t v_isShared_5203_; uint8_t v_isSharedCheck_5241_; 
v_a_5200_ = lean_ctor_get(v___x_5199_, 0);
v_isSharedCheck_5241_ = !lean_is_exclusive(v___x_5199_);
if (v_isSharedCheck_5241_ == 0)
{
v___x_5202_ = v___x_5199_;
v_isShared_5203_ = v_isSharedCheck_5241_;
goto v_resetjp_5201_;
}
else
{
lean_inc(v_a_5200_);
lean_dec(v___x_5199_);
v___x_5202_ = lean_box(0);
v_isShared_5203_ = v_isSharedCheck_5241_;
goto v_resetjp_5201_;
}
v_resetjp_5201_:
{
lean_object* v_descr_5204_; uint64_t v_hash_5205_; lean_object* v_ext_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___y_5210_; lean_object* v___x_5233_; lean_object* v___x_5234_; uint8_t v___x_5235_; 
v_descr_5204_ = lean_ctor_get(v_a_5200_, 0);
v_hash_5205_ = lean_ctor_get_uint64(v_descr_5204_, sizeof(void*)*1);
v_ext_5206_ = lean_ctor_get(v_descr_5204_, 0);
v___x_5207_ = l_Lake_Package_cacheScope(v_val_5178_);
v___x_5208_ = lean_box(0);
v___x_5233_ = lean_string_utf8_byte_size(v_ext_5206_);
v___x_5234_ = lean_unsigned_to_nat(0u);
v___x_5235_ = lean_nat_dec_eq(v___x_5233_, v___x_5234_);
if (v___x_5235_ == 0)
{
lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; 
v___x_5236_ = l_Lake_lowerHexUInt64(v_hash_5205_);
v___x_5237_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5238_ = lean_string_append(v___x_5236_, v___x_5237_);
v___x_5239_ = lean_string_append(v___x_5238_, v_ext_5206_);
v___y_5210_ = v___x_5239_;
goto v___jp_5209_;
}
else
{
lean_object* v___x_5240_; 
v___x_5240_ = l_Lake_lowerHexUInt64(v_hash_5205_);
v___y_5210_ = v___x_5240_;
goto v___jp_5209_;
}
v___jp_5209_:
{
lean_object* v___x_5212_; 
if (v_isShared_5203_ == 0)
{
lean_ctor_set_tag(v___x_5202_, 3);
lean_ctor_set(v___x_5202_, 0, v___y_5210_);
v___x_5212_ = v___x_5202_;
goto v_reusejp_5211_;
}
else
{
lean_object* v_reuseFailAlloc_5232_; 
v_reuseFailAlloc_5232_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5232_, 0, v___y_5210_);
v___x_5212_ = v_reuseFailAlloc_5232_;
goto v_reusejp_5211_;
}
v_reusejp_5211_:
{
lean_object* v___x_5213_; 
lean_inc_ref(v_lakeCache_5198_);
v___x_5213_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_5198_, v___x_5207_, v_hash_5179_, v___x_5212_, v___x_5208_, v___x_5208_, v_a_5180_);
if (lean_obj_tag(v___x_5213_) == 0)
{
lean_object* v___x_5214_; 
lean_dec_ref_known(v___x_5213_, 1);
v___x_5214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5214_, 0, v_a_5200_);
lean_ctor_set(v___x_5214_, 1, v___y_5187_);
return v___x_5214_;
}
else
{
lean_object* v___x_5216_; uint8_t v_isShared_5217_; uint8_t v_isSharedCheck_5228_; 
lean_inc(v_buildTime_5197_);
lean_inc_ref(v_trace_5196_);
lean_inc_ref(v_log_5193_);
lean_dec(v_a_5200_);
v_isSharedCheck_5228_ = !lean_is_exclusive(v___y_5187_);
if (v_isSharedCheck_5228_ == 0)
{
lean_object* v_unused_5229_; lean_object* v_unused_5230_; lean_object* v_unused_5231_; 
v_unused_5229_ = lean_ctor_get(v___y_5187_, 2);
lean_dec(v_unused_5229_);
v_unused_5230_ = lean_ctor_get(v___y_5187_, 1);
lean_dec(v_unused_5230_);
v_unused_5231_ = lean_ctor_get(v___y_5187_, 0);
lean_dec(v_unused_5231_);
v___x_5216_ = v___y_5187_;
v_isShared_5217_ = v_isSharedCheck_5228_;
goto v_resetjp_5215_;
}
else
{
lean_dec(v___y_5187_);
v___x_5216_ = lean_box(0);
v_isShared_5217_ = v_isSharedCheck_5228_;
goto v_resetjp_5215_;
}
v_resetjp_5215_:
{
lean_object* v_a_5218_; lean_object* v___x_5219_; uint8_t v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5225_; 
v_a_5218_ = lean_ctor_get(v___x_5213_, 0);
lean_inc(v_a_5218_);
lean_dec_ref_known(v___x_5213_, 1);
v___x_5219_ = lean_io_error_to_string(v_a_5218_);
v___x_5220_ = 3;
v___x_5221_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5221_, 0, v___x_5219_);
lean_ctor_set_uint8(v___x_5221_, sizeof(void*)*1, v___x_5220_);
v___x_5222_ = lean_array_get_size(v_log_5193_);
v___x_5223_ = lean_array_push(v_log_5193_, v___x_5221_);
if (v_isShared_5217_ == 0)
{
lean_ctor_set(v___x_5216_, 0, v___x_5223_);
v___x_5225_ = v___x_5216_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5227_; 
v_reuseFailAlloc_5227_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5227_, 0, v___x_5223_);
lean_ctor_set(v_reuseFailAlloc_5227_, 1, v_trace_5196_);
lean_ctor_set(v_reuseFailAlloc_5227_, 2, v_buildTime_5197_);
lean_ctor_set_uint8(v_reuseFailAlloc_5227_, sizeof(void*)*3, v_action_5194_);
lean_ctor_set_uint8(v_reuseFailAlloc_5227_, sizeof(void*)*3 + 1, v_wantsRebuild_5195_);
v___x_5225_ = v_reuseFailAlloc_5227_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
lean_object* v___x_5226_; 
v___x_5226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5226_, 0, v___x_5222_);
lean_ctor_set(v___x_5226_, 1, v___x_5225_);
return v___x_5226_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5243_; uint8_t v_isShared_5244_; uint8_t v_isSharedCheck_5255_; 
lean_inc(v_buildTime_5197_);
lean_inc_ref(v_trace_5196_);
lean_inc_ref(v_log_5193_);
lean_dec_ref(v_val_5178_);
v_isSharedCheck_5255_ = !lean_is_exclusive(v___y_5187_);
if (v_isSharedCheck_5255_ == 0)
{
lean_object* v_unused_5256_; lean_object* v_unused_5257_; lean_object* v_unused_5258_; 
v_unused_5256_ = lean_ctor_get(v___y_5187_, 2);
lean_dec(v_unused_5256_);
v_unused_5257_ = lean_ctor_get(v___y_5187_, 1);
lean_dec(v_unused_5257_);
v_unused_5258_ = lean_ctor_get(v___y_5187_, 0);
lean_dec(v_unused_5258_);
v___x_5243_ = v___y_5187_;
v_isShared_5244_ = v_isSharedCheck_5255_;
goto v_resetjp_5242_;
}
else
{
lean_dec(v___y_5187_);
v___x_5243_ = lean_box(0);
v_isShared_5244_ = v_isSharedCheck_5255_;
goto v_resetjp_5242_;
}
v_resetjp_5242_:
{
lean_object* v_a_5245_; lean_object* v___x_5246_; uint8_t v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5252_; 
v_a_5245_ = lean_ctor_get(v___x_5199_, 0);
lean_inc(v_a_5245_);
lean_dec_ref_known(v___x_5199_, 1);
v___x_5246_ = lean_io_error_to_string(v_a_5245_);
v___x_5247_ = 3;
v___x_5248_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5248_, 0, v___x_5246_);
lean_ctor_set_uint8(v___x_5248_, sizeof(void*)*1, v___x_5247_);
v___x_5249_ = lean_array_get_size(v_log_5193_);
v___x_5250_ = lean_array_push(v_log_5193_, v___x_5248_);
if (v_isShared_5244_ == 0)
{
lean_ctor_set(v___x_5243_, 0, v___x_5250_);
v___x_5252_ = v___x_5243_;
goto v_reusejp_5251_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v___x_5250_);
lean_ctor_set(v_reuseFailAlloc_5254_, 1, v_trace_5196_);
lean_ctor_set(v_reuseFailAlloc_5254_, 2, v_buildTime_5197_);
lean_ctor_set_uint8(v_reuseFailAlloc_5254_, sizeof(void*)*3, v_action_5194_);
lean_ctor_set_uint8(v_reuseFailAlloc_5254_, sizeof(void*)*3 + 1, v_wantsRebuild_5195_);
v___x_5252_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5251_;
}
v_reusejp_5251_:
{
lean_object* v___x_5253_; 
v___x_5253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5253_, 0, v___x_5249_);
lean_ctor_set(v___x_5253_, 1, v___x_5252_);
return v___x_5253_;
}
}
}
}
else
{
lean_object* v___x_5259_; 
lean_dec_ref(v_val_5178_);
v___x_5259_ = l_Lake_computeArtifact___redArg(v_file_5173_, v_ext_5174_, v_text_5175_, v___y_5186_, v___y_5187_);
return v___x_5259_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___boxed(lean_object** _args){
lean_object* v_a_5260_ = _args[0];
lean_object* v_file_5261_ = _args[1];
lean_object* v_ext_5262_ = _args[2];
lean_object* v_text_5263_ = _args[3];
lean_object* v_exe_5264_ = _args[4];
lean_object* v___y_5265_ = _args[5];
lean_object* v_val_5266_ = _args[6];
lean_object* v_hash_5267_ = _args[7];
lean_object* v_a_5268_ = _args[8];
lean_object* v_____r_5269_ = _args[9];
lean_object* v___y_5270_ = _args[10];
lean_object* v___y_5271_ = _args[11];
lean_object* v___y_5272_ = _args[12];
lean_object* v___y_5273_ = _args[13];
lean_object* v___y_5274_ = _args[14];
lean_object* v___y_5275_ = _args[15];
lean_object* v___y_5276_ = _args[16];
_start:
{
uint8_t v_a_287943__boxed_5277_; uint8_t v_text_boxed_5278_; uint8_t v_exe_boxed_5279_; uint8_t v___y_287944__boxed_5280_; uint64_t v_hash_boxed_5281_; uint8_t v_a_287946__boxed_5282_; lean_object* v_res_5283_; 
v_a_287943__boxed_5277_ = lean_unbox(v_a_5260_);
v_text_boxed_5278_ = lean_unbox(v_text_5263_);
v_exe_boxed_5279_ = lean_unbox(v_exe_5264_);
v___y_287944__boxed_5280_ = lean_unbox(v___y_5265_);
v_hash_boxed_5281_ = lean_unbox_uint64(v_hash_5267_);
lean_dec_ref(v_hash_5267_);
v_a_287946__boxed_5282_ = lean_unbox(v_a_5268_);
v_res_5283_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v_a_287943__boxed_5277_, v_file_5261_, v_ext_5262_, v_text_boxed_5278_, v_exe_boxed_5279_, v___y_287944__boxed_5280_, v_val_5266_, v_hash_boxed_5281_, v_a_287946__boxed_5282_, v_____r_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_);
lean_dec_ref(v___y_5274_);
lean_dec(v___y_5273_);
lean_dec(v___y_5272_);
lean_dec(v___y_5271_);
lean_dec_ref(v___y_5270_);
return v_res_5283_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object* v_file_5284_, lean_object* v_build_5285_, uint8_t v_text_5286_, lean_object* v_ext_5287_, uint8_t v_restore_5288_, uint8_t v_exe_5289_, uint8_t v_platformIndependent_5290_, lean_object* v_a_5291_, lean_object* v_a_5292_, lean_object* v_a_5293_, lean_object* v_a_5294_, lean_object* v_a_5295_, lean_object* v_a_5296_){
_start:
{
lean_object* v_log_5298_; uint8_t v_action_5299_; uint8_t v_wantsRebuild_5300_; lean_object* v_trace_5301_; lean_object* v_buildTime_5302_; lean_object* v___x_5304_; uint8_t v_isShared_5305_; uint8_t v_isSharedCheck_5567_; 
v_log_5298_ = lean_ctor_get(v_a_5296_, 0);
v_action_5299_ = lean_ctor_get_uint8(v_a_5296_, sizeof(void*)*3);
v_wantsRebuild_5300_ = lean_ctor_get_uint8(v_a_5296_, sizeof(void*)*3 + 1);
v_trace_5301_ = lean_ctor_get(v_a_5296_, 1);
v_buildTime_5302_ = lean_ctor_get(v_a_5296_, 2);
v_isSharedCheck_5567_ = !lean_is_exclusive(v_a_5296_);
if (v_isSharedCheck_5567_ == 0)
{
v___x_5304_ = v_a_5296_;
v_isShared_5305_ = v_isSharedCheck_5567_;
goto v_resetjp_5303_;
}
else
{
lean_inc(v_buildTime_5302_);
lean_inc(v_trace_5301_);
lean_inc(v_log_5298_);
lean_dec(v_a_5296_);
v___x_5304_ = lean_box(0);
v_isShared_5305_ = v_isSharedCheck_5567_;
goto v_resetjp_5303_;
}
v_resetjp_5303_:
{
lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___y_5309_; lean_object* v_log_5310_; uint8_t v_action_5311_; uint8_t v_wantsRebuild_5312_; lean_object* v_buildTime_5313_; lean_object* v_art_5320_; lean_object* v___y_5321_; lean_object* v___x_5336_; 
v___x_5306_ = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(v_file_5284_);
v___x_5307_ = lean_string_append(v_file_5284_, v___x_5306_);
lean_inc_ref(v___x_5307_);
v___x_5336_ = l_Lake_readTraceFile(v___x_5307_, v_log_5298_);
if (lean_obj_tag(v___x_5336_) == 0)
{
if (lean_obj_tag(v_a_5292_) == 1)
{
lean_object* v_a_5337_; lean_object* v_a_5338_; lean_object* v_val_5339_; uint64_t v_hash_5340_; lean_object* v_mtime_5341_; lean_object* v___y_5343_; uint8_t v___y_5344_; lean_object* v___y_5345_; uint8_t v___y_5346_; lean_object* v___y_5347_; lean_object* v___y_5348_; lean_object* v___y_5349_; lean_object* v___y_5350_; lean_object* v___y_5351_; lean_object* v_wsIdx_5355_; lean_object* v_config_5356_; lean_object* v_a_5358_; lean_object* v_a_5359_; lean_object* v___y_5389_; lean_object* v_enableArtifactCache_x3f_5392_; lean_object* v_restoreAllArtifacts_x3f_5393_; uint8_t v___y_5395_; lean_object* v___y_5396_; uint8_t v___y_5397_; uint8_t v___y_5437_; uint8_t v___y_5438_; uint8_t v_a_5439_; lean_object* v_a_5440_; uint8_t v___y_5442_; lean_object* v_a_5443_; uint8_t v___y_5460_; uint8_t v_a_5461_; lean_object* v_a_5462_; lean_object* v_a_5465_; uint8_t v_a_5499_; lean_object* v_a_5500_; lean_object* v___x_5516_; 
v_a_5337_ = lean_ctor_get(v___x_5336_, 0);
lean_inc(v_a_5337_);
v_a_5338_ = lean_ctor_get(v___x_5336_, 1);
lean_inc(v_a_5338_);
lean_dec_ref_known(v___x_5336_, 2);
v_val_5339_ = lean_ctor_get(v_a_5292_, 0);
v_hash_5340_ = lean_ctor_get_uint64(v_trace_5301_, sizeof(void*)*3);
v_mtime_5341_ = lean_ctor_get(v_trace_5301_, 2);
v_wsIdx_5355_ = lean_ctor_get(v_val_5339_, 0);
v_config_5356_ = lean_ctor_get(v_val_5339_, 6);
v_enableArtifactCache_x3f_5392_ = lean_ctor_get(v_config_5356_, 24);
v_restoreAllArtifacts_x3f_5393_ = lean_ctor_get(v_config_5356_, 25);
lean_inc_ref(v_trace_5301_);
v___x_5516_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5516_, 0, v_a_5338_);
lean_ctor_set(v___x_5516_, 1, v_trace_5301_);
lean_ctor_set(v___x_5516_, 2, v_buildTime_5302_);
lean_ctor_set_uint8(v___x_5516_, sizeof(void*)*3, v_action_5299_);
lean_ctor_set_uint8(v___x_5516_, sizeof(void*)*3 + 1, v_wantsRebuild_5300_);
if (lean_obj_tag(v_enableArtifactCache_x3f_5392_) == 0)
{
lean_object* v_toContext_5517_; lean_object* v_lakeEnv_5518_; lean_object* v_enableArtifactCache_x3f_5519_; 
v_toContext_5517_ = lean_ctor_get(v_a_5295_, 1);
v_lakeEnv_5518_ = lean_ctor_get(v_toContext_5517_, 0);
v_enableArtifactCache_x3f_5519_ = lean_ctor_get(v_lakeEnv_5518_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_5519_) == 0)
{
lean_object* v_packages_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v_config_5523_; lean_object* v_enableArtifactCache_x3f_5524_; 
v_packages_5520_ = lean_ctor_get(v_toContext_5517_, 4);
v___x_5521_ = lean_unsigned_to_nat(0u);
v___x_5522_ = lean_array_fget_borrowed(v_packages_5520_, v___x_5521_);
v_config_5523_ = lean_ctor_get(v___x_5522_, 6);
v_enableArtifactCache_x3f_5524_ = lean_ctor_get(v_config_5523_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_5524_) == 0)
{
v_a_5465_ = v___x_5516_;
goto v___jp_5464_;
}
else
{
lean_object* v_val_5525_; uint8_t v___x_5526_; 
v_val_5525_ = lean_ctor_get(v_enableArtifactCache_x3f_5524_, 0);
v___x_5526_ = lean_unbox(v_val_5525_);
v_a_5499_ = v___x_5526_;
v_a_5500_ = v___x_5516_;
goto v___jp_5498_;
}
}
else
{
lean_object* v_val_5527_; uint8_t v___x_5528_; 
v_val_5527_ = lean_ctor_get(v_enableArtifactCache_x3f_5519_, 0);
v___x_5528_ = lean_unbox(v_val_5527_);
v_a_5499_ = v___x_5528_;
v_a_5500_ = v___x_5516_;
goto v___jp_5498_;
}
}
else
{
lean_object* v_val_5529_; uint8_t v___x_5530_; 
v_val_5529_ = lean_ctor_get(v_enableArtifactCache_x3f_5392_, 0);
v___x_5530_ = lean_unbox(v_val_5529_);
v_a_5499_ = v___x_5530_;
v_a_5500_ = v___x_5516_;
goto v___jp_5498_;
}
v___jp_5342_:
{
lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; 
lean_dec_ref(v___y_5349_);
v___x_5352_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5352_, 0, v___y_5351_);
v___x_5353_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_hash_5340_, v___x_5352_, v___y_5350_, v_platformIndependent_5290_);
v___x_5354_ = lean_st_ref_put(v___y_5347_, v___x_5353_);
v___y_5309_ = v___y_5343_;
v_log_5310_ = v___y_5345_;
v_action_5311_ = v___y_5344_;
v_wantsRebuild_5312_ = v___y_5346_;
v_buildTime_5313_ = v___y_5348_;
goto v___jp_5308_;
}
v___jp_5357_:
{
lean_object* v___x_5360_; uint8_t v___x_5361_; 
v___x_5360_ = lean_unsigned_to_nat(0u);
v___x_5361_ = lean_nat_dec_eq(v_wsIdx_5355_, v___x_5360_);
if (v___x_5361_ == 0)
{
lean_object* v_log_5362_; uint8_t v_action_5363_; uint8_t v_wantsRebuild_5364_; lean_object* v_buildTime_5365_; 
v_log_5362_ = lean_ctor_get(v_a_5359_, 0);
lean_inc_ref(v_log_5362_);
v_action_5363_ = lean_ctor_get_uint8(v_a_5359_, sizeof(void*)*3);
v_wantsRebuild_5364_ = lean_ctor_get_uint8(v_a_5359_, sizeof(void*)*3 + 1);
v_buildTime_5365_ = lean_ctor_get(v_a_5359_, 2);
lean_inc(v_buildTime_5365_);
lean_dec_ref(v_a_5359_);
v___y_5309_ = v_a_5358_;
v_log_5310_ = v_log_5362_;
v_action_5311_ = v_action_5363_;
v_wantsRebuild_5312_ = v_wantsRebuild_5364_;
v_buildTime_5313_ = v_buildTime_5365_;
goto v___jp_5308_;
}
else
{
lean_object* v_outputsRef_x3f_5366_; 
v_outputsRef_x3f_5366_ = lean_ctor_get(v_a_5295_, 5);
if (lean_obj_tag(v_outputsRef_x3f_5366_) == 1)
{
lean_object* v_log_5367_; uint8_t v_action_5368_; uint8_t v_wantsRebuild_5369_; lean_object* v_trace_5370_; lean_object* v_buildTime_5371_; lean_object* v_val_5372_; lean_object* v_descr_5373_; lean_object* v___x_5374_; uint64_t v_hash_5375_; lean_object* v_ext_5376_; lean_object* v___x_5377_; uint8_t v___x_5378_; 
v_log_5367_ = lean_ctor_get(v_a_5359_, 0);
lean_inc_ref(v_log_5367_);
v_action_5368_ = lean_ctor_get_uint8(v_a_5359_, sizeof(void*)*3);
v_wantsRebuild_5369_ = lean_ctor_get_uint8(v_a_5359_, sizeof(void*)*3 + 1);
v_trace_5370_ = lean_ctor_get(v_a_5359_, 1);
lean_inc_ref(v_trace_5370_);
v_buildTime_5371_ = lean_ctor_get(v_a_5359_, 2);
lean_inc(v_buildTime_5371_);
lean_dec_ref(v_a_5359_);
v_val_5372_ = lean_ctor_get(v_outputsRef_x3f_5366_, 0);
v_descr_5373_ = lean_ctor_get(v_a_5358_, 0);
v___x_5374_ = lean_st_ref_take(v_val_5372_);
v_hash_5375_ = lean_ctor_get_uint64(v_descr_5373_, sizeof(void*)*1);
v_ext_5376_ = lean_ctor_get(v_descr_5373_, 0);
v___x_5377_ = lean_string_utf8_byte_size(v_ext_5376_);
v___x_5378_ = lean_nat_dec_eq(v___x_5377_, v___x_5360_);
if (v___x_5378_ == 0)
{
lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; 
v___x_5379_ = l_Lake_lowerHexUInt64(v_hash_5375_);
v___x_5380_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5381_ = lean_string_append(v___x_5379_, v___x_5380_);
v___x_5382_ = lean_string_append(v___x_5381_, v_ext_5376_);
v___y_5343_ = v_a_5358_;
v___y_5344_ = v_action_5368_;
v___y_5345_ = v_log_5367_;
v___y_5346_ = v_wantsRebuild_5369_;
v___y_5347_ = v_val_5372_;
v___y_5348_ = v_buildTime_5371_;
v___y_5349_ = v_trace_5370_;
v___y_5350_ = v___x_5374_;
v___y_5351_ = v___x_5382_;
goto v___jp_5342_;
}
else
{
lean_object* v___x_5383_; 
v___x_5383_ = l_Lake_lowerHexUInt64(v_hash_5375_);
v___y_5343_ = v_a_5358_;
v___y_5344_ = v_action_5368_;
v___y_5345_ = v_log_5367_;
v___y_5346_ = v_wantsRebuild_5369_;
v___y_5347_ = v_val_5372_;
v___y_5348_ = v_buildTime_5371_;
v___y_5349_ = v_trace_5370_;
v___y_5350_ = v___x_5374_;
v___y_5351_ = v___x_5383_;
goto v___jp_5342_;
}
}
else
{
lean_object* v_log_5384_; uint8_t v_action_5385_; uint8_t v_wantsRebuild_5386_; lean_object* v_buildTime_5387_; 
v_log_5384_ = lean_ctor_get(v_a_5359_, 0);
lean_inc_ref(v_log_5384_);
v_action_5385_ = lean_ctor_get_uint8(v_a_5359_, sizeof(void*)*3);
v_wantsRebuild_5386_ = lean_ctor_get_uint8(v_a_5359_, sizeof(void*)*3 + 1);
v_buildTime_5387_ = lean_ctor_get(v_a_5359_, 2);
lean_inc(v_buildTime_5387_);
lean_dec_ref(v_a_5359_);
v___y_5309_ = v_a_5358_;
v_log_5310_ = v_log_5384_;
v_action_5311_ = v_action_5385_;
v_wantsRebuild_5312_ = v_wantsRebuild_5386_;
v_buildTime_5313_ = v_buildTime_5387_;
goto v___jp_5308_;
}
}
}
v___jp_5388_:
{
if (lean_obj_tag(v___y_5389_) == 0)
{
lean_object* v_a_5390_; lean_object* v_a_5391_; 
v_a_5390_ = lean_ctor_get(v___y_5389_, 0);
lean_inc(v_a_5390_);
v_a_5391_ = lean_ctor_get(v___y_5389_, 1);
lean_inc(v_a_5391_);
lean_dec_ref_known(v___y_5389_, 2);
v_a_5358_ = v_a_5390_;
v_a_5359_ = v_a_5391_;
goto v___jp_5357_;
}
else
{
lean_dec_ref(v___x_5307_);
lean_del_object(v___x_5304_);
return v___y_5389_;
}
}
v___jp_5394_:
{
lean_object* v___x_5398_; 
lean_inc_ref(v_a_5291_);
lean_inc(v_val_5339_);
lean_inc(v_a_5337_);
lean_inc_ref(v___x_5307_);
lean_inc_ref(v_file_5284_);
v___x_5398_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_file_5284_, v_exe_5289_, v_hash_5340_, v___x_5307_, v_a_5337_, v_val_5339_, v___y_5397_, v_a_5291_, v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v___y_5396_);
if (lean_obj_tag(v___x_5398_) == 0)
{
lean_object* v_a_5399_; 
v_a_5399_ = lean_ctor_get(v___x_5398_, 0);
lean_inc(v_a_5399_);
if (lean_obj_tag(v_a_5399_) == 1)
{
lean_object* v_a_5400_; lean_object* v_val_5401_; 
lean_dec(v_a_5337_);
lean_dec_ref(v_trace_5301_);
lean_dec_ref(v_a_5291_);
lean_dec_ref(v_ext_5287_);
lean_dec_ref(v_build_5285_);
lean_dec_ref(v_file_5284_);
v_a_5400_ = lean_ctor_get(v___x_5398_, 1);
lean_inc(v_a_5400_);
lean_dec_ref_known(v___x_5398_, 2);
v_val_5401_ = lean_ctor_get(v_a_5399_, 0);
lean_inc(v_val_5401_);
lean_dec_ref_known(v_a_5399_, 1);
v_a_5358_ = v_val_5401_;
v_a_5359_ = v_a_5400_;
goto v___jp_5357_;
}
else
{
lean_object* v_a_5402_; lean_object* v___x_5403_; 
lean_dec(v_a_5399_);
v_a_5402_ = lean_ctor_get(v___x_5398_, 1);
lean_inc(v_a_5402_);
lean_dec_ref_known(v___x_5398_, 2);
v___x_5403_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5291_, v_file_5284_, v_trace_5301_, v_a_5337_, v_mtime_5341_, v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5402_);
if (lean_obj_tag(v___x_5403_) == 0)
{
lean_object* v_a_5404_; lean_object* v_a_5405_; uint8_t v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; uint8_t v___x_5409_; 
v_a_5404_ = lean_ctor_get(v___x_5403_, 0);
lean_inc(v_a_5404_);
v_a_5405_ = lean_ctor_get(v___x_5403_, 1);
lean_inc(v_a_5405_);
lean_dec_ref_known(v___x_5403_, 2);
v___x_5406_ = lean_unbox(v_a_5404_);
v___x_5407_ = l_Lake_OutputStatus_ctorIdx(v___x_5406_);
v___x_5408_ = lean_obj_once(&l_Lake_OutputStatus_isUpToDate___closed__0, &l_Lake_OutputStatus_isUpToDate___closed__0_once, _init_l_Lake_OutputStatus_isUpToDate___closed__0);
v___x_5409_ = lean_nat_dec_eq(v___x_5407_, v___x_5408_);
lean_dec(v___x_5407_);
if (v___x_5409_ == 0)
{
lean_object* v___x_5410_; uint8_t v___x_5411_; lean_object* v___x_5412_; 
lean_dec_ref(v_trace_5301_);
lean_dec_ref(v_build_5285_);
v___x_5410_ = lean_box(0);
v___x_5411_ = lean_unbox(v_a_5404_);
lean_dec(v_a_5404_);
lean_inc(v_val_5339_);
v___x_5412_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v___x_5411_, v_file_5284_, v_ext_5287_, v_text_5286_, v_exe_5289_, v___y_5397_, v_val_5339_, v_hash_5340_, v___y_5395_, v___x_5410_, v_a_5291_, v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5405_);
lean_dec_ref(v_a_5291_);
v___y_5389_ = v___x_5412_;
goto v___jp_5388_;
}
else
{
lean_object* v___x_5413_; lean_object* v___x_5414_; 
v___x_5413_ = lean_box(0);
lean_inc_ref(v_a_5291_);
lean_inc_ref(v___x_5307_);
lean_inc_ref(v_ext_5287_);
lean_inc_ref(v_file_5284_);
v___x_5414_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5284_, v_build_5285_, v_text_5286_, v_ext_5287_, v_trace_5301_, v___x_5307_, v_a_5291_, v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5405_);
lean_dec_ref(v_trace_5301_);
if (lean_obj_tag(v___x_5414_) == 0)
{
lean_object* v_a_5415_; uint8_t v___x_5416_; lean_object* v___x_5417_; 
v_a_5415_ = lean_ctor_get(v___x_5414_, 1);
lean_inc(v_a_5415_);
lean_dec_ref_known(v___x_5414_, 2);
v___x_5416_ = lean_unbox(v_a_5404_);
lean_dec(v_a_5404_);
lean_inc(v_val_5339_);
v___x_5417_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v___x_5416_, v_file_5284_, v_ext_5287_, v_text_5286_, v_exe_5289_, v___y_5397_, v_val_5339_, v_hash_5340_, v___y_5395_, v___x_5413_, v_a_5291_, v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5415_);
lean_dec_ref(v_a_5291_);
v___y_5389_ = v___x_5417_;
goto v___jp_5388_;
}
else
{
lean_dec(v_a_5404_);
lean_dec_ref(v___x_5307_);
lean_del_object(v___x_5304_);
lean_dec_ref(v_a_5291_);
lean_dec_ref(v_ext_5287_);
lean_dec_ref(v_file_5284_);
return v___x_5414_;
}
}
}
else
{
lean_object* v_a_5418_; lean_object* v_a_5419_; lean_object* v___x_5421_; uint8_t v_isShared_5422_; uint8_t v_isSharedCheck_5426_; 
lean_dec_ref(v___x_5307_);
lean_del_object(v___x_5304_);
lean_dec_ref(v_trace_5301_);
lean_dec_ref(v_a_5291_);
lean_dec_ref(v_ext_5287_);
lean_dec_ref(v_build_5285_);
lean_dec_ref(v_file_5284_);
v_a_5418_ = lean_ctor_get(v___x_5403_, 0);
v_a_5419_ = lean_ctor_get(v___x_5403_, 1);
v_isSharedCheck_5426_ = !lean_is_exclusive(v___x_5403_);
if (v_isSharedCheck_5426_ == 0)
{
v___x_5421_ = v___x_5403_;
v_isShared_5422_ = v_isSharedCheck_5426_;
goto v_resetjp_5420_;
}
else
{
lean_inc(v_a_5419_);
lean_inc(v_a_5418_);
lean_dec(v___x_5403_);
v___x_5421_ = lean_box(0);
v_isShared_5422_ = v_isSharedCheck_5426_;
goto v_resetjp_5420_;
}
v_resetjp_5420_:
{
lean_object* v___x_5424_; 
if (v_isShared_5422_ == 0)
{
v___x_5424_ = v___x_5421_;
goto v_reusejp_5423_;
}
else
{
lean_object* v_reuseFailAlloc_5425_; 
v_reuseFailAlloc_5425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5425_, 0, v_a_5418_);
lean_ctor_set(v_reuseFailAlloc_5425_, 1, v_a_5419_);
v___x_5424_ = v_reuseFailAlloc_5425_;
goto v_reusejp_5423_;
}
v_reusejp_5423_:
{
return v___x_5424_;
}
}
}
}
}
else
{
lean_object* v_a_5427_; lean_object* v_a_5428_; lean_object* v___x_5430_; uint8_t v_isShared_5431_; uint8_t v_isSharedCheck_5435_; 
lean_dec(v_a_5337_);
lean_dec_ref(v___x_5307_);
lean_del_object(v___x_5304_);
lean_dec_ref(v_trace_5301_);
lean_dec_ref(v_a_5291_);
lean_dec_ref(v_ext_5287_);
lean_dec_ref(v_build_5285_);
lean_dec_ref(v_file_5284_);
v_a_5427_ = lean_ctor_get(v___x_5398_, 0);
v_a_5428_ = lean_ctor_get(v___x_5398_, 1);
v_isSharedCheck_5435_ = !lean_is_exclusive(v___x_5398_);
if (v_isSharedCheck_5435_ == 0)
{
v___x_5430_ = v___x_5398_;
v_isShared_5431_ = v_isSharedCheck_5435_;
goto v_resetjp_5429_;
}
else
{
lean_inc(v_a_5428_);
lean_inc(v_a_5427_);
lean_dec(v___x_5398_);
v___x_5430_ = lean_box(0);
v_isShared_5431_ = v_isSharedCheck_5435_;
goto v_resetjp_5429_;
}
v_resetjp_5429_:
{
lean_object* v___x_5433_; 
if (v_isShared_5431_ == 0)
{
v___x_5433_ = v___x_5430_;
goto v_reusejp_5432_;
}
else
{
lean_object* v_reuseFailAlloc_5434_; 
v_reuseFailAlloc_5434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5434_, 0, v_a_5427_);
lean_ctor_set(v_reuseFailAlloc_5434_, 1, v_a_5428_);
v___x_5433_ = v_reuseFailAlloc_5434_;
goto v_reusejp_5432_;
}
v_reusejp_5432_:
{
return v___x_5433_;
}
}
}
}
v___jp_5436_:
{
if (v_restore_5288_ == 0)
{
v___y_5395_ = v___y_5437_;
v___y_5396_ = v_a_5440_;
v___y_5397_ = v_a_5439_;
goto v___jp_5394_;
}
else
{
v___y_5395_ = v___y_5437_;
v___y_5396_ = v_a_5440_;
v___y_5397_ = v___y_5438_;
goto v___jp_5394_;
}
}
v___jp_5441_:
{
lean_object* v___x_5444_; 
lean_inc_ref(v_a_5291_);
lean_inc(v_val_5339_);
lean_inc_ref(v___x_5307_);
lean_inc_ref(v_file_5284_);
v___x_5444_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_file_5284_, v_exe_5289_, v_hash_5340_, v___x_5307_, v_a_5337_, v_val_5339_, v___y_5442_, v_a_5291_, v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5443_);
if (lean_obj_tag(v___x_5444_) == 0)
{
lean_object* v_a_5445_; 
v_a_5445_ = lean_ctor_get(v___x_5444_, 0);
lean_inc(v_a_5445_);
if (lean_obj_tag(v_a_5445_) == 1)
{
lean_object* v_a_5446_; lean_object* v_val_5447_; 
lean_dec_ref(v_trace_5301_);
lean_dec_ref(v_a_5291_);
lean_dec_ref(v_ext_5287_);
lean_dec_ref(v_build_5285_);
lean_dec_ref(v_file_5284_);
v_a_5446_ = lean_ctor_get(v___x_5444_, 1);
lean_inc(v_a_5446_);
lean_dec_ref_known(v___x_5444_, 2);
v_val_5447_ = lean_ctor_get(v_a_5445_, 0);
lean_inc(v_val_5447_);
lean_dec_ref_known(v_a_5445_, 1);
v_a_5358_ = v_val_5447_;
v_a_5359_ = v_a_5446_;
goto v___jp_5357_;
}
else
{
lean_object* v_a_5448_; lean_object* v___x_5449_; 
lean_dec(v_a_5445_);
v_a_5448_ = lean_ctor_get(v___x_5444_, 1);
lean_inc(v_a_5448_);
lean_dec_ref_known(v___x_5444_, 2);
lean_inc_ref(v___x_5307_);
v___x_5449_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5284_, v_build_5285_, v_text_5286_, v_ext_5287_, v_trace_5301_, v___x_5307_, v_a_5291_, v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5448_);
lean_dec_ref(v_trace_5301_);
v___y_5389_ = v___x_5449_;
goto v___jp_5388_;
}
}
else
{
lean_object* v_a_5450_; lean_object* v_a_5451_; lean_object* v___x_5453_; uint8_t v_isShared_5454_; uint8_t v_isSharedCheck_5458_; 
lean_dec_ref(v___x_5307_);
lean_del_object(v___x_5304_);
lean_dec_ref(v_trace_5301_);
lean_dec_ref(v_a_5291_);
lean_dec_ref(v_ext_5287_);
lean_dec_ref(v_build_5285_);
lean_dec_ref(v_file_5284_);
v_a_5450_ = lean_ctor_get(v___x_5444_, 0);
v_a_5451_ = lean_ctor_get(v___x_5444_, 1);
v_isSharedCheck_5458_ = !lean_is_exclusive(v___x_5444_);
if (v_isSharedCheck_5458_ == 0)
{
v___x_5453_ = v___x_5444_;
v_isShared_5454_ = v_isSharedCheck_5458_;
goto v_resetjp_5452_;
}
else
{
lean_inc(v_a_5451_);
lean_inc(v_a_5450_);
lean_dec(v___x_5444_);
v___x_5453_ = lean_box(0);
v_isShared_5454_ = v_isSharedCheck_5458_;
goto v_resetjp_5452_;
}
v_resetjp_5452_:
{
lean_object* v___x_5456_; 
if (v_isShared_5454_ == 0)
{
v___x_5456_ = v___x_5453_;
goto v_reusejp_5455_;
}
else
{
lean_object* v_reuseFailAlloc_5457_; 
v_reuseFailAlloc_5457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5457_, 0, v_a_5450_);
lean_ctor_set(v_reuseFailAlloc_5457_, 1, v_a_5451_);
v___x_5456_ = v_reuseFailAlloc_5457_;
goto v_reusejp_5455_;
}
v_reusejp_5455_:
{
return v___x_5456_;
}
}
}
}
v___jp_5459_:
{
if (v_a_5461_ == 0)
{
lean_object* v___x_5463_; 
lean_dec(v_a_5337_);
lean_inc_ref(v___x_5307_);
v___x_5463_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5284_, v_build_5285_, v_text_5286_, v_ext_5287_, v_trace_5301_, v___x_5307_, v_a_5291_, v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5462_);
lean_dec_ref(v_trace_5301_);
v___y_5389_ = v___x_5463_;
goto v___jp_5388_;
}
else
{
v___y_5442_ = v___y_5460_;
v_a_5443_ = v_a_5462_;
goto v___jp_5441_;
}
}
v___jp_5464_:
{
uint8_t v___x_5466_; lean_object* v___x_5467_; 
v___x_5466_ = 1;
lean_inc(v_a_5337_);
v___x_5467_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5291_, v_file_5284_, v_trace_5301_, v_a_5337_, v_mtime_5341_, v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5465_);
if (lean_obj_tag(v___x_5467_) == 0)
{
lean_object* v_a_5468_; lean_object* v_a_5469_; uint8_t v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; uint8_t v___x_5473_; 
v_a_5468_ = lean_ctor_get(v___x_5467_, 0);
lean_inc(v_a_5468_);
v_a_5469_ = lean_ctor_get(v___x_5467_, 1);
lean_inc(v_a_5469_);
lean_dec_ref_known(v___x_5467_, 2);
v___x_5470_ = lean_unbox(v_a_5468_);
lean_dec(v_a_5468_);
v___x_5471_ = l_Lake_OutputStatus_ctorIdx(v___x_5470_);
v___x_5472_ = lean_obj_once(&l_Lake_OutputStatus_isUpToDate___closed__0, &l_Lake_OutputStatus_isUpToDate___closed__0_once, _init_l_Lake_OutputStatus_isUpToDate___closed__0);
v___x_5473_ = lean_nat_dec_eq(v___x_5471_, v___x_5472_);
lean_dec(v___x_5471_);
if (v___x_5473_ == 0)
{
lean_object* v___x_5474_; 
lean_dec(v_a_5337_);
lean_dec_ref(v_trace_5301_);
lean_dec_ref(v_a_5291_);
lean_dec_ref(v_build_5285_);
v___x_5474_ = l_Lake_computeArtifact___redArg(v_file_5284_, v_ext_5287_, v_text_5286_, v_a_5295_, v_a_5469_);
v___y_5389_ = v___x_5474_;
goto v___jp_5388_;
}
else
{
if (lean_obj_tag(v_enableArtifactCache_x3f_5392_) == 0)
{
lean_object* v_toContext_5475_; lean_object* v_lakeEnv_5476_; lean_object* v_enableArtifactCache_x3f_5477_; 
v_toContext_5475_ = lean_ctor_get(v_a_5295_, 1);
v_lakeEnv_5476_ = lean_ctor_get(v_toContext_5475_, 0);
v_enableArtifactCache_x3f_5477_ = lean_ctor_get(v_lakeEnv_5476_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_5477_) == 0)
{
lean_object* v_packages_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v_config_5481_; lean_object* v_enableArtifactCache_x3f_5482_; 
v_packages_5478_ = lean_ctor_get(v_toContext_5475_, 4);
v___x_5479_ = lean_unsigned_to_nat(0u);
v___x_5480_ = lean_array_fget_borrowed(v_packages_5478_, v___x_5479_);
v_config_5481_ = lean_ctor_get(v___x_5480_, 6);
v_enableArtifactCache_x3f_5482_ = lean_ctor_get(v_config_5481_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_5482_) == 0)
{
v___y_5442_ = v___x_5466_;
v_a_5443_ = v_a_5469_;
goto v___jp_5441_;
}
else
{
lean_object* v_val_5483_; uint8_t v___x_5484_; 
v_val_5483_ = lean_ctor_get(v_enableArtifactCache_x3f_5482_, 0);
v___x_5484_ = lean_unbox(v_val_5483_);
v___y_5460_ = v___x_5466_;
v_a_5461_ = v___x_5484_;
v_a_5462_ = v_a_5469_;
goto v___jp_5459_;
}
}
else
{
lean_object* v_val_5485_; uint8_t v___x_5486_; 
v_val_5485_ = lean_ctor_get(v_enableArtifactCache_x3f_5477_, 0);
v___x_5486_ = lean_unbox(v_val_5485_);
v___y_5460_ = v___x_5466_;
v_a_5461_ = v___x_5486_;
v_a_5462_ = v_a_5469_;
goto v___jp_5459_;
}
}
else
{
lean_object* v_val_5487_; uint8_t v___x_5488_; 
v_val_5487_ = lean_ctor_get(v_enableArtifactCache_x3f_5392_, 0);
v___x_5488_ = lean_unbox(v_val_5487_);
v___y_5460_ = v___x_5466_;
v_a_5461_ = v___x_5488_;
v_a_5462_ = v_a_5469_;
goto v___jp_5459_;
}
}
}
else
{
lean_object* v_a_5489_; lean_object* v_a_5490_; lean_object* v___x_5492_; uint8_t v_isShared_5493_; uint8_t v_isSharedCheck_5497_; 
lean_dec(v_a_5337_);
lean_dec_ref(v___x_5307_);
lean_del_object(v___x_5304_);
lean_dec_ref(v_trace_5301_);
lean_dec_ref(v_a_5291_);
lean_dec_ref(v_ext_5287_);
lean_dec_ref(v_build_5285_);
lean_dec_ref(v_file_5284_);
v_a_5489_ = lean_ctor_get(v___x_5467_, 0);
v_a_5490_ = lean_ctor_get(v___x_5467_, 1);
v_isSharedCheck_5497_ = !lean_is_exclusive(v___x_5467_);
if (v_isSharedCheck_5497_ == 0)
{
v___x_5492_ = v___x_5467_;
v_isShared_5493_ = v_isSharedCheck_5497_;
goto v_resetjp_5491_;
}
else
{
lean_inc(v_a_5490_);
lean_inc(v_a_5489_);
lean_dec(v___x_5467_);
v___x_5492_ = lean_box(0);
v_isShared_5493_ = v_isSharedCheck_5497_;
goto v_resetjp_5491_;
}
v_resetjp_5491_:
{
lean_object* v___x_5495_; 
if (v_isShared_5493_ == 0)
{
v___x_5495_ = v___x_5492_;
goto v_reusejp_5494_;
}
else
{
lean_object* v_reuseFailAlloc_5496_; 
v_reuseFailAlloc_5496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5496_, 0, v_a_5489_);
lean_ctor_set(v_reuseFailAlloc_5496_, 1, v_a_5490_);
v___x_5495_ = v_reuseFailAlloc_5496_;
goto v_reusejp_5494_;
}
v_reusejp_5494_:
{
return v___x_5495_;
}
}
}
}
v___jp_5498_:
{
if (v_a_5499_ == 0)
{
v_a_5465_ = v_a_5500_;
goto v___jp_5464_;
}
else
{
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5393_) == 0)
{
lean_object* v_toContext_5501_; lean_object* v_lakeEnv_5502_; lean_object* v_restoreAllArtifacts_x3f_5503_; 
v_toContext_5501_ = lean_ctor_get(v_a_5295_, 1);
v_lakeEnv_5502_ = lean_ctor_get(v_toContext_5501_, 0);
v_restoreAllArtifacts_x3f_5503_ = lean_ctor_get(v_lakeEnv_5502_, 7);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5503_) == 0)
{
lean_object* v_packages_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v_config_5507_; lean_object* v_restoreAllArtifacts_x3f_5508_; 
v_packages_5504_ = lean_ctor_get(v_toContext_5501_, 4);
v___x_5505_ = lean_unsigned_to_nat(0u);
v___x_5506_ = lean_array_fget_borrowed(v_packages_5504_, v___x_5505_);
v_config_5507_ = lean_ctor_get(v___x_5506_, 6);
v_restoreAllArtifacts_x3f_5508_ = lean_ctor_get(v_config_5507_, 25);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5508_) == 0)
{
uint8_t v___x_5509_; 
v___x_5509_ = 0;
v___y_5437_ = v_a_5499_;
v___y_5438_ = v_a_5499_;
v_a_5439_ = v___x_5509_;
v_a_5440_ = v_a_5500_;
goto v___jp_5436_;
}
else
{
lean_object* v_val_5510_; uint8_t v___x_5511_; 
v_val_5510_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5508_, 0);
v___x_5511_ = lean_unbox(v_val_5510_);
v___y_5437_ = v_a_5499_;
v___y_5438_ = v_a_5499_;
v_a_5439_ = v___x_5511_;
v_a_5440_ = v_a_5500_;
goto v___jp_5436_;
}
}
else
{
lean_object* v_val_5512_; uint8_t v___x_5513_; 
v_val_5512_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5503_, 0);
v___x_5513_ = lean_unbox(v_val_5512_);
v___y_5437_ = v_a_5499_;
v___y_5438_ = v_a_5499_;
v_a_5439_ = v___x_5513_;
v_a_5440_ = v_a_5500_;
goto v___jp_5436_;
}
}
else
{
lean_object* v_val_5514_; uint8_t v___x_5515_; 
v_val_5514_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5393_, 0);
v___x_5515_ = lean_unbox(v_val_5514_);
v___y_5437_ = v_a_5499_;
v___y_5438_ = v_a_5499_;
v_a_5439_ = v___x_5515_;
v_a_5440_ = v_a_5500_;
goto v___jp_5436_;
}
}
}
}
else
{
lean_object* v_a_5531_; lean_object* v_a_5532_; lean_object* v_mtime_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; 
lean_del_object(v___x_5304_);
v_a_5531_ = lean_ctor_get(v___x_5336_, 0);
lean_inc(v_a_5531_);
v_a_5532_ = lean_ctor_get(v___x_5336_, 1);
lean_inc(v_a_5532_);
lean_dec_ref_known(v___x_5336_, 2);
v_mtime_5533_ = lean_ctor_get(v_trace_5301_, 2);
lean_inc_ref(v_trace_5301_);
v___x_5534_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5534_, 0, v_a_5532_);
lean_ctor_set(v___x_5534_, 1, v_trace_5301_);
lean_ctor_set(v___x_5534_, 2, v_buildTime_5302_);
lean_ctor_set_uint8(v___x_5534_, sizeof(void*)*3, v_action_5299_);
lean_ctor_set_uint8(v___x_5534_, sizeof(void*)*3 + 1, v_wantsRebuild_5300_);
v___x_5535_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5291_, v_file_5284_, v_trace_5301_, v_a_5531_, v_mtime_5533_, v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v___x_5534_);
if (lean_obj_tag(v___x_5535_) == 0)
{
lean_object* v_a_5536_; lean_object* v_a_5537_; uint8_t v___x_5538_; lean_object* v___x_5539_; lean_object* v___x_5540_; uint8_t v___x_5541_; 
v_a_5536_ = lean_ctor_get(v___x_5535_, 0);
lean_inc(v_a_5536_);
v_a_5537_ = lean_ctor_get(v___x_5535_, 1);
lean_inc(v_a_5537_);
lean_dec_ref_known(v___x_5535_, 2);
v___x_5538_ = lean_unbox(v_a_5536_);
lean_dec(v_a_5536_);
v___x_5539_ = l_Lake_OutputStatus_ctorIdx(v___x_5538_);
v___x_5540_ = lean_obj_once(&l_Lake_OutputStatus_isUpToDate___closed__0, &l_Lake_OutputStatus_isUpToDate___closed__0_once, _init_l_Lake_OutputStatus_isUpToDate___closed__0);
v___x_5541_ = lean_nat_dec_eq(v___x_5539_, v___x_5540_);
lean_dec(v___x_5539_);
if (v___x_5541_ == 0)
{
lean_object* v___x_5542_; 
lean_dec_ref(v_trace_5301_);
lean_dec_ref(v_a_5291_);
lean_dec_ref(v_build_5285_);
v___x_5542_ = l_Lake_computeArtifact___redArg(v_file_5284_, v_ext_5287_, v_text_5286_, v_a_5295_, v_a_5537_);
if (lean_obj_tag(v___x_5542_) == 0)
{
lean_object* v_a_5543_; lean_object* v_a_5544_; 
v_a_5543_ = lean_ctor_get(v___x_5542_, 0);
lean_inc(v_a_5543_);
v_a_5544_ = lean_ctor_get(v___x_5542_, 1);
lean_inc(v_a_5544_);
lean_dec_ref_known(v___x_5542_, 2);
v_art_5320_ = v_a_5543_;
v___y_5321_ = v_a_5544_;
goto v___jp_5319_;
}
else
{
lean_dec_ref(v___x_5307_);
return v___x_5542_;
}
}
else
{
lean_object* v___x_5545_; 
lean_inc_ref(v___x_5307_);
v___x_5545_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5284_, v_build_5285_, v_text_5286_, v_ext_5287_, v_trace_5301_, v___x_5307_, v_a_5291_, v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5537_);
lean_dec_ref(v_trace_5301_);
if (lean_obj_tag(v___x_5545_) == 0)
{
lean_object* v_a_5546_; lean_object* v_a_5547_; 
v_a_5546_ = lean_ctor_get(v___x_5545_, 0);
lean_inc(v_a_5546_);
v_a_5547_ = lean_ctor_get(v___x_5545_, 1);
lean_inc(v_a_5547_);
lean_dec_ref_known(v___x_5545_, 2);
v_art_5320_ = v_a_5546_;
v___y_5321_ = v_a_5547_;
goto v___jp_5319_;
}
else
{
lean_dec_ref(v___x_5307_);
return v___x_5545_;
}
}
}
else
{
lean_object* v_a_5548_; lean_object* v_a_5549_; lean_object* v___x_5551_; uint8_t v_isShared_5552_; uint8_t v_isSharedCheck_5556_; 
lean_dec_ref(v___x_5307_);
lean_dec_ref(v_trace_5301_);
lean_dec_ref(v_a_5291_);
lean_dec_ref(v_ext_5287_);
lean_dec_ref(v_build_5285_);
lean_dec_ref(v_file_5284_);
v_a_5548_ = lean_ctor_get(v___x_5535_, 0);
v_a_5549_ = lean_ctor_get(v___x_5535_, 1);
v_isSharedCheck_5556_ = !lean_is_exclusive(v___x_5535_);
if (v_isSharedCheck_5556_ == 0)
{
v___x_5551_ = v___x_5535_;
v_isShared_5552_ = v_isSharedCheck_5556_;
goto v_resetjp_5550_;
}
else
{
lean_inc(v_a_5549_);
lean_inc(v_a_5548_);
lean_dec(v___x_5535_);
v___x_5551_ = lean_box(0);
v_isShared_5552_ = v_isSharedCheck_5556_;
goto v_resetjp_5550_;
}
v_resetjp_5550_:
{
lean_object* v___x_5554_; 
if (v_isShared_5552_ == 0)
{
v___x_5554_ = v___x_5551_;
goto v_reusejp_5553_;
}
else
{
lean_object* v_reuseFailAlloc_5555_; 
v_reuseFailAlloc_5555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5555_, 0, v_a_5548_);
lean_ctor_set(v_reuseFailAlloc_5555_, 1, v_a_5549_);
v___x_5554_ = v_reuseFailAlloc_5555_;
goto v_reusejp_5553_;
}
v_reusejp_5553_:
{
return v___x_5554_;
}
}
}
}
}
else
{
lean_object* v_a_5557_; lean_object* v_a_5558_; lean_object* v___x_5560_; uint8_t v_isShared_5561_; uint8_t v_isSharedCheck_5566_; 
lean_dec_ref(v___x_5307_);
lean_del_object(v___x_5304_);
lean_dec_ref(v_a_5291_);
lean_dec_ref(v_ext_5287_);
lean_dec_ref(v_build_5285_);
lean_dec_ref(v_file_5284_);
v_a_5557_ = lean_ctor_get(v___x_5336_, 0);
v_a_5558_ = lean_ctor_get(v___x_5336_, 1);
v_isSharedCheck_5566_ = !lean_is_exclusive(v___x_5336_);
if (v_isSharedCheck_5566_ == 0)
{
v___x_5560_ = v___x_5336_;
v_isShared_5561_ = v_isSharedCheck_5566_;
goto v_resetjp_5559_;
}
else
{
lean_inc(v_a_5558_);
lean_inc(v_a_5557_);
lean_dec(v___x_5336_);
v___x_5560_ = lean_box(0);
v_isShared_5561_ = v_isSharedCheck_5566_;
goto v_resetjp_5559_;
}
v_resetjp_5559_:
{
lean_object* v___x_5562_; lean_object* v___x_5564_; 
v___x_5562_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5562_, 0, v_a_5558_);
lean_ctor_set(v___x_5562_, 1, v_trace_5301_);
lean_ctor_set(v___x_5562_, 2, v_buildTime_5302_);
lean_ctor_set_uint8(v___x_5562_, sizeof(void*)*3, v_action_5299_);
lean_ctor_set_uint8(v___x_5562_, sizeof(void*)*3 + 1, v_wantsRebuild_5300_);
if (v_isShared_5561_ == 0)
{
lean_ctor_set(v___x_5560_, 1, v___x_5562_);
v___x_5564_ = v___x_5560_;
goto v_reusejp_5563_;
}
else
{
lean_object* v_reuseFailAlloc_5565_; 
v_reuseFailAlloc_5565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5565_, 0, v_a_5557_);
lean_ctor_set(v_reuseFailAlloc_5565_, 1, v___x_5562_);
v___x_5564_ = v_reuseFailAlloc_5565_;
goto v_reusejp_5563_;
}
v_reusejp_5563_:
{
return v___x_5564_;
}
}
}
v___jp_5308_:
{
lean_object* v___x_5314_; lean_object* v___x_5316_; 
v___x_5314_ = l_Lake_Artifact_trace(v___y_5309_);
if (v_isShared_5305_ == 0)
{
lean_ctor_set(v___x_5304_, 2, v_buildTime_5313_);
lean_ctor_set(v___x_5304_, 1, v___x_5314_);
lean_ctor_set(v___x_5304_, 0, v_log_5310_);
v___x_5316_ = v___x_5304_;
goto v_reusejp_5315_;
}
else
{
lean_object* v_reuseFailAlloc_5318_; 
v_reuseFailAlloc_5318_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5318_, 0, v_log_5310_);
lean_ctor_set(v_reuseFailAlloc_5318_, 1, v___x_5314_);
lean_ctor_set(v_reuseFailAlloc_5318_, 2, v_buildTime_5313_);
v___x_5316_ = v_reuseFailAlloc_5318_;
goto v_reusejp_5315_;
}
v_reusejp_5315_:
{
lean_object* v___x_5317_; 
lean_ctor_set_uint8(v___x_5316_, sizeof(void*)*3, v_action_5311_);
lean_ctor_set_uint8(v___x_5316_, sizeof(void*)*3 + 1, v_wantsRebuild_5312_);
v___x_5317_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v___y_5309_, v___x_5307_, v___x_5316_);
lean_dec_ref(v___x_5307_);
return v___x_5317_;
}
}
v___jp_5319_:
{
lean_object* v_log_5322_; uint8_t v_action_5323_; uint8_t v_wantsRebuild_5324_; lean_object* v_buildTime_5325_; lean_object* v___x_5327_; uint8_t v_isShared_5328_; uint8_t v_isSharedCheck_5334_; 
v_log_5322_ = lean_ctor_get(v___y_5321_, 0);
v_action_5323_ = lean_ctor_get_uint8(v___y_5321_, sizeof(void*)*3);
v_wantsRebuild_5324_ = lean_ctor_get_uint8(v___y_5321_, sizeof(void*)*3 + 1);
v_buildTime_5325_ = lean_ctor_get(v___y_5321_, 2);
v_isSharedCheck_5334_ = !lean_is_exclusive(v___y_5321_);
if (v_isSharedCheck_5334_ == 0)
{
lean_object* v_unused_5335_; 
v_unused_5335_ = lean_ctor_get(v___y_5321_, 1);
lean_dec(v_unused_5335_);
v___x_5327_ = v___y_5321_;
v_isShared_5328_ = v_isSharedCheck_5334_;
goto v_resetjp_5326_;
}
else
{
lean_inc(v_buildTime_5325_);
lean_inc(v_log_5322_);
lean_dec(v___y_5321_);
v___x_5327_ = lean_box(0);
v_isShared_5328_ = v_isSharedCheck_5334_;
goto v_resetjp_5326_;
}
v_resetjp_5326_:
{
lean_object* v___x_5329_; lean_object* v___x_5331_; 
v___x_5329_ = l_Lake_Artifact_trace(v_art_5320_);
if (v_isShared_5328_ == 0)
{
lean_ctor_set(v___x_5327_, 1, v___x_5329_);
v___x_5331_ = v___x_5327_;
goto v_reusejp_5330_;
}
else
{
lean_object* v_reuseFailAlloc_5333_; 
v_reuseFailAlloc_5333_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5333_, 0, v_log_5322_);
lean_ctor_set(v_reuseFailAlloc_5333_, 1, v___x_5329_);
lean_ctor_set(v_reuseFailAlloc_5333_, 2, v_buildTime_5325_);
lean_ctor_set_uint8(v_reuseFailAlloc_5333_, sizeof(void*)*3, v_action_5323_);
lean_ctor_set_uint8(v_reuseFailAlloc_5333_, sizeof(void*)*3 + 1, v_wantsRebuild_5324_);
v___x_5331_ = v_reuseFailAlloc_5333_;
goto v_reusejp_5330_;
}
v_reusejp_5330_:
{
lean_object* v___x_5332_; 
v___x_5332_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_5320_, v___x_5307_, v___x_5331_);
lean_dec_ref(v___x_5307_);
return v___x_5332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___boxed(lean_object* v_file_5568_, lean_object* v_build_5569_, lean_object* v_text_5570_, lean_object* v_ext_5571_, lean_object* v_restore_5572_, lean_object* v_exe_5573_, lean_object* v_platformIndependent_5574_, lean_object* v_a_5575_, lean_object* v_a_5576_, lean_object* v_a_5577_, lean_object* v_a_5578_, lean_object* v_a_5579_, lean_object* v_a_5580_, lean_object* v_a_5581_){
_start:
{
uint8_t v_text_boxed_5582_; uint8_t v_restore_boxed_5583_; uint8_t v_exe_boxed_5584_; uint8_t v_platformIndependent_boxed_5585_; lean_object* v_res_5586_; 
v_text_boxed_5582_ = lean_unbox(v_text_5570_);
v_restore_boxed_5583_ = lean_unbox(v_restore_5572_);
v_exe_boxed_5584_ = lean_unbox(v_exe_5573_);
v_platformIndependent_boxed_5585_ = lean_unbox(v_platformIndependent_5574_);
v_res_5586_ = l_Lake_buildArtifactUnlessUpToDate(v_file_5568_, v_build_5569_, v_text_boxed_5582_, v_ext_5571_, v_restore_boxed_5583_, v_exe_boxed_5584_, v_platformIndependent_boxed_5585_, v_a_5575_, v_a_5576_, v_a_5577_, v_a_5578_, v_a_5579_, v_a_5580_);
lean_dec_ref(v_a_5579_);
lean_dec(v_a_5578_);
lean_dec(v_a_5577_);
lean_dec(v_a_5576_);
return v_res_5586_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0(lean_object* v_extraDepTrace_5588_, lean_object* v_build_5589_, lean_object* v_file_5590_, uint8_t v_text_5591_, lean_object* v_depInfo_5592_, lean_object* v___y_5593_, lean_object* v___y_5594_, lean_object* v___y_5595_, lean_object* v___y_5596_, lean_object* v___y_5597_, lean_object* v___y_5598_){
_start:
{
lean_object* v___x_5600_; 
lean_inc_ref(v___y_5597_);
lean_inc(v___y_5596_);
lean_inc(v___y_5595_);
lean_inc(v___y_5594_);
lean_inc_ref(v___y_5593_);
v___x_5600_ = lean_apply_7(v_extraDepTrace_5588_, v___y_5593_, v___y_5594_, v___y_5595_, v___y_5596_, v___y_5597_, v___y_5598_, lean_box(0));
if (lean_obj_tag(v___x_5600_) == 0)
{
lean_object* v_a_5601_; lean_object* v_a_5602_; lean_object* v_log_5603_; uint8_t v_action_5604_; uint8_t v_wantsRebuild_5605_; lean_object* v_trace_5606_; lean_object* v_buildTime_5607_; lean_object* v___x_5609_; uint8_t v_isShared_5610_; uint8_t v_isSharedCheck_5638_; 
v_a_5601_ = lean_ctor_get(v___x_5600_, 1);
lean_inc(v_a_5601_);
v_a_5602_ = lean_ctor_get(v___x_5600_, 0);
lean_inc(v_a_5602_);
lean_dec_ref_known(v___x_5600_, 2);
v_log_5603_ = lean_ctor_get(v_a_5601_, 0);
v_action_5604_ = lean_ctor_get_uint8(v_a_5601_, sizeof(void*)*3);
v_wantsRebuild_5605_ = lean_ctor_get_uint8(v_a_5601_, sizeof(void*)*3 + 1);
v_trace_5606_ = lean_ctor_get(v_a_5601_, 1);
v_buildTime_5607_ = lean_ctor_get(v_a_5601_, 2);
v_isSharedCheck_5638_ = !lean_is_exclusive(v_a_5601_);
if (v_isSharedCheck_5638_ == 0)
{
v___x_5609_ = v_a_5601_;
v_isShared_5610_ = v_isSharedCheck_5638_;
goto v_resetjp_5608_;
}
else
{
lean_inc(v_buildTime_5607_);
lean_inc(v_trace_5606_);
lean_inc(v_log_5603_);
lean_dec(v_a_5601_);
v___x_5609_ = lean_box(0);
v_isShared_5610_ = v_isSharedCheck_5638_;
goto v_resetjp_5608_;
}
v_resetjp_5608_:
{
lean_object* v___x_5611_; lean_object* v___x_5613_; 
v___x_5611_ = l_Lake_BuildTrace_mix(v_trace_5606_, v_a_5602_);
if (v_isShared_5610_ == 0)
{
lean_ctor_set(v___x_5609_, 1, v___x_5611_);
v___x_5613_ = v___x_5609_;
goto v_reusejp_5612_;
}
else
{
lean_object* v_reuseFailAlloc_5637_; 
v_reuseFailAlloc_5637_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5637_, 0, v_log_5603_);
lean_ctor_set(v_reuseFailAlloc_5637_, 1, v___x_5611_);
lean_ctor_set(v_reuseFailAlloc_5637_, 2, v_buildTime_5607_);
lean_ctor_set_uint8(v_reuseFailAlloc_5637_, sizeof(void*)*3, v_action_5604_);
lean_ctor_set_uint8(v_reuseFailAlloc_5637_, sizeof(void*)*3 + 1, v_wantsRebuild_5605_);
v___x_5613_ = v_reuseFailAlloc_5637_;
goto v_reusejp_5612_;
}
v_reusejp_5612_:
{
lean_object* v___x_5614_; lean_object* v___x_5615_; uint8_t v___x_5616_; lean_object* v___x_5617_; 
v___x_5614_ = lean_apply_1(v_build_5589_, v_depInfo_5592_);
v___x_5615_ = ((lean_object*)(l_Lake_buildFileAfterDep___redArg___lam__0___closed__0));
v___x_5616_ = 0;
v___x_5617_ = l_Lake_buildArtifactUnlessUpToDate(v_file_5590_, v___x_5614_, v_text_5591_, v___x_5615_, v___x_5616_, v___x_5616_, v___x_5616_, v___y_5593_, v___y_5594_, v___y_5595_, v___y_5596_, v___y_5597_, v___x_5613_);
if (lean_obj_tag(v___x_5617_) == 0)
{
lean_object* v_a_5618_; lean_object* v_a_5619_; lean_object* v___x_5621_; uint8_t v_isShared_5622_; uint8_t v_isSharedCheck_5627_; 
v_a_5618_ = lean_ctor_get(v___x_5617_, 0);
v_a_5619_ = lean_ctor_get(v___x_5617_, 1);
v_isSharedCheck_5627_ = !lean_is_exclusive(v___x_5617_);
if (v_isSharedCheck_5627_ == 0)
{
v___x_5621_ = v___x_5617_;
v_isShared_5622_ = v_isSharedCheck_5627_;
goto v_resetjp_5620_;
}
else
{
lean_inc(v_a_5619_);
lean_inc(v_a_5618_);
lean_dec(v___x_5617_);
v___x_5621_ = lean_box(0);
v_isShared_5622_ = v_isSharedCheck_5627_;
goto v_resetjp_5620_;
}
v_resetjp_5620_:
{
lean_object* v_path_5623_; lean_object* v___x_5625_; 
v_path_5623_ = lean_ctor_get(v_a_5618_, 1);
lean_inc_ref(v_path_5623_);
lean_dec(v_a_5618_);
if (v_isShared_5622_ == 0)
{
lean_ctor_set(v___x_5621_, 0, v_path_5623_);
v___x_5625_ = v___x_5621_;
goto v_reusejp_5624_;
}
else
{
lean_object* v_reuseFailAlloc_5626_; 
v_reuseFailAlloc_5626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5626_, 0, v_path_5623_);
lean_ctor_set(v_reuseFailAlloc_5626_, 1, v_a_5619_);
v___x_5625_ = v_reuseFailAlloc_5626_;
goto v_reusejp_5624_;
}
v_reusejp_5624_:
{
return v___x_5625_;
}
}
}
else
{
lean_object* v_a_5628_; lean_object* v_a_5629_; lean_object* v___x_5631_; uint8_t v_isShared_5632_; uint8_t v_isSharedCheck_5636_; 
v_a_5628_ = lean_ctor_get(v___x_5617_, 0);
v_a_5629_ = lean_ctor_get(v___x_5617_, 1);
v_isSharedCheck_5636_ = !lean_is_exclusive(v___x_5617_);
if (v_isSharedCheck_5636_ == 0)
{
v___x_5631_ = v___x_5617_;
v_isShared_5632_ = v_isSharedCheck_5636_;
goto v_resetjp_5630_;
}
else
{
lean_inc(v_a_5629_);
lean_inc(v_a_5628_);
lean_dec(v___x_5617_);
v___x_5631_ = lean_box(0);
v_isShared_5632_ = v_isSharedCheck_5636_;
goto v_resetjp_5630_;
}
v_resetjp_5630_:
{
lean_object* v___x_5634_; 
if (v_isShared_5632_ == 0)
{
v___x_5634_ = v___x_5631_;
goto v_reusejp_5633_;
}
else
{
lean_object* v_reuseFailAlloc_5635_; 
v_reuseFailAlloc_5635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5635_, 0, v_a_5628_);
lean_ctor_set(v_reuseFailAlloc_5635_, 1, v_a_5629_);
v___x_5634_ = v_reuseFailAlloc_5635_;
goto v_reusejp_5633_;
}
v_reusejp_5633_:
{
return v___x_5634_;
}
}
}
}
}
}
else
{
lean_object* v_a_5639_; lean_object* v_a_5640_; lean_object* v___x_5642_; uint8_t v_isShared_5643_; uint8_t v_isSharedCheck_5647_; 
lean_dec_ref(v___y_5593_);
lean_dec(v_depInfo_5592_);
lean_dec_ref(v_file_5590_);
lean_dec_ref(v_build_5589_);
v_a_5639_ = lean_ctor_get(v___x_5600_, 0);
v_a_5640_ = lean_ctor_get(v___x_5600_, 1);
v_isSharedCheck_5647_ = !lean_is_exclusive(v___x_5600_);
if (v_isSharedCheck_5647_ == 0)
{
v___x_5642_ = v___x_5600_;
v_isShared_5643_ = v_isSharedCheck_5647_;
goto v_resetjp_5641_;
}
else
{
lean_inc(v_a_5640_);
lean_inc(v_a_5639_);
lean_dec(v___x_5600_);
v___x_5642_ = lean_box(0);
v_isShared_5643_ = v_isSharedCheck_5647_;
goto v_resetjp_5641_;
}
v_resetjp_5641_:
{
lean_object* v___x_5645_; 
if (v_isShared_5643_ == 0)
{
v___x_5645_ = v___x_5642_;
goto v_reusejp_5644_;
}
else
{
lean_object* v_reuseFailAlloc_5646_; 
v_reuseFailAlloc_5646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5646_, 0, v_a_5639_);
lean_ctor_set(v_reuseFailAlloc_5646_, 1, v_a_5640_);
v___x_5645_ = v_reuseFailAlloc_5646_;
goto v_reusejp_5644_;
}
v_reusejp_5644_:
{
return v___x_5645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___boxed(lean_object* v_extraDepTrace_5648_, lean_object* v_build_5649_, lean_object* v_file_5650_, lean_object* v_text_5651_, lean_object* v_depInfo_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_, lean_object* v___y_5655_, lean_object* v___y_5656_, lean_object* v___y_5657_, lean_object* v___y_5658_, lean_object* v___y_5659_){
_start:
{
uint8_t v_text_boxed_5660_; lean_object* v_res_5661_; 
v_text_boxed_5660_ = lean_unbox(v_text_5651_);
v_res_5661_ = l_Lake_buildFileAfterDep___redArg___lam__0(v_extraDepTrace_5648_, v_build_5649_, v_file_5650_, v_text_boxed_5660_, v_depInfo_5652_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_);
lean_dec_ref(v___y_5657_);
lean_dec(v___y_5656_);
lean_dec(v___y_5655_);
lean_dec(v___y_5654_);
return v_res_5661_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg(lean_object* v_file_5662_, lean_object* v_dep_5663_, lean_object* v_build_5664_, lean_object* v_extraDepTrace_5665_, uint8_t v_text_5666_, lean_object* v_a_5667_, lean_object* v_a_5668_, lean_object* v_a_5669_, lean_object* v_a_5670_, lean_object* v_a_5671_, lean_object* v_a_5672_){
_start:
{
lean_object* v___x_5674_; lean_object* v___f_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; uint8_t v___x_5678_; lean_object* v___x_5679_; 
v___x_5674_ = lean_box(v_text_5666_);
v___f_5675_ = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_5675_, 0, v_extraDepTrace_5665_);
lean_closure_set(v___f_5675_, 1, v_build_5664_);
lean_closure_set(v___f_5675_, 2, v_file_5662_);
lean_closure_set(v___f_5675_, 3, v___x_5674_);
v___x_5676_ = l_Lake_instDataKindFilePath;
v___x_5677_ = lean_unsigned_to_nat(0u);
v___x_5678_ = 0;
v___x_5679_ = l_Lake_Job_mapM___redArg(v___x_5676_, v_dep_5663_, v___f_5675_, v___x_5677_, v___x_5678_, v_a_5667_, v_a_5668_, v_a_5669_, v_a_5670_, v_a_5671_, v_a_5672_);
return v___x_5679_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___boxed(lean_object* v_file_5680_, lean_object* v_dep_5681_, lean_object* v_build_5682_, lean_object* v_extraDepTrace_5683_, lean_object* v_text_5684_, lean_object* v_a_5685_, lean_object* v_a_5686_, lean_object* v_a_5687_, lean_object* v_a_5688_, lean_object* v_a_5689_, lean_object* v_a_5690_, lean_object* v_a_5691_){
_start:
{
uint8_t v_text_boxed_5692_; lean_object* v_res_5693_; 
v_text_boxed_5692_ = lean_unbox(v_text_5684_);
v_res_5693_ = l_Lake_buildFileAfterDep___redArg(v_file_5680_, v_dep_5681_, v_build_5682_, v_extraDepTrace_5683_, v_text_boxed_5692_, v_a_5685_, v_a_5686_, v_a_5687_, v_a_5688_, v_a_5689_, v_a_5690_);
lean_dec_ref(v_a_5690_);
lean_dec_ref(v_a_5689_);
lean_dec(v_a_5688_);
lean_dec(v_a_5687_);
lean_dec(v_a_5686_);
return v_res_5693_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object* v_00_u03b1_5694_, lean_object* v_file_5695_, lean_object* v_dep_5696_, lean_object* v_build_5697_, lean_object* v_extraDepTrace_5698_, uint8_t v_text_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_, lean_object* v_a_5703_, lean_object* v_a_5704_, lean_object* v_a_5705_){
_start:
{
lean_object* v___x_5707_; lean_object* v___f_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; uint8_t v___x_5711_; lean_object* v___x_5712_; 
v___x_5707_ = lean_box(v_text_5699_);
v___f_5708_ = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_5708_, 0, v_extraDepTrace_5698_);
lean_closure_set(v___f_5708_, 1, v_build_5697_);
lean_closure_set(v___f_5708_, 2, v_file_5695_);
lean_closure_set(v___f_5708_, 3, v___x_5707_);
v___x_5709_ = l_Lake_instDataKindFilePath;
v___x_5710_ = lean_unsigned_to_nat(0u);
v___x_5711_ = 0;
v___x_5712_ = l_Lake_Job_mapM___redArg(v___x_5709_, v_dep_5696_, v___f_5708_, v___x_5710_, v___x_5711_, v_a_5700_, v_a_5701_, v_a_5702_, v_a_5703_, v_a_5704_, v_a_5705_);
return v___x_5712_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___boxed(lean_object* v_00_u03b1_5713_, lean_object* v_file_5714_, lean_object* v_dep_5715_, lean_object* v_build_5716_, lean_object* v_extraDepTrace_5717_, lean_object* v_text_5718_, lean_object* v_a_5719_, lean_object* v_a_5720_, lean_object* v_a_5721_, lean_object* v_a_5722_, lean_object* v_a_5723_, lean_object* v_a_5724_, lean_object* v_a_5725_){
_start:
{
uint8_t v_text_boxed_5726_; lean_object* v_res_5727_; 
v_text_boxed_5726_ = lean_unbox(v_text_5718_);
v_res_5727_ = l_Lake_buildFileAfterDep(v_00_u03b1_5713_, v_file_5714_, v_dep_5715_, v_build_5716_, v_extraDepTrace_5717_, v_text_boxed_5726_, v_a_5719_, v_a_5720_, v_a_5721_, v_a_5722_, v_a_5723_, v_a_5724_);
lean_dec_ref(v_a_5724_);
lean_dec_ref(v_a_5723_);
lean_dec(v_a_5722_);
lean_dec(v_a_5721_);
lean_dec(v_a_5720_);
return v_res_5727_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(lean_object* v_info_5728_){
_start:
{
lean_object* v___x_5730_; 
v___x_5730_ = l_Lake_computeBinFileHash(v_info_5728_);
if (lean_obj_tag(v___x_5730_) == 0)
{
lean_object* v_a_5731_; lean_object* v___x_5732_; 
v_a_5731_ = lean_ctor_get(v___x_5730_, 0);
lean_inc(v_a_5731_);
lean_dec_ref_known(v___x_5730_, 1);
v___x_5732_ = lean_io_metadata(v_info_5728_);
if (lean_obj_tag(v___x_5732_) == 0)
{
lean_object* v_a_5733_; lean_object* v___x_5735_; uint8_t v_isShared_5736_; uint8_t v_isSharedCheck_5744_; 
v_a_5733_ = lean_ctor_get(v___x_5732_, 0);
v_isSharedCheck_5744_ = !lean_is_exclusive(v___x_5732_);
if (v_isSharedCheck_5744_ == 0)
{
v___x_5735_ = v___x_5732_;
v_isShared_5736_ = v_isSharedCheck_5744_;
goto v_resetjp_5734_;
}
else
{
lean_inc(v_a_5733_);
lean_dec(v___x_5732_);
v___x_5735_ = lean_box(0);
v_isShared_5736_ = v_isSharedCheck_5744_;
goto v_resetjp_5734_;
}
v_resetjp_5734_:
{
lean_object* v_modified_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; uint64_t v___x_5740_; lean_object* v___x_5742_; 
v_modified_5737_ = lean_ctor_get(v_a_5733_, 1);
lean_inc_ref(v_modified_5737_);
lean_dec(v_a_5733_);
v___x_5738_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_5739_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_5739_, 0, v_info_5728_);
lean_ctor_set(v___x_5739_, 1, v___x_5738_);
lean_ctor_set(v___x_5739_, 2, v_modified_5737_);
v___x_5740_ = lean_unbox_uint64(v_a_5731_);
lean_dec(v_a_5731_);
lean_ctor_set_uint64(v___x_5739_, sizeof(void*)*3, v___x_5740_);
if (v_isShared_5736_ == 0)
{
lean_ctor_set(v___x_5735_, 0, v___x_5739_);
v___x_5742_ = v___x_5735_;
goto v_reusejp_5741_;
}
else
{
lean_object* v_reuseFailAlloc_5743_; 
v_reuseFailAlloc_5743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5743_, 0, v___x_5739_);
v___x_5742_ = v_reuseFailAlloc_5743_;
goto v_reusejp_5741_;
}
v_reusejp_5741_:
{
return v___x_5742_;
}
}
}
else
{
lean_object* v_a_5745_; lean_object* v___x_5747_; uint8_t v_isShared_5748_; uint8_t v_isSharedCheck_5752_; 
lean_dec(v_a_5731_);
lean_dec_ref(v_info_5728_);
v_a_5745_ = lean_ctor_get(v___x_5732_, 0);
v_isSharedCheck_5752_ = !lean_is_exclusive(v___x_5732_);
if (v_isSharedCheck_5752_ == 0)
{
v___x_5747_ = v___x_5732_;
v_isShared_5748_ = v_isSharedCheck_5752_;
goto v_resetjp_5746_;
}
else
{
lean_inc(v_a_5745_);
lean_dec(v___x_5732_);
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
else
{
lean_object* v_a_5753_; lean_object* v___x_5755_; uint8_t v_isShared_5756_; uint8_t v_isSharedCheck_5760_; 
lean_dec_ref(v_info_5728_);
v_a_5753_ = lean_ctor_get(v___x_5730_, 0);
v_isSharedCheck_5760_ = !lean_is_exclusive(v___x_5730_);
if (v_isSharedCheck_5760_ == 0)
{
v___x_5755_ = v___x_5730_;
v_isShared_5756_ = v_isSharedCheck_5760_;
goto v_resetjp_5754_;
}
else
{
lean_inc(v_a_5753_);
lean_dec(v___x_5730_);
v___x_5755_ = lean_box(0);
v_isShared_5756_ = v_isSharedCheck_5760_;
goto v_resetjp_5754_;
}
v_resetjp_5754_:
{
lean_object* v___x_5758_; 
if (v_isShared_5756_ == 0)
{
v___x_5758_ = v___x_5755_;
goto v_reusejp_5757_;
}
else
{
lean_object* v_reuseFailAlloc_5759_; 
v_reuseFailAlloc_5759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5759_, 0, v_a_5753_);
v___x_5758_ = v_reuseFailAlloc_5759_;
goto v_reusejp_5757_;
}
v_reusejp_5757_:
{
return v___x_5758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0___boxed(lean_object* v_info_5761_, lean_object* v_a_5762_){
_start:
{
lean_object* v_res_5763_; 
v_res_5763_ = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(v_info_5761_);
return v_res_5763_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0(lean_object* v_path_5764_, lean_object* v___y_5765_, lean_object* v___y_5766_, lean_object* v___y_5767_, lean_object* v___y_5768_, lean_object* v___y_5769_, lean_object* v___y_5770_){
_start:
{
lean_object* v_log_5772_; uint8_t v_action_5773_; uint8_t v_wantsRebuild_5774_; lean_object* v_trace_5775_; lean_object* v_buildTime_5776_; lean_object* v___x_5778_; uint8_t v_isShared_5779_; uint8_t v_isSharedCheck_5796_; 
v_log_5772_ = lean_ctor_get(v___y_5770_, 0);
v_action_5773_ = lean_ctor_get_uint8(v___y_5770_, sizeof(void*)*3);
v_wantsRebuild_5774_ = lean_ctor_get_uint8(v___y_5770_, sizeof(void*)*3 + 1);
v_trace_5775_ = lean_ctor_get(v___y_5770_, 1);
v_buildTime_5776_ = lean_ctor_get(v___y_5770_, 2);
v_isSharedCheck_5796_ = !lean_is_exclusive(v___y_5770_);
if (v_isSharedCheck_5796_ == 0)
{
v___x_5778_ = v___y_5770_;
v_isShared_5779_ = v_isSharedCheck_5796_;
goto v_resetjp_5777_;
}
else
{
lean_inc(v_buildTime_5776_);
lean_inc(v_trace_5775_);
lean_inc(v_log_5772_);
lean_dec(v___y_5770_);
v___x_5778_ = lean_box(0);
v_isShared_5779_ = v_isSharedCheck_5796_;
goto v_resetjp_5777_;
}
v_resetjp_5777_:
{
lean_object* v___x_5780_; 
lean_inc_ref(v_path_5764_);
v___x_5780_ = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(v_path_5764_);
if (lean_obj_tag(v___x_5780_) == 0)
{
lean_object* v_a_5781_; lean_object* v___x_5783_; 
lean_dec_ref(v_trace_5775_);
v_a_5781_ = lean_ctor_get(v___x_5780_, 0);
lean_inc(v_a_5781_);
lean_dec_ref_known(v___x_5780_, 1);
if (v_isShared_5779_ == 0)
{
lean_ctor_set(v___x_5778_, 1, v_a_5781_);
v___x_5783_ = v___x_5778_;
goto v_reusejp_5782_;
}
else
{
lean_object* v_reuseFailAlloc_5785_; 
v_reuseFailAlloc_5785_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5785_, 0, v_log_5772_);
lean_ctor_set(v_reuseFailAlloc_5785_, 1, v_a_5781_);
lean_ctor_set(v_reuseFailAlloc_5785_, 2, v_buildTime_5776_);
lean_ctor_set_uint8(v_reuseFailAlloc_5785_, sizeof(void*)*3, v_action_5773_);
lean_ctor_set_uint8(v_reuseFailAlloc_5785_, sizeof(void*)*3 + 1, v_wantsRebuild_5774_);
v___x_5783_ = v_reuseFailAlloc_5785_;
goto v_reusejp_5782_;
}
v_reusejp_5782_:
{
lean_object* v___x_5784_; 
v___x_5784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5784_, 0, v_path_5764_);
lean_ctor_set(v___x_5784_, 1, v___x_5783_);
return v___x_5784_;
}
}
else
{
lean_object* v_a_5786_; lean_object* v___x_5787_; uint8_t v___x_5788_; lean_object* v___x_5789_; lean_object* v___x_5790_; lean_object* v___x_5791_; lean_object* v___x_5793_; 
lean_dec_ref(v_path_5764_);
v_a_5786_ = lean_ctor_get(v___x_5780_, 0);
lean_inc(v_a_5786_);
lean_dec_ref_known(v___x_5780_, 1);
v___x_5787_ = lean_io_error_to_string(v_a_5786_);
v___x_5788_ = 3;
v___x_5789_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5789_, 0, v___x_5787_);
lean_ctor_set_uint8(v___x_5789_, sizeof(void*)*1, v___x_5788_);
v___x_5790_ = lean_array_get_size(v_log_5772_);
v___x_5791_ = lean_array_push(v_log_5772_, v___x_5789_);
if (v_isShared_5779_ == 0)
{
lean_ctor_set(v___x_5778_, 0, v___x_5791_);
v___x_5793_ = v___x_5778_;
goto v_reusejp_5792_;
}
else
{
lean_object* v_reuseFailAlloc_5795_; 
v_reuseFailAlloc_5795_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5795_, 0, v___x_5791_);
lean_ctor_set(v_reuseFailAlloc_5795_, 1, v_trace_5775_);
lean_ctor_set(v_reuseFailAlloc_5795_, 2, v_buildTime_5776_);
lean_ctor_set_uint8(v_reuseFailAlloc_5795_, sizeof(void*)*3, v_action_5773_);
lean_ctor_set_uint8(v_reuseFailAlloc_5795_, sizeof(void*)*3 + 1, v_wantsRebuild_5774_);
v___x_5793_ = v_reuseFailAlloc_5795_;
goto v_reusejp_5792_;
}
v_reusejp_5792_:
{
lean_object* v___x_5794_; 
v___x_5794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5794_, 0, v___x_5790_);
lean_ctor_set(v___x_5794_, 1, v___x_5793_);
return v___x_5794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0___boxed(lean_object* v_path_5797_, lean_object* v___y_5798_, lean_object* v___y_5799_, lean_object* v___y_5800_, lean_object* v___y_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_, lean_object* v___y_5804_){
_start:
{
lean_object* v_res_5805_; 
v_res_5805_ = l_Lake_inputBinFile___redArg___lam__0(v_path_5797_, v___y_5798_, v___y_5799_, v___y_5800_, v___y_5801_, v___y_5802_, v___y_5803_);
lean_dec_ref(v___y_5802_);
lean_dec(v___y_5801_);
lean_dec(v___y_5800_);
lean_dec(v___y_5799_);
lean_dec_ref(v___y_5798_);
return v_res_5805_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg(lean_object* v_path_5807_, lean_object* v_a_5808_, lean_object* v_a_5809_, lean_object* v_a_5810_, lean_object* v_a_5811_, lean_object* v_a_5812_){
_start:
{
lean_object* v___f_5814_; lean_object* v___x_5815_; lean_object* v___x_5816_; lean_object* v___x_5817_; lean_object* v___x_5818_; 
v___f_5814_ = lean_alloc_closure((void*)(l_Lake_inputBinFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5814_, 0, v_path_5807_);
v___x_5815_ = l_Lake_instDataKindFilePath;
v___x_5816_ = lean_unsigned_to_nat(0u);
v___x_5817_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
v___x_5818_ = l_Lake_Job_async___redArg(v___x_5815_, v___f_5814_, v___x_5816_, v___x_5817_, v_a_5808_, v_a_5809_, v_a_5810_, v_a_5811_, v_a_5812_);
return v___x_5818_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___boxed(lean_object* v_path_5819_, lean_object* v_a_5820_, lean_object* v_a_5821_, lean_object* v_a_5822_, lean_object* v_a_5823_, lean_object* v_a_5824_, lean_object* v_a_5825_){
_start:
{
lean_object* v_res_5826_; 
v_res_5826_ = l_Lake_inputBinFile___redArg(v_path_5819_, v_a_5820_, v_a_5821_, v_a_5822_, v_a_5823_, v_a_5824_);
lean_dec_ref(v_a_5824_);
lean_dec(v_a_5823_);
lean_dec(v_a_5822_);
lean_dec(v_a_5821_);
return v_res_5826_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object* v_path_5827_, lean_object* v_a_5828_, lean_object* v_a_5829_, lean_object* v_a_5830_, lean_object* v_a_5831_, lean_object* v_a_5832_, lean_object* v_a_5833_){
_start:
{
lean_object* v___x_5835_; 
v___x_5835_ = l_Lake_inputBinFile___redArg(v_path_5827_, v_a_5828_, v_a_5829_, v_a_5830_, v_a_5831_, v_a_5832_);
return v___x_5835_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___boxed(lean_object* v_path_5836_, lean_object* v_a_5837_, lean_object* v_a_5838_, lean_object* v_a_5839_, lean_object* v_a_5840_, lean_object* v_a_5841_, lean_object* v_a_5842_, lean_object* v_a_5843_){
_start:
{
lean_object* v_res_5844_; 
v_res_5844_ = l_Lake_inputBinFile(v_path_5836_, v_a_5837_, v_a_5838_, v_a_5839_, v_a_5840_, v_a_5841_, v_a_5842_);
lean_dec_ref(v_a_5842_);
lean_dec_ref(v_a_5841_);
lean_dec(v_a_5840_);
lean_dec(v_a_5839_);
lean_dec(v_a_5838_);
return v_res_5844_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(lean_object* v_info_5845_){
_start:
{
lean_object* v___x_5847_; 
v___x_5847_ = l_Lake_computeTextFileHash(v_info_5845_);
if (lean_obj_tag(v___x_5847_) == 0)
{
lean_object* v_a_5848_; lean_object* v___x_5849_; 
v_a_5848_ = lean_ctor_get(v___x_5847_, 0);
lean_inc(v_a_5848_);
lean_dec_ref_known(v___x_5847_, 1);
v___x_5849_ = lean_io_metadata(v_info_5845_);
if (lean_obj_tag(v___x_5849_) == 0)
{
lean_object* v_a_5850_; lean_object* v___x_5852_; uint8_t v_isShared_5853_; uint8_t v_isSharedCheck_5861_; 
v_a_5850_ = lean_ctor_get(v___x_5849_, 0);
v_isSharedCheck_5861_ = !lean_is_exclusive(v___x_5849_);
if (v_isSharedCheck_5861_ == 0)
{
v___x_5852_ = v___x_5849_;
v_isShared_5853_ = v_isSharedCheck_5861_;
goto v_resetjp_5851_;
}
else
{
lean_inc(v_a_5850_);
lean_dec(v___x_5849_);
v___x_5852_ = lean_box(0);
v_isShared_5853_ = v_isSharedCheck_5861_;
goto v_resetjp_5851_;
}
v_resetjp_5851_:
{
lean_object* v_modified_5854_; lean_object* v___x_5855_; lean_object* v___x_5856_; uint64_t v___x_5857_; lean_object* v___x_5859_; 
v_modified_5854_ = lean_ctor_get(v_a_5850_, 1);
lean_inc_ref(v_modified_5854_);
lean_dec(v_a_5850_);
v___x_5855_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_5856_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_5856_, 0, v_info_5845_);
lean_ctor_set(v___x_5856_, 1, v___x_5855_);
lean_ctor_set(v___x_5856_, 2, v_modified_5854_);
v___x_5857_ = lean_unbox_uint64(v_a_5848_);
lean_dec(v_a_5848_);
lean_ctor_set_uint64(v___x_5856_, sizeof(void*)*3, v___x_5857_);
if (v_isShared_5853_ == 0)
{
lean_ctor_set(v___x_5852_, 0, v___x_5856_);
v___x_5859_ = v___x_5852_;
goto v_reusejp_5858_;
}
else
{
lean_object* v_reuseFailAlloc_5860_; 
v_reuseFailAlloc_5860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5860_, 0, v___x_5856_);
v___x_5859_ = v_reuseFailAlloc_5860_;
goto v_reusejp_5858_;
}
v_reusejp_5858_:
{
return v___x_5859_;
}
}
}
else
{
lean_object* v_a_5862_; lean_object* v___x_5864_; uint8_t v_isShared_5865_; uint8_t v_isSharedCheck_5869_; 
lean_dec(v_a_5848_);
lean_dec_ref(v_info_5845_);
v_a_5862_ = lean_ctor_get(v___x_5849_, 0);
v_isSharedCheck_5869_ = !lean_is_exclusive(v___x_5849_);
if (v_isSharedCheck_5869_ == 0)
{
v___x_5864_ = v___x_5849_;
v_isShared_5865_ = v_isSharedCheck_5869_;
goto v_resetjp_5863_;
}
else
{
lean_inc(v_a_5862_);
lean_dec(v___x_5849_);
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
else
{
lean_object* v_a_5870_; lean_object* v___x_5872_; uint8_t v_isShared_5873_; uint8_t v_isSharedCheck_5877_; 
lean_dec_ref(v_info_5845_);
v_a_5870_ = lean_ctor_get(v___x_5847_, 0);
v_isSharedCheck_5877_ = !lean_is_exclusive(v___x_5847_);
if (v_isSharedCheck_5877_ == 0)
{
v___x_5872_ = v___x_5847_;
v_isShared_5873_ = v_isSharedCheck_5877_;
goto v_resetjp_5871_;
}
else
{
lean_inc(v_a_5870_);
lean_dec(v___x_5847_);
v___x_5872_ = lean_box(0);
v_isShared_5873_ = v_isSharedCheck_5877_;
goto v_resetjp_5871_;
}
v_resetjp_5871_:
{
lean_object* v___x_5875_; 
if (v_isShared_5873_ == 0)
{
v___x_5875_ = v___x_5872_;
goto v_reusejp_5874_;
}
else
{
lean_object* v_reuseFailAlloc_5876_; 
v_reuseFailAlloc_5876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5876_, 0, v_a_5870_);
v___x_5875_ = v_reuseFailAlloc_5876_;
goto v_reusejp_5874_;
}
v_reusejp_5874_:
{
return v___x_5875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0___boxed(lean_object* v_info_5878_, lean_object* v_a_5879_){
_start:
{
lean_object* v_res_5880_; 
v_res_5880_ = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(v_info_5878_);
return v_res_5880_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0(lean_object* v_path_5881_, lean_object* v___y_5882_, lean_object* v___y_5883_, lean_object* v___y_5884_, lean_object* v___y_5885_, lean_object* v___y_5886_, lean_object* v___y_5887_){
_start:
{
lean_object* v_log_5889_; uint8_t v_action_5890_; uint8_t v_wantsRebuild_5891_; lean_object* v_trace_5892_; lean_object* v_buildTime_5893_; lean_object* v___x_5895_; uint8_t v_isShared_5896_; uint8_t v_isSharedCheck_5913_; 
v_log_5889_ = lean_ctor_get(v___y_5887_, 0);
v_action_5890_ = lean_ctor_get_uint8(v___y_5887_, sizeof(void*)*3);
v_wantsRebuild_5891_ = lean_ctor_get_uint8(v___y_5887_, sizeof(void*)*3 + 1);
v_trace_5892_ = lean_ctor_get(v___y_5887_, 1);
v_buildTime_5893_ = lean_ctor_get(v___y_5887_, 2);
v_isSharedCheck_5913_ = !lean_is_exclusive(v___y_5887_);
if (v_isSharedCheck_5913_ == 0)
{
v___x_5895_ = v___y_5887_;
v_isShared_5896_ = v_isSharedCheck_5913_;
goto v_resetjp_5894_;
}
else
{
lean_inc(v_buildTime_5893_);
lean_inc(v_trace_5892_);
lean_inc(v_log_5889_);
lean_dec(v___y_5887_);
v___x_5895_ = lean_box(0);
v_isShared_5896_ = v_isSharedCheck_5913_;
goto v_resetjp_5894_;
}
v_resetjp_5894_:
{
lean_object* v___x_5897_; 
lean_inc_ref(v_path_5881_);
v___x_5897_ = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(v_path_5881_);
if (lean_obj_tag(v___x_5897_) == 0)
{
lean_object* v_a_5898_; lean_object* v___x_5900_; 
lean_dec_ref(v_trace_5892_);
v_a_5898_ = lean_ctor_get(v___x_5897_, 0);
lean_inc(v_a_5898_);
lean_dec_ref_known(v___x_5897_, 1);
if (v_isShared_5896_ == 0)
{
lean_ctor_set(v___x_5895_, 1, v_a_5898_);
v___x_5900_ = v___x_5895_;
goto v_reusejp_5899_;
}
else
{
lean_object* v_reuseFailAlloc_5902_; 
v_reuseFailAlloc_5902_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5902_, 0, v_log_5889_);
lean_ctor_set(v_reuseFailAlloc_5902_, 1, v_a_5898_);
lean_ctor_set(v_reuseFailAlloc_5902_, 2, v_buildTime_5893_);
lean_ctor_set_uint8(v_reuseFailAlloc_5902_, sizeof(void*)*3, v_action_5890_);
lean_ctor_set_uint8(v_reuseFailAlloc_5902_, sizeof(void*)*3 + 1, v_wantsRebuild_5891_);
v___x_5900_ = v_reuseFailAlloc_5902_;
goto v_reusejp_5899_;
}
v_reusejp_5899_:
{
lean_object* v___x_5901_; 
v___x_5901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5901_, 0, v_path_5881_);
lean_ctor_set(v___x_5901_, 1, v___x_5900_);
return v___x_5901_;
}
}
else
{
lean_object* v_a_5903_; lean_object* v___x_5904_; uint8_t v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5910_; 
lean_dec_ref(v_path_5881_);
v_a_5903_ = lean_ctor_get(v___x_5897_, 0);
lean_inc(v_a_5903_);
lean_dec_ref_known(v___x_5897_, 1);
v___x_5904_ = lean_io_error_to_string(v_a_5903_);
v___x_5905_ = 3;
v___x_5906_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5906_, 0, v___x_5904_);
lean_ctor_set_uint8(v___x_5906_, sizeof(void*)*1, v___x_5905_);
v___x_5907_ = lean_array_get_size(v_log_5889_);
v___x_5908_ = lean_array_push(v_log_5889_, v___x_5906_);
if (v_isShared_5896_ == 0)
{
lean_ctor_set(v___x_5895_, 0, v___x_5908_);
v___x_5910_ = v___x_5895_;
goto v_reusejp_5909_;
}
else
{
lean_object* v_reuseFailAlloc_5912_; 
v_reuseFailAlloc_5912_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5912_, 0, v___x_5908_);
lean_ctor_set(v_reuseFailAlloc_5912_, 1, v_trace_5892_);
lean_ctor_set(v_reuseFailAlloc_5912_, 2, v_buildTime_5893_);
lean_ctor_set_uint8(v_reuseFailAlloc_5912_, sizeof(void*)*3, v_action_5890_);
lean_ctor_set_uint8(v_reuseFailAlloc_5912_, sizeof(void*)*3 + 1, v_wantsRebuild_5891_);
v___x_5910_ = v_reuseFailAlloc_5912_;
goto v_reusejp_5909_;
}
v_reusejp_5909_:
{
lean_object* v___x_5911_; 
v___x_5911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5911_, 0, v___x_5907_);
lean_ctor_set(v___x_5911_, 1, v___x_5910_);
return v___x_5911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0___boxed(lean_object* v_path_5914_, lean_object* v___y_5915_, lean_object* v___y_5916_, lean_object* v___y_5917_, lean_object* v___y_5918_, lean_object* v___y_5919_, lean_object* v___y_5920_, lean_object* v___y_5921_){
_start:
{
lean_object* v_res_5922_; 
v_res_5922_ = l_Lake_inputTextFile___redArg___lam__0(v_path_5914_, v___y_5915_, v___y_5916_, v___y_5917_, v___y_5918_, v___y_5919_, v___y_5920_);
lean_dec_ref(v___y_5919_);
lean_dec(v___y_5918_);
lean_dec(v___y_5917_);
lean_dec(v___y_5916_);
lean_dec_ref(v___y_5915_);
return v_res_5922_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg(lean_object* v_path_5923_, lean_object* v_a_5924_, lean_object* v_a_5925_, lean_object* v_a_5926_, lean_object* v_a_5927_, lean_object* v_a_5928_){
_start:
{
lean_object* v___f_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; 
v___f_5930_ = lean_alloc_closure((void*)(l_Lake_inputTextFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5930_, 0, v_path_5923_);
v___x_5931_ = l_Lake_instDataKindFilePath;
v___x_5932_ = lean_unsigned_to_nat(0u);
v___x_5933_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
v___x_5934_ = l_Lake_Job_async___redArg(v___x_5931_, v___f_5930_, v___x_5932_, v___x_5933_, v_a_5924_, v_a_5925_, v_a_5926_, v_a_5927_, v_a_5928_);
return v___x_5934_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___boxed(lean_object* v_path_5935_, lean_object* v_a_5936_, lean_object* v_a_5937_, lean_object* v_a_5938_, lean_object* v_a_5939_, lean_object* v_a_5940_, lean_object* v_a_5941_){
_start:
{
lean_object* v_res_5942_; 
v_res_5942_ = l_Lake_inputTextFile___redArg(v_path_5935_, v_a_5936_, v_a_5937_, v_a_5938_, v_a_5939_, v_a_5940_);
lean_dec_ref(v_a_5940_);
lean_dec(v_a_5939_);
lean_dec(v_a_5938_);
lean_dec(v_a_5937_);
return v_res_5942_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object* v_path_5943_, lean_object* v_a_5944_, lean_object* v_a_5945_, lean_object* v_a_5946_, lean_object* v_a_5947_, lean_object* v_a_5948_, lean_object* v_a_5949_){
_start:
{
lean_object* v___x_5951_; 
v___x_5951_ = l_Lake_inputTextFile___redArg(v_path_5943_, v_a_5944_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_);
return v___x_5951_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___boxed(lean_object* v_path_5952_, lean_object* v_a_5953_, lean_object* v_a_5954_, lean_object* v_a_5955_, lean_object* v_a_5956_, lean_object* v_a_5957_, lean_object* v_a_5958_, lean_object* v_a_5959_){
_start:
{
lean_object* v_res_5960_; 
v_res_5960_ = l_Lake_inputTextFile(v_path_5952_, v_a_5953_, v_a_5954_, v_a_5955_, v_a_5956_, v_a_5957_, v_a_5958_);
lean_dec_ref(v_a_5958_);
lean_dec_ref(v_a_5957_);
lean_dec(v_a_5956_);
lean_dec(v_a_5955_);
lean_dec(v_a_5954_);
return v_res_5960_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg(lean_object* v_path_5961_, uint8_t v_text_5962_, lean_object* v_a_5963_, lean_object* v_a_5964_, lean_object* v_a_5965_, lean_object* v_a_5966_, lean_object* v_a_5967_){
_start:
{
if (v_text_5962_ == 0)
{
lean_object* v___x_5969_; 
v___x_5969_ = l_Lake_inputBinFile___redArg(v_path_5961_, v_a_5963_, v_a_5964_, v_a_5965_, v_a_5966_, v_a_5967_);
return v___x_5969_;
}
else
{
lean_object* v___x_5970_; 
v___x_5970_ = l_Lake_inputTextFile___redArg(v_path_5961_, v_a_5963_, v_a_5964_, v_a_5965_, v_a_5966_, v_a_5967_);
return v___x_5970_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg___boxed(lean_object* v_path_5971_, lean_object* v_text_5972_, lean_object* v_a_5973_, lean_object* v_a_5974_, lean_object* v_a_5975_, lean_object* v_a_5976_, lean_object* v_a_5977_, lean_object* v_a_5978_){
_start:
{
uint8_t v_text_boxed_5979_; lean_object* v_res_5980_; 
v_text_boxed_5979_ = lean_unbox(v_text_5972_);
v_res_5980_ = l_Lake_inputFile___redArg(v_path_5971_, v_text_boxed_5979_, v_a_5973_, v_a_5974_, v_a_5975_, v_a_5976_, v_a_5977_);
lean_dec_ref(v_a_5977_);
lean_dec(v_a_5976_);
lean_dec(v_a_5975_);
lean_dec(v_a_5974_);
return v_res_5980_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object* v_path_5981_, uint8_t v_text_5982_, lean_object* v_a_5983_, lean_object* v_a_5984_, lean_object* v_a_5985_, lean_object* v_a_5986_, lean_object* v_a_5987_, lean_object* v_a_5988_){
_start:
{
if (v_text_5982_ == 0)
{
lean_object* v___x_5990_; 
v___x_5990_ = l_Lake_inputBinFile___redArg(v_path_5981_, v_a_5983_, v_a_5984_, v_a_5985_, v_a_5986_, v_a_5987_);
return v___x_5990_;
}
else
{
lean_object* v___x_5991_; 
v___x_5991_ = l_Lake_inputTextFile___redArg(v_path_5981_, v_a_5983_, v_a_5984_, v_a_5985_, v_a_5986_, v_a_5987_);
return v___x_5991_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object* v_path_5992_, lean_object* v_text_5993_, lean_object* v_a_5994_, lean_object* v_a_5995_, lean_object* v_a_5996_, lean_object* v_a_5997_, lean_object* v_a_5998_, lean_object* v_a_5999_, lean_object* v_a_6000_){
_start:
{
uint8_t v_text_boxed_6001_; lean_object* v_res_6002_; 
v_text_boxed_6001_ = lean_unbox(v_text_5993_);
v_res_6002_ = l_Lake_inputFile(v_path_5992_, v_text_boxed_6001_, v_a_5994_, v_a_5995_, v_a_5996_, v_a_5997_, v_a_5998_, v_a_5999_);
lean_dec_ref(v_a_5999_);
lean_dec_ref(v_a_5998_);
lean_dec(v_a_5997_);
lean_dec(v_a_5996_);
lean_dec(v_a_5995_);
return v_res_6002_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0(lean_object* v_x_6003_){
_start:
{
uint8_t v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; 
v___x_6005_ = 1;
v___x_6006_ = lean_box(v___x_6005_);
v___x_6007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6007_, 0, v___x_6006_);
return v___x_6007_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0___boxed(lean_object* v_x_6008_, lean_object* v___y_6009_){
_start:
{
lean_object* v_res_6010_; 
v_res_6010_ = l_Lake_inputDir___lam__0(v_x_6008_);
lean_dec_ref(v_x_6008_);
return v_res_6010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(uint8_t v_text_6011_, size_t v_sz_6012_, size_t v_i_6013_, lean_object* v_bs_6014_, lean_object* v___y_6015_, lean_object* v___y_6016_, lean_object* v___y_6017_, lean_object* v___y_6018_, lean_object* v___y_6019_, lean_object* v___y_6020_){
_start:
{
uint8_t v___x_6022_; 
v___x_6022_ = lean_usize_dec_lt(v_i_6013_, v_sz_6012_);
if (v___x_6022_ == 0)
{
lean_object* v___x_6023_; 
lean_dec_ref(v___y_6015_);
v___x_6023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6023_, 0, v_bs_6014_);
lean_ctor_set(v___x_6023_, 1, v___y_6020_);
return v___x_6023_;
}
else
{
lean_object* v_v_6024_; lean_object* v___x_6025_; lean_object* v_bs_x27_6026_; lean_object* v___y_6028_; 
v_v_6024_ = lean_array_uget(v_bs_6014_, v_i_6013_);
v___x_6025_ = lean_unsigned_to_nat(0u);
v_bs_x27_6026_ = lean_array_uset(v_bs_6014_, v_i_6013_, v___x_6025_);
if (v_text_6011_ == 0)
{
lean_object* v___x_6033_; 
lean_inc_ref(v___y_6015_);
v___x_6033_ = l_Lake_inputBinFile___redArg(v_v_6024_, v___y_6015_, v___y_6016_, v___y_6017_, v___y_6018_, v___y_6019_);
v___y_6028_ = v___x_6033_;
goto v___jp_6027_;
}
else
{
lean_object* v___x_6034_; 
lean_inc_ref(v___y_6015_);
v___x_6034_ = l_Lake_inputTextFile___redArg(v_v_6024_, v___y_6015_, v___y_6016_, v___y_6017_, v___y_6018_, v___y_6019_);
v___y_6028_ = v___x_6034_;
goto v___jp_6027_;
}
v___jp_6027_:
{
size_t v___x_6029_; size_t v___x_6030_; lean_object* v___x_6031_; 
v___x_6029_ = ((size_t)1ULL);
v___x_6030_ = lean_usize_add(v_i_6013_, v___x_6029_);
v___x_6031_ = lean_array_uset(v_bs_x27_6026_, v_i_6013_, v___y_6028_);
v_i_6013_ = v___x_6030_;
v_bs_6014_ = v___x_6031_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0___boxed(lean_object* v_text_6035_, lean_object* v_sz_6036_, lean_object* v_i_6037_, lean_object* v_bs_6038_, lean_object* v___y_6039_, lean_object* v___y_6040_, lean_object* v___y_6041_, lean_object* v___y_6042_, lean_object* v___y_6043_, lean_object* v___y_6044_, lean_object* v___y_6045_){
_start:
{
uint8_t v_text_boxed_6046_; size_t v_sz_boxed_6047_; size_t v_i_boxed_6048_; lean_object* v_res_6049_; 
v_text_boxed_6046_ = lean_unbox(v_text_6035_);
v_sz_boxed_6047_ = lean_unbox_usize(v_sz_6036_);
lean_dec(v_sz_6036_);
v_i_boxed_6048_ = lean_unbox_usize(v_i_6037_);
lean_dec(v_i_6037_);
v_res_6049_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(v_text_boxed_6046_, v_sz_boxed_6047_, v_i_boxed_6048_, v_bs_6038_, v___y_6039_, v___y_6040_, v___y_6041_, v___y_6042_, v___y_6043_, v___y_6044_);
lean_dec_ref(v___y_6043_);
lean_dec(v___y_6042_);
lean_dec(v___y_6041_);
lean_dec(v___y_6040_);
return v_res_6049_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1(uint8_t v_text_6050_, lean_object* v_path_6051_, lean_object* v_ps_6052_, lean_object* v___y_6053_, lean_object* v___y_6054_, lean_object* v___y_6055_, lean_object* v___y_6056_, lean_object* v___y_6057_, lean_object* v___y_6058_){
_start:
{
size_t v_sz_6060_; size_t v___x_6061_; lean_object* v___x_6062_; 
v_sz_6060_ = lean_array_size(v_ps_6052_);
v___x_6061_ = ((size_t)0ULL);
v___x_6062_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(v_text_6050_, v_sz_6060_, v___x_6061_, v_ps_6052_, v___y_6053_, v___y_6054_, v___y_6055_, v___y_6056_, v___y_6057_, v___y_6058_);
if (lean_obj_tag(v___x_6062_) == 0)
{
lean_object* v_a_6063_; lean_object* v_a_6064_; lean_object* v___x_6066_; uint8_t v_isShared_6067_; uint8_t v_isSharedCheck_6072_; 
v_a_6063_ = lean_ctor_get(v___x_6062_, 0);
v_a_6064_ = lean_ctor_get(v___x_6062_, 1);
v_isSharedCheck_6072_ = !lean_is_exclusive(v___x_6062_);
if (v_isSharedCheck_6072_ == 0)
{
v___x_6066_ = v___x_6062_;
v_isShared_6067_ = v_isSharedCheck_6072_;
goto v_resetjp_6065_;
}
else
{
lean_inc(v_a_6064_);
lean_inc(v_a_6063_);
lean_dec(v___x_6062_);
v___x_6066_ = lean_box(0);
v_isShared_6067_ = v_isSharedCheck_6072_;
goto v_resetjp_6065_;
}
v_resetjp_6065_:
{
lean_object* v___x_6068_; lean_object* v___x_6070_; 
v___x_6068_ = l_Lake_Job_collectArray___redArg(v_a_6063_, v_path_6051_);
lean_dec(v_a_6063_);
if (v_isShared_6067_ == 0)
{
lean_ctor_set(v___x_6066_, 0, v___x_6068_);
v___x_6070_ = v___x_6066_;
goto v_reusejp_6069_;
}
else
{
lean_object* v_reuseFailAlloc_6071_; 
v_reuseFailAlloc_6071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6071_, 0, v___x_6068_);
lean_ctor_set(v_reuseFailAlloc_6071_, 1, v_a_6064_);
v___x_6070_ = v_reuseFailAlloc_6071_;
goto v_reusejp_6069_;
}
v_reusejp_6069_:
{
return v___x_6070_;
}
}
}
else
{
lean_object* v_a_6073_; lean_object* v_a_6074_; lean_object* v___x_6076_; uint8_t v_isShared_6077_; uint8_t v_isSharedCheck_6081_; 
lean_dec_ref(v_path_6051_);
v_a_6073_ = lean_ctor_get(v___x_6062_, 0);
v_a_6074_ = lean_ctor_get(v___x_6062_, 1);
v_isSharedCheck_6081_ = !lean_is_exclusive(v___x_6062_);
if (v_isSharedCheck_6081_ == 0)
{
v___x_6076_ = v___x_6062_;
v_isShared_6077_ = v_isSharedCheck_6081_;
goto v_resetjp_6075_;
}
else
{
lean_inc(v_a_6074_);
lean_inc(v_a_6073_);
lean_dec(v___x_6062_);
v___x_6076_ = lean_box(0);
v_isShared_6077_ = v_isSharedCheck_6081_;
goto v_resetjp_6075_;
}
v_resetjp_6075_:
{
lean_object* v___x_6079_; 
if (v_isShared_6077_ == 0)
{
v___x_6079_ = v___x_6076_;
goto v_reusejp_6078_;
}
else
{
lean_object* v_reuseFailAlloc_6080_; 
v_reuseFailAlloc_6080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6080_, 0, v_a_6073_);
lean_ctor_set(v_reuseFailAlloc_6080_, 1, v_a_6074_);
v___x_6079_ = v_reuseFailAlloc_6080_;
goto v_reusejp_6078_;
}
v_reusejp_6078_:
{
return v___x_6079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1___boxed(lean_object* v_text_6082_, lean_object* v_path_6083_, lean_object* v_ps_6084_, lean_object* v___y_6085_, lean_object* v___y_6086_, lean_object* v___y_6087_, lean_object* v___y_6088_, lean_object* v___y_6089_, lean_object* v___y_6090_, lean_object* v___y_6091_){
_start:
{
uint8_t v_text_boxed_6092_; lean_object* v_res_6093_; 
v_text_boxed_6092_ = lean_unbox(v_text_6082_);
v_res_6093_ = l_Lake_inputDir___lam__1(v_text_boxed_6092_, v_path_6083_, v_ps_6084_, v___y_6085_, v___y_6086_, v___y_6087_, v___y_6088_, v___y_6089_, v___y_6090_);
lean_dec_ref(v___y_6089_);
lean_dec(v___y_6088_);
lean_dec(v___y_6087_);
lean_dec(v___y_6086_);
return v_res_6093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(lean_object* v_filter_6094_, lean_object* v_as_6095_, size_t v_i_6096_, size_t v_stop_6097_, lean_object* v_b_6098_, lean_object* v___y_6099_){
_start:
{
lean_object* v_a_6102_; lean_object* v_a_6103_; uint8_t v___x_6107_; 
v___x_6107_ = lean_usize_dec_eq(v_i_6096_, v_stop_6097_);
if (v___x_6107_ == 0)
{
lean_object* v___x_6108_; uint8_t v___x_6109_; 
v___x_6108_ = lean_array_uget_borrowed(v_as_6095_, v_i_6096_);
v___x_6109_ = l_System_FilePath_isDir(v___x_6108_);
if (v___x_6109_ == 0)
{
lean_object* v___x_6110_; uint8_t v___x_6111_; 
lean_inc_ref(v_filter_6094_);
lean_inc(v___x_6108_);
v___x_6110_ = lean_apply_1(v_filter_6094_, v___x_6108_);
v___x_6111_ = lean_unbox(v___x_6110_);
if (v___x_6111_ == 0)
{
v_a_6102_ = v_b_6098_;
v_a_6103_ = v___y_6099_;
goto v___jp_6101_;
}
else
{
lean_object* v___x_6112_; 
lean_inc(v___x_6108_);
v___x_6112_ = lean_array_push(v_b_6098_, v___x_6108_);
v_a_6102_ = v___x_6112_;
v_a_6103_ = v___y_6099_;
goto v___jp_6101_;
}
}
else
{
v_a_6102_ = v_b_6098_;
v_a_6103_ = v___y_6099_;
goto v___jp_6101_;
}
}
else
{
lean_object* v___x_6113_; 
lean_dec_ref(v_filter_6094_);
v___x_6113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6113_, 0, v_b_6098_);
lean_ctor_set(v___x_6113_, 1, v___y_6099_);
return v___x_6113_;
}
v___jp_6101_:
{
size_t v___x_6104_; size_t v___x_6105_; 
v___x_6104_ = ((size_t)1ULL);
v___x_6105_ = lean_usize_add(v_i_6096_, v___x_6104_);
v_i_6096_ = v___x_6105_;
v_b_6098_ = v_a_6102_;
v___y_6099_ = v_a_6103_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg___boxed(lean_object* v_filter_6114_, lean_object* v_as_6115_, lean_object* v_i_6116_, lean_object* v_stop_6117_, lean_object* v_b_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_){
_start:
{
size_t v_i_boxed_6121_; size_t v_stop_boxed_6122_; lean_object* v_res_6123_; 
v_i_boxed_6121_ = lean_unbox_usize(v_i_6116_);
lean_dec(v_i_6116_);
v_stop_boxed_6122_ = lean_unbox_usize(v_stop_6117_);
lean_dec(v_stop_6117_);
v_res_6123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6114_, v_as_6115_, v_i_boxed_6121_, v_stop_boxed_6122_, v_b_6118_, v___y_6119_);
lean_dec_ref(v_as_6115_);
return v_res_6123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(lean_object* v_hi_6124_, lean_object* v_pivot_6125_, lean_object* v_as_6126_, lean_object* v_i_6127_, lean_object* v_k_6128_){
_start:
{
uint8_t v___x_6129_; 
v___x_6129_ = lean_nat_dec_lt(v_k_6128_, v_hi_6124_);
if (v___x_6129_ == 0)
{
lean_object* v___x_6130_; lean_object* v___x_6131_; 
lean_dec(v_k_6128_);
v___x_6130_ = lean_array_fswap(v_as_6126_, v_i_6127_, v_hi_6124_);
v___x_6131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6131_, 0, v_i_6127_);
lean_ctor_set(v___x_6131_, 1, v___x_6130_);
return v___x_6131_;
}
else
{
lean_object* v___x_6132_; uint8_t v___x_6133_; 
v___x_6132_ = lean_array_fget_borrowed(v_as_6126_, v_k_6128_);
v___x_6133_ = lean_string_dec_lt(v___x_6132_, v_pivot_6125_);
if (v___x_6133_ == 0)
{
lean_object* v___x_6134_; lean_object* v___x_6135_; 
v___x_6134_ = lean_unsigned_to_nat(1u);
v___x_6135_ = lean_nat_add(v_k_6128_, v___x_6134_);
lean_dec(v_k_6128_);
v_k_6128_ = v___x_6135_;
goto _start;
}
else
{
lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; 
v___x_6137_ = lean_array_fswap(v_as_6126_, v_i_6127_, v_k_6128_);
v___x_6138_ = lean_unsigned_to_nat(1u);
v___x_6139_ = lean_nat_add(v_i_6127_, v___x_6138_);
lean_dec(v_i_6127_);
v___x_6140_ = lean_nat_add(v_k_6128_, v___x_6138_);
lean_dec(v_k_6128_);
v_as_6126_ = v___x_6137_;
v_i_6127_ = v___x_6139_;
v_k_6128_ = v___x_6140_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg___boxed(lean_object* v_hi_6142_, lean_object* v_pivot_6143_, lean_object* v_as_6144_, lean_object* v_i_6145_, lean_object* v_k_6146_){
_start:
{
lean_object* v_res_6147_; 
v_res_6147_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(v_hi_6142_, v_pivot_6143_, v_as_6144_, v_i_6145_, v_k_6146_);
lean_dec_ref(v_pivot_6143_);
lean_dec(v_hi_6142_);
return v_res_6147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(lean_object* v_n_6148_, lean_object* v_as_6149_, lean_object* v_lo_6150_, lean_object* v_hi_6151_){
_start:
{
lean_object* v___y_6153_; uint8_t v___x_6163_; 
v___x_6163_ = lean_nat_dec_lt(v_lo_6150_, v_hi_6151_);
if (v___x_6163_ == 0)
{
lean_dec(v_lo_6150_);
return v_as_6149_;
}
else
{
lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v_mid_6166_; lean_object* v___y_6168_; lean_object* v___y_6174_; lean_object* v___x_6179_; lean_object* v___x_6180_; uint8_t v___x_6181_; 
v___x_6164_ = lean_nat_add(v_lo_6150_, v_hi_6151_);
v___x_6165_ = lean_unsigned_to_nat(1u);
v_mid_6166_ = lean_nat_shiftr(v___x_6164_, v___x_6165_);
lean_dec(v___x_6164_);
v___x_6179_ = lean_array_fget_borrowed(v_as_6149_, v_mid_6166_);
v___x_6180_ = lean_array_fget_borrowed(v_as_6149_, v_lo_6150_);
v___x_6181_ = lean_string_dec_lt(v___x_6179_, v___x_6180_);
if (v___x_6181_ == 0)
{
v___y_6174_ = v_as_6149_;
goto v___jp_6173_;
}
else
{
lean_object* v___x_6182_; 
v___x_6182_ = lean_array_fswap(v_as_6149_, v_lo_6150_, v_mid_6166_);
v___y_6174_ = v___x_6182_;
goto v___jp_6173_;
}
v___jp_6167_:
{
lean_object* v___x_6169_; lean_object* v___x_6170_; uint8_t v___x_6171_; 
v___x_6169_ = lean_array_fget_borrowed(v___y_6168_, v_mid_6166_);
v___x_6170_ = lean_array_fget_borrowed(v___y_6168_, v_hi_6151_);
v___x_6171_ = lean_string_dec_lt(v___x_6169_, v___x_6170_);
if (v___x_6171_ == 0)
{
lean_dec(v_mid_6166_);
v___y_6153_ = v___y_6168_;
goto v___jp_6152_;
}
else
{
lean_object* v___x_6172_; 
v___x_6172_ = lean_array_fswap(v___y_6168_, v_mid_6166_, v_hi_6151_);
lean_dec(v_mid_6166_);
v___y_6153_ = v___x_6172_;
goto v___jp_6152_;
}
}
v___jp_6173_:
{
lean_object* v___x_6175_; lean_object* v___x_6176_; uint8_t v___x_6177_; 
v___x_6175_ = lean_array_fget_borrowed(v___y_6174_, v_hi_6151_);
v___x_6176_ = lean_array_fget_borrowed(v___y_6174_, v_lo_6150_);
v___x_6177_ = lean_string_dec_lt(v___x_6175_, v___x_6176_);
if (v___x_6177_ == 0)
{
v___y_6168_ = v___y_6174_;
goto v___jp_6167_;
}
else
{
lean_object* v___x_6178_; 
v___x_6178_ = lean_array_fswap(v___y_6174_, v_lo_6150_, v_hi_6151_);
v___y_6168_ = v___x_6178_;
goto v___jp_6167_;
}
}
}
v___jp_6152_:
{
lean_object* v_pivot_6154_; lean_object* v___x_6155_; lean_object* v_fst_6156_; lean_object* v_snd_6157_; uint8_t v___x_6158_; 
v_pivot_6154_ = lean_array_fget(v___y_6153_, v_hi_6151_);
lean_inc_n(v_lo_6150_, 2);
v___x_6155_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(v_hi_6151_, v_pivot_6154_, v___y_6153_, v_lo_6150_, v_lo_6150_);
lean_dec(v_pivot_6154_);
v_fst_6156_ = lean_ctor_get(v___x_6155_, 0);
lean_inc(v_fst_6156_);
v_snd_6157_ = lean_ctor_get(v___x_6155_, 1);
lean_inc(v_snd_6157_);
lean_dec_ref(v___x_6155_);
v___x_6158_ = lean_nat_dec_le(v_hi_6151_, v_fst_6156_);
if (v___x_6158_ == 0)
{
lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; 
v___x_6159_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_n_6148_, v_snd_6157_, v_lo_6150_, v_fst_6156_);
v___x_6160_ = lean_unsigned_to_nat(1u);
v___x_6161_ = lean_nat_add(v_fst_6156_, v___x_6160_);
lean_dec(v_fst_6156_);
v_as_6149_ = v___x_6159_;
v_lo_6150_ = v___x_6161_;
goto _start;
}
else
{
lean_dec(v_fst_6156_);
lean_dec(v_lo_6150_);
return v_snd_6157_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___boxed(lean_object* v_n_6183_, lean_object* v_as_6184_, lean_object* v_lo_6185_, lean_object* v_hi_6186_){
_start:
{
lean_object* v_res_6187_; 
v_res_6187_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_n_6183_, v_as_6184_, v_lo_6185_, v_hi_6186_);
lean_dec(v_hi_6186_);
lean_dec(v_n_6183_);
return v_res_6187_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2(lean_object* v_path_6190_, lean_object* v___f_6191_, lean_object* v_filter_6192_, lean_object* v___y_6193_, lean_object* v___y_6194_, lean_object* v___y_6195_, lean_object* v___y_6196_, lean_object* v___y_6197_, lean_object* v___y_6198_){
_start:
{
lean_object* v___y_6201_; lean_object* v___y_6202_; lean_object* v___y_6205_; lean_object* v___y_6206_; lean_object* v___y_6207_; lean_object* v___y_6208_; lean_object* v___y_6209_; lean_object* v___y_6212_; lean_object* v___y_6213_; lean_object* v___y_6214_; lean_object* v___y_6215_; lean_object* v___y_6216_; lean_object* v_log_6218_; uint8_t v_action_6219_; uint8_t v_wantsRebuild_6220_; lean_object* v_trace_6221_; lean_object* v_buildTime_6222_; lean_object* v___x_6223_; 
v_log_6218_ = lean_ctor_get(v___y_6198_, 0);
v_action_6219_ = lean_ctor_get_uint8(v___y_6198_, sizeof(void*)*3);
v_wantsRebuild_6220_ = lean_ctor_get_uint8(v___y_6198_, sizeof(void*)*3 + 1);
v_trace_6221_ = lean_ctor_get(v___y_6198_, 1);
v_buildTime_6222_ = lean_ctor_get(v___y_6198_, 2);
v___x_6223_ = l_System_FilePath_walkDir(v_path_6190_, v___f_6191_);
if (lean_obj_tag(v___x_6223_) == 0)
{
lean_object* v_a_6224_; lean_object* v___x_6225_; lean_object* v_a_6227_; lean_object* v_a_6228_; lean_object* v___y_6235_; lean_object* v___x_6238_; lean_object* v___x_6239_; uint8_t v___x_6240_; 
v_a_6224_ = lean_ctor_get(v___x_6223_, 0);
lean_inc(v_a_6224_);
lean_dec_ref_known(v___x_6223_, 1);
v___x_6225_ = lean_unsigned_to_nat(0u);
v___x_6238_ = lean_array_get_size(v_a_6224_);
v___x_6239_ = ((lean_object*)(l_Lake_inputDir___lam__2___closed__0));
v___x_6240_ = lean_nat_dec_lt(v___x_6225_, v___x_6238_);
if (v___x_6240_ == 0)
{
lean_dec(v_a_6224_);
lean_dec_ref(v_filter_6192_);
v_a_6227_ = v___x_6239_;
v_a_6228_ = v___y_6198_;
goto v___jp_6226_;
}
else
{
uint8_t v___x_6241_; 
v___x_6241_ = lean_nat_dec_le(v___x_6238_, v___x_6238_);
if (v___x_6241_ == 0)
{
if (v___x_6240_ == 0)
{
lean_dec(v_a_6224_);
lean_dec_ref(v_filter_6192_);
v_a_6227_ = v___x_6239_;
v_a_6228_ = v___y_6198_;
goto v___jp_6226_;
}
else
{
size_t v___x_6242_; size_t v___x_6243_; lean_object* v___x_6244_; 
v___x_6242_ = ((size_t)0ULL);
v___x_6243_ = lean_usize_of_nat(v___x_6238_);
v___x_6244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6192_, v_a_6224_, v___x_6242_, v___x_6243_, v___x_6239_, v___y_6198_);
lean_dec(v_a_6224_);
v___y_6235_ = v___x_6244_;
goto v___jp_6234_;
}
}
else
{
size_t v___x_6245_; size_t v___x_6246_; lean_object* v___x_6247_; 
v___x_6245_ = ((size_t)0ULL);
v___x_6246_ = lean_usize_of_nat(v___x_6238_);
v___x_6247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6192_, v_a_6224_, v___x_6245_, v___x_6246_, v___x_6239_, v___y_6198_);
lean_dec(v_a_6224_);
v___y_6235_ = v___x_6247_;
goto v___jp_6234_;
}
}
v___jp_6226_:
{
lean_object* v___x_6229_; uint8_t v___x_6230_; 
v___x_6229_ = lean_array_get_size(v_a_6227_);
v___x_6230_ = lean_nat_dec_eq(v___x_6229_, v___x_6225_);
if (v___x_6230_ == 0)
{
lean_object* v___x_6231_; lean_object* v___x_6232_; uint8_t v___x_6233_; 
v___x_6231_ = lean_unsigned_to_nat(1u);
v___x_6232_ = lean_nat_sub(v___x_6229_, v___x_6231_);
v___x_6233_ = lean_nat_dec_le(v___x_6225_, v___x_6232_);
if (v___x_6233_ == 0)
{
lean_inc(v___x_6232_);
v___y_6212_ = v___x_6229_;
v___y_6213_ = v___x_6232_;
v___y_6214_ = v_a_6228_;
v___y_6215_ = v_a_6227_;
v___y_6216_ = v___x_6232_;
goto v___jp_6211_;
}
else
{
v___y_6212_ = v___x_6229_;
v___y_6213_ = v___x_6232_;
v___y_6214_ = v_a_6228_;
v___y_6215_ = v_a_6227_;
v___y_6216_ = v___x_6225_;
goto v___jp_6211_;
}
}
else
{
v___y_6201_ = v_a_6228_;
v___y_6202_ = v_a_6227_;
goto v___jp_6200_;
}
}
v___jp_6234_:
{
if (lean_obj_tag(v___y_6235_) == 0)
{
lean_object* v_a_6236_; lean_object* v_a_6237_; 
v_a_6236_ = lean_ctor_get(v___y_6235_, 0);
lean_inc(v_a_6236_);
v_a_6237_ = lean_ctor_get(v___y_6235_, 1);
lean_inc(v_a_6237_);
lean_dec_ref_known(v___y_6235_, 2);
v_a_6227_ = v_a_6236_;
v_a_6228_ = v_a_6237_;
goto v___jp_6226_;
}
else
{
return v___y_6235_;
}
}
}
else
{
lean_object* v___x_6249_; uint8_t v_isShared_6250_; uint8_t v_isSharedCheck_6261_; 
lean_inc(v_buildTime_6222_);
lean_inc_ref(v_trace_6221_);
lean_inc_ref(v_log_6218_);
lean_dec_ref(v_filter_6192_);
v_isSharedCheck_6261_ = !lean_is_exclusive(v___y_6198_);
if (v_isSharedCheck_6261_ == 0)
{
lean_object* v_unused_6262_; lean_object* v_unused_6263_; lean_object* v_unused_6264_; 
v_unused_6262_ = lean_ctor_get(v___y_6198_, 2);
lean_dec(v_unused_6262_);
v_unused_6263_ = lean_ctor_get(v___y_6198_, 1);
lean_dec(v_unused_6263_);
v_unused_6264_ = lean_ctor_get(v___y_6198_, 0);
lean_dec(v_unused_6264_);
v___x_6249_ = v___y_6198_;
v_isShared_6250_ = v_isSharedCheck_6261_;
goto v_resetjp_6248_;
}
else
{
lean_dec(v___y_6198_);
v___x_6249_ = lean_box(0);
v_isShared_6250_ = v_isSharedCheck_6261_;
goto v_resetjp_6248_;
}
v_resetjp_6248_:
{
lean_object* v_a_6251_; lean_object* v___x_6252_; uint8_t v___x_6253_; lean_object* v___x_6254_; lean_object* v___x_6255_; lean_object* v___x_6256_; lean_object* v___x_6258_; 
v_a_6251_ = lean_ctor_get(v___x_6223_, 0);
lean_inc(v_a_6251_);
lean_dec_ref_known(v___x_6223_, 1);
v___x_6252_ = lean_io_error_to_string(v_a_6251_);
v___x_6253_ = 3;
v___x_6254_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6254_, 0, v___x_6252_);
lean_ctor_set_uint8(v___x_6254_, sizeof(void*)*1, v___x_6253_);
v___x_6255_ = lean_array_get_size(v_log_6218_);
v___x_6256_ = lean_array_push(v_log_6218_, v___x_6254_);
if (v_isShared_6250_ == 0)
{
lean_ctor_set(v___x_6249_, 0, v___x_6256_);
v___x_6258_ = v___x_6249_;
goto v_reusejp_6257_;
}
else
{
lean_object* v_reuseFailAlloc_6260_; 
v_reuseFailAlloc_6260_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6260_, 0, v___x_6256_);
lean_ctor_set(v_reuseFailAlloc_6260_, 1, v_trace_6221_);
lean_ctor_set(v_reuseFailAlloc_6260_, 2, v_buildTime_6222_);
lean_ctor_set_uint8(v_reuseFailAlloc_6260_, sizeof(void*)*3, v_action_6219_);
lean_ctor_set_uint8(v_reuseFailAlloc_6260_, sizeof(void*)*3 + 1, v_wantsRebuild_6220_);
v___x_6258_ = v_reuseFailAlloc_6260_;
goto v_reusejp_6257_;
}
v_reusejp_6257_:
{
lean_object* v___x_6259_; 
v___x_6259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6259_, 0, v___x_6255_);
lean_ctor_set(v___x_6259_, 1, v___x_6258_);
return v___x_6259_;
}
}
}
v___jp_6200_:
{
lean_object* v___x_6203_; 
v___x_6203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6203_, 0, v___y_6202_);
lean_ctor_set(v___x_6203_, 1, v___y_6201_);
return v___x_6203_;
}
v___jp_6204_:
{
lean_object* v___x_6210_; 
v___x_6210_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v___y_6205_, v___y_6208_, v___y_6207_, v___y_6209_);
lean_dec(v___y_6209_);
lean_dec(v___y_6205_);
v___y_6201_ = v___y_6206_;
v___y_6202_ = v___x_6210_;
goto v___jp_6200_;
}
v___jp_6211_:
{
uint8_t v___x_6217_; 
v___x_6217_ = lean_nat_dec_le(v___y_6216_, v___y_6213_);
if (v___x_6217_ == 0)
{
lean_dec(v___y_6213_);
lean_inc(v___y_6216_);
v___y_6205_ = v___y_6212_;
v___y_6206_ = v___y_6214_;
v___y_6207_ = v___y_6216_;
v___y_6208_ = v___y_6215_;
v___y_6209_ = v___y_6216_;
goto v___jp_6204_;
}
else
{
v___y_6205_ = v___y_6212_;
v___y_6206_ = v___y_6214_;
v___y_6207_ = v___y_6216_;
v___y_6208_ = v___y_6215_;
v___y_6209_ = v___y_6213_;
goto v___jp_6204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2___boxed(lean_object* v_path_6265_, lean_object* v___f_6266_, lean_object* v_filter_6267_, lean_object* v___y_6268_, lean_object* v___y_6269_, lean_object* v___y_6270_, lean_object* v___y_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_, lean_object* v___y_6274_){
_start:
{
lean_object* v_res_6275_; 
v_res_6275_ = l_Lake_inputDir___lam__2(v_path_6265_, v___f_6266_, v_filter_6267_, v___y_6268_, v___y_6269_, v___y_6270_, v___y_6271_, v___y_6272_, v___y_6273_);
lean_dec_ref(v___y_6272_);
lean_dec(v___y_6271_);
lean_dec(v___y_6270_);
lean_dec(v___y_6269_);
lean_dec_ref(v___y_6268_);
return v_res_6275_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir(lean_object* v_path_6277_, uint8_t v_text_6278_, lean_object* v_filter_6279_, lean_object* v_a_6280_, lean_object* v_a_6281_, lean_object* v_a_6282_, lean_object* v_a_6283_, lean_object* v_a_6284_, lean_object* v_a_6285_){
_start:
{
lean_object* v___f_6287_; lean_object* v___x_6288_; lean_object* v___f_6289_; lean_object* v___f_6290_; lean_object* v___x_6291_; lean_object* v___x_6292_; lean_object* v___x_6293_; lean_object* v___x_6294_; uint8_t v___x_6295_; lean_object* v___x_6296_; 
v___f_6287_ = ((lean_object*)(l_Lake_inputDir___closed__0));
v___x_6288_ = lean_box(v_text_6278_);
lean_inc_ref(v_path_6277_);
v___f_6289_ = lean_alloc_closure((void*)(l_Lake_inputDir___lam__1___boxed), 10, 2);
lean_closure_set(v___f_6289_, 0, v___x_6288_);
lean_closure_set(v___f_6289_, 1, v_path_6277_);
v___f_6290_ = lean_alloc_closure((void*)(l_Lake_inputDir___lam__2___boxed), 10, 3);
lean_closure_set(v___f_6290_, 0, v_path_6277_);
lean_closure_set(v___f_6290_, 1, v___f_6287_);
lean_closure_set(v___f_6290_, 2, v_filter_6279_);
v___x_6291_ = lean_box(0);
v___x_6292_ = lean_unsigned_to_nat(0u);
v___x_6293_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
lean_inc_ref(v_a_6280_);
v___x_6294_ = l_Lake_Job_async___redArg(v___x_6291_, v___f_6290_, v___x_6292_, v___x_6293_, v_a_6280_, v_a_6281_, v_a_6282_, v_a_6283_, v_a_6284_);
v___x_6295_ = 0;
v___x_6296_ = l_Lake_Job_bindM___redArg(v___x_6291_, v___x_6294_, v___f_6289_, v___x_6292_, v___x_6295_, v_a_6280_, v_a_6281_, v_a_6282_, v_a_6283_, v_a_6284_, v_a_6285_);
return v___x_6296_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___boxed(lean_object* v_path_6297_, lean_object* v_text_6298_, lean_object* v_filter_6299_, lean_object* v_a_6300_, lean_object* v_a_6301_, lean_object* v_a_6302_, lean_object* v_a_6303_, lean_object* v_a_6304_, lean_object* v_a_6305_, lean_object* v_a_6306_){
_start:
{
uint8_t v_text_boxed_6307_; lean_object* v_res_6308_; 
v_text_boxed_6307_ = lean_unbox(v_text_6298_);
v_res_6308_ = l_Lake_inputDir(v_path_6297_, v_text_boxed_6307_, v_filter_6299_, v_a_6300_, v_a_6301_, v_a_6302_, v_a_6303_, v_a_6304_, v_a_6305_);
lean_dec_ref(v_a_6305_);
lean_dec_ref(v_a_6304_);
lean_dec(v_a_6303_);
lean_dec(v_a_6302_);
lean_dec(v_a_6301_);
return v_res_6308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(lean_object* v_n_6309_, lean_object* v_as_6310_, lean_object* v_lo_6311_, lean_object* v_hi_6312_, lean_object* v_w_6313_, lean_object* v_hlo_6314_, lean_object* v_hhi_6315_){
_start:
{
lean_object* v___x_6316_; 
v___x_6316_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_n_6309_, v_as_6310_, v_lo_6311_, v_hi_6312_);
return v___x_6316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___boxed(lean_object* v_n_6317_, lean_object* v_as_6318_, lean_object* v_lo_6319_, lean_object* v_hi_6320_, lean_object* v_w_6321_, lean_object* v_hlo_6322_, lean_object* v_hhi_6323_){
_start:
{
lean_object* v_res_6324_; 
v_res_6324_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(v_n_6317_, v_as_6318_, v_lo_6319_, v_hi_6320_, v_w_6321_, v_hlo_6322_, v_hhi_6323_);
lean_dec(v_hi_6320_);
lean_dec(v_n_6317_);
return v_res_6324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(lean_object* v_filter_6325_, lean_object* v_as_6326_, size_t v_i_6327_, size_t v_stop_6328_, lean_object* v_b_6329_, lean_object* v___y_6330_, lean_object* v___y_6331_, lean_object* v___y_6332_, lean_object* v___y_6333_, lean_object* v___y_6334_, lean_object* v___y_6335_){
_start:
{
lean_object* v___x_6337_; 
v___x_6337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6325_, v_as_6326_, v_i_6327_, v_stop_6328_, v_b_6329_, v___y_6335_);
return v___x_6337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___boxed(lean_object* v_filter_6338_, lean_object* v_as_6339_, lean_object* v_i_6340_, lean_object* v_stop_6341_, lean_object* v_b_6342_, lean_object* v___y_6343_, lean_object* v___y_6344_, lean_object* v___y_6345_, lean_object* v___y_6346_, lean_object* v___y_6347_, lean_object* v___y_6348_, lean_object* v___y_6349_){
_start:
{
size_t v_i_boxed_6350_; size_t v_stop_boxed_6351_; lean_object* v_res_6352_; 
v_i_boxed_6350_ = lean_unbox_usize(v_i_6340_);
lean_dec(v_i_6340_);
v_stop_boxed_6351_ = lean_unbox_usize(v_stop_6341_);
lean_dec(v_stop_6341_);
v_res_6352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(v_filter_6338_, v_as_6339_, v_i_boxed_6350_, v_stop_boxed_6351_, v_b_6342_, v___y_6343_, v___y_6344_, v___y_6345_, v___y_6346_, v___y_6347_, v___y_6348_);
lean_dec_ref(v___y_6347_);
lean_dec(v___y_6346_);
lean_dec(v___y_6345_);
lean_dec(v___y_6344_);
lean_dec_ref(v___y_6343_);
lean_dec_ref(v_as_6339_);
return v_res_6352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1(lean_object* v_n_6353_, lean_object* v_lo_6354_, lean_object* v_hi_6355_, lean_object* v_hhi_6356_, lean_object* v_pivot_6357_, lean_object* v_as_6358_, lean_object* v_i_6359_, lean_object* v_k_6360_, lean_object* v_ilo_6361_, lean_object* v_ik_6362_, lean_object* v_w_6363_){
_start:
{
lean_object* v___x_6364_; 
v___x_6364_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(v_hi_6355_, v_pivot_6357_, v_as_6358_, v_i_6359_, v_k_6360_);
return v___x_6364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___boxed(lean_object* v_n_6365_, lean_object* v_lo_6366_, lean_object* v_hi_6367_, lean_object* v_hhi_6368_, lean_object* v_pivot_6369_, lean_object* v_as_6370_, lean_object* v_i_6371_, lean_object* v_k_6372_, lean_object* v_ilo_6373_, lean_object* v_ik_6374_, lean_object* v_w_6375_){
_start:
{
lean_object* v_res_6376_; 
v_res_6376_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1(v_n_6365_, v_lo_6366_, v_hi_6367_, v_hhi_6368_, v_pivot_6369_, v_as_6370_, v_i_6371_, v_k_6372_, v_ilo_6373_, v_ik_6374_, v_w_6375_);
lean_dec_ref(v_pivot_6369_);
lean_dec(v_hi_6367_);
lean_dec(v_lo_6366_);
lean_dec(v_n_6365_);
return v_res_6376_;
}
}
LEAN_EXPORT uint64_t l_Lake_buildO___lam__0(uint64_t v_ts_6377_, lean_object* v_t_6378_){
_start:
{
uint64_t v___x_6379_; uint64_t v___x_6380_; uint64_t v___x_6381_; uint64_t v___x_6382_; 
v___x_6379_ = l_Lake_Hash_nil;
v___x_6380_ = lean_string_hash(v_t_6378_);
v___x_6381_ = lean_uint64_mix_hash(v___x_6379_, v___x_6380_);
v___x_6382_ = lean_uint64_mix_hash(v_ts_6377_, v___x_6381_);
return v___x_6382_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__0___boxed(lean_object* v_ts_6383_, lean_object* v_t_6384_){
_start:
{
uint64_t v_ts_boxed_6385_; uint64_t v_res_6386_; lean_object* v_r_6387_; 
v_ts_boxed_6385_ = lean_unbox_uint64(v_ts_6383_);
lean_dec_ref(v_ts_6383_);
v_res_6386_ = l_Lake_buildO___lam__0(v_ts_boxed_6385_, v_t_6384_);
lean_dec_ref(v_t_6384_);
v_r_6387_ = lean_box_uint64(v_res_6386_);
return v_r_6387_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1(lean_object* v_oFile_6388_, lean_object* v_srcFile_6389_, lean_object* v___x_6390_, lean_object* v_compiler_6391_, lean_object* v___y_6392_, lean_object* v___y_6393_, lean_object* v___y_6394_, lean_object* v___y_6395_, lean_object* v___y_6396_, lean_object* v___y_6397_){
_start:
{
lean_object* v_log_6399_; uint8_t v_action_6400_; uint8_t v_wantsRebuild_6401_; lean_object* v_trace_6402_; lean_object* v_buildTime_6403_; lean_object* v___x_6405_; uint8_t v_isShared_6406_; uint8_t v_isSharedCheck_6432_; 
v_log_6399_ = lean_ctor_get(v___y_6397_, 0);
v_action_6400_ = lean_ctor_get_uint8(v___y_6397_, sizeof(void*)*3);
v_wantsRebuild_6401_ = lean_ctor_get_uint8(v___y_6397_, sizeof(void*)*3 + 1);
v_trace_6402_ = lean_ctor_get(v___y_6397_, 1);
v_buildTime_6403_ = lean_ctor_get(v___y_6397_, 2);
v_isSharedCheck_6432_ = !lean_is_exclusive(v___y_6397_);
if (v_isSharedCheck_6432_ == 0)
{
v___x_6405_ = v___y_6397_;
v_isShared_6406_ = v_isSharedCheck_6432_;
goto v_resetjp_6404_;
}
else
{
lean_inc(v_buildTime_6403_);
lean_inc(v_trace_6402_);
lean_inc(v_log_6399_);
lean_dec(v___y_6397_);
v___x_6405_ = lean_box(0);
v_isShared_6406_ = v_isSharedCheck_6432_;
goto v_resetjp_6404_;
}
v_resetjp_6404_:
{
lean_object* v___x_6407_; 
v___x_6407_ = l_Lake_compileO(v_oFile_6388_, v_srcFile_6389_, v___x_6390_, v_compiler_6391_, v_log_6399_);
if (lean_obj_tag(v___x_6407_) == 0)
{
lean_object* v_a_6408_; lean_object* v_a_6409_; lean_object* v___x_6411_; uint8_t v_isShared_6412_; uint8_t v_isSharedCheck_6419_; 
v_a_6408_ = lean_ctor_get(v___x_6407_, 0);
v_a_6409_ = lean_ctor_get(v___x_6407_, 1);
v_isSharedCheck_6419_ = !lean_is_exclusive(v___x_6407_);
if (v_isSharedCheck_6419_ == 0)
{
v___x_6411_ = v___x_6407_;
v_isShared_6412_ = v_isSharedCheck_6419_;
goto v_resetjp_6410_;
}
else
{
lean_inc(v_a_6409_);
lean_inc(v_a_6408_);
lean_dec(v___x_6407_);
v___x_6411_ = lean_box(0);
v_isShared_6412_ = v_isSharedCheck_6419_;
goto v_resetjp_6410_;
}
v_resetjp_6410_:
{
lean_object* v___x_6414_; 
if (v_isShared_6406_ == 0)
{
lean_ctor_set(v___x_6405_, 0, v_a_6409_);
v___x_6414_ = v___x_6405_;
goto v_reusejp_6413_;
}
else
{
lean_object* v_reuseFailAlloc_6418_; 
v_reuseFailAlloc_6418_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6418_, 0, v_a_6409_);
lean_ctor_set(v_reuseFailAlloc_6418_, 1, v_trace_6402_);
lean_ctor_set(v_reuseFailAlloc_6418_, 2, v_buildTime_6403_);
lean_ctor_set_uint8(v_reuseFailAlloc_6418_, sizeof(void*)*3, v_action_6400_);
lean_ctor_set_uint8(v_reuseFailAlloc_6418_, sizeof(void*)*3 + 1, v_wantsRebuild_6401_);
v___x_6414_ = v_reuseFailAlloc_6418_;
goto v_reusejp_6413_;
}
v_reusejp_6413_:
{
lean_object* v___x_6416_; 
if (v_isShared_6412_ == 0)
{
lean_ctor_set(v___x_6411_, 1, v___x_6414_);
v___x_6416_ = v___x_6411_;
goto v_reusejp_6415_;
}
else
{
lean_object* v_reuseFailAlloc_6417_; 
v_reuseFailAlloc_6417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6417_, 0, v_a_6408_);
lean_ctor_set(v_reuseFailAlloc_6417_, 1, v___x_6414_);
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
else
{
lean_object* v_a_6420_; lean_object* v_a_6421_; lean_object* v___x_6423_; uint8_t v_isShared_6424_; uint8_t v_isSharedCheck_6431_; 
v_a_6420_ = lean_ctor_get(v___x_6407_, 0);
v_a_6421_ = lean_ctor_get(v___x_6407_, 1);
v_isSharedCheck_6431_ = !lean_is_exclusive(v___x_6407_);
if (v_isSharedCheck_6431_ == 0)
{
v___x_6423_ = v___x_6407_;
v_isShared_6424_ = v_isSharedCheck_6431_;
goto v_resetjp_6422_;
}
else
{
lean_inc(v_a_6421_);
lean_inc(v_a_6420_);
lean_dec(v___x_6407_);
v___x_6423_ = lean_box(0);
v_isShared_6424_ = v_isSharedCheck_6431_;
goto v_resetjp_6422_;
}
v_resetjp_6422_:
{
lean_object* v___x_6426_; 
if (v_isShared_6406_ == 0)
{
lean_ctor_set(v___x_6405_, 0, v_a_6421_);
v___x_6426_ = v___x_6405_;
goto v_reusejp_6425_;
}
else
{
lean_object* v_reuseFailAlloc_6430_; 
v_reuseFailAlloc_6430_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6430_, 0, v_a_6421_);
lean_ctor_set(v_reuseFailAlloc_6430_, 1, v_trace_6402_);
lean_ctor_set(v_reuseFailAlloc_6430_, 2, v_buildTime_6403_);
lean_ctor_set_uint8(v_reuseFailAlloc_6430_, sizeof(void*)*3, v_action_6400_);
lean_ctor_set_uint8(v_reuseFailAlloc_6430_, sizeof(void*)*3 + 1, v_wantsRebuild_6401_);
v___x_6426_ = v_reuseFailAlloc_6430_;
goto v_reusejp_6425_;
}
v_reusejp_6425_:
{
lean_object* v___x_6428_; 
if (v_isShared_6424_ == 0)
{
lean_ctor_set(v___x_6423_, 1, v___x_6426_);
v___x_6428_ = v___x_6423_;
goto v_reusejp_6427_;
}
else
{
lean_object* v_reuseFailAlloc_6429_; 
v_reuseFailAlloc_6429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6429_, 0, v_a_6420_);
lean_ctor_set(v_reuseFailAlloc_6429_, 1, v___x_6426_);
v___x_6428_ = v_reuseFailAlloc_6429_;
goto v_reusejp_6427_;
}
v_reusejp_6427_:
{
return v___x_6428_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1___boxed(lean_object* v_oFile_6433_, lean_object* v_srcFile_6434_, lean_object* v___x_6435_, lean_object* v_compiler_6436_, lean_object* v___y_6437_, lean_object* v___y_6438_, lean_object* v___y_6439_, lean_object* v___y_6440_, lean_object* v___y_6441_, lean_object* v___y_6442_, lean_object* v___y_6443_){
_start:
{
lean_object* v_res_6444_; 
v_res_6444_ = l_Lake_buildO___lam__1(v_oFile_6433_, v_srcFile_6434_, v___x_6435_, v_compiler_6436_, v___y_6437_, v___y_6438_, v___y_6439_, v___y_6440_, v___y_6441_, v___y_6442_);
lean_dec_ref(v___y_6441_);
lean_dec(v___y_6440_);
lean_dec(v___y_6439_);
lean_dec(v___y_6438_);
lean_dec_ref(v___y_6437_);
lean_dec_ref(v___x_6435_);
return v_res_6444_;
}
}
static lean_object* _init_l_Lake_buildO___lam__2___boxed__const__1(void){
_start:
{
uint64_t v___x_6448_; lean_object* v___x_6449_; 
v___x_6448_ = l_Lake_Hash_nil;
v___x_6449_ = lean_box_uint64(v___x_6448_);
return v___x_6449_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2(lean_object* v_traceArgs_6450_, lean_object* v___f_6451_, lean_object* v_extraDepTrace_6452_, lean_object* v_weakArgs_6453_, lean_object* v_oFile_6454_, lean_object* v_compiler_6455_, lean_object* v___x_6456_, lean_object* v___f_6457_, lean_object* v_srcFile_6458_, lean_object* v___y_6459_, lean_object* v___y_6460_, lean_object* v___y_6461_, lean_object* v___y_6462_, lean_object* v___y_6463_, lean_object* v___y_6464_){
_start:
{
lean_object* v_log_6466_; uint8_t v_action_6467_; uint8_t v_wantsRebuild_6468_; lean_object* v_trace_6469_; lean_object* v_buildTime_6470_; lean_object* v___x_6472_; uint8_t v_isShared_6473_; uint8_t v_isSharedCheck_6549_; 
v_log_6466_ = lean_ctor_get(v___y_6464_, 0);
v_action_6467_ = lean_ctor_get_uint8(v___y_6464_, sizeof(void*)*3);
v_wantsRebuild_6468_ = lean_ctor_get_uint8(v___y_6464_, sizeof(void*)*3 + 1);
v_trace_6469_ = lean_ctor_get(v___y_6464_, 1);
v_buildTime_6470_ = lean_ctor_get(v___y_6464_, 2);
v_isSharedCheck_6549_ = !lean_is_exclusive(v___y_6464_);
if (v_isSharedCheck_6549_ == 0)
{
v___x_6472_ = v___y_6464_;
v_isShared_6473_ = v_isSharedCheck_6549_;
goto v_resetjp_6471_;
}
else
{
lean_inc(v_buildTime_6470_);
lean_inc(v_trace_6469_);
lean_inc(v_log_6466_);
lean_dec(v___y_6464_);
v___x_6472_ = lean_box(0);
v_isShared_6473_ = v_isSharedCheck_6549_;
goto v_resetjp_6471_;
}
v_resetjp_6471_:
{
lean_object* v___x_6474_; lean_object* v___x_6475_; uint64_t v___y_6477_; uint64_t v___x_6540_; lean_object* v___x_6541_; lean_object* v___x_6542_; uint8_t v___x_6543_; 
v___x_6474_ = l_Lake_platformTrace;
v___x_6475_ = l_Lake_BuildTrace_mix(v_trace_6469_, v___x_6474_);
v___x_6540_ = l_Lake_Hash_nil;
v___x_6541_ = lean_unsigned_to_nat(0u);
v___x_6542_ = lean_array_get_size(v_traceArgs_6450_);
v___x_6543_ = lean_nat_dec_lt(v___x_6541_, v___x_6542_);
if (v___x_6543_ == 0)
{
lean_dec_ref(v___f_6457_);
lean_dec_ref(v___x_6456_);
v___y_6477_ = v___x_6540_;
goto v___jp_6476_;
}
else
{
size_t v___x_6544_; size_t v___x_6545_; lean_object* v___x_6546_; lean_object* v___x_6547_; uint64_t v___x_6548_; 
v___x_6544_ = ((size_t)0ULL);
v___x_6545_ = lean_usize_of_nat(v___x_6542_);
v___x_6546_ = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(v_traceArgs_6450_);
v___x_6547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_6456_, v___f_6457_, v_traceArgs_6450_, v___x_6544_, v___x_6545_, v___x_6546_);
v___x_6548_ = lean_unbox_uint64(v___x_6547_);
lean_dec(v___x_6547_);
v___y_6477_ = v___x_6548_;
goto v___jp_6476_;
}
v___jp_6476_:
{
lean_object* v___x_6478_; lean_object* v___x_6479_; lean_object* v___x_6480_; lean_object* v___x_6481_; lean_object* v___x_6482_; lean_object* v___x_6483_; lean_object* v___x_6484_; lean_object* v___x_6485_; lean_object* v___x_6486_; lean_object* v___x_6487_; lean_object* v___x_6489_; 
v___x_6478_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_6479_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_6450_);
v___x_6480_ = lean_array_to_list(v_traceArgs_6450_);
v___x_6481_ = l_List_toString___redArg(v___f_6451_, v___x_6480_);
v___x_6482_ = lean_string_append(v___x_6479_, v___x_6481_);
lean_dec_ref(v___x_6481_);
v___x_6483_ = lean_string_append(v___x_6478_, v___x_6482_);
lean_dec_ref(v___x_6482_);
v___x_6484_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_6485_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_6486_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6486_, 0, v___x_6483_);
lean_ctor_set(v___x_6486_, 1, v___x_6484_);
lean_ctor_set(v___x_6486_, 2, v___x_6485_);
lean_ctor_set_uint64(v___x_6486_, sizeof(void*)*3, v___y_6477_);
v___x_6487_ = l_Lake_BuildTrace_mix(v___x_6475_, v___x_6486_);
if (v_isShared_6473_ == 0)
{
lean_ctor_set(v___x_6472_, 1, v___x_6487_);
v___x_6489_ = v___x_6472_;
goto v_reusejp_6488_;
}
else
{
lean_object* v_reuseFailAlloc_6539_; 
v_reuseFailAlloc_6539_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6539_, 0, v_log_6466_);
lean_ctor_set(v_reuseFailAlloc_6539_, 1, v___x_6487_);
lean_ctor_set(v_reuseFailAlloc_6539_, 2, v_buildTime_6470_);
lean_ctor_set_uint8(v_reuseFailAlloc_6539_, sizeof(void*)*3, v_action_6467_);
lean_ctor_set_uint8(v_reuseFailAlloc_6539_, sizeof(void*)*3 + 1, v_wantsRebuild_6468_);
v___x_6489_ = v_reuseFailAlloc_6539_;
goto v_reusejp_6488_;
}
v_reusejp_6488_:
{
lean_object* v___x_6490_; 
lean_inc_ref(v___y_6463_);
lean_inc(v___y_6462_);
lean_inc(v___y_6461_);
lean_inc(v___y_6460_);
lean_inc_ref(v___y_6459_);
v___x_6490_ = lean_apply_7(v_extraDepTrace_6452_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___x_6489_, lean_box(0));
if (lean_obj_tag(v___x_6490_) == 0)
{
lean_object* v_a_6491_; lean_object* v_a_6492_; lean_object* v_log_6493_; uint8_t v_action_6494_; uint8_t v_wantsRebuild_6495_; lean_object* v_trace_6496_; lean_object* v_buildTime_6497_; lean_object* v___x_6499_; uint8_t v_isShared_6500_; uint8_t v_isSharedCheck_6529_; 
v_a_6491_ = lean_ctor_get(v___x_6490_, 1);
lean_inc(v_a_6491_);
v_a_6492_ = lean_ctor_get(v___x_6490_, 0);
lean_inc(v_a_6492_);
lean_dec_ref_known(v___x_6490_, 2);
v_log_6493_ = lean_ctor_get(v_a_6491_, 0);
v_action_6494_ = lean_ctor_get_uint8(v_a_6491_, sizeof(void*)*3);
v_wantsRebuild_6495_ = lean_ctor_get_uint8(v_a_6491_, sizeof(void*)*3 + 1);
v_trace_6496_ = lean_ctor_get(v_a_6491_, 1);
v_buildTime_6497_ = lean_ctor_get(v_a_6491_, 2);
v_isSharedCheck_6529_ = !lean_is_exclusive(v_a_6491_);
if (v_isSharedCheck_6529_ == 0)
{
v___x_6499_ = v_a_6491_;
v_isShared_6500_ = v_isSharedCheck_6529_;
goto v_resetjp_6498_;
}
else
{
lean_inc(v_buildTime_6497_);
lean_inc(v_trace_6496_);
lean_inc(v_log_6493_);
lean_dec(v_a_6491_);
v___x_6499_ = lean_box(0);
v_isShared_6500_ = v_isSharedCheck_6529_;
goto v_resetjp_6498_;
}
v_resetjp_6498_:
{
lean_object* v___x_6501_; lean_object* v___x_6503_; 
v___x_6501_ = l_Lake_BuildTrace_mix(v_trace_6496_, v_a_6492_);
if (v_isShared_6500_ == 0)
{
lean_ctor_set(v___x_6499_, 1, v___x_6501_);
v___x_6503_ = v___x_6499_;
goto v_reusejp_6502_;
}
else
{
lean_object* v_reuseFailAlloc_6528_; 
v_reuseFailAlloc_6528_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6528_, 0, v_log_6493_);
lean_ctor_set(v_reuseFailAlloc_6528_, 1, v___x_6501_);
lean_ctor_set(v_reuseFailAlloc_6528_, 2, v_buildTime_6497_);
lean_ctor_set_uint8(v_reuseFailAlloc_6528_, sizeof(void*)*3, v_action_6494_);
lean_ctor_set_uint8(v_reuseFailAlloc_6528_, sizeof(void*)*3 + 1, v_wantsRebuild_6495_);
v___x_6503_ = v_reuseFailAlloc_6528_;
goto v_reusejp_6502_;
}
v_reusejp_6502_:
{
lean_object* v___x_6504_; lean_object* v___f_6505_; uint8_t v___x_6506_; lean_object* v___x_6507_; lean_object* v___x_6508_; 
v___x_6504_ = l_Array_append___redArg(v_weakArgs_6453_, v_traceArgs_6450_);
lean_dec_ref(v_traceArgs_6450_);
lean_inc_ref(v_oFile_6454_);
v___f_6505_ = lean_alloc_closure((void*)(l_Lake_buildO___lam__1___boxed), 11, 4);
lean_closure_set(v___f_6505_, 0, v_oFile_6454_);
lean_closure_set(v___f_6505_, 1, v_srcFile_6458_);
lean_closure_set(v___f_6505_, 2, v___x_6504_);
lean_closure_set(v___f_6505_, 3, v_compiler_6455_);
v___x_6506_ = 0;
v___x_6507_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
v___x_6508_ = l_Lake_buildArtifactUnlessUpToDate(v_oFile_6454_, v___f_6505_, v___x_6506_, v___x_6507_, v___x_6506_, v___x_6506_, v___x_6506_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___x_6503_);
if (lean_obj_tag(v___x_6508_) == 0)
{
lean_object* v_a_6509_; lean_object* v_a_6510_; lean_object* v___x_6512_; uint8_t v_isShared_6513_; uint8_t v_isSharedCheck_6518_; 
v_a_6509_ = lean_ctor_get(v___x_6508_, 0);
v_a_6510_ = lean_ctor_get(v___x_6508_, 1);
v_isSharedCheck_6518_ = !lean_is_exclusive(v___x_6508_);
if (v_isSharedCheck_6518_ == 0)
{
v___x_6512_ = v___x_6508_;
v_isShared_6513_ = v_isSharedCheck_6518_;
goto v_resetjp_6511_;
}
else
{
lean_inc(v_a_6510_);
lean_inc(v_a_6509_);
lean_dec(v___x_6508_);
v___x_6512_ = lean_box(0);
v_isShared_6513_ = v_isSharedCheck_6518_;
goto v_resetjp_6511_;
}
v_resetjp_6511_:
{
lean_object* v_path_6514_; lean_object* v___x_6516_; 
v_path_6514_ = lean_ctor_get(v_a_6509_, 1);
lean_inc_ref(v_path_6514_);
lean_dec(v_a_6509_);
if (v_isShared_6513_ == 0)
{
lean_ctor_set(v___x_6512_, 0, v_path_6514_);
v___x_6516_ = v___x_6512_;
goto v_reusejp_6515_;
}
else
{
lean_object* v_reuseFailAlloc_6517_; 
v_reuseFailAlloc_6517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6517_, 0, v_path_6514_);
lean_ctor_set(v_reuseFailAlloc_6517_, 1, v_a_6510_);
v___x_6516_ = v_reuseFailAlloc_6517_;
goto v_reusejp_6515_;
}
v_reusejp_6515_:
{
return v___x_6516_;
}
}
}
else
{
lean_object* v_a_6519_; lean_object* v_a_6520_; lean_object* v___x_6522_; uint8_t v_isShared_6523_; uint8_t v_isSharedCheck_6527_; 
v_a_6519_ = lean_ctor_get(v___x_6508_, 0);
v_a_6520_ = lean_ctor_get(v___x_6508_, 1);
v_isSharedCheck_6527_ = !lean_is_exclusive(v___x_6508_);
if (v_isSharedCheck_6527_ == 0)
{
v___x_6522_ = v___x_6508_;
v_isShared_6523_ = v_isSharedCheck_6527_;
goto v_resetjp_6521_;
}
else
{
lean_inc(v_a_6520_);
lean_inc(v_a_6519_);
lean_dec(v___x_6508_);
v___x_6522_ = lean_box(0);
v_isShared_6523_ = v_isSharedCheck_6527_;
goto v_resetjp_6521_;
}
v_resetjp_6521_:
{
lean_object* v___x_6525_; 
if (v_isShared_6523_ == 0)
{
v___x_6525_ = v___x_6522_;
goto v_reusejp_6524_;
}
else
{
lean_object* v_reuseFailAlloc_6526_; 
v_reuseFailAlloc_6526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6526_, 0, v_a_6519_);
lean_ctor_set(v_reuseFailAlloc_6526_, 1, v_a_6520_);
v___x_6525_ = v_reuseFailAlloc_6526_;
goto v_reusejp_6524_;
}
v_reusejp_6524_:
{
return v___x_6525_;
}
}
}
}
}
}
else
{
lean_object* v_a_6530_; lean_object* v_a_6531_; lean_object* v___x_6533_; uint8_t v_isShared_6534_; uint8_t v_isSharedCheck_6538_; 
lean_dec_ref(v___y_6459_);
lean_dec_ref(v_srcFile_6458_);
lean_dec_ref(v_compiler_6455_);
lean_dec_ref(v_oFile_6454_);
lean_dec_ref(v_weakArgs_6453_);
lean_dec_ref(v_traceArgs_6450_);
v_a_6530_ = lean_ctor_get(v___x_6490_, 0);
v_a_6531_ = lean_ctor_get(v___x_6490_, 1);
v_isSharedCheck_6538_ = !lean_is_exclusive(v___x_6490_);
if (v_isSharedCheck_6538_ == 0)
{
v___x_6533_ = v___x_6490_;
v_isShared_6534_ = v_isSharedCheck_6538_;
goto v_resetjp_6532_;
}
else
{
lean_inc(v_a_6531_);
lean_inc(v_a_6530_);
lean_dec(v___x_6490_);
v___x_6533_ = lean_box(0);
v_isShared_6534_ = v_isSharedCheck_6538_;
goto v_resetjp_6532_;
}
v_resetjp_6532_:
{
lean_object* v___x_6536_; 
if (v_isShared_6534_ == 0)
{
v___x_6536_ = v___x_6533_;
goto v_reusejp_6535_;
}
else
{
lean_object* v_reuseFailAlloc_6537_; 
v_reuseFailAlloc_6537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6537_, 0, v_a_6530_);
lean_ctor_set(v_reuseFailAlloc_6537_, 1, v_a_6531_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed(lean_object* v_traceArgs_6550_, lean_object* v___f_6551_, lean_object* v_extraDepTrace_6552_, lean_object* v_weakArgs_6553_, lean_object* v_oFile_6554_, lean_object* v_compiler_6555_, lean_object* v___x_6556_, lean_object* v___f_6557_, lean_object* v_srcFile_6558_, lean_object* v___y_6559_, lean_object* v___y_6560_, lean_object* v___y_6561_, lean_object* v___y_6562_, lean_object* v___y_6563_, lean_object* v___y_6564_, lean_object* v___y_6565_){
_start:
{
lean_object* v_res_6566_; 
v_res_6566_ = l_Lake_buildO___lam__2(v_traceArgs_6550_, v___f_6551_, v_extraDepTrace_6552_, v_weakArgs_6553_, v_oFile_6554_, v_compiler_6555_, v___x_6556_, v___f_6557_, v_srcFile_6558_, v___y_6559_, v___y_6560_, v___y_6561_, v___y_6562_, v___y_6563_, v___y_6564_);
lean_dec_ref(v___y_6563_);
lean_dec(v___y_6562_);
lean_dec(v___y_6561_);
lean_dec(v___y_6560_);
return v_res_6566_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object* v_oFile_6569_, lean_object* v_srcJob_6570_, lean_object* v_weakArgs_6571_, lean_object* v_traceArgs_6572_, lean_object* v_compiler_6573_, lean_object* v_extraDepTrace_6574_, lean_object* v_a_6575_, lean_object* v_a_6576_, lean_object* v_a_6577_, lean_object* v_a_6578_, lean_object* v_a_6579_, lean_object* v_a_6580_){
_start:
{
lean_object* v___f_6582_; lean_object* v___x_6583_; lean_object* v___f_6584_; lean_object* v___x_6585_; lean_object* v___f_6586_; lean_object* v___x_6587_; uint8_t v___x_6588_; lean_object* v___x_6589_; 
v___f_6582_ = ((lean_object*)(l_Lake_buildO___closed__0));
v___x_6583_ = l_Lake_instDataKindFilePath;
v___f_6584_ = ((lean_object*)(l_Lake_buildO___closed__1));
v___x_6585_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__9));
v___f_6586_ = lean_alloc_closure((void*)(l_Lake_buildO___lam__2___boxed), 16, 8);
lean_closure_set(v___f_6586_, 0, v_traceArgs_6572_);
lean_closure_set(v___f_6586_, 1, v___f_6584_);
lean_closure_set(v___f_6586_, 2, v_extraDepTrace_6574_);
lean_closure_set(v___f_6586_, 3, v_weakArgs_6571_);
lean_closure_set(v___f_6586_, 4, v_oFile_6569_);
lean_closure_set(v___f_6586_, 5, v_compiler_6573_);
lean_closure_set(v___f_6586_, 6, v___x_6585_);
lean_closure_set(v___f_6586_, 7, v___f_6582_);
v___x_6587_ = lean_unsigned_to_nat(0u);
v___x_6588_ = 0;
v___x_6589_ = l_Lake_Job_mapM___redArg(v___x_6583_, v_srcJob_6570_, v___f_6586_, v___x_6587_, v___x_6588_, v_a_6575_, v_a_6576_, v_a_6577_, v_a_6578_, v_a_6579_, v_a_6580_);
return v___x_6589_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___boxed(lean_object* v_oFile_6590_, lean_object* v_srcJob_6591_, lean_object* v_weakArgs_6592_, lean_object* v_traceArgs_6593_, lean_object* v_compiler_6594_, lean_object* v_extraDepTrace_6595_, lean_object* v_a_6596_, lean_object* v_a_6597_, lean_object* v_a_6598_, lean_object* v_a_6599_, lean_object* v_a_6600_, lean_object* v_a_6601_, lean_object* v_a_6602_){
_start:
{
lean_object* v_res_6603_; 
v_res_6603_ = l_Lake_buildO(v_oFile_6590_, v_srcJob_6591_, v_weakArgs_6592_, v_traceArgs_6593_, v_compiler_6594_, v_extraDepTrace_6595_, v_a_6596_, v_a_6597_, v_a_6598_, v_a_6599_, v_a_6600_, v_a_6601_);
lean_dec_ref(v_a_6601_);
lean_dec_ref(v_a_6600_);
lean_dec(v_a_6599_);
lean_dec(v_a_6598_);
lean_dec(v_a_6597_);
return v_res_6603_;
}
}
static lean_object* _init_l_Lake_Internal_buildLeanO___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6605_; lean_object* v___x_6606_; lean_object* v___x_6607_; lean_object* v___x_6608_; 
v___x_6605_ = ((lean_object*)(l_Lake_Internal_buildLeanO___lam__0___closed__0));
v___x_6606_ = lean_unsigned_to_nat(2u);
v___x_6607_ = lean_mk_empty_array_with_capacity(v___x_6606_);
v___x_6608_ = lean_array_push(v___x_6607_, v___x_6605_);
return v___x_6608_;
}
}
LEAN_EXPORT lean_object* l_Lake_Internal_buildLeanO___lam__0(lean_object* v_weakArgs_6609_, lean_object* v_traceArgs_6610_, lean_object* v_oFile_6611_, lean_object* v_srcFile_6612_, lean_object* v_leanIncludeDir_x3f_6613_, lean_object* v___y_6614_, lean_object* v___y_6615_, lean_object* v___y_6616_, lean_object* v___y_6617_, lean_object* v___y_6618_, lean_object* v___y_6619_){
_start:
{
lean_object* v_toContext_6621_; lean_object* v_lakeEnv_6622_; lean_object* v_log_6623_; uint8_t v_action_6624_; uint8_t v_wantsRebuild_6625_; lean_object* v_trace_6626_; lean_object* v_buildTime_6627_; lean_object* v___x_6629_; uint8_t v_isShared_6630_; uint8_t v_isSharedCheck_6669_; 
v_toContext_6621_ = lean_ctor_get(v___y_6618_, 1);
v_lakeEnv_6622_ = lean_ctor_get(v_toContext_6621_, 0);
v_log_6623_ = lean_ctor_get(v___y_6619_, 0);
v_action_6624_ = lean_ctor_get_uint8(v___y_6619_, sizeof(void*)*3);
v_wantsRebuild_6625_ = lean_ctor_get_uint8(v___y_6619_, sizeof(void*)*3 + 1);
v_trace_6626_ = lean_ctor_get(v___y_6619_, 1);
v_buildTime_6627_ = lean_ctor_get(v___y_6619_, 2);
v_isSharedCheck_6669_ = !lean_is_exclusive(v___y_6619_);
if (v_isSharedCheck_6669_ == 0)
{
v___x_6629_ = v___y_6619_;
v_isShared_6630_ = v_isSharedCheck_6669_;
goto v_resetjp_6628_;
}
else
{
lean_inc(v_buildTime_6627_);
lean_inc(v_trace_6626_);
lean_inc(v_log_6623_);
lean_dec(v___y_6619_);
v___x_6629_ = lean_box(0);
v_isShared_6630_ = v_isSharedCheck_6669_;
goto v_resetjp_6628_;
}
v_resetjp_6628_:
{
lean_object* v_lean_6631_; lean_object* v___y_6633_; 
v_lean_6631_ = lean_ctor_get(v_lakeEnv_6622_, 1);
if (lean_obj_tag(v_leanIncludeDir_x3f_6613_) == 0)
{
lean_object* v_includeDir_6666_; 
v_includeDir_6666_ = lean_ctor_get(v_lean_6631_, 4);
lean_inc_ref(v_includeDir_6666_);
v___y_6633_ = v_includeDir_6666_;
goto v___jp_6632_;
}
else
{
lean_object* v_val_6667_; lean_object* v_fst_6668_; 
v_val_6667_ = lean_ctor_get(v_leanIncludeDir_x3f_6613_, 0);
lean_inc(v_val_6667_);
lean_dec_ref_known(v_leanIncludeDir_x3f_6613_, 1);
v_fst_6668_ = lean_ctor_get(v_val_6667_, 0);
lean_inc(v_fst_6668_);
lean_dec(v_val_6667_);
v___y_6633_ = v_fst_6668_;
goto v___jp_6632_;
}
v___jp_6632_:
{
lean_object* v_cc_6634_; lean_object* v_ccFlags_6635_; lean_object* v___x_6636_; lean_object* v___x_6637_; lean_object* v___x_6638_; lean_object* v___x_6639_; lean_object* v___x_6640_; lean_object* v___x_6641_; 
v_cc_6634_ = lean_ctor_get(v_lean_6631_, 14);
v_ccFlags_6635_ = lean_ctor_get(v_lean_6631_, 18);
v___x_6636_ = lean_obj_once(&l_Lake_Internal_buildLeanO___lam__0___closed__1, &l_Lake_Internal_buildLeanO___lam__0___closed__1_once, _init_l_Lake_Internal_buildLeanO___lam__0___closed__1);
v___x_6637_ = lean_array_push(v___x_6636_, v___y_6633_);
v___x_6638_ = l_Array_append___redArg(v___x_6637_, v_ccFlags_6635_);
v___x_6639_ = l_Array_append___redArg(v___x_6638_, v_weakArgs_6609_);
v___x_6640_ = l_Array_append___redArg(v___x_6639_, v_traceArgs_6610_);
lean_inc_ref(v_cc_6634_);
v___x_6641_ = l_Lake_compileO(v_oFile_6611_, v_srcFile_6612_, v___x_6640_, v_cc_6634_, v_log_6623_);
lean_dec_ref(v___x_6640_);
if (lean_obj_tag(v___x_6641_) == 0)
{
lean_object* v_a_6642_; lean_object* v_a_6643_; lean_object* v___x_6645_; uint8_t v_isShared_6646_; uint8_t v_isSharedCheck_6653_; 
v_a_6642_ = lean_ctor_get(v___x_6641_, 0);
v_a_6643_ = lean_ctor_get(v___x_6641_, 1);
v_isSharedCheck_6653_ = !lean_is_exclusive(v___x_6641_);
if (v_isSharedCheck_6653_ == 0)
{
v___x_6645_ = v___x_6641_;
v_isShared_6646_ = v_isSharedCheck_6653_;
goto v_resetjp_6644_;
}
else
{
lean_inc(v_a_6643_);
lean_inc(v_a_6642_);
lean_dec(v___x_6641_);
v___x_6645_ = lean_box(0);
v_isShared_6646_ = v_isSharedCheck_6653_;
goto v_resetjp_6644_;
}
v_resetjp_6644_:
{
lean_object* v___x_6648_; 
if (v_isShared_6630_ == 0)
{
lean_ctor_set(v___x_6629_, 0, v_a_6643_);
v___x_6648_ = v___x_6629_;
goto v_reusejp_6647_;
}
else
{
lean_object* v_reuseFailAlloc_6652_; 
v_reuseFailAlloc_6652_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6652_, 0, v_a_6643_);
lean_ctor_set(v_reuseFailAlloc_6652_, 1, v_trace_6626_);
lean_ctor_set(v_reuseFailAlloc_6652_, 2, v_buildTime_6627_);
lean_ctor_set_uint8(v_reuseFailAlloc_6652_, sizeof(void*)*3, v_action_6624_);
lean_ctor_set_uint8(v_reuseFailAlloc_6652_, sizeof(void*)*3 + 1, v_wantsRebuild_6625_);
v___x_6648_ = v_reuseFailAlloc_6652_;
goto v_reusejp_6647_;
}
v_reusejp_6647_:
{
lean_object* v___x_6650_; 
if (v_isShared_6646_ == 0)
{
lean_ctor_set(v___x_6645_, 1, v___x_6648_);
v___x_6650_ = v___x_6645_;
goto v_reusejp_6649_;
}
else
{
lean_object* v_reuseFailAlloc_6651_; 
v_reuseFailAlloc_6651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6651_, 0, v_a_6642_);
lean_ctor_set(v_reuseFailAlloc_6651_, 1, v___x_6648_);
v___x_6650_ = v_reuseFailAlloc_6651_;
goto v_reusejp_6649_;
}
v_reusejp_6649_:
{
return v___x_6650_;
}
}
}
}
else
{
lean_object* v_a_6654_; lean_object* v_a_6655_; lean_object* v___x_6657_; uint8_t v_isShared_6658_; uint8_t v_isSharedCheck_6665_; 
v_a_6654_ = lean_ctor_get(v___x_6641_, 0);
v_a_6655_ = lean_ctor_get(v___x_6641_, 1);
v_isSharedCheck_6665_ = !lean_is_exclusive(v___x_6641_);
if (v_isSharedCheck_6665_ == 0)
{
v___x_6657_ = v___x_6641_;
v_isShared_6658_ = v_isSharedCheck_6665_;
goto v_resetjp_6656_;
}
else
{
lean_inc(v_a_6655_);
lean_inc(v_a_6654_);
lean_dec(v___x_6641_);
v___x_6657_ = lean_box(0);
v_isShared_6658_ = v_isSharedCheck_6665_;
goto v_resetjp_6656_;
}
v_resetjp_6656_:
{
lean_object* v___x_6660_; 
if (v_isShared_6630_ == 0)
{
lean_ctor_set(v___x_6629_, 0, v_a_6655_);
v___x_6660_ = v___x_6629_;
goto v_reusejp_6659_;
}
else
{
lean_object* v_reuseFailAlloc_6664_; 
v_reuseFailAlloc_6664_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6664_, 0, v_a_6655_);
lean_ctor_set(v_reuseFailAlloc_6664_, 1, v_trace_6626_);
lean_ctor_set(v_reuseFailAlloc_6664_, 2, v_buildTime_6627_);
lean_ctor_set_uint8(v_reuseFailAlloc_6664_, sizeof(void*)*3, v_action_6624_);
lean_ctor_set_uint8(v_reuseFailAlloc_6664_, sizeof(void*)*3 + 1, v_wantsRebuild_6625_);
v___x_6660_ = v_reuseFailAlloc_6664_;
goto v_reusejp_6659_;
}
v_reusejp_6659_:
{
lean_object* v___x_6662_; 
if (v_isShared_6658_ == 0)
{
lean_ctor_set(v___x_6657_, 1, v___x_6660_);
v___x_6662_ = v___x_6657_;
goto v_reusejp_6661_;
}
else
{
lean_object* v_reuseFailAlloc_6663_; 
v_reuseFailAlloc_6663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6663_, 0, v_a_6654_);
lean_ctor_set(v_reuseFailAlloc_6663_, 1, v___x_6660_);
v___x_6662_ = v_reuseFailAlloc_6663_;
goto v_reusejp_6661_;
}
v_reusejp_6661_:
{
return v___x_6662_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Internal_buildLeanO___lam__0___boxed(lean_object* v_weakArgs_6670_, lean_object* v_traceArgs_6671_, lean_object* v_oFile_6672_, lean_object* v_srcFile_6673_, lean_object* v_leanIncludeDir_x3f_6674_, lean_object* v___y_6675_, lean_object* v___y_6676_, lean_object* v___y_6677_, lean_object* v___y_6678_, lean_object* v___y_6679_, lean_object* v___y_6680_, lean_object* v___y_6681_){
_start:
{
lean_object* v_res_6682_; 
v_res_6682_ = l_Lake_Internal_buildLeanO___lam__0(v_weakArgs_6670_, v_traceArgs_6671_, v_oFile_6672_, v_srcFile_6673_, v_leanIncludeDir_x3f_6674_, v___y_6675_, v___y_6676_, v___y_6677_, v___y_6678_, v___y_6679_, v___y_6680_);
lean_dec_ref(v___y_6679_);
lean_dec(v___y_6678_);
lean_dec(v___y_6677_);
lean_dec(v___y_6676_);
lean_dec_ref(v___y_6675_);
lean_dec_ref(v_traceArgs_6671_);
lean_dec_ref(v_weakArgs_6670_);
return v_res_6682_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_Internal_buildLeanO_spec__0_spec__0(lean_object* v_x_6684_, lean_object* v_x_6685_){
_start:
{
if (lean_obj_tag(v_x_6685_) == 0)
{
return v_x_6684_;
}
else
{
lean_object* v_head_6686_; lean_object* v_tail_6687_; lean_object* v___x_6688_; lean_object* v___x_6689_; lean_object* v___x_6690_; 
v_head_6686_ = lean_ctor_get(v_x_6685_, 0);
v_tail_6687_ = lean_ctor_get(v_x_6685_, 1);
v___x_6688_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lake_Internal_buildLeanO_spec__0_spec__0___closed__0));
v___x_6689_ = lean_string_append(v_x_6684_, v___x_6688_);
v___x_6690_ = lean_string_append(v___x_6689_, v_head_6686_);
v_x_6684_ = v___x_6690_;
v_x_6685_ = v_tail_6687_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_Internal_buildLeanO_spec__0_spec__0___boxed(lean_object* v_x_6692_, lean_object* v_x_6693_){
_start:
{
lean_object* v_res_6694_; 
v_res_6694_ = l_List_foldl___at___00List_toString___at___00Lake_Internal_buildLeanO_spec__0_spec__0(v_x_6692_, v_x_6693_);
lean_dec(v_x_6693_);
return v_res_6694_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_Internal_buildLeanO_spec__0(lean_object* v_x_6698_){
_start:
{
if (lean_obj_tag(v_x_6698_) == 0)
{
lean_object* v___x_6699_; 
v___x_6699_ = ((lean_object*)(l_List_toString___at___00Lake_Internal_buildLeanO_spec__0___closed__0));
return v___x_6699_;
}
else
{
lean_object* v_tail_6700_; 
v_tail_6700_ = lean_ctor_get(v_x_6698_, 1);
if (lean_obj_tag(v_tail_6700_) == 0)
{
lean_object* v_head_6701_; lean_object* v___x_6702_; lean_object* v___x_6703_; lean_object* v___x_6704_; lean_object* v___x_6705_; 
v_head_6701_ = lean_ctor_get(v_x_6698_, 0);
v___x_6702_ = ((lean_object*)(l_List_toString___at___00Lake_Internal_buildLeanO_spec__0___closed__1));
v___x_6703_ = lean_string_append(v___x_6702_, v_head_6701_);
v___x_6704_ = ((lean_object*)(l_List_toString___at___00Lake_Internal_buildLeanO_spec__0___closed__2));
v___x_6705_ = lean_string_append(v___x_6703_, v___x_6704_);
return v___x_6705_;
}
else
{
lean_object* v_head_6706_; lean_object* v___x_6707_; lean_object* v___x_6708_; lean_object* v___x_6709_; uint32_t v___x_6710_; lean_object* v___x_6711_; 
v_head_6706_ = lean_ctor_get(v_x_6698_, 0);
v___x_6707_ = ((lean_object*)(l_List_toString___at___00Lake_Internal_buildLeanO_spec__0___closed__1));
v___x_6708_ = lean_string_append(v___x_6707_, v_head_6706_);
v___x_6709_ = l_List_foldl___at___00List_toString___at___00Lake_Internal_buildLeanO_spec__0_spec__0(v___x_6708_, v_tail_6700_);
v___x_6710_ = 93;
v___x_6711_ = lean_string_push(v___x_6709_, v___x_6710_);
return v___x_6711_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_Internal_buildLeanO_spec__0___boxed(lean_object* v_x_6712_){
_start:
{
lean_object* v_res_6713_; 
v_res_6713_ = l_List_toString___at___00Lake_Internal_buildLeanO_spec__0(v_x_6712_);
lean_dec(v_x_6712_);
return v_res_6713_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Internal_buildLeanO_spec__1(lean_object* v_as_6714_, size_t v_i_6715_, size_t v_stop_6716_, uint64_t v_b_6717_){
_start:
{
uint8_t v___x_6718_; 
v___x_6718_ = lean_usize_dec_eq(v_i_6715_, v_stop_6716_);
if (v___x_6718_ == 0)
{
lean_object* v___x_6719_; uint64_t v___x_6720_; uint64_t v___x_6721_; uint64_t v___x_6722_; uint64_t v___x_6723_; size_t v___x_6724_; size_t v___x_6725_; 
v___x_6719_ = lean_array_uget_borrowed(v_as_6714_, v_i_6715_);
v___x_6720_ = l_Lake_Hash_nil;
v___x_6721_ = lean_string_hash(v___x_6719_);
v___x_6722_ = lean_uint64_mix_hash(v___x_6720_, v___x_6721_);
v___x_6723_ = lean_uint64_mix_hash(v_b_6717_, v___x_6722_);
v___x_6724_ = ((size_t)1ULL);
v___x_6725_ = lean_usize_add(v_i_6715_, v___x_6724_);
v_i_6715_ = v___x_6725_;
v_b_6717_ = v___x_6723_;
goto _start;
}
else
{
return v_b_6717_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Internal_buildLeanO_spec__1___boxed(lean_object* v_as_6727_, lean_object* v_i_6728_, lean_object* v_stop_6729_, lean_object* v_b_6730_){
_start:
{
size_t v_i_boxed_6731_; size_t v_stop_boxed_6732_; uint64_t v_b_boxed_6733_; uint64_t v_res_6734_; lean_object* v_r_6735_; 
v_i_boxed_6731_ = lean_unbox_usize(v_i_6728_);
lean_dec(v_i_6728_);
v_stop_boxed_6732_ = lean_unbox_usize(v_stop_6729_);
lean_dec(v_stop_6729_);
v_b_boxed_6733_ = lean_unbox_uint64(v_b_6730_);
lean_dec_ref(v_b_6730_);
v_res_6734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Internal_buildLeanO_spec__1(v_as_6727_, v_i_boxed_6731_, v_stop_boxed_6732_, v_b_boxed_6733_);
lean_dec_ref(v_as_6727_);
v_r_6735_ = lean_box_uint64(v_res_6734_);
return v_r_6735_;
}
}
LEAN_EXPORT lean_object* l_Lake_Internal_buildLeanO___lam__1(lean_object* v_weakArgs_6736_, lean_object* v_traceArgs_6737_, lean_object* v_oFile_6738_, lean_object* v_leanIncludeDir_x3f_6739_, lean_object* v_srcFile_6740_, lean_object* v___y_6741_, lean_object* v___y_6742_, lean_object* v___y_6743_, lean_object* v___y_6744_, lean_object* v___y_6745_, lean_object* v___y_6746_){
_start:
{
lean_object* v_log_6748_; uint8_t v_action_6749_; uint8_t v_wantsRebuild_6750_; lean_object* v_trace_6751_; lean_object* v_buildTime_6752_; lean_object* v___x_6754_; uint8_t v_isShared_6755_; uint8_t v_isSharedCheck_6836_; 
v_log_6748_ = lean_ctor_get(v___y_6746_, 0);
v_action_6749_ = lean_ctor_get_uint8(v___y_6746_, sizeof(void*)*3);
v_wantsRebuild_6750_ = lean_ctor_get_uint8(v___y_6746_, sizeof(void*)*3 + 1);
v_trace_6751_ = lean_ctor_get(v___y_6746_, 1);
v_buildTime_6752_ = lean_ctor_get(v___y_6746_, 2);
v_isSharedCheck_6836_ = !lean_is_exclusive(v___y_6746_);
if (v_isSharedCheck_6836_ == 0)
{
v___x_6754_ = v___y_6746_;
v_isShared_6755_ = v_isSharedCheck_6836_;
goto v_resetjp_6753_;
}
else
{
lean_inc(v_buildTime_6752_);
lean_inc(v_trace_6751_);
lean_inc(v_log_6748_);
lean_dec(v___y_6746_);
v___x_6754_ = lean_box(0);
v_isShared_6755_ = v_isSharedCheck_6836_;
goto v_resetjp_6753_;
}
v_resetjp_6753_:
{
lean_object* v_leanTrace_6756_; lean_object* v___f_6757_; lean_object* v___y_6759_; lean_object* v___y_6760_; lean_object* v___y_6761_; lean_object* v___y_6762_; lean_object* v___y_6763_; lean_object* v___y_6764_; uint64_t v___y_6765_; lean_object* v___y_6813_; lean_object* v___y_6814_; lean_object* v___y_6815_; lean_object* v___y_6816_; lean_object* v___y_6817_; lean_object* v___y_6818_; lean_object* v___x_6826_; 
v_leanTrace_6756_ = lean_ctor_get(v___y_6745_, 2);
lean_inc(v_leanIncludeDir_x3f_6739_);
lean_inc_ref(v_oFile_6738_);
lean_inc_ref(v_traceArgs_6737_);
v___f_6757_ = lean_alloc_closure((void*)(l_Lake_Internal_buildLeanO___lam__0___boxed), 12, 5);
lean_closure_set(v___f_6757_, 0, v_weakArgs_6736_);
lean_closure_set(v___f_6757_, 1, v_traceArgs_6737_);
lean_closure_set(v___f_6757_, 2, v_oFile_6738_);
lean_closure_set(v___f_6757_, 3, v_srcFile_6740_);
lean_closure_set(v___f_6757_, 4, v_leanIncludeDir_x3f_6739_);
lean_inc_ref(v_leanTrace_6756_);
v___x_6826_ = l_Lake_BuildTrace_mix(v_trace_6751_, v_leanTrace_6756_);
if (lean_obj_tag(v_leanIncludeDir_x3f_6739_) == 1)
{
lean_object* v_val_6827_; lean_object* v_snd_6828_; lean_object* v___x_6829_; lean_object* v___x_6831_; 
v_val_6827_ = lean_ctor_get(v_leanIncludeDir_x3f_6739_, 0);
lean_inc(v_val_6827_);
lean_dec_ref_known(v_leanIncludeDir_x3f_6739_, 1);
v_snd_6828_ = lean_ctor_get(v_val_6827_, 1);
lean_inc(v_snd_6828_);
lean_dec(v_val_6827_);
v___x_6829_ = l_Lake_BuildTrace_mix(v___x_6826_, v_snd_6828_);
if (v_isShared_6755_ == 0)
{
lean_ctor_set(v___x_6754_, 1, v___x_6829_);
v___x_6831_ = v___x_6754_;
goto v_reusejp_6830_;
}
else
{
lean_object* v_reuseFailAlloc_6832_; 
v_reuseFailAlloc_6832_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6832_, 0, v_log_6748_);
lean_ctor_set(v_reuseFailAlloc_6832_, 1, v___x_6829_);
lean_ctor_set(v_reuseFailAlloc_6832_, 2, v_buildTime_6752_);
lean_ctor_set_uint8(v_reuseFailAlloc_6832_, sizeof(void*)*3, v_action_6749_);
lean_ctor_set_uint8(v_reuseFailAlloc_6832_, sizeof(void*)*3 + 1, v_wantsRebuild_6750_);
v___x_6831_ = v_reuseFailAlloc_6832_;
goto v_reusejp_6830_;
}
v_reusejp_6830_:
{
v___y_6813_ = v___y_6741_;
v___y_6814_ = v___y_6742_;
v___y_6815_ = v___y_6743_;
v___y_6816_ = v___y_6744_;
v___y_6817_ = v___y_6745_;
v___y_6818_ = v___x_6831_;
goto v___jp_6812_;
}
}
else
{
lean_object* v___x_6834_; 
lean_dec(v_leanIncludeDir_x3f_6739_);
if (v_isShared_6755_ == 0)
{
lean_ctor_set(v___x_6754_, 1, v___x_6826_);
v___x_6834_ = v___x_6754_;
goto v_reusejp_6833_;
}
else
{
lean_object* v_reuseFailAlloc_6835_; 
v_reuseFailAlloc_6835_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6835_, 0, v_log_6748_);
lean_ctor_set(v_reuseFailAlloc_6835_, 1, v___x_6826_);
lean_ctor_set(v_reuseFailAlloc_6835_, 2, v_buildTime_6752_);
lean_ctor_set_uint8(v_reuseFailAlloc_6835_, sizeof(void*)*3, v_action_6749_);
lean_ctor_set_uint8(v_reuseFailAlloc_6835_, sizeof(void*)*3 + 1, v_wantsRebuild_6750_);
v___x_6834_ = v_reuseFailAlloc_6835_;
goto v_reusejp_6833_;
}
v_reusejp_6833_:
{
v___y_6813_ = v___y_6741_;
v___y_6814_ = v___y_6742_;
v___y_6815_ = v___y_6743_;
v___y_6816_ = v___y_6744_;
v___y_6817_ = v___y_6745_;
v___y_6818_ = v___x_6834_;
goto v___jp_6812_;
}
}
v___jp_6758_:
{
lean_object* v_log_6766_; uint8_t v_action_6767_; uint8_t v_wantsRebuild_6768_; lean_object* v_trace_6769_; lean_object* v_buildTime_6770_; lean_object* v___x_6772_; uint8_t v_isShared_6773_; uint8_t v_isSharedCheck_6811_; 
v_log_6766_ = lean_ctor_get(v___y_6759_, 0);
v_action_6767_ = lean_ctor_get_uint8(v___y_6759_, sizeof(void*)*3);
v_wantsRebuild_6768_ = lean_ctor_get_uint8(v___y_6759_, sizeof(void*)*3 + 1);
v_trace_6769_ = lean_ctor_get(v___y_6759_, 1);
v_buildTime_6770_ = lean_ctor_get(v___y_6759_, 2);
v_isSharedCheck_6811_ = !lean_is_exclusive(v___y_6759_);
if (v_isSharedCheck_6811_ == 0)
{
v___x_6772_ = v___y_6759_;
v_isShared_6773_ = v_isSharedCheck_6811_;
goto v_resetjp_6771_;
}
else
{
lean_inc(v_buildTime_6770_);
lean_inc(v_trace_6769_);
lean_inc(v_log_6766_);
lean_dec(v___y_6759_);
v___x_6772_ = lean_box(0);
v_isShared_6773_ = v_isSharedCheck_6811_;
goto v_resetjp_6771_;
}
v_resetjp_6771_:
{
lean_object* v___x_6774_; lean_object* v___x_6775_; lean_object* v___x_6776_; lean_object* v___x_6777_; lean_object* v___x_6778_; lean_object* v___x_6779_; lean_object* v___x_6780_; lean_object* v___x_6781_; lean_object* v___x_6782_; lean_object* v___x_6783_; lean_object* v___x_6784_; lean_object* v___x_6785_; lean_object* v___x_6787_; 
v___x_6774_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_6775_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_6776_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_6777_ = lean_array_to_list(v_traceArgs_6737_);
v___x_6778_ = l_List_toString___at___00Lake_Internal_buildLeanO_spec__0(v___x_6777_);
lean_dec(v___x_6777_);
v___x_6779_ = lean_string_append(v___x_6776_, v___x_6778_);
lean_dec_ref(v___x_6778_);
v___x_6780_ = lean_string_append(v___x_6775_, v___x_6779_);
lean_dec_ref(v___x_6779_);
v___x_6781_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_6782_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6782_, 0, v___x_6780_);
lean_ctor_set(v___x_6782_, 1, v___x_6774_);
lean_ctor_set(v___x_6782_, 2, v___x_6781_);
lean_ctor_set_uint64(v___x_6782_, sizeof(void*)*3, v___y_6765_);
v___x_6783_ = l_Lake_BuildTrace_mix(v_trace_6769_, v___x_6782_);
v___x_6784_ = l_Lake_platformTrace;
v___x_6785_ = l_Lake_BuildTrace_mix(v___x_6783_, v___x_6784_);
if (v_isShared_6773_ == 0)
{
lean_ctor_set(v___x_6772_, 1, v___x_6785_);
v___x_6787_ = v___x_6772_;
goto v_reusejp_6786_;
}
else
{
lean_object* v_reuseFailAlloc_6810_; 
v_reuseFailAlloc_6810_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6810_, 0, v_log_6766_);
lean_ctor_set(v_reuseFailAlloc_6810_, 1, v___x_6785_);
lean_ctor_set(v_reuseFailAlloc_6810_, 2, v_buildTime_6770_);
lean_ctor_set_uint8(v_reuseFailAlloc_6810_, sizeof(void*)*3, v_action_6767_);
lean_ctor_set_uint8(v_reuseFailAlloc_6810_, sizeof(void*)*3 + 1, v_wantsRebuild_6768_);
v___x_6787_ = v_reuseFailAlloc_6810_;
goto v_reusejp_6786_;
}
v_reusejp_6786_:
{
uint8_t v___x_6788_; lean_object* v___x_6789_; lean_object* v___x_6790_; 
v___x_6788_ = 0;
v___x_6789_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
v___x_6790_ = l_Lake_buildArtifactUnlessUpToDate(v_oFile_6738_, v___f_6757_, v___x_6788_, v___x_6789_, v___x_6788_, v___x_6788_, v___x_6788_, v___y_6762_, v___y_6764_, v___y_6763_, v___y_6761_, v___y_6760_, v___x_6787_);
if (lean_obj_tag(v___x_6790_) == 0)
{
lean_object* v_a_6791_; lean_object* v_a_6792_; lean_object* v___x_6794_; uint8_t v_isShared_6795_; uint8_t v_isSharedCheck_6800_; 
v_a_6791_ = lean_ctor_get(v___x_6790_, 0);
v_a_6792_ = lean_ctor_get(v___x_6790_, 1);
v_isSharedCheck_6800_ = !lean_is_exclusive(v___x_6790_);
if (v_isSharedCheck_6800_ == 0)
{
v___x_6794_ = v___x_6790_;
v_isShared_6795_ = v_isSharedCheck_6800_;
goto v_resetjp_6793_;
}
else
{
lean_inc(v_a_6792_);
lean_inc(v_a_6791_);
lean_dec(v___x_6790_);
v___x_6794_ = lean_box(0);
v_isShared_6795_ = v_isSharedCheck_6800_;
goto v_resetjp_6793_;
}
v_resetjp_6793_:
{
lean_object* v_path_6796_; lean_object* v___x_6798_; 
v_path_6796_ = lean_ctor_get(v_a_6791_, 1);
lean_inc_ref(v_path_6796_);
lean_dec(v_a_6791_);
if (v_isShared_6795_ == 0)
{
lean_ctor_set(v___x_6794_, 0, v_path_6796_);
v___x_6798_ = v___x_6794_;
goto v_reusejp_6797_;
}
else
{
lean_object* v_reuseFailAlloc_6799_; 
v_reuseFailAlloc_6799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6799_, 0, v_path_6796_);
lean_ctor_set(v_reuseFailAlloc_6799_, 1, v_a_6792_);
v___x_6798_ = v_reuseFailAlloc_6799_;
goto v_reusejp_6797_;
}
v_reusejp_6797_:
{
return v___x_6798_;
}
}
}
else
{
lean_object* v_a_6801_; lean_object* v_a_6802_; lean_object* v___x_6804_; uint8_t v_isShared_6805_; uint8_t v_isSharedCheck_6809_; 
v_a_6801_ = lean_ctor_get(v___x_6790_, 0);
v_a_6802_ = lean_ctor_get(v___x_6790_, 1);
v_isSharedCheck_6809_ = !lean_is_exclusive(v___x_6790_);
if (v_isSharedCheck_6809_ == 0)
{
v___x_6804_ = v___x_6790_;
v_isShared_6805_ = v_isSharedCheck_6809_;
goto v_resetjp_6803_;
}
else
{
lean_inc(v_a_6802_);
lean_inc(v_a_6801_);
lean_dec(v___x_6790_);
v___x_6804_ = lean_box(0);
v_isShared_6805_ = v_isSharedCheck_6809_;
goto v_resetjp_6803_;
}
v_resetjp_6803_:
{
lean_object* v___x_6807_; 
if (v_isShared_6805_ == 0)
{
v___x_6807_ = v___x_6804_;
goto v_reusejp_6806_;
}
else
{
lean_object* v_reuseFailAlloc_6808_; 
v_reuseFailAlloc_6808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6808_, 0, v_a_6801_);
lean_ctor_set(v_reuseFailAlloc_6808_, 1, v_a_6802_);
v___x_6807_ = v_reuseFailAlloc_6808_;
goto v_reusejp_6806_;
}
v_reusejp_6806_:
{
return v___x_6807_;
}
}
}
}
}
}
v___jp_6812_:
{
uint64_t v___x_6819_; lean_object* v___x_6820_; lean_object* v___x_6821_; uint8_t v___x_6822_; 
v___x_6819_ = l_Lake_Hash_nil;
v___x_6820_ = lean_unsigned_to_nat(0u);
v___x_6821_ = lean_array_get_size(v_traceArgs_6737_);
v___x_6822_ = lean_nat_dec_lt(v___x_6820_, v___x_6821_);
if (v___x_6822_ == 0)
{
v___y_6759_ = v___y_6818_;
v___y_6760_ = v___y_6817_;
v___y_6761_ = v___y_6816_;
v___y_6762_ = v___y_6813_;
v___y_6763_ = v___y_6815_;
v___y_6764_ = v___y_6814_;
v___y_6765_ = v___x_6819_;
goto v___jp_6758_;
}
else
{
size_t v___x_6823_; size_t v___x_6824_; uint64_t v___x_6825_; 
v___x_6823_ = ((size_t)0ULL);
v___x_6824_ = lean_usize_of_nat(v___x_6821_);
v___x_6825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Internal_buildLeanO_spec__1(v_traceArgs_6737_, v___x_6823_, v___x_6824_, v___x_6819_);
v___y_6759_ = v___y_6818_;
v___y_6760_ = v___y_6817_;
v___y_6761_ = v___y_6816_;
v___y_6762_ = v___y_6813_;
v___y_6763_ = v___y_6815_;
v___y_6764_ = v___y_6814_;
v___y_6765_ = v___x_6825_;
goto v___jp_6758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Internal_buildLeanO___lam__1___boxed(lean_object* v_weakArgs_6837_, lean_object* v_traceArgs_6838_, lean_object* v_oFile_6839_, lean_object* v_leanIncludeDir_x3f_6840_, lean_object* v_srcFile_6841_, lean_object* v___y_6842_, lean_object* v___y_6843_, lean_object* v___y_6844_, lean_object* v___y_6845_, lean_object* v___y_6846_, lean_object* v___y_6847_, lean_object* v___y_6848_){
_start:
{
lean_object* v_res_6849_; 
v_res_6849_ = l_Lake_Internal_buildLeanO___lam__1(v_weakArgs_6837_, v_traceArgs_6838_, v_oFile_6839_, v_leanIncludeDir_x3f_6840_, v_srcFile_6841_, v___y_6842_, v___y_6843_, v___y_6844_, v___y_6845_, v___y_6846_, v___y_6847_);
lean_dec_ref(v___y_6846_);
lean_dec(v___y_6845_);
lean_dec(v___y_6844_);
lean_dec(v___y_6843_);
return v_res_6849_;
}
}
LEAN_EXPORT lean_object* l_Lake_Internal_buildLeanO(lean_object* v_oFile_6850_, lean_object* v_srcJob_6851_, lean_object* v_weakArgs_6852_, lean_object* v_traceArgs_6853_, lean_object* v_leanIncludeDir_x3f_6854_, lean_object* v_a_6855_, lean_object* v_a_6856_, lean_object* v_a_6857_, lean_object* v_a_6858_, lean_object* v_a_6859_, lean_object* v_a_6860_){
_start:
{
lean_object* v___f_6862_; lean_object* v___x_6863_; lean_object* v___x_6864_; uint8_t v___x_6865_; lean_object* v___x_6866_; 
v___f_6862_ = lean_alloc_closure((void*)(l_Lake_Internal_buildLeanO___lam__1___boxed), 12, 4);
lean_closure_set(v___f_6862_, 0, v_weakArgs_6852_);
lean_closure_set(v___f_6862_, 1, v_traceArgs_6853_);
lean_closure_set(v___f_6862_, 2, v_oFile_6850_);
lean_closure_set(v___f_6862_, 3, v_leanIncludeDir_x3f_6854_);
v___x_6863_ = l_Lake_instDataKindFilePath;
v___x_6864_ = lean_unsigned_to_nat(0u);
v___x_6865_ = 0;
v___x_6866_ = l_Lake_Job_mapM___redArg(v___x_6863_, v_srcJob_6851_, v___f_6862_, v___x_6864_, v___x_6865_, v_a_6855_, v_a_6856_, v_a_6857_, v_a_6858_, v_a_6859_, v_a_6860_);
return v___x_6866_;
}
}
LEAN_EXPORT lean_object* l_Lake_Internal_buildLeanO___boxed(lean_object* v_oFile_6867_, lean_object* v_srcJob_6868_, lean_object* v_weakArgs_6869_, lean_object* v_traceArgs_6870_, lean_object* v_leanIncludeDir_x3f_6871_, lean_object* v_a_6872_, lean_object* v_a_6873_, lean_object* v_a_6874_, lean_object* v_a_6875_, lean_object* v_a_6876_, lean_object* v_a_6877_, lean_object* v_a_6878_){
_start:
{
lean_object* v_res_6879_; 
v_res_6879_ = l_Lake_Internal_buildLeanO(v_oFile_6867_, v_srcJob_6868_, v_weakArgs_6869_, v_traceArgs_6870_, v_leanIncludeDir_x3f_6871_, v_a_6872_, v_a_6873_, v_a_6874_, v_a_6875_, v_a_6876_, v_a_6877_);
lean_dec_ref(v_a_6877_);
lean_dec_ref(v_a_6876_);
lean_dec(v_a_6875_);
lean_dec(v_a_6874_);
lean_dec(v_a_6873_);
return v_res_6879_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object* v_oFile_6880_, lean_object* v_srcJob_6881_, lean_object* v_weakArgs_6882_, lean_object* v_traceArgs_6883_, lean_object* v_a_6884_, lean_object* v_a_6885_, lean_object* v_a_6886_, lean_object* v_a_6887_, lean_object* v_a_6888_, lean_object* v_a_6889_){
_start:
{
lean_object* v___x_6891_; lean_object* v___x_6892_; 
v___x_6891_ = lean_box(0);
v___x_6892_ = l_Lake_Internal_buildLeanO(v_oFile_6880_, v_srcJob_6881_, v_weakArgs_6882_, v_traceArgs_6883_, v___x_6891_, v_a_6884_, v_a_6885_, v_a_6886_, v_a_6887_, v_a_6888_, v_a_6889_);
return v___x_6892_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___boxed(lean_object* v_oFile_6893_, lean_object* v_srcJob_6894_, lean_object* v_weakArgs_6895_, lean_object* v_traceArgs_6896_, lean_object* v_a_6897_, lean_object* v_a_6898_, lean_object* v_a_6899_, lean_object* v_a_6900_, lean_object* v_a_6901_, lean_object* v_a_6902_, lean_object* v_a_6903_){
_start:
{
lean_object* v_res_6904_; 
v_res_6904_ = l_Lake_buildLeanO(v_oFile_6893_, v_srcJob_6894_, v_weakArgs_6895_, v_traceArgs_6896_, v_a_6897_, v_a_6898_, v_a_6899_, v_a_6900_, v_a_6901_, v_a_6902_);
lean_dec_ref(v_a_6902_);
lean_dec_ref(v_a_6901_);
lean_dec(v_a_6900_);
lean_dec(v_a_6899_);
lean_dec(v_a_6898_);
return v_res_6904_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0(lean_object* v_libFile_6905_, lean_object* v_oFiles_6906_, uint8_t v_thin_6907_, lean_object* v___y_6908_, lean_object* v___y_6909_, lean_object* v___y_6910_, lean_object* v___y_6911_, lean_object* v___y_6912_, lean_object* v___y_6913_){
_start:
{
lean_object* v_toContext_6915_; lean_object* v_lakeEnv_6916_; lean_object* v_lean_6917_; lean_object* v_log_6918_; uint8_t v_action_6919_; uint8_t v_wantsRebuild_6920_; lean_object* v_trace_6921_; lean_object* v_buildTime_6922_; lean_object* v___x_6924_; uint8_t v_isShared_6925_; uint8_t v_isSharedCheck_6952_; 
v_toContext_6915_ = lean_ctor_get(v___y_6912_, 1);
v_lakeEnv_6916_ = lean_ctor_get(v_toContext_6915_, 0);
v_lean_6917_ = lean_ctor_get(v_lakeEnv_6916_, 1);
v_log_6918_ = lean_ctor_get(v___y_6913_, 0);
v_action_6919_ = lean_ctor_get_uint8(v___y_6913_, sizeof(void*)*3);
v_wantsRebuild_6920_ = lean_ctor_get_uint8(v___y_6913_, sizeof(void*)*3 + 1);
v_trace_6921_ = lean_ctor_get(v___y_6913_, 1);
v_buildTime_6922_ = lean_ctor_get(v___y_6913_, 2);
v_isSharedCheck_6952_ = !lean_is_exclusive(v___y_6913_);
if (v_isSharedCheck_6952_ == 0)
{
v___x_6924_ = v___y_6913_;
v_isShared_6925_ = v_isSharedCheck_6952_;
goto v_resetjp_6923_;
}
else
{
lean_inc(v_buildTime_6922_);
lean_inc(v_trace_6921_);
lean_inc(v_log_6918_);
lean_dec(v___y_6913_);
v___x_6924_ = lean_box(0);
v_isShared_6925_ = v_isSharedCheck_6952_;
goto v_resetjp_6923_;
}
v_resetjp_6923_:
{
lean_object* v_ar_6926_; lean_object* v___x_6927_; 
v_ar_6926_ = lean_ctor_get(v_lean_6917_, 13);
lean_inc_ref(v_ar_6926_);
v___x_6927_ = l_Lake_compileStaticLib(v_libFile_6905_, v_oFiles_6906_, v_ar_6926_, v_thin_6907_, v_log_6918_);
if (lean_obj_tag(v___x_6927_) == 0)
{
lean_object* v_a_6928_; lean_object* v_a_6929_; lean_object* v___x_6931_; uint8_t v_isShared_6932_; uint8_t v_isSharedCheck_6939_; 
v_a_6928_ = lean_ctor_get(v___x_6927_, 0);
v_a_6929_ = lean_ctor_get(v___x_6927_, 1);
v_isSharedCheck_6939_ = !lean_is_exclusive(v___x_6927_);
if (v_isSharedCheck_6939_ == 0)
{
v___x_6931_ = v___x_6927_;
v_isShared_6932_ = v_isSharedCheck_6939_;
goto v_resetjp_6930_;
}
else
{
lean_inc(v_a_6929_);
lean_inc(v_a_6928_);
lean_dec(v___x_6927_);
v___x_6931_ = lean_box(0);
v_isShared_6932_ = v_isSharedCheck_6939_;
goto v_resetjp_6930_;
}
v_resetjp_6930_:
{
lean_object* v___x_6934_; 
if (v_isShared_6925_ == 0)
{
lean_ctor_set(v___x_6924_, 0, v_a_6929_);
v___x_6934_ = v___x_6924_;
goto v_reusejp_6933_;
}
else
{
lean_object* v_reuseFailAlloc_6938_; 
v_reuseFailAlloc_6938_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6938_, 0, v_a_6929_);
lean_ctor_set(v_reuseFailAlloc_6938_, 1, v_trace_6921_);
lean_ctor_set(v_reuseFailAlloc_6938_, 2, v_buildTime_6922_);
lean_ctor_set_uint8(v_reuseFailAlloc_6938_, sizeof(void*)*3, v_action_6919_);
lean_ctor_set_uint8(v_reuseFailAlloc_6938_, sizeof(void*)*3 + 1, v_wantsRebuild_6920_);
v___x_6934_ = v_reuseFailAlloc_6938_;
goto v_reusejp_6933_;
}
v_reusejp_6933_:
{
lean_object* v___x_6936_; 
if (v_isShared_6932_ == 0)
{
lean_ctor_set(v___x_6931_, 1, v___x_6934_);
v___x_6936_ = v___x_6931_;
goto v_reusejp_6935_;
}
else
{
lean_object* v_reuseFailAlloc_6937_; 
v_reuseFailAlloc_6937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6937_, 0, v_a_6928_);
lean_ctor_set(v_reuseFailAlloc_6937_, 1, v___x_6934_);
v___x_6936_ = v_reuseFailAlloc_6937_;
goto v_reusejp_6935_;
}
v_reusejp_6935_:
{
return v___x_6936_;
}
}
}
}
else
{
lean_object* v_a_6940_; lean_object* v_a_6941_; lean_object* v___x_6943_; uint8_t v_isShared_6944_; uint8_t v_isSharedCheck_6951_; 
v_a_6940_ = lean_ctor_get(v___x_6927_, 0);
v_a_6941_ = lean_ctor_get(v___x_6927_, 1);
v_isSharedCheck_6951_ = !lean_is_exclusive(v___x_6927_);
if (v_isSharedCheck_6951_ == 0)
{
v___x_6943_ = v___x_6927_;
v_isShared_6944_ = v_isSharedCheck_6951_;
goto v_resetjp_6942_;
}
else
{
lean_inc(v_a_6941_);
lean_inc(v_a_6940_);
lean_dec(v___x_6927_);
v___x_6943_ = lean_box(0);
v_isShared_6944_ = v_isSharedCheck_6951_;
goto v_resetjp_6942_;
}
v_resetjp_6942_:
{
lean_object* v___x_6946_; 
if (v_isShared_6925_ == 0)
{
lean_ctor_set(v___x_6924_, 0, v_a_6941_);
v___x_6946_ = v___x_6924_;
goto v_reusejp_6945_;
}
else
{
lean_object* v_reuseFailAlloc_6950_; 
v_reuseFailAlloc_6950_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6950_, 0, v_a_6941_);
lean_ctor_set(v_reuseFailAlloc_6950_, 1, v_trace_6921_);
lean_ctor_set(v_reuseFailAlloc_6950_, 2, v_buildTime_6922_);
lean_ctor_set_uint8(v_reuseFailAlloc_6950_, sizeof(void*)*3, v_action_6919_);
lean_ctor_set_uint8(v_reuseFailAlloc_6950_, sizeof(void*)*3 + 1, v_wantsRebuild_6920_);
v___x_6946_ = v_reuseFailAlloc_6950_;
goto v_reusejp_6945_;
}
v_reusejp_6945_:
{
lean_object* v___x_6948_; 
if (v_isShared_6944_ == 0)
{
lean_ctor_set(v___x_6943_, 1, v___x_6946_);
v___x_6948_ = v___x_6943_;
goto v_reusejp_6947_;
}
else
{
lean_object* v_reuseFailAlloc_6949_; 
v_reuseFailAlloc_6949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6949_, 0, v_a_6940_);
lean_ctor_set(v_reuseFailAlloc_6949_, 1, v___x_6946_);
v___x_6948_ = v_reuseFailAlloc_6949_;
goto v_reusejp_6947_;
}
v_reusejp_6947_:
{
return v___x_6948_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0___boxed(lean_object* v_libFile_6953_, lean_object* v_oFiles_6954_, lean_object* v_thin_6955_, lean_object* v___y_6956_, lean_object* v___y_6957_, lean_object* v___y_6958_, lean_object* v___y_6959_, lean_object* v___y_6960_, lean_object* v___y_6961_, lean_object* v___y_6962_){
_start:
{
uint8_t v_thin_boxed_6963_; lean_object* v_res_6964_; 
v_thin_boxed_6963_ = lean_unbox(v_thin_6955_);
v_res_6964_ = l_Lake_buildStaticLib___lam__0(v_libFile_6953_, v_oFiles_6954_, v_thin_boxed_6963_, v___y_6956_, v___y_6957_, v___y_6958_, v___y_6959_, v___y_6960_, v___y_6961_);
lean_dec_ref(v___y_6960_);
lean_dec(v___y_6959_);
lean_dec(v___y_6958_);
lean_dec(v___y_6957_);
lean_dec_ref(v___y_6956_);
return v_res_6964_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1(lean_object* v_libFile_6966_, uint8_t v_thin_6967_, lean_object* v_oFiles_6968_, lean_object* v___y_6969_, lean_object* v___y_6970_, lean_object* v___y_6971_, lean_object* v___y_6972_, lean_object* v___y_6973_, lean_object* v___y_6974_){
_start:
{
lean_object* v___x_6976_; lean_object* v___f_6977_; uint8_t v___x_6978_; lean_object* v___x_6979_; uint8_t v___x_6980_; lean_object* v___x_6981_; 
v___x_6976_ = lean_box(v_thin_6967_);
lean_inc_ref(v_libFile_6966_);
v___f_6977_ = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6977_, 0, v_libFile_6966_);
lean_closure_set(v___f_6977_, 1, v_oFiles_6968_);
lean_closure_set(v___f_6977_, 2, v___x_6976_);
v___x_6978_ = 0;
v___x_6979_ = ((lean_object*)(l_Lake_buildStaticLib___lam__1___closed__0));
v___x_6980_ = 1;
v___x_6981_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_6966_, v___f_6977_, v___x_6978_, v___x_6979_, v___x_6980_, v___x_6978_, v___x_6978_, v___y_6969_, v___y_6970_, v___y_6971_, v___y_6972_, v___y_6973_, v___y_6974_);
if (lean_obj_tag(v___x_6981_) == 0)
{
lean_object* v_a_6982_; lean_object* v_a_6983_; lean_object* v___x_6985_; uint8_t v_isShared_6986_; uint8_t v_isSharedCheck_6991_; 
v_a_6982_ = lean_ctor_get(v___x_6981_, 0);
v_a_6983_ = lean_ctor_get(v___x_6981_, 1);
v_isSharedCheck_6991_ = !lean_is_exclusive(v___x_6981_);
if (v_isSharedCheck_6991_ == 0)
{
v___x_6985_ = v___x_6981_;
v_isShared_6986_ = v_isSharedCheck_6991_;
goto v_resetjp_6984_;
}
else
{
lean_inc(v_a_6983_);
lean_inc(v_a_6982_);
lean_dec(v___x_6981_);
v___x_6985_ = lean_box(0);
v_isShared_6986_ = v_isSharedCheck_6991_;
goto v_resetjp_6984_;
}
v_resetjp_6984_:
{
lean_object* v_path_6987_; lean_object* v___x_6989_; 
v_path_6987_ = lean_ctor_get(v_a_6982_, 1);
lean_inc_ref(v_path_6987_);
lean_dec(v_a_6982_);
if (v_isShared_6986_ == 0)
{
lean_ctor_set(v___x_6985_, 0, v_path_6987_);
v___x_6989_ = v___x_6985_;
goto v_reusejp_6988_;
}
else
{
lean_object* v_reuseFailAlloc_6990_; 
v_reuseFailAlloc_6990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6990_, 0, v_path_6987_);
lean_ctor_set(v_reuseFailAlloc_6990_, 1, v_a_6983_);
v___x_6989_ = v_reuseFailAlloc_6990_;
goto v_reusejp_6988_;
}
v_reusejp_6988_:
{
return v___x_6989_;
}
}
}
else
{
lean_object* v_a_6992_; lean_object* v_a_6993_; lean_object* v___x_6995_; uint8_t v_isShared_6996_; uint8_t v_isSharedCheck_7000_; 
v_a_6992_ = lean_ctor_get(v___x_6981_, 0);
v_a_6993_ = lean_ctor_get(v___x_6981_, 1);
v_isSharedCheck_7000_ = !lean_is_exclusive(v___x_6981_);
if (v_isSharedCheck_7000_ == 0)
{
v___x_6995_ = v___x_6981_;
v_isShared_6996_ = v_isSharedCheck_7000_;
goto v_resetjp_6994_;
}
else
{
lean_inc(v_a_6993_);
lean_inc(v_a_6992_);
lean_dec(v___x_6981_);
v___x_6995_ = lean_box(0);
v_isShared_6996_ = v_isSharedCheck_7000_;
goto v_resetjp_6994_;
}
v_resetjp_6994_:
{
lean_object* v___x_6998_; 
if (v_isShared_6996_ == 0)
{
v___x_6998_ = v___x_6995_;
goto v_reusejp_6997_;
}
else
{
lean_object* v_reuseFailAlloc_6999_; 
v_reuseFailAlloc_6999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6999_, 0, v_a_6992_);
lean_ctor_set(v_reuseFailAlloc_6999_, 1, v_a_6993_);
v___x_6998_ = v_reuseFailAlloc_6999_;
goto v_reusejp_6997_;
}
v_reusejp_6997_:
{
return v___x_6998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1___boxed(lean_object* v_libFile_7001_, lean_object* v_thin_7002_, lean_object* v_oFiles_7003_, lean_object* v___y_7004_, lean_object* v___y_7005_, lean_object* v___y_7006_, lean_object* v___y_7007_, lean_object* v___y_7008_, lean_object* v___y_7009_, lean_object* v___y_7010_){
_start:
{
uint8_t v_thin_boxed_7011_; lean_object* v_res_7012_; 
v_thin_boxed_7011_ = lean_unbox(v_thin_7002_);
v_res_7012_ = l_Lake_buildStaticLib___lam__1(v_libFile_7001_, v_thin_boxed_7011_, v_oFiles_7003_, v___y_7004_, v___y_7005_, v___y_7006_, v___y_7007_, v___y_7008_, v___y_7009_);
lean_dec_ref(v___y_7008_);
lean_dec(v___y_7007_);
lean_dec(v___y_7006_);
lean_dec(v___y_7005_);
return v_res_7012_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object* v_libFile_7014_, lean_object* v_oFileJobs_7015_, uint8_t v_thin_7016_, lean_object* v_a_7017_, lean_object* v_a_7018_, lean_object* v_a_7019_, lean_object* v_a_7020_, lean_object* v_a_7021_, lean_object* v_a_7022_){
_start:
{
lean_object* v___x_7024_; lean_object* v___f_7025_; lean_object* v___x_7026_; lean_object* v___x_7027_; lean_object* v___x_7028_; lean_object* v___x_7029_; uint8_t v___x_7030_; lean_object* v___x_7031_; 
v___x_7024_ = lean_box(v_thin_7016_);
v___f_7025_ = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__1___boxed), 10, 2);
lean_closure_set(v___f_7025_, 0, v_libFile_7014_);
lean_closure_set(v___f_7025_, 1, v___x_7024_);
v___x_7026_ = l_Lake_instDataKindFilePath;
v___x_7027_ = ((lean_object*)(l_Lake_buildStaticLib___closed__0));
v___x_7028_ = l_Lake_Job_collectArray___redArg(v_oFileJobs_7015_, v___x_7027_);
v___x_7029_ = lean_unsigned_to_nat(0u);
v___x_7030_ = 0;
v___x_7031_ = l_Lake_Job_mapM___redArg(v___x_7026_, v___x_7028_, v___f_7025_, v___x_7029_, v___x_7030_, v_a_7017_, v_a_7018_, v_a_7019_, v_a_7020_, v_a_7021_, v_a_7022_);
return v___x_7031_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object* v_libFile_7032_, lean_object* v_oFileJobs_7033_, lean_object* v_thin_7034_, lean_object* v_a_7035_, lean_object* v_a_7036_, lean_object* v_a_7037_, lean_object* v_a_7038_, lean_object* v_a_7039_, lean_object* v_a_7040_, lean_object* v_a_7041_){
_start:
{
uint8_t v_thin_boxed_7042_; lean_object* v_res_7043_; 
v_thin_boxed_7042_ = lean_unbox(v_thin_7034_);
v_res_7043_ = l_Lake_buildStaticLib(v_libFile_7032_, v_oFileJobs_7033_, v_thin_boxed_7042_, v_a_7035_, v_a_7036_, v_a_7037_, v_a_7038_, v_a_7039_, v_a_7040_);
lean_dec_ref(v_a_7040_);
lean_dec_ref(v_a_7039_);
lean_dec(v_a_7038_);
lean_dec(v_a_7037_);
lean_dec(v_a_7036_);
lean_dec_ref(v_oFileJobs_7033_);
return v_res_7043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(lean_object* v_as_7044_, size_t v_sz_7045_, size_t v_i_7046_, lean_object* v_b_7047_){
_start:
{
uint8_t v___x_7048_; 
v___x_7048_ = lean_usize_dec_lt(v_i_7046_, v_sz_7045_);
if (v___x_7048_ == 0)
{
return v_b_7047_;
}
else
{
lean_object* v_a_7049_; lean_object* v___x_7050_; size_t v___x_7051_; size_t v___x_7052_; 
v_a_7049_ = lean_array_uget_borrowed(v_as_7044_, v_i_7046_);
lean_inc(v_a_7049_);
v___x_7050_ = lean_array_push(v_b_7047_, v_a_7049_);
v___x_7051_ = ((size_t)1ULL);
v___x_7052_ = lean_usize_add(v_i_7046_, v___x_7051_);
v_i_7046_ = v___x_7052_;
v_b_7047_ = v___x_7050_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0___boxed(lean_object* v_as_7054_, lean_object* v_sz_7055_, lean_object* v_i_7056_, lean_object* v_b_7057_){
_start:
{
size_t v_sz_boxed_7058_; size_t v_i_boxed_7059_; lean_object* v_res_7060_; 
v_sz_boxed_7058_ = lean_unbox_usize(v_sz_7055_);
lean_dec(v_sz_7055_);
v_i_boxed_7059_ = lean_unbox_usize(v_i_7056_);
lean_dec(v_i_7056_);
v_res_7060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(v_as_7054_, v_sz_boxed_7058_, v_i_boxed_7059_, v_b_7057_);
lean_dec_ref(v_as_7054_);
return v_res_7060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(lean_object* v_as_7063_, size_t v_sz_7064_, size_t v_i_7065_, lean_object* v_b_7066_){
_start:
{
uint8_t v___x_7067_; 
v___x_7067_ = lean_usize_dec_lt(v_i_7065_, v_sz_7064_);
if (v___x_7067_ == 0)
{
return v_b_7066_;
}
else
{
lean_object* v_a_7068_; lean_object* v_args_7070_; lean_object* v___x_7078_; 
v_a_7068_ = lean_array_uget_borrowed(v_as_7063_, v_i_7065_);
lean_inc(v_a_7068_);
v___x_7078_ = l_Lake_Dynlib_dir_x3f(v_a_7068_);
if (lean_obj_tag(v___x_7078_) == 1)
{
lean_object* v_val_7079_; lean_object* v___x_7080_; lean_object* v___x_7081_; lean_object* v___x_7082_; 
v_val_7079_ = lean_ctor_get(v___x_7078_, 0);
lean_inc(v_val_7079_);
lean_dec_ref_known(v___x_7078_, 1);
v___x_7080_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
v___x_7081_ = lean_string_append(v___x_7080_, v_val_7079_);
lean_dec(v_val_7079_);
v___x_7082_ = lean_array_push(v_b_7066_, v___x_7081_);
v_args_7070_ = v___x_7082_;
goto v___jp_7069_;
}
else
{
lean_dec(v___x_7078_);
v_args_7070_ = v_b_7066_;
goto v___jp_7069_;
}
v___jp_7069_:
{
lean_object* v_name_7071_; lean_object* v___x_7072_; lean_object* v___x_7073_; lean_object* v___x_7074_; size_t v___x_7075_; size_t v___x_7076_; 
v_name_7071_ = lean_ctor_get(v_a_7068_, 1);
v___x_7072_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0));
v___x_7073_ = lean_string_append(v___x_7072_, v_name_7071_);
v___x_7074_ = lean_array_push(v_args_7070_, v___x_7073_);
v___x_7075_ = ((size_t)1ULL);
v___x_7076_ = lean_usize_add(v_i_7065_, v___x_7075_);
v_i_7065_ = v___x_7076_;
v_b_7066_ = v___x_7074_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___boxed(lean_object* v_as_7083_, lean_object* v_sz_7084_, lean_object* v_i_7085_, lean_object* v_b_7086_){
_start:
{
size_t v_sz_boxed_7087_; size_t v_i_boxed_7088_; lean_object* v_res_7089_; 
v_sz_boxed_7087_ = lean_unbox_usize(v_sz_7084_);
lean_dec(v_sz_7084_);
v_i_boxed_7088_ = lean_unbox_usize(v_i_7085_);
lean_dec(v_i_7085_);
v_res_7089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(v_as_7083_, v_sz_boxed_7087_, v_i_boxed_7088_, v_b_7086_);
lean_dec_ref(v_as_7083_);
return v_res_7089_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(lean_object* v_objs_7090_, lean_object* v_libs_7091_){
_start:
{
lean_object* v_args_7092_; size_t v_sz_7093_; size_t v___x_7094_; lean_object* v___x_7095_; size_t v_sz_7096_; lean_object* v___x_7097_; 
v_args_7092_ = ((lean_object*)(l_Lake_inputDir___lam__2___closed__0));
v_sz_7093_ = lean_array_size(v_objs_7090_);
v___x_7094_ = ((size_t)0ULL);
v___x_7095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(v_objs_7090_, v_sz_7093_, v___x_7094_, v_args_7092_);
v_sz_7096_ = lean_array_size(v_libs_7091_);
v___x_7097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(v_libs_7091_, v_sz_7096_, v___x_7094_, v___x_7095_);
return v___x_7097_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs___boxed(lean_object* v_objs_7098_, lean_object* v_libs_7099_){
_start:
{
lean_object* v_res_7100_; 
v_res_7100_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7098_, v_libs_7099_);
lean_dec_ref(v_libs_7099_);
lean_dec_ref(v_objs_7098_);
return v_res_7100_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(lean_object* v_k_7101_, lean_object* v_t_7102_){
_start:
{
if (lean_obj_tag(v_t_7102_) == 0)
{
lean_object* v_k_7103_; lean_object* v_l_7104_; lean_object* v_r_7105_; uint8_t v___x_7106_; 
v_k_7103_ = lean_ctor_get(v_t_7102_, 1);
v_l_7104_ = lean_ctor_get(v_t_7102_, 3);
v_r_7105_ = lean_ctor_get(v_t_7102_, 4);
v___x_7106_ = lean_string_compare(v_k_7101_, v_k_7103_);
switch(v___x_7106_)
{
case 0:
{
v_t_7102_ = v_l_7104_;
goto _start;
}
case 1:
{
uint8_t v___x_7108_; 
v___x_7108_ = 1;
return v___x_7108_;
}
default: 
{
v_t_7102_ = v_r_7105_;
goto _start;
}
}
}
else
{
uint8_t v___x_7110_; 
v___x_7110_ = 0;
return v___x_7110_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg___boxed(lean_object* v_k_7111_, lean_object* v_t_7112_){
_start:
{
uint8_t v_res_7113_; lean_object* v_r_7114_; 
v_res_7113_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_k_7111_, v_t_7112_);
lean_dec(v_t_7112_);
lean_dec_ref(v_k_7111_);
v_r_7114_ = lean_box(v_res_7113_);
return v_r_7114_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(lean_object* v_a_7115_, lean_object* v_x_7116_){
_start:
{
if (lean_obj_tag(v_x_7116_) == 0)
{
uint8_t v___x_7117_; 
v___x_7117_ = 0;
return v___x_7117_;
}
else
{
lean_object* v_head_7118_; lean_object* v_tail_7119_; uint8_t v___x_7120_; 
v_head_7118_ = lean_ctor_get(v_x_7116_, 0);
v_tail_7119_ = lean_ctor_get(v_x_7116_, 1);
v___x_7120_ = lean_string_dec_eq(v_a_7115_, v_head_7118_);
if (v___x_7120_ == 0)
{
v_x_7116_ = v_tail_7119_;
goto _start;
}
else
{
return v___x_7120_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1___boxed(lean_object* v_a_7122_, lean_object* v_x_7123_){
_start:
{
uint8_t v_res_7124_; lean_object* v_r_7125_; 
v_res_7124_ = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(v_a_7122_, v_x_7123_);
lean_dec(v_x_7123_);
lean_dec_ref(v_a_7122_);
v_r_7125_ = lean_box(v_res_7124_);
return v_r_7125_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(lean_object* v_k_7126_, lean_object* v_v_7127_, lean_object* v_t_7128_){
_start:
{
if (lean_obj_tag(v_t_7128_) == 0)
{
lean_object* v_size_7129_; lean_object* v_k_7130_; lean_object* v_v_7131_; lean_object* v_l_7132_; lean_object* v_r_7133_; lean_object* v___x_7135_; uint8_t v_isShared_7136_; uint8_t v_isSharedCheck_7413_; 
v_size_7129_ = lean_ctor_get(v_t_7128_, 0);
v_k_7130_ = lean_ctor_get(v_t_7128_, 1);
v_v_7131_ = lean_ctor_get(v_t_7128_, 2);
v_l_7132_ = lean_ctor_get(v_t_7128_, 3);
v_r_7133_ = lean_ctor_get(v_t_7128_, 4);
v_isSharedCheck_7413_ = !lean_is_exclusive(v_t_7128_);
if (v_isSharedCheck_7413_ == 0)
{
v___x_7135_ = v_t_7128_;
v_isShared_7136_ = v_isSharedCheck_7413_;
goto v_resetjp_7134_;
}
else
{
lean_inc(v_r_7133_);
lean_inc(v_l_7132_);
lean_inc(v_v_7131_);
lean_inc(v_k_7130_);
lean_inc(v_size_7129_);
lean_dec(v_t_7128_);
v___x_7135_ = lean_box(0);
v_isShared_7136_ = v_isSharedCheck_7413_;
goto v_resetjp_7134_;
}
v_resetjp_7134_:
{
uint8_t v___x_7137_; 
v___x_7137_ = lean_string_compare(v_k_7126_, v_k_7130_);
switch(v___x_7137_)
{
case 0:
{
lean_object* v_impl_7138_; lean_object* v___x_7139_; 
lean_dec(v_size_7129_);
v_impl_7138_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7126_, v_v_7127_, v_l_7132_);
v___x_7139_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_7133_) == 0)
{
lean_object* v_size_7140_; lean_object* v_size_7141_; lean_object* v_k_7142_; lean_object* v_v_7143_; lean_object* v_l_7144_; lean_object* v_r_7145_; lean_object* v___x_7146_; lean_object* v___x_7147_; uint8_t v___x_7148_; 
v_size_7140_ = lean_ctor_get(v_r_7133_, 0);
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
if (v_isShared_7136_ == 0)
{
lean_ctor_set(v___x_7135_, 3, v_impl_7138_);
lean_ctor_set(v___x_7135_, 0, v___x_7150_);
v___x_7152_ = v___x_7135_;
goto v_reusejp_7151_;
}
else
{
lean_object* v_reuseFailAlloc_7153_; 
v_reuseFailAlloc_7153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7153_, 0, v___x_7150_);
lean_ctor_set(v_reuseFailAlloc_7153_, 1, v_k_7130_);
lean_ctor_set(v_reuseFailAlloc_7153_, 2, v_v_7131_);
lean_ctor_set(v_reuseFailAlloc_7153_, 3, v_impl_7138_);
lean_ctor_set(v_reuseFailAlloc_7153_, 4, v_r_7133_);
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
v___x_7175_ = lean_nat_add(v___y_7172_, v___y_7174_);
lean_dec(v___y_7174_);
lean_dec(v___y_7172_);
if (v_isShared_7168_ == 0)
{
lean_ctor_set(v___x_7167_, 4, v_r_7133_);
lean_ctor_set(v___x_7167_, 3, v_r_7162_);
lean_ctor_set(v___x_7167_, 2, v_v_7131_);
lean_ctor_set(v___x_7167_, 1, v_k_7130_);
lean_ctor_set(v___x_7167_, 0, v___x_7175_);
v___x_7177_ = v___x_7167_;
goto v_reusejp_7176_;
}
else
{
lean_object* v_reuseFailAlloc_7181_; 
v_reuseFailAlloc_7181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7181_, 0, v___x_7175_);
lean_ctor_set(v_reuseFailAlloc_7181_, 1, v_k_7130_);
lean_ctor_set(v_reuseFailAlloc_7181_, 2, v_v_7131_);
lean_ctor_set(v_reuseFailAlloc_7181_, 3, v_r_7162_);
lean_ctor_set(v_reuseFailAlloc_7181_, 4, v_r_7133_);
v___x_7177_ = v_reuseFailAlloc_7181_;
goto v_reusejp_7176_;
}
v_reusejp_7176_:
{
lean_object* v___x_7179_; 
if (v_isShared_7156_ == 0)
{
lean_ctor_set(v___x_7155_, 4, v___x_7177_);
lean_ctor_set(v___x_7155_, 3, v___y_7173_);
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
lean_ctor_set(v_reuseFailAlloc_7180_, 3, v___y_7173_);
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
if (v_isShared_7136_ == 0)
{
lean_ctor_set(v___x_7135_, 4, v_l_7161_);
lean_ctor_set(v___x_7135_, 3, v_l_7144_);
lean_ctor_set(v___x_7135_, 2, v_v_7143_);
lean_ctor_set(v___x_7135_, 1, v_k_7142_);
lean_ctor_set(v___x_7135_, 0, v___x_7185_);
v___x_7187_ = v___x_7135_;
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
v___y_7172_ = v___x_7188_;
v___y_7173_ = v___x_7187_;
v___y_7174_ = v_size_7189_;
goto v___jp_7171_;
}
else
{
lean_object* v___x_7190_; 
v___x_7190_ = lean_unsigned_to_nat(0u);
v___y_7172_ = v___x_7188_;
v___y_7173_ = v___x_7187_;
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
lean_del_object(v___x_7135_);
v___x_7200_ = lean_nat_add(v___x_7139_, v_size_7141_);
lean_dec(v_size_7141_);
v___x_7201_ = lean_nat_add(v___x_7200_, v_size_7140_);
lean_dec(v___x_7200_);
v___x_7202_ = lean_nat_add(v___x_7139_, v_size_7140_);
v___x_7203_ = lean_nat_add(v___x_7202_, v_size_7158_);
lean_dec(v___x_7202_);
lean_inc_ref(v_r_7133_);
if (v_isShared_7156_ == 0)
{
lean_ctor_set(v___x_7155_, 4, v_r_7133_);
lean_ctor_set(v___x_7155_, 3, v_r_7145_);
lean_ctor_set(v___x_7155_, 2, v_v_7131_);
lean_ctor_set(v___x_7155_, 1, v_k_7130_);
lean_ctor_set(v___x_7155_, 0, v___x_7203_);
v___x_7205_ = v___x_7155_;
goto v_reusejp_7204_;
}
else
{
lean_object* v_reuseFailAlloc_7218_; 
v_reuseFailAlloc_7218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7218_, 0, v___x_7203_);
lean_ctor_set(v_reuseFailAlloc_7218_, 1, v_k_7130_);
lean_ctor_set(v_reuseFailAlloc_7218_, 2, v_v_7131_);
lean_ctor_set(v_reuseFailAlloc_7218_, 3, v_r_7145_);
lean_ctor_set(v_reuseFailAlloc_7218_, 4, v_r_7133_);
v___x_7205_ = v_reuseFailAlloc_7218_;
goto v_reusejp_7204_;
}
v_reusejp_7204_:
{
lean_object* v___x_7207_; uint8_t v_isShared_7208_; uint8_t v_isSharedCheck_7212_; 
v_isSharedCheck_7212_ = !lean_is_exclusive(v_r_7133_);
if (v_isSharedCheck_7212_ == 0)
{
lean_object* v_unused_7213_; lean_object* v_unused_7214_; lean_object* v_unused_7215_; lean_object* v_unused_7216_; lean_object* v_unused_7217_; 
v_unused_7213_ = lean_ctor_get(v_r_7133_, 4);
lean_dec(v_unused_7213_);
v_unused_7214_ = lean_ctor_get(v_r_7133_, 3);
lean_dec(v_unused_7214_);
v_unused_7215_ = lean_ctor_get(v_r_7133_, 2);
lean_dec(v_unused_7215_);
v_unused_7216_ = lean_ctor_get(v_r_7133_, 1);
lean_dec(v_unused_7216_);
v_unused_7217_ = lean_ctor_get(v_r_7133_, 0);
lean_dec(v_unused_7217_);
v___x_7207_ = v_r_7133_;
v_isShared_7208_ = v_isSharedCheck_7212_;
goto v_resetjp_7206_;
}
else
{
lean_dec(v_r_7133_);
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
lean_ctor_set(v___x_7230_, 2, v_v_7131_);
lean_ctor_set(v___x_7230_, 1, v_k_7130_);
lean_ctor_set(v___x_7230_, 0, v___x_7139_);
v___x_7234_ = v___x_7230_;
goto v_reusejp_7233_;
}
else
{
lean_object* v_reuseFailAlloc_7238_; 
v_reuseFailAlloc_7238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7238_, 0, v___x_7139_);
lean_ctor_set(v_reuseFailAlloc_7238_, 1, v_k_7130_);
lean_ctor_set(v_reuseFailAlloc_7238_, 2, v_v_7131_);
lean_ctor_set(v_reuseFailAlloc_7238_, 3, v_r_7226_);
lean_ctor_set(v_reuseFailAlloc_7238_, 4, v_r_7226_);
v___x_7234_ = v_reuseFailAlloc_7238_;
goto v_reusejp_7233_;
}
v_reusejp_7233_:
{
lean_object* v___x_7236_; 
if (v_isShared_7136_ == 0)
{
lean_ctor_set(v___x_7135_, 4, v___x_7234_);
lean_ctor_set(v___x_7135_, 3, v_l_7225_);
lean_ctor_set(v___x_7135_, 2, v_v_7228_);
lean_ctor_set(v___x_7135_, 1, v_k_7227_);
lean_ctor_set(v___x_7135_, 0, v___x_7232_);
v___x_7236_ = v___x_7135_;
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
lean_ctor_set(v___x_7246_, 2, v_v_7131_);
lean_ctor_set(v___x_7246_, 1, v_k_7130_);
lean_ctor_set(v___x_7246_, 0, v___x_7139_);
v___x_7257_ = v___x_7246_;
goto v_reusejp_7256_;
}
else
{
lean_object* v_reuseFailAlloc_7261_; 
v_reuseFailAlloc_7261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7261_, 0, v___x_7139_);
lean_ctor_set(v_reuseFailAlloc_7261_, 1, v_k_7130_);
lean_ctor_set(v_reuseFailAlloc_7261_, 2, v_v_7131_);
lean_ctor_set(v_reuseFailAlloc_7261_, 3, v_l_7225_);
lean_ctor_set(v_reuseFailAlloc_7261_, 4, v_l_7225_);
v___x_7257_ = v_reuseFailAlloc_7261_;
goto v_reusejp_7256_;
}
v_reusejp_7256_:
{
lean_object* v___x_7259_; 
if (v_isShared_7136_ == 0)
{
lean_ctor_set(v___x_7135_, 4, v___x_7257_);
lean_ctor_set(v___x_7135_, 3, v___x_7255_);
lean_ctor_set(v___x_7135_, 2, v_v_7249_);
lean_ctor_set(v___x_7135_, 1, v_k_7248_);
lean_ctor_set(v___x_7135_, 0, v___x_7253_);
v___x_7259_ = v___x_7135_;
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
if (v_isShared_7136_ == 0)
{
lean_ctor_set(v___x_7135_, 4, v_r_7242_);
lean_ctor_set(v___x_7135_, 3, v_impl_7138_);
lean_ctor_set(v___x_7135_, 0, v___x_7271_);
v___x_7273_ = v___x_7135_;
goto v_reusejp_7272_;
}
else
{
lean_object* v_reuseFailAlloc_7274_; 
v_reuseFailAlloc_7274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7274_, 0, v___x_7271_);
lean_ctor_set(v_reuseFailAlloc_7274_, 1, v_k_7130_);
lean_ctor_set(v_reuseFailAlloc_7274_, 2, v_v_7131_);
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
case 1:
{
lean_object* v___x_7276_; 
lean_dec(v_v_7131_);
lean_dec(v_k_7130_);
if (v_isShared_7136_ == 0)
{
lean_ctor_set(v___x_7135_, 2, v_v_7127_);
lean_ctor_set(v___x_7135_, 1, v_k_7126_);
v___x_7276_ = v___x_7135_;
goto v_reusejp_7275_;
}
else
{
lean_object* v_reuseFailAlloc_7277_; 
v_reuseFailAlloc_7277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7277_, 0, v_size_7129_);
lean_ctor_set(v_reuseFailAlloc_7277_, 1, v_k_7126_);
lean_ctor_set(v_reuseFailAlloc_7277_, 2, v_v_7127_);
lean_ctor_set(v_reuseFailAlloc_7277_, 3, v_l_7132_);
lean_ctor_set(v_reuseFailAlloc_7277_, 4, v_r_7133_);
v___x_7276_ = v_reuseFailAlloc_7277_;
goto v_reusejp_7275_;
}
v_reusejp_7275_:
{
return v___x_7276_;
}
}
default: 
{
lean_object* v_impl_7278_; lean_object* v___x_7279_; 
lean_dec(v_size_7129_);
v_impl_7278_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7126_, v_v_7127_, v_r_7133_);
v___x_7279_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_7132_) == 0)
{
lean_object* v_size_7280_; lean_object* v_size_7281_; lean_object* v_k_7282_; lean_object* v_v_7283_; lean_object* v_l_7284_; lean_object* v_r_7285_; lean_object* v___x_7286_; lean_object* v___x_7287_; uint8_t v___x_7288_; 
v_size_7280_ = lean_ctor_get(v_l_7132_, 0);
v_size_7281_ = lean_ctor_get(v_impl_7278_, 0);
lean_inc(v_size_7281_);
v_k_7282_ = lean_ctor_get(v_impl_7278_, 1);
lean_inc(v_k_7282_);
v_v_7283_ = lean_ctor_get(v_impl_7278_, 2);
lean_inc(v_v_7283_);
v_l_7284_ = lean_ctor_get(v_impl_7278_, 3);
lean_inc(v_l_7284_);
v_r_7285_ = lean_ctor_get(v_impl_7278_, 4);
lean_inc(v_r_7285_);
v___x_7286_ = lean_unsigned_to_nat(3u);
v___x_7287_ = lean_nat_mul(v___x_7286_, v_size_7280_);
v___x_7288_ = lean_nat_dec_lt(v___x_7287_, v_size_7281_);
lean_dec(v___x_7287_);
if (v___x_7288_ == 0)
{
lean_object* v___x_7289_; lean_object* v___x_7290_; lean_object* v___x_7292_; 
lean_dec(v_r_7285_);
lean_dec(v_l_7284_);
lean_dec(v_v_7283_);
lean_dec(v_k_7282_);
v___x_7289_ = lean_nat_add(v___x_7279_, v_size_7280_);
v___x_7290_ = lean_nat_add(v___x_7289_, v_size_7281_);
lean_dec(v_size_7281_);
lean_dec(v___x_7289_);
if (v_isShared_7136_ == 0)
{
lean_ctor_set(v___x_7135_, 4, v_impl_7278_);
lean_ctor_set(v___x_7135_, 0, v___x_7290_);
v___x_7292_ = v___x_7135_;
goto v_reusejp_7291_;
}
else
{
lean_object* v_reuseFailAlloc_7293_; 
v_reuseFailAlloc_7293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7293_, 0, v___x_7290_);
lean_ctor_set(v_reuseFailAlloc_7293_, 1, v_k_7130_);
lean_ctor_set(v_reuseFailAlloc_7293_, 2, v_v_7131_);
lean_ctor_set(v_reuseFailAlloc_7293_, 3, v_l_7132_);
lean_ctor_set(v_reuseFailAlloc_7293_, 4, v_impl_7278_);
v___x_7292_ = v_reuseFailAlloc_7293_;
goto v_reusejp_7291_;
}
v_reusejp_7291_:
{
return v___x_7292_;
}
}
else
{
lean_object* v___x_7295_; uint8_t v_isShared_7296_; uint8_t v_isSharedCheck_7357_; 
v_isSharedCheck_7357_ = !lean_is_exclusive(v_impl_7278_);
if (v_isSharedCheck_7357_ == 0)
{
lean_object* v_unused_7358_; lean_object* v_unused_7359_; lean_object* v_unused_7360_; lean_object* v_unused_7361_; lean_object* v_unused_7362_; 
v_unused_7358_ = lean_ctor_get(v_impl_7278_, 4);
lean_dec(v_unused_7358_);
v_unused_7359_ = lean_ctor_get(v_impl_7278_, 3);
lean_dec(v_unused_7359_);
v_unused_7360_ = lean_ctor_get(v_impl_7278_, 2);
lean_dec(v_unused_7360_);
v_unused_7361_ = lean_ctor_get(v_impl_7278_, 1);
lean_dec(v_unused_7361_);
v_unused_7362_ = lean_ctor_get(v_impl_7278_, 0);
lean_dec(v_unused_7362_);
v___x_7295_ = v_impl_7278_;
v_isShared_7296_ = v_isSharedCheck_7357_;
goto v_resetjp_7294_;
}
else
{
lean_dec(v_impl_7278_);
v___x_7295_ = lean_box(0);
v_isShared_7296_ = v_isSharedCheck_7357_;
goto v_resetjp_7294_;
}
v_resetjp_7294_:
{
lean_object* v_size_7297_; lean_object* v_k_7298_; lean_object* v_v_7299_; lean_object* v_l_7300_; lean_object* v_r_7301_; lean_object* v_size_7302_; lean_object* v___x_7303_; lean_object* v___x_7304_; uint8_t v___x_7305_; 
v_size_7297_ = lean_ctor_get(v_l_7284_, 0);
v_k_7298_ = lean_ctor_get(v_l_7284_, 1);
v_v_7299_ = lean_ctor_get(v_l_7284_, 2);
v_l_7300_ = lean_ctor_get(v_l_7284_, 3);
v_r_7301_ = lean_ctor_get(v_l_7284_, 4);
v_size_7302_ = lean_ctor_get(v_r_7285_, 0);
v___x_7303_ = lean_unsigned_to_nat(2u);
v___x_7304_ = lean_nat_mul(v___x_7303_, v_size_7302_);
v___x_7305_ = lean_nat_dec_lt(v_size_7297_, v___x_7304_);
lean_dec(v___x_7304_);
if (v___x_7305_ == 0)
{
lean_object* v___x_7307_; uint8_t v_isShared_7308_; uint8_t v_isSharedCheck_7333_; 
lean_inc(v_r_7301_);
lean_inc(v_l_7300_);
lean_inc(v_v_7299_);
lean_inc(v_k_7298_);
v_isSharedCheck_7333_ = !lean_is_exclusive(v_l_7284_);
if (v_isSharedCheck_7333_ == 0)
{
lean_object* v_unused_7334_; lean_object* v_unused_7335_; lean_object* v_unused_7336_; lean_object* v_unused_7337_; lean_object* v_unused_7338_; 
v_unused_7334_ = lean_ctor_get(v_l_7284_, 4);
lean_dec(v_unused_7334_);
v_unused_7335_ = lean_ctor_get(v_l_7284_, 3);
lean_dec(v_unused_7335_);
v_unused_7336_ = lean_ctor_get(v_l_7284_, 2);
lean_dec(v_unused_7336_);
v_unused_7337_ = lean_ctor_get(v_l_7284_, 1);
lean_dec(v_unused_7337_);
v_unused_7338_ = lean_ctor_get(v_l_7284_, 0);
lean_dec(v_unused_7338_);
v___x_7307_ = v_l_7284_;
v_isShared_7308_ = v_isSharedCheck_7333_;
goto v_resetjp_7306_;
}
else
{
lean_dec(v_l_7284_);
v___x_7307_ = lean_box(0);
v_isShared_7308_ = v_isSharedCheck_7333_;
goto v_resetjp_7306_;
}
v_resetjp_7306_:
{
lean_object* v___x_7309_; lean_object* v___x_7310_; lean_object* v___y_7312_; lean_object* v___y_7313_; lean_object* v___y_7314_; lean_object* v___y_7323_; 
v___x_7309_ = lean_nat_add(v___x_7279_, v_size_7280_);
v___x_7310_ = lean_nat_add(v___x_7309_, v_size_7281_);
lean_dec(v_size_7281_);
if (lean_obj_tag(v_l_7300_) == 0)
{
lean_object* v_size_7331_; 
v_size_7331_ = lean_ctor_get(v_l_7300_, 0);
lean_inc(v_size_7331_);
v___y_7323_ = v_size_7331_;
goto v___jp_7322_;
}
else
{
lean_object* v___x_7332_; 
v___x_7332_ = lean_unsigned_to_nat(0u);
v___y_7323_ = v___x_7332_;
goto v___jp_7322_;
}
v___jp_7311_:
{
lean_object* v___x_7315_; lean_object* v___x_7317_; 
v___x_7315_ = lean_nat_add(v___y_7312_, v___y_7314_);
lean_dec(v___y_7314_);
lean_dec(v___y_7312_);
if (v_isShared_7308_ == 0)
{
lean_ctor_set(v___x_7307_, 4, v_r_7285_);
lean_ctor_set(v___x_7307_, 3, v_r_7301_);
lean_ctor_set(v___x_7307_, 2, v_v_7283_);
lean_ctor_set(v___x_7307_, 1, v_k_7282_);
lean_ctor_set(v___x_7307_, 0, v___x_7315_);
v___x_7317_ = v___x_7307_;
goto v_reusejp_7316_;
}
else
{
lean_object* v_reuseFailAlloc_7321_; 
v_reuseFailAlloc_7321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7321_, 0, v___x_7315_);
lean_ctor_set(v_reuseFailAlloc_7321_, 1, v_k_7282_);
lean_ctor_set(v_reuseFailAlloc_7321_, 2, v_v_7283_);
lean_ctor_set(v_reuseFailAlloc_7321_, 3, v_r_7301_);
lean_ctor_set(v_reuseFailAlloc_7321_, 4, v_r_7285_);
v___x_7317_ = v_reuseFailAlloc_7321_;
goto v_reusejp_7316_;
}
v_reusejp_7316_:
{
lean_object* v___x_7319_; 
if (v_isShared_7296_ == 0)
{
lean_ctor_set(v___x_7295_, 4, v___x_7317_);
lean_ctor_set(v___x_7295_, 3, v___y_7313_);
lean_ctor_set(v___x_7295_, 2, v_v_7299_);
lean_ctor_set(v___x_7295_, 1, v_k_7298_);
lean_ctor_set(v___x_7295_, 0, v___x_7310_);
v___x_7319_ = v___x_7295_;
goto v_reusejp_7318_;
}
else
{
lean_object* v_reuseFailAlloc_7320_; 
v_reuseFailAlloc_7320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7320_, 0, v___x_7310_);
lean_ctor_set(v_reuseFailAlloc_7320_, 1, v_k_7298_);
lean_ctor_set(v_reuseFailAlloc_7320_, 2, v_v_7299_);
lean_ctor_set(v_reuseFailAlloc_7320_, 3, v___y_7313_);
lean_ctor_set(v_reuseFailAlloc_7320_, 4, v___x_7317_);
v___x_7319_ = v_reuseFailAlloc_7320_;
goto v_reusejp_7318_;
}
v_reusejp_7318_:
{
return v___x_7319_;
}
}
}
v___jp_7322_:
{
lean_object* v___x_7324_; lean_object* v___x_7326_; 
v___x_7324_ = lean_nat_add(v___x_7309_, v___y_7323_);
lean_dec(v___y_7323_);
lean_dec(v___x_7309_);
if (v_isShared_7136_ == 0)
{
lean_ctor_set(v___x_7135_, 4, v_l_7300_);
lean_ctor_set(v___x_7135_, 0, v___x_7324_);
v___x_7326_ = v___x_7135_;
goto v_reusejp_7325_;
}
else
{
lean_object* v_reuseFailAlloc_7330_; 
v_reuseFailAlloc_7330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7330_, 0, v___x_7324_);
lean_ctor_set(v_reuseFailAlloc_7330_, 1, v_k_7130_);
lean_ctor_set(v_reuseFailAlloc_7330_, 2, v_v_7131_);
lean_ctor_set(v_reuseFailAlloc_7330_, 3, v_l_7132_);
lean_ctor_set(v_reuseFailAlloc_7330_, 4, v_l_7300_);
v___x_7326_ = v_reuseFailAlloc_7330_;
goto v_reusejp_7325_;
}
v_reusejp_7325_:
{
lean_object* v___x_7327_; 
v___x_7327_ = lean_nat_add(v___x_7279_, v_size_7302_);
if (lean_obj_tag(v_r_7301_) == 0)
{
lean_object* v_size_7328_; 
v_size_7328_ = lean_ctor_get(v_r_7301_, 0);
lean_inc(v_size_7328_);
v___y_7312_ = v___x_7327_;
v___y_7313_ = v___x_7326_;
v___y_7314_ = v_size_7328_;
goto v___jp_7311_;
}
else
{
lean_object* v___x_7329_; 
v___x_7329_ = lean_unsigned_to_nat(0u);
v___y_7312_ = v___x_7327_;
v___y_7313_ = v___x_7326_;
v___y_7314_ = v___x_7329_;
goto v___jp_7311_;
}
}
}
}
}
else
{
lean_object* v___x_7339_; lean_object* v___x_7340_; lean_object* v___x_7341_; lean_object* v___x_7343_; 
lean_del_object(v___x_7135_);
v___x_7339_ = lean_nat_add(v___x_7279_, v_size_7280_);
v___x_7340_ = lean_nat_add(v___x_7339_, v_size_7281_);
lean_dec(v_size_7281_);
v___x_7341_ = lean_nat_add(v___x_7339_, v_size_7297_);
lean_dec(v___x_7339_);
lean_inc_ref(v_l_7132_);
if (v_isShared_7296_ == 0)
{
lean_ctor_set(v___x_7295_, 4, v_l_7284_);
lean_ctor_set(v___x_7295_, 3, v_l_7132_);
lean_ctor_set(v___x_7295_, 2, v_v_7131_);
lean_ctor_set(v___x_7295_, 1, v_k_7130_);
lean_ctor_set(v___x_7295_, 0, v___x_7341_);
v___x_7343_ = v___x_7295_;
goto v_reusejp_7342_;
}
else
{
lean_object* v_reuseFailAlloc_7356_; 
v_reuseFailAlloc_7356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7356_, 0, v___x_7341_);
lean_ctor_set(v_reuseFailAlloc_7356_, 1, v_k_7130_);
lean_ctor_set(v_reuseFailAlloc_7356_, 2, v_v_7131_);
lean_ctor_set(v_reuseFailAlloc_7356_, 3, v_l_7132_);
lean_ctor_set(v_reuseFailAlloc_7356_, 4, v_l_7284_);
v___x_7343_ = v_reuseFailAlloc_7356_;
goto v_reusejp_7342_;
}
v_reusejp_7342_:
{
lean_object* v___x_7345_; uint8_t v_isShared_7346_; uint8_t v_isSharedCheck_7350_; 
v_isSharedCheck_7350_ = !lean_is_exclusive(v_l_7132_);
if (v_isSharedCheck_7350_ == 0)
{
lean_object* v_unused_7351_; lean_object* v_unused_7352_; lean_object* v_unused_7353_; lean_object* v_unused_7354_; lean_object* v_unused_7355_; 
v_unused_7351_ = lean_ctor_get(v_l_7132_, 4);
lean_dec(v_unused_7351_);
v_unused_7352_ = lean_ctor_get(v_l_7132_, 3);
lean_dec(v_unused_7352_);
v_unused_7353_ = lean_ctor_get(v_l_7132_, 2);
lean_dec(v_unused_7353_);
v_unused_7354_ = lean_ctor_get(v_l_7132_, 1);
lean_dec(v_unused_7354_);
v_unused_7355_ = lean_ctor_get(v_l_7132_, 0);
lean_dec(v_unused_7355_);
v___x_7345_ = v_l_7132_;
v_isShared_7346_ = v_isSharedCheck_7350_;
goto v_resetjp_7344_;
}
else
{
lean_dec(v_l_7132_);
v___x_7345_ = lean_box(0);
v_isShared_7346_ = v_isSharedCheck_7350_;
goto v_resetjp_7344_;
}
v_resetjp_7344_:
{
lean_object* v___x_7348_; 
if (v_isShared_7346_ == 0)
{
lean_ctor_set(v___x_7345_, 4, v_r_7285_);
lean_ctor_set(v___x_7345_, 3, v___x_7343_);
lean_ctor_set(v___x_7345_, 2, v_v_7283_);
lean_ctor_set(v___x_7345_, 1, v_k_7282_);
lean_ctor_set(v___x_7345_, 0, v___x_7340_);
v___x_7348_ = v___x_7345_;
goto v_reusejp_7347_;
}
else
{
lean_object* v_reuseFailAlloc_7349_; 
v_reuseFailAlloc_7349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7349_, 0, v___x_7340_);
lean_ctor_set(v_reuseFailAlloc_7349_, 1, v_k_7282_);
lean_ctor_set(v_reuseFailAlloc_7349_, 2, v_v_7283_);
lean_ctor_set(v_reuseFailAlloc_7349_, 3, v___x_7343_);
lean_ctor_set(v_reuseFailAlloc_7349_, 4, v_r_7285_);
v___x_7348_ = v_reuseFailAlloc_7349_;
goto v_reusejp_7347_;
}
v_reusejp_7347_:
{
return v___x_7348_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_7363_; 
v_l_7363_ = lean_ctor_get(v_impl_7278_, 3);
lean_inc(v_l_7363_);
if (lean_obj_tag(v_l_7363_) == 0)
{
lean_object* v_r_7364_; lean_object* v_k_7365_; lean_object* v_v_7366_; lean_object* v___x_7368_; uint8_t v_isShared_7369_; uint8_t v_isSharedCheck_7389_; 
v_r_7364_ = lean_ctor_get(v_impl_7278_, 4);
v_k_7365_ = lean_ctor_get(v_impl_7278_, 1);
v_v_7366_ = lean_ctor_get(v_impl_7278_, 2);
v_isSharedCheck_7389_ = !lean_is_exclusive(v_impl_7278_);
if (v_isSharedCheck_7389_ == 0)
{
lean_object* v_unused_7390_; lean_object* v_unused_7391_; 
v_unused_7390_ = lean_ctor_get(v_impl_7278_, 3);
lean_dec(v_unused_7390_);
v_unused_7391_ = lean_ctor_get(v_impl_7278_, 0);
lean_dec(v_unused_7391_);
v___x_7368_ = v_impl_7278_;
v_isShared_7369_ = v_isSharedCheck_7389_;
goto v_resetjp_7367_;
}
else
{
lean_inc(v_r_7364_);
lean_inc(v_v_7366_);
lean_inc(v_k_7365_);
lean_dec(v_impl_7278_);
v___x_7368_ = lean_box(0);
v_isShared_7369_ = v_isSharedCheck_7389_;
goto v_resetjp_7367_;
}
v_resetjp_7367_:
{
lean_object* v_k_7370_; lean_object* v_v_7371_; lean_object* v___x_7373_; uint8_t v_isShared_7374_; uint8_t v_isSharedCheck_7385_; 
v_k_7370_ = lean_ctor_get(v_l_7363_, 1);
v_v_7371_ = lean_ctor_get(v_l_7363_, 2);
v_isSharedCheck_7385_ = !lean_is_exclusive(v_l_7363_);
if (v_isSharedCheck_7385_ == 0)
{
lean_object* v_unused_7386_; lean_object* v_unused_7387_; lean_object* v_unused_7388_; 
v_unused_7386_ = lean_ctor_get(v_l_7363_, 4);
lean_dec(v_unused_7386_);
v_unused_7387_ = lean_ctor_get(v_l_7363_, 3);
lean_dec(v_unused_7387_);
v_unused_7388_ = lean_ctor_get(v_l_7363_, 0);
lean_dec(v_unused_7388_);
v___x_7373_ = v_l_7363_;
v_isShared_7374_ = v_isSharedCheck_7385_;
goto v_resetjp_7372_;
}
else
{
lean_inc(v_v_7371_);
lean_inc(v_k_7370_);
lean_dec(v_l_7363_);
v___x_7373_ = lean_box(0);
v_isShared_7374_ = v_isSharedCheck_7385_;
goto v_resetjp_7372_;
}
v_resetjp_7372_:
{
lean_object* v___x_7375_; lean_object* v___x_7377_; 
v___x_7375_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_7364_, 2);
if (v_isShared_7374_ == 0)
{
lean_ctor_set(v___x_7373_, 4, v_r_7364_);
lean_ctor_set(v___x_7373_, 3, v_r_7364_);
lean_ctor_set(v___x_7373_, 2, v_v_7131_);
lean_ctor_set(v___x_7373_, 1, v_k_7130_);
lean_ctor_set(v___x_7373_, 0, v___x_7279_);
v___x_7377_ = v___x_7373_;
goto v_reusejp_7376_;
}
else
{
lean_object* v_reuseFailAlloc_7384_; 
v_reuseFailAlloc_7384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7384_, 0, v___x_7279_);
lean_ctor_set(v_reuseFailAlloc_7384_, 1, v_k_7130_);
lean_ctor_set(v_reuseFailAlloc_7384_, 2, v_v_7131_);
lean_ctor_set(v_reuseFailAlloc_7384_, 3, v_r_7364_);
lean_ctor_set(v_reuseFailAlloc_7384_, 4, v_r_7364_);
v___x_7377_ = v_reuseFailAlloc_7384_;
goto v_reusejp_7376_;
}
v_reusejp_7376_:
{
lean_object* v___x_7379_; 
lean_inc(v_r_7364_);
if (v_isShared_7369_ == 0)
{
lean_ctor_set(v___x_7368_, 3, v_r_7364_);
lean_ctor_set(v___x_7368_, 0, v___x_7279_);
v___x_7379_ = v___x_7368_;
goto v_reusejp_7378_;
}
else
{
lean_object* v_reuseFailAlloc_7383_; 
v_reuseFailAlloc_7383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7383_, 0, v___x_7279_);
lean_ctor_set(v_reuseFailAlloc_7383_, 1, v_k_7365_);
lean_ctor_set(v_reuseFailAlloc_7383_, 2, v_v_7366_);
lean_ctor_set(v_reuseFailAlloc_7383_, 3, v_r_7364_);
lean_ctor_set(v_reuseFailAlloc_7383_, 4, v_r_7364_);
v___x_7379_ = v_reuseFailAlloc_7383_;
goto v_reusejp_7378_;
}
v_reusejp_7378_:
{
lean_object* v___x_7381_; 
if (v_isShared_7136_ == 0)
{
lean_ctor_set(v___x_7135_, 4, v___x_7379_);
lean_ctor_set(v___x_7135_, 3, v___x_7377_);
lean_ctor_set(v___x_7135_, 2, v_v_7371_);
lean_ctor_set(v___x_7135_, 1, v_k_7370_);
lean_ctor_set(v___x_7135_, 0, v___x_7375_);
v___x_7381_ = v___x_7135_;
goto v_reusejp_7380_;
}
else
{
lean_object* v_reuseFailAlloc_7382_; 
v_reuseFailAlloc_7382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7382_, 0, v___x_7375_);
lean_ctor_set(v_reuseFailAlloc_7382_, 1, v_k_7370_);
lean_ctor_set(v_reuseFailAlloc_7382_, 2, v_v_7371_);
lean_ctor_set(v_reuseFailAlloc_7382_, 3, v___x_7377_);
lean_ctor_set(v_reuseFailAlloc_7382_, 4, v___x_7379_);
v___x_7381_ = v_reuseFailAlloc_7382_;
goto v_reusejp_7380_;
}
v_reusejp_7380_:
{
return v___x_7381_;
}
}
}
}
}
}
else
{
lean_object* v_r_7392_; 
v_r_7392_ = lean_ctor_get(v_impl_7278_, 4);
lean_inc(v_r_7392_);
if (lean_obj_tag(v_r_7392_) == 0)
{
lean_object* v_k_7393_; lean_object* v_v_7394_; lean_object* v___x_7396_; uint8_t v_isShared_7397_; uint8_t v_isSharedCheck_7405_; 
v_k_7393_ = lean_ctor_get(v_impl_7278_, 1);
v_v_7394_ = lean_ctor_get(v_impl_7278_, 2);
v_isSharedCheck_7405_ = !lean_is_exclusive(v_impl_7278_);
if (v_isSharedCheck_7405_ == 0)
{
lean_object* v_unused_7406_; lean_object* v_unused_7407_; lean_object* v_unused_7408_; 
v_unused_7406_ = lean_ctor_get(v_impl_7278_, 4);
lean_dec(v_unused_7406_);
v_unused_7407_ = lean_ctor_get(v_impl_7278_, 3);
lean_dec(v_unused_7407_);
v_unused_7408_ = lean_ctor_get(v_impl_7278_, 0);
lean_dec(v_unused_7408_);
v___x_7396_ = v_impl_7278_;
v_isShared_7397_ = v_isSharedCheck_7405_;
goto v_resetjp_7395_;
}
else
{
lean_inc(v_v_7394_);
lean_inc(v_k_7393_);
lean_dec(v_impl_7278_);
v___x_7396_ = lean_box(0);
v_isShared_7397_ = v_isSharedCheck_7405_;
goto v_resetjp_7395_;
}
v_resetjp_7395_:
{
lean_object* v___x_7398_; lean_object* v___x_7400_; 
v___x_7398_ = lean_unsigned_to_nat(3u);
if (v_isShared_7397_ == 0)
{
lean_ctor_set(v___x_7396_, 4, v_l_7363_);
lean_ctor_set(v___x_7396_, 2, v_v_7131_);
lean_ctor_set(v___x_7396_, 1, v_k_7130_);
lean_ctor_set(v___x_7396_, 0, v___x_7279_);
v___x_7400_ = v___x_7396_;
goto v_reusejp_7399_;
}
else
{
lean_object* v_reuseFailAlloc_7404_; 
v_reuseFailAlloc_7404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7404_, 0, v___x_7279_);
lean_ctor_set(v_reuseFailAlloc_7404_, 1, v_k_7130_);
lean_ctor_set(v_reuseFailAlloc_7404_, 2, v_v_7131_);
lean_ctor_set(v_reuseFailAlloc_7404_, 3, v_l_7363_);
lean_ctor_set(v_reuseFailAlloc_7404_, 4, v_l_7363_);
v___x_7400_ = v_reuseFailAlloc_7404_;
goto v_reusejp_7399_;
}
v_reusejp_7399_:
{
lean_object* v___x_7402_; 
if (v_isShared_7136_ == 0)
{
lean_ctor_set(v___x_7135_, 4, v_r_7392_);
lean_ctor_set(v___x_7135_, 3, v___x_7400_);
lean_ctor_set(v___x_7135_, 2, v_v_7394_);
lean_ctor_set(v___x_7135_, 1, v_k_7393_);
lean_ctor_set(v___x_7135_, 0, v___x_7398_);
v___x_7402_ = v___x_7135_;
goto v_reusejp_7401_;
}
else
{
lean_object* v_reuseFailAlloc_7403_; 
v_reuseFailAlloc_7403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7403_, 0, v___x_7398_);
lean_ctor_set(v_reuseFailAlloc_7403_, 1, v_k_7393_);
lean_ctor_set(v_reuseFailAlloc_7403_, 2, v_v_7394_);
lean_ctor_set(v_reuseFailAlloc_7403_, 3, v___x_7400_);
lean_ctor_set(v_reuseFailAlloc_7403_, 4, v_r_7392_);
v___x_7402_ = v_reuseFailAlloc_7403_;
goto v_reusejp_7401_;
}
v_reusejp_7401_:
{
return v___x_7402_;
}
}
}
}
else
{
lean_object* v___x_7409_; lean_object* v___x_7411_; 
v___x_7409_ = lean_unsigned_to_nat(2u);
if (v_isShared_7136_ == 0)
{
lean_ctor_set(v___x_7135_, 4, v_impl_7278_);
lean_ctor_set(v___x_7135_, 3, v_r_7392_);
lean_ctor_set(v___x_7135_, 0, v___x_7409_);
v___x_7411_ = v___x_7135_;
goto v_reusejp_7410_;
}
else
{
lean_object* v_reuseFailAlloc_7412_; 
v_reuseFailAlloc_7412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7412_, 0, v___x_7409_);
lean_ctor_set(v_reuseFailAlloc_7412_, 1, v_k_7130_);
lean_ctor_set(v_reuseFailAlloc_7412_, 2, v_v_7131_);
lean_ctor_set(v_reuseFailAlloc_7412_, 3, v_r_7392_);
lean_ctor_set(v_reuseFailAlloc_7412_, 4, v_impl_7278_);
v___x_7411_ = v_reuseFailAlloc_7412_;
goto v_reusejp_7410_;
}
v_reusejp_7410_:
{
return v___x_7411_;
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
lean_object* v___x_7414_; lean_object* v___x_7415_; 
v___x_7414_ = lean_unsigned_to_nat(1u);
v___x_7415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_7415_, 0, v___x_7414_);
lean_ctor_set(v___x_7415_, 1, v_k_7126_);
lean_ctor_set(v___x_7415_, 2, v_v_7127_);
lean_ctor_set(v___x_7415_, 3, v_t_7128_);
lean_ctor_set(v___x_7415_, 4, v_t_7128_);
return v___x_7415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(lean_object* v_lib_7416_, lean_object* v_ps_7417_, lean_object* v_v_7418_, lean_object* v_o_7419_){
_start:
{
lean_object* v_name_7420_; lean_object* v_deps_7421_; lean_object* v_o_7422_; uint8_t v___x_7423_; 
v_name_7420_ = lean_ctor_get(v_lib_7416_, 1);
lean_inc_ref(v_name_7420_);
v_deps_7421_ = lean_ctor_get(v_lib_7416_, 2);
lean_inc_ref(v_deps_7421_);
v_o_7422_ = lean_array_push(v_o_7419_, v_lib_7416_);
v___x_7423_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_name_7420_, v_v_7418_);
if (v___x_7423_ == 0)
{
uint8_t v___x_7424_; 
v___x_7424_ = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(v_name_7420_, v_ps_7417_);
if (v___x_7424_ == 0)
{
lean_object* v_ps_7425_; lean_object* v___y_7427_; 
lean_inc_ref(v_name_7420_);
v_ps_7425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_ps_7425_, 0, v_name_7420_);
lean_ctor_set(v_ps_7425_, 1, v_ps_7417_);
if (v___x_7423_ == 0)
{
lean_object* v___x_7441_; lean_object* v___x_7442_; 
v___x_7441_ = lean_box(0);
v___x_7442_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_name_7420_, v___x_7441_, v_v_7418_);
v___y_7427_ = v___x_7442_;
goto v___jp_7426_;
}
else
{
lean_dec_ref(v_name_7420_);
v___y_7427_ = v_v_7418_;
goto v___jp_7426_;
}
v___jp_7426_:
{
lean_object* v___x_7428_; lean_object* v___x_7429_; lean_object* v___x_7430_; uint8_t v___x_7431_; 
v___x_7428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7428_, 0, v___y_7427_);
lean_ctor_set(v___x_7428_, 1, v_o_7422_);
v___x_7429_ = lean_unsigned_to_nat(0u);
v___x_7430_ = lean_array_get_size(v_deps_7421_);
v___x_7431_ = lean_nat_dec_lt(v___x_7429_, v___x_7430_);
if (v___x_7431_ == 0)
{
lean_object* v___x_7432_; 
lean_dec_ref_known(v_ps_7425_, 2);
lean_dec_ref(v_deps_7421_);
v___x_7432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7432_, 0, v___x_7428_);
return v___x_7432_;
}
else
{
uint8_t v___x_7433_; 
v___x_7433_ = lean_nat_dec_le(v___x_7430_, v___x_7430_);
if (v___x_7433_ == 0)
{
if (v___x_7431_ == 0)
{
lean_object* v___x_7434_; 
lean_dec_ref_known(v_ps_7425_, 2);
lean_dec_ref(v_deps_7421_);
v___x_7434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7434_, 0, v___x_7428_);
return v___x_7434_;
}
else
{
size_t v___x_7435_; size_t v___x_7436_; lean_object* v___x_7437_; 
v___x_7435_ = ((size_t)0ULL);
v___x_7436_ = lean_usize_of_nat(v___x_7430_);
v___x_7437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7425_, v_deps_7421_, v___x_7435_, v___x_7436_, v___x_7428_);
lean_dec_ref(v_deps_7421_);
return v___x_7437_;
}
}
else
{
size_t v___x_7438_; size_t v___x_7439_; lean_object* v___x_7440_; 
v___x_7438_ = ((size_t)0ULL);
v___x_7439_ = lean_usize_of_nat(v___x_7430_);
v___x_7440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7425_, v_deps_7421_, v___x_7438_, v___x_7439_, v___x_7428_);
lean_dec_ref(v_deps_7421_);
return v___x_7440_;
}
}
}
}
else
{
lean_object* v___x_7443_; lean_object* v___x_7444_; 
lean_dec_ref(v_o_7422_);
lean_dec_ref(v_deps_7421_);
lean_dec(v_v_7418_);
v___x_7443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7443_, 0, v_name_7420_);
lean_ctor_set(v___x_7443_, 1, v_ps_7417_);
v___x_7444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7444_, 0, v___x_7443_);
return v___x_7444_;
}
}
else
{
lean_object* v___x_7445_; lean_object* v___x_7446_; 
lean_dec_ref(v_deps_7421_);
lean_dec_ref(v_name_7420_);
lean_dec(v_ps_7417_);
v___x_7445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7445_, 0, v_v_7418_);
lean_ctor_set(v___x_7445_, 1, v_o_7422_);
v___x_7446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7446_, 0, v___x_7445_);
return v___x_7446_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(lean_object* v_ps_7447_, lean_object* v_as_7448_, size_t v_i_7449_, size_t v_stop_7450_, lean_object* v_b_7451_){
_start:
{
uint8_t v___x_7452_; 
v___x_7452_ = lean_usize_dec_eq(v_i_7449_, v_stop_7450_);
if (v___x_7452_ == 0)
{
lean_object* v_fst_7453_; lean_object* v_snd_7454_; lean_object* v___x_7455_; lean_object* v___x_7456_; 
v_fst_7453_ = lean_ctor_get(v_b_7451_, 0);
lean_inc(v_fst_7453_);
v_snd_7454_ = lean_ctor_get(v_b_7451_, 1);
lean_inc(v_snd_7454_);
lean_dec_ref(v_b_7451_);
v___x_7455_ = lean_array_uget_borrowed(v_as_7448_, v_i_7449_);
lean_inc(v_ps_7447_);
lean_inc(v___x_7455_);
v___x_7456_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(v___x_7455_, v_ps_7447_, v_fst_7453_, v_snd_7454_);
if (lean_obj_tag(v___x_7456_) == 0)
{
lean_dec(v_ps_7447_);
return v___x_7456_;
}
else
{
lean_object* v_a_7457_; size_t v___x_7458_; size_t v___x_7459_; 
v_a_7457_ = lean_ctor_get(v___x_7456_, 0);
lean_inc(v_a_7457_);
lean_dec_ref_known(v___x_7456_, 1);
v___x_7458_ = ((size_t)1ULL);
v___x_7459_ = lean_usize_add(v_i_7449_, v___x_7458_);
v_i_7449_ = v___x_7459_;
v_b_7451_ = v_a_7457_;
goto _start;
}
}
else
{
lean_object* v___x_7461_; 
lean_dec(v_ps_7447_);
v___x_7461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7461_, 0, v_b_7451_);
return v___x_7461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2___boxed(lean_object* v_ps_7462_, lean_object* v_as_7463_, lean_object* v_i_7464_, lean_object* v_stop_7465_, lean_object* v_b_7466_){
_start:
{
size_t v_i_boxed_7467_; size_t v_stop_boxed_7468_; lean_object* v_res_7469_; 
v_i_boxed_7467_ = lean_unbox_usize(v_i_7464_);
lean_dec(v_i_7464_);
v_stop_boxed_7468_ = lean_unbox_usize(v_stop_7465_);
lean_dec(v_stop_7465_);
v_res_7469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7462_, v_as_7463_, v_i_boxed_7467_, v_stop_boxed_7468_, v_b_7466_);
lean_dec_ref(v_as_7463_);
return v_res_7469_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(lean_object* v_00_u03b2_7470_, lean_object* v_k_7471_, lean_object* v_t_7472_){
_start:
{
uint8_t v___x_7473_; 
v___x_7473_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_k_7471_, v_t_7472_);
return v___x_7473_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___boxed(lean_object* v_00_u03b2_7474_, lean_object* v_k_7475_, lean_object* v_t_7476_){
_start:
{
uint8_t v_res_7477_; lean_object* v_r_7478_; 
v_res_7477_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(v_00_u03b2_7474_, v_k_7475_, v_t_7476_);
lean_dec(v_t_7476_);
lean_dec_ref(v_k_7475_);
v_r_7478_ = lean_box(v_res_7477_);
return v_r_7478_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3(lean_object* v_00_u03b2_7479_, lean_object* v_k_7480_, lean_object* v_v_7481_, lean_object* v_t_7482_, lean_object* v_hl_7483_){
_start:
{
lean_object* v___x_7484_; 
v___x_7484_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7480_, v_v_7481_, v_t_7482_);
return v___x_7484_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0_spec__0(lean_object* v_a_7486_, lean_object* v_a_7487_){
_start:
{
if (lean_obj_tag(v_a_7486_) == 0)
{
lean_object* v___x_7488_; 
v___x_7488_ = l_List_reverse___redArg(v_a_7487_);
return v___x_7488_;
}
else
{
lean_object* v_head_7489_; lean_object* v_tail_7490_; lean_object* v___x_7492_; uint8_t v_isShared_7493_; uint8_t v_isSharedCheck_7500_; 
v_head_7489_ = lean_ctor_get(v_a_7486_, 0);
v_tail_7490_ = lean_ctor_get(v_a_7486_, 1);
v_isSharedCheck_7500_ = !lean_is_exclusive(v_a_7486_);
if (v_isSharedCheck_7500_ == 0)
{
v___x_7492_ = v_a_7486_;
v_isShared_7493_ = v_isSharedCheck_7500_;
goto v_resetjp_7491_;
}
else
{
lean_inc(v_tail_7490_);
lean_inc(v_head_7489_);
lean_dec(v_a_7486_);
v___x_7492_ = lean_box(0);
v_isShared_7493_ = v_isSharedCheck_7500_;
goto v_resetjp_7491_;
}
v_resetjp_7491_:
{
lean_object* v___x_7494_; lean_object* v___x_7495_; lean_object* v___x_7497_; 
v___x_7494_ = ((lean_object*)(l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0_spec__0___closed__0));
v___x_7495_ = lean_string_append(v___x_7494_, v_head_7489_);
lean_dec(v_head_7489_);
if (v_isShared_7493_ == 0)
{
lean_ctor_set(v___x_7492_, 1, v_a_7487_);
lean_ctor_set(v___x_7492_, 0, v___x_7495_);
v___x_7497_ = v___x_7492_;
goto v_reusejp_7496_;
}
else
{
lean_object* v_reuseFailAlloc_7499_; 
v_reuseFailAlloc_7499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7499_, 0, v___x_7495_);
lean_ctor_set(v_reuseFailAlloc_7499_, 1, v_a_7487_);
v___x_7497_ = v_reuseFailAlloc_7499_;
goto v_reusejp_7496_;
}
v_reusejp_7496_:
{
v_a_7486_ = v_tail_7490_;
v_a_7487_ = v___x_7497_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0(lean_object* v_cycle_7501_){
_start:
{
lean_object* v___x_7502_; lean_object* v___x_7503_; lean_object* v___x_7504_; lean_object* v___x_7505_; 
v___x_7502_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__1));
v___x_7503_ = lean_box(0);
v___x_7504_ = l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0_spec__0(v_cycle_7501_, v___x_7503_);
v___x_7505_ = l_String_intercalate(v___x_7502_, v___x_7504_);
return v___x_7505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1(lean_object* v_as_7506_, size_t v_i_7507_, size_t v_stop_7508_, lean_object* v_b_7509_){
_start:
{
uint8_t v___x_7510_; 
v___x_7510_ = lean_usize_dec_eq(v_i_7507_, v_stop_7508_);
if (v___x_7510_ == 0)
{
lean_object* v_fst_7511_; lean_object* v_snd_7512_; lean_object* v___x_7513_; lean_object* v___x_7514_; lean_object* v___x_7515_; 
v_fst_7511_ = lean_ctor_get(v_b_7509_, 0);
lean_inc(v_fst_7511_);
v_snd_7512_ = lean_ctor_get(v_b_7509_, 1);
lean_inc(v_snd_7512_);
lean_dec_ref(v_b_7509_);
v___x_7513_ = lean_array_uget_borrowed(v_as_7506_, v_i_7507_);
v___x_7514_ = lean_box(0);
lean_inc(v___x_7513_);
v___x_7515_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(v___x_7513_, v___x_7514_, v_fst_7511_, v_snd_7512_);
if (lean_obj_tag(v___x_7515_) == 0)
{
return v___x_7515_;
}
else
{
lean_object* v_a_7516_; size_t v___x_7517_; size_t v___x_7518_; 
v_a_7516_ = lean_ctor_get(v___x_7515_, 0);
lean_inc(v_a_7516_);
lean_dec_ref_known(v___x_7515_, 1);
v___x_7517_ = ((size_t)1ULL);
v___x_7518_ = lean_usize_add(v_i_7507_, v___x_7517_);
v_i_7507_ = v___x_7518_;
v_b_7509_ = v_a_7516_;
goto _start;
}
}
else
{
lean_object* v___x_7520_; 
v___x_7520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7520_, 0, v_b_7509_);
return v___x_7520_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1___boxed(lean_object* v_as_7521_, lean_object* v_i_7522_, lean_object* v_stop_7523_, lean_object* v_b_7524_){
_start:
{
size_t v_i_boxed_7525_; size_t v_stop_boxed_7526_; lean_object* v_res_7527_; 
v_i_boxed_7525_ = lean_unbox_usize(v_i_7522_);
lean_dec(v_i_7522_);
v_stop_boxed_7526_ = lean_unbox_usize(v_stop_7523_);
lean_dec(v_stop_7523_);
v_res_7527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1(v_as_7521_, v_i_boxed_7525_, v_stop_boxed_7526_, v_b_7524_);
lean_dec_ref(v_as_7521_);
return v_res_7527_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder___redArg(lean_object* v_libs_7534_, lean_object* v_a_7535_){
_start:
{
lean_object* v_snd_7538_; lean_object* v___y_7541_; lean_object* v___x_7565_; lean_object* v___x_7566_; lean_object* v___x_7567_; uint8_t v___x_7568_; 
v___x_7565_ = lean_unsigned_to_nat(0u);
v___x_7566_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v___x_7567_ = lean_array_get_size(v_libs_7534_);
v___x_7568_ = lean_nat_dec_lt(v___x_7565_, v___x_7567_);
if (v___x_7568_ == 0)
{
v_snd_7538_ = v___x_7566_;
goto v___jp_7537_;
}
else
{
lean_object* v___x_7569_; uint8_t v___x_7570_; 
v___x_7569_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__2));
v___x_7570_ = lean_nat_dec_le(v___x_7567_, v___x_7567_);
if (v___x_7570_ == 0)
{
if (v___x_7568_ == 0)
{
v_snd_7538_ = v___x_7566_;
goto v___jp_7537_;
}
else
{
size_t v___x_7571_; size_t v___x_7572_; lean_object* v___x_7573_; 
v___x_7571_ = ((size_t)0ULL);
v___x_7572_ = lean_usize_of_nat(v___x_7567_);
v___x_7573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1(v_libs_7534_, v___x_7571_, v___x_7572_, v___x_7569_);
v___y_7541_ = v___x_7573_;
goto v___jp_7540_;
}
}
else
{
size_t v___x_7574_; size_t v___x_7575_; lean_object* v___x_7576_; 
v___x_7574_ = ((size_t)0ULL);
v___x_7575_ = lean_usize_of_nat(v___x_7567_);
v___x_7576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1(v_libs_7534_, v___x_7574_, v___x_7575_, v___x_7569_);
v___y_7541_ = v___x_7576_;
goto v___jp_7540_;
}
}
v___jp_7537_:
{
lean_object* v___x_7539_; 
v___x_7539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7539_, 0, v_snd_7538_);
lean_ctor_set(v___x_7539_, 1, v_a_7535_);
return v___x_7539_;
}
v___jp_7540_:
{
if (lean_obj_tag(v___y_7541_) == 0)
{
lean_object* v_a_7542_; lean_object* v_log_7543_; uint8_t v_action_7544_; uint8_t v_wantsRebuild_7545_; lean_object* v_trace_7546_; lean_object* v_buildTime_7547_; lean_object* v___x_7549_; uint8_t v_isShared_7550_; uint8_t v_isSharedCheck_7562_; 
v_a_7542_ = lean_ctor_get(v___y_7541_, 0);
lean_inc(v_a_7542_);
lean_dec_ref_known(v___y_7541_, 1);
v_log_7543_ = lean_ctor_get(v_a_7535_, 0);
v_action_7544_ = lean_ctor_get_uint8(v_a_7535_, sizeof(void*)*3);
v_wantsRebuild_7545_ = lean_ctor_get_uint8(v_a_7535_, sizeof(void*)*3 + 1);
v_trace_7546_ = lean_ctor_get(v_a_7535_, 1);
v_buildTime_7547_ = lean_ctor_get(v_a_7535_, 2);
v_isSharedCheck_7562_ = !lean_is_exclusive(v_a_7535_);
if (v_isSharedCheck_7562_ == 0)
{
v___x_7549_ = v_a_7535_;
v_isShared_7550_ = v_isSharedCheck_7562_;
goto v_resetjp_7548_;
}
else
{
lean_inc(v_buildTime_7547_);
lean_inc(v_trace_7546_);
lean_inc(v_log_7543_);
lean_dec(v_a_7535_);
v___x_7549_ = lean_box(0);
v_isShared_7550_ = v_isSharedCheck_7562_;
goto v_resetjp_7548_;
}
v_resetjp_7548_:
{
lean_object* v___x_7551_; lean_object* v___x_7552_; lean_object* v___x_7553_; uint8_t v___x_7554_; lean_object* v___x_7555_; lean_object* v___x_7556_; lean_object* v___x_7557_; lean_object* v___x_7559_; 
v___x_7551_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__0));
v___x_7552_ = l_Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0(v_a_7542_);
v___x_7553_ = lean_string_append(v___x_7551_, v___x_7552_);
lean_dec_ref(v___x_7552_);
v___x_7554_ = 3;
v___x_7555_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7555_, 0, v___x_7553_);
lean_ctor_set_uint8(v___x_7555_, sizeof(void*)*1, v___x_7554_);
v___x_7556_ = lean_array_get_size(v_log_7543_);
v___x_7557_ = lean_array_push(v_log_7543_, v___x_7555_);
if (v_isShared_7550_ == 0)
{
lean_ctor_set(v___x_7549_, 0, v___x_7557_);
v___x_7559_ = v___x_7549_;
goto v_reusejp_7558_;
}
else
{
lean_object* v_reuseFailAlloc_7561_; 
v_reuseFailAlloc_7561_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7561_, 0, v___x_7557_);
lean_ctor_set(v_reuseFailAlloc_7561_, 1, v_trace_7546_);
lean_ctor_set(v_reuseFailAlloc_7561_, 2, v_buildTime_7547_);
lean_ctor_set_uint8(v_reuseFailAlloc_7561_, sizeof(void*)*3, v_action_7544_);
lean_ctor_set_uint8(v_reuseFailAlloc_7561_, sizeof(void*)*3 + 1, v_wantsRebuild_7545_);
v___x_7559_ = v_reuseFailAlloc_7561_;
goto v_reusejp_7558_;
}
v_reusejp_7558_:
{
lean_object* v___x_7560_; 
v___x_7560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7560_, 0, v___x_7556_);
lean_ctor_set(v___x_7560_, 1, v___x_7559_);
return v___x_7560_;
}
}
}
else
{
lean_object* v_a_7563_; lean_object* v_snd_7564_; 
v_a_7563_ = lean_ctor_get(v___y_7541_, 0);
lean_inc(v_a_7563_);
lean_dec_ref_known(v___y_7541_, 1);
v_snd_7564_ = lean_ctor_get(v_a_7563_, 1);
lean_inc(v_snd_7564_);
lean_dec(v_a_7563_);
v_snd_7538_ = v_snd_7564_;
goto v___jp_7537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder___redArg___boxed(lean_object* v_libs_7577_, lean_object* v_a_7578_, lean_object* v_a_7579_){
_start:
{
lean_object* v_res_7580_; 
v_res_7580_ = l_Lake_mkLinkOrder___redArg(v_libs_7577_, v_a_7578_);
lean_dec_ref(v_libs_7577_);
return v_res_7580_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder(lean_object* v_libs_7581_, lean_object* v_a_7582_, lean_object* v_a_7583_, lean_object* v_a_7584_, lean_object* v_a_7585_, lean_object* v_a_7586_, lean_object* v_a_7587_){
_start:
{
lean_object* v___x_7589_; 
v___x_7589_ = l_Lake_mkLinkOrder___redArg(v_libs_7581_, v_a_7587_);
return v___x_7589_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder___boxed(lean_object* v_libs_7590_, lean_object* v_a_7591_, lean_object* v_a_7592_, lean_object* v_a_7593_, lean_object* v_a_7594_, lean_object* v_a_7595_, lean_object* v_a_7596_, lean_object* v_a_7597_){
_start:
{
lean_object* v_res_7598_; 
v_res_7598_ = l_Lake_mkLinkOrder(v_libs_7590_, v_a_7591_, v_a_7592_, v_a_7593_, v_a_7594_, v_a_7595_, v_a_7596_);
lean_dec_ref(v_a_7595_);
lean_dec(v_a_7594_);
lean_dec(v_a_7593_);
lean_dec(v_a_7592_);
lean_dec_ref(v_a_7591_);
lean_dec_ref(v_libs_7590_);
return v_res_7598_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs___redArg(lean_object* v_objs_7599_, lean_object* v_libs_7600_, uint8_t v_linkDeps_7601_, lean_object* v_a_7602_){
_start:
{
lean_object* v_libs_7605_; lean_object* v___y_7606_; 
if (v_linkDeps_7601_ == 0)
{
lean_object* v___x_7609_; 
v___x_7609_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7605_ = v___x_7609_;
v___y_7606_ = v_a_7602_;
goto v___jp_7604_;
}
else
{
lean_object* v___x_7610_; 
v___x_7610_ = l_Lake_mkLinkOrder___redArg(v_libs_7600_, v_a_7602_);
if (lean_obj_tag(v___x_7610_) == 0)
{
lean_object* v_a_7611_; lean_object* v_a_7612_; 
v_a_7611_ = lean_ctor_get(v___x_7610_, 0);
lean_inc(v_a_7611_);
v_a_7612_ = lean_ctor_get(v___x_7610_, 1);
lean_inc(v_a_7612_);
lean_dec_ref_known(v___x_7610_, 2);
v_libs_7605_ = v_a_7611_;
v___y_7606_ = v_a_7612_;
goto v___jp_7604_;
}
else
{
lean_object* v_a_7613_; lean_object* v_a_7614_; lean_object* v___x_7616_; uint8_t v_isShared_7617_; uint8_t v_isSharedCheck_7621_; 
v_a_7613_ = lean_ctor_get(v___x_7610_, 0);
v_a_7614_ = lean_ctor_get(v___x_7610_, 1);
v_isSharedCheck_7621_ = !lean_is_exclusive(v___x_7610_);
if (v_isSharedCheck_7621_ == 0)
{
v___x_7616_ = v___x_7610_;
v_isShared_7617_ = v_isSharedCheck_7621_;
goto v_resetjp_7615_;
}
else
{
lean_inc(v_a_7614_);
lean_inc(v_a_7613_);
lean_dec(v___x_7610_);
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
v___jp_7604_:
{
lean_object* v___x_7607_; lean_object* v___x_7608_; 
v___x_7607_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7599_, v_libs_7605_);
lean_dec_ref(v_libs_7605_);
v___x_7608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7608_, 0, v___x_7607_);
lean_ctor_set(v___x_7608_, 1, v___y_7606_);
return v___x_7608_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs___redArg___boxed(lean_object* v_objs_7622_, lean_object* v_libs_7623_, lean_object* v_linkDeps_7624_, lean_object* v_a_7625_, lean_object* v_a_7626_){
_start:
{
uint8_t v_linkDeps_boxed_7627_; lean_object* v_res_7628_; 
v_linkDeps_boxed_7627_ = lean_unbox(v_linkDeps_7624_);
v_res_7628_ = l_Lake_mkLinkArgs___redArg(v_objs_7622_, v_libs_7623_, v_linkDeps_boxed_7627_, v_a_7625_);
lean_dec_ref(v_libs_7623_);
lean_dec_ref(v_objs_7622_);
return v_res_7628_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs(lean_object* v_objs_7629_, lean_object* v_libs_7630_, uint8_t v_linkDeps_7631_, lean_object* v_a_7632_, lean_object* v_a_7633_, lean_object* v_a_7634_, lean_object* v_a_7635_, lean_object* v_a_7636_, lean_object* v_a_7637_){
_start:
{
lean_object* v_libs_7640_; lean_object* v___y_7641_; 
if (v_linkDeps_7631_ == 0)
{
lean_object* v___x_7644_; 
v___x_7644_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7640_ = v___x_7644_;
v___y_7641_ = v_a_7637_;
goto v___jp_7639_;
}
else
{
lean_object* v___x_7645_; 
v___x_7645_ = l_Lake_mkLinkOrder___redArg(v_libs_7630_, v_a_7637_);
if (lean_obj_tag(v___x_7645_) == 0)
{
lean_object* v_a_7646_; lean_object* v_a_7647_; 
v_a_7646_ = lean_ctor_get(v___x_7645_, 0);
lean_inc(v_a_7646_);
v_a_7647_ = lean_ctor_get(v___x_7645_, 1);
lean_inc(v_a_7647_);
lean_dec_ref_known(v___x_7645_, 2);
v_libs_7640_ = v_a_7646_;
v___y_7641_ = v_a_7647_;
goto v___jp_7639_;
}
else
{
lean_object* v_a_7648_; lean_object* v_a_7649_; lean_object* v___x_7651_; uint8_t v_isShared_7652_; uint8_t v_isSharedCheck_7656_; 
v_a_7648_ = lean_ctor_get(v___x_7645_, 0);
v_a_7649_ = lean_ctor_get(v___x_7645_, 1);
v_isSharedCheck_7656_ = !lean_is_exclusive(v___x_7645_);
if (v_isSharedCheck_7656_ == 0)
{
v___x_7651_ = v___x_7645_;
v_isShared_7652_ = v_isSharedCheck_7656_;
goto v_resetjp_7650_;
}
else
{
lean_inc(v_a_7649_);
lean_inc(v_a_7648_);
lean_dec(v___x_7645_);
v___x_7651_ = lean_box(0);
v_isShared_7652_ = v_isSharedCheck_7656_;
goto v_resetjp_7650_;
}
v_resetjp_7650_:
{
lean_object* v___x_7654_; 
if (v_isShared_7652_ == 0)
{
v___x_7654_ = v___x_7651_;
goto v_reusejp_7653_;
}
else
{
lean_object* v_reuseFailAlloc_7655_; 
v_reuseFailAlloc_7655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7655_, 0, v_a_7648_);
lean_ctor_set(v_reuseFailAlloc_7655_, 1, v_a_7649_);
v___x_7654_ = v_reuseFailAlloc_7655_;
goto v_reusejp_7653_;
}
v_reusejp_7653_:
{
return v___x_7654_;
}
}
}
}
v___jp_7639_:
{
lean_object* v___x_7642_; lean_object* v___x_7643_; 
v___x_7642_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7629_, v_libs_7640_);
lean_dec_ref(v_libs_7640_);
v___x_7643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7643_, 0, v___x_7642_);
lean_ctor_set(v___x_7643_, 1, v___y_7641_);
return v___x_7643_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs___boxed(lean_object* v_objs_7657_, lean_object* v_libs_7658_, lean_object* v_linkDeps_7659_, lean_object* v_a_7660_, lean_object* v_a_7661_, lean_object* v_a_7662_, lean_object* v_a_7663_, lean_object* v_a_7664_, lean_object* v_a_7665_, lean_object* v_a_7666_){
_start:
{
uint8_t v_linkDeps_boxed_7667_; lean_object* v_res_7668_; 
v_linkDeps_boxed_7667_ = lean_unbox(v_linkDeps_7659_);
v_res_7668_ = l_Lake_mkLinkArgs(v_objs_7657_, v_libs_7658_, v_linkDeps_boxed_7667_, v_a_7660_, v_a_7661_, v_a_7662_, v_a_7663_, v_a_7664_, v_a_7665_);
lean_dec_ref(v_a_7664_);
lean_dec(v_a_7663_);
lean_dec(v_a_7662_);
lean_dec(v_a_7661_);
lean_dec_ref(v_a_7660_);
lean_dec_ref(v_libs_7658_);
lean_dec_ref(v_objs_7657_);
return v_res_7668_;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0(void){
_start:
{
lean_object* v___x_7669_; lean_object* v___x_7670_; lean_object* v___x_7671_; lean_object* v___x_7672_; 
v___x_7669_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
v___x_7670_ = lean_unsigned_to_nat(2u);
v___x_7671_ = lean_mk_empty_array_with_capacity(v___x_7670_);
v___x_7672_ = lean_array_push(v___x_7671_, v___x_7669_);
return v___x_7672_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg(lean_object* v_objs_7673_, lean_object* v_libs_7674_, lean_object* v_args_7675_, uint8_t v_linkDeps_7676_, uint8_t v_sharedLean_7677_, lean_object* v_a_7678_, lean_object* v_a_7679_){
_start:
{
lean_object* v_toContext_7681_; lean_object* v_lakeEnv_7682_; lean_object* v_lean_7683_; lean_object* v_libs_7685_; lean_object* v___y_7686_; 
v_toContext_7681_ = lean_ctor_get(v_a_7678_, 1);
v_lakeEnv_7682_ = lean_ctor_get(v_toContext_7681_, 0);
v_lean_7683_ = lean_ctor_get(v_lakeEnv_7682_, 1);
if (v_linkDeps_7676_ == 0)
{
lean_object* v___x_7696_; 
v___x_7696_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7685_ = v___x_7696_;
v___y_7686_ = v_a_7679_;
goto v___jp_7684_;
}
else
{
lean_object* v___x_7697_; 
v___x_7697_ = l_Lake_mkLinkOrder___redArg(v_libs_7674_, v_a_7679_);
if (lean_obj_tag(v___x_7697_) == 0)
{
lean_object* v_a_7698_; lean_object* v_a_7699_; 
v_a_7698_ = lean_ctor_get(v___x_7697_, 0);
lean_inc(v_a_7698_);
v_a_7699_ = lean_ctor_get(v___x_7697_, 1);
lean_inc(v_a_7699_);
lean_dec_ref_known(v___x_7697_, 2);
v_libs_7685_ = v_a_7698_;
v___y_7686_ = v_a_7699_;
goto v___jp_7684_;
}
else
{
lean_object* v_a_7700_; lean_object* v_a_7701_; lean_object* v___x_7703_; uint8_t v_isShared_7704_; uint8_t v_isSharedCheck_7708_; 
v_a_7700_ = lean_ctor_get(v___x_7697_, 0);
v_a_7701_ = lean_ctor_get(v___x_7697_, 1);
v_isSharedCheck_7708_ = !lean_is_exclusive(v___x_7697_);
if (v_isSharedCheck_7708_ == 0)
{
v___x_7703_ = v___x_7697_;
v_isShared_7704_ = v_isSharedCheck_7708_;
goto v_resetjp_7702_;
}
else
{
lean_inc(v_a_7701_);
lean_inc(v_a_7700_);
lean_dec(v___x_7697_);
v___x_7703_ = lean_box(0);
v_isShared_7704_ = v_isSharedCheck_7708_;
goto v_resetjp_7702_;
}
v_resetjp_7702_:
{
lean_object* v___x_7706_; 
if (v_isShared_7704_ == 0)
{
v___x_7706_ = v___x_7703_;
goto v_reusejp_7705_;
}
else
{
lean_object* v_reuseFailAlloc_7707_; 
v_reuseFailAlloc_7707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7707_, 0, v_a_7700_);
lean_ctor_set(v_reuseFailAlloc_7707_, 1, v_a_7701_);
v___x_7706_ = v_reuseFailAlloc_7707_;
goto v_reusejp_7705_;
}
v_reusejp_7705_:
{
return v___x_7706_;
}
}
}
}
v___jp_7684_:
{
lean_object* v_leanLibDir_7687_; lean_object* v___x_7688_; lean_object* v___x_7689_; lean_object* v___x_7690_; lean_object* v___x_7691_; lean_object* v___x_7692_; lean_object* v___x_7693_; lean_object* v___x_7694_; lean_object* v___x_7695_; 
v_leanLibDir_7687_ = lean_ctor_get(v_lean_7683_, 3);
v___x_7688_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7673_, v_libs_7685_);
lean_dec_ref(v_libs_7685_);
v___x_7689_ = l_Array_append___redArg(v___x_7688_, v_args_7675_);
v___x_7690_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0);
lean_inc_ref(v_leanLibDir_7687_);
v___x_7691_ = lean_array_push(v___x_7690_, v_leanLibDir_7687_);
v___x_7692_ = l_Array_append___redArg(v___x_7689_, v___x_7691_);
lean_dec_ref(v___x_7691_);
v___x_7693_ = l_Lake_LeanInstall_ccLinkFlags(v_sharedLean_7677_, v_lean_7683_);
v___x_7694_ = l_Array_append___redArg(v___x_7692_, v___x_7693_);
lean_dec_ref(v___x_7693_);
v___x_7695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7695_, 0, v___x_7694_);
lean_ctor_set(v___x_7695_, 1, v___y_7686_);
return v___x_7695_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___boxed(lean_object* v_objs_7709_, lean_object* v_libs_7710_, lean_object* v_args_7711_, lean_object* v_linkDeps_7712_, lean_object* v_sharedLean_7713_, lean_object* v_a_7714_, lean_object* v_a_7715_, lean_object* v_a_7716_){
_start:
{
uint8_t v_linkDeps_boxed_7717_; uint8_t v_sharedLean_boxed_7718_; lean_object* v_res_7719_; 
v_linkDeps_boxed_7717_ = lean_unbox(v_linkDeps_7712_);
v_sharedLean_boxed_7718_ = lean_unbox(v_sharedLean_7713_);
v_res_7719_ = l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg(v_objs_7709_, v_libs_7710_, v_args_7711_, v_linkDeps_boxed_7717_, v_sharedLean_boxed_7718_, v_a_7714_, v_a_7715_);
lean_dec_ref(v_a_7714_);
lean_dec_ref(v_args_7711_);
lean_dec_ref(v_libs_7710_);
lean_dec_ref(v_objs_7709_);
return v_res_7719_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs(lean_object* v_objs_7720_, lean_object* v_libs_7721_, lean_object* v_args_7722_, uint8_t v_linkDeps_7723_, uint8_t v_sharedLean_7724_, lean_object* v_a_7725_, lean_object* v_a_7726_, lean_object* v_a_7727_, lean_object* v_a_7728_, lean_object* v_a_7729_, lean_object* v_a_7730_){
_start:
{
lean_object* v_toContext_7732_; lean_object* v_lakeEnv_7733_; lean_object* v_lean_7734_; lean_object* v_libs_7736_; lean_object* v___y_7737_; 
v_toContext_7732_ = lean_ctor_get(v_a_7729_, 1);
v_lakeEnv_7733_ = lean_ctor_get(v_toContext_7732_, 0);
v_lean_7734_ = lean_ctor_get(v_lakeEnv_7733_, 1);
if (v_linkDeps_7723_ == 0)
{
lean_object* v___x_7749_; 
v___x_7749_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7736_ = v___x_7749_;
v___y_7737_ = v_a_7730_;
goto v___jp_7735_;
}
else
{
lean_object* v___x_7750_; 
v___x_7750_ = l_Lake_mkLinkOrder___redArg(v_libs_7721_, v_a_7730_);
if (lean_obj_tag(v___x_7750_) == 0)
{
lean_object* v_a_7751_; lean_object* v_a_7752_; 
v_a_7751_ = lean_ctor_get(v___x_7750_, 0);
lean_inc(v_a_7751_);
v_a_7752_ = lean_ctor_get(v___x_7750_, 1);
lean_inc(v_a_7752_);
lean_dec_ref_known(v___x_7750_, 2);
v_libs_7736_ = v_a_7751_;
v___y_7737_ = v_a_7752_;
goto v___jp_7735_;
}
else
{
lean_object* v_a_7753_; lean_object* v_a_7754_; lean_object* v___x_7756_; uint8_t v_isShared_7757_; uint8_t v_isSharedCheck_7761_; 
v_a_7753_ = lean_ctor_get(v___x_7750_, 0);
v_a_7754_ = lean_ctor_get(v___x_7750_, 1);
v_isSharedCheck_7761_ = !lean_is_exclusive(v___x_7750_);
if (v_isSharedCheck_7761_ == 0)
{
v___x_7756_ = v___x_7750_;
v_isShared_7757_ = v_isSharedCheck_7761_;
goto v_resetjp_7755_;
}
else
{
lean_inc(v_a_7754_);
lean_inc(v_a_7753_);
lean_dec(v___x_7750_);
v___x_7756_ = lean_box(0);
v_isShared_7757_ = v_isSharedCheck_7761_;
goto v_resetjp_7755_;
}
v_resetjp_7755_:
{
lean_object* v___x_7759_; 
if (v_isShared_7757_ == 0)
{
v___x_7759_ = v___x_7756_;
goto v_reusejp_7758_;
}
else
{
lean_object* v_reuseFailAlloc_7760_; 
v_reuseFailAlloc_7760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7760_, 0, v_a_7753_);
lean_ctor_set(v_reuseFailAlloc_7760_, 1, v_a_7754_);
v___x_7759_ = v_reuseFailAlloc_7760_;
goto v_reusejp_7758_;
}
v_reusejp_7758_:
{
return v___x_7759_;
}
}
}
}
v___jp_7735_:
{
lean_object* v_leanLibDir_7738_; lean_object* v___x_7739_; lean_object* v___x_7740_; lean_object* v___x_7741_; lean_object* v___x_7742_; lean_object* v___x_7743_; lean_object* v___x_7744_; lean_object* v___x_7745_; lean_object* v___x_7746_; lean_object* v___x_7747_; lean_object* v___x_7748_; 
v_leanLibDir_7738_ = lean_ctor_get(v_lean_7734_, 3);
v___x_7739_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7720_, v_libs_7736_);
lean_dec_ref(v_libs_7736_);
v___x_7740_ = l_Array_append___redArg(v___x_7739_, v_args_7722_);
v___x_7741_ = lean_unsigned_to_nat(2u);
v___x_7742_ = lean_mk_empty_array_with_capacity(v___x_7741_);
lean_dec_ref(v___x_7742_);
v___x_7743_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0);
lean_inc_ref(v_leanLibDir_7738_);
v___x_7744_ = lean_array_push(v___x_7743_, v_leanLibDir_7738_);
v___x_7745_ = l_Array_append___redArg(v___x_7740_, v___x_7744_);
lean_dec_ref(v___x_7744_);
v___x_7746_ = l_Lake_LeanInstall_ccLinkFlags(v_sharedLean_7724_, v_lean_7734_);
v___x_7747_ = l_Array_append___redArg(v___x_7745_, v___x_7746_);
lean_dec_ref(v___x_7746_);
v___x_7748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7748_, 0, v___x_7747_);
lean_ctor_set(v___x_7748_, 1, v___y_7737_);
return v___x_7748_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___boxed(lean_object* v_objs_7762_, lean_object* v_libs_7763_, lean_object* v_args_7764_, lean_object* v_linkDeps_7765_, lean_object* v_sharedLean_7766_, lean_object* v_a_7767_, lean_object* v_a_7768_, lean_object* v_a_7769_, lean_object* v_a_7770_, lean_object* v_a_7771_, lean_object* v_a_7772_, lean_object* v_a_7773_){
_start:
{
uint8_t v_linkDeps_boxed_7774_; uint8_t v_sharedLean_boxed_7775_; lean_object* v_res_7776_; 
v_linkDeps_boxed_7774_ = lean_unbox(v_linkDeps_7765_);
v_sharedLean_boxed_7775_ = lean_unbox(v_sharedLean_7766_);
v_res_7776_ = l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs(v_objs_7762_, v_libs_7763_, v_args_7764_, v_linkDeps_boxed_7774_, v_sharedLean_boxed_7775_, v_a_7767_, v_a_7768_, v_a_7769_, v_a_7770_, v_a_7771_, v_a_7772_);
lean_dec_ref(v_a_7771_);
lean_dec(v_a_7770_);
lean_dec(v_a_7769_);
lean_dec(v_a_7768_);
lean_dec_ref(v_a_7767_);
lean_dec_ref(v_args_7764_);
lean_dec_ref(v_libs_7763_);
lean_dec_ref(v_objs_7762_);
return v_res_7776_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync___lam__0(lean_object* v_linkObjs_7777_, lean_object* v_args_7778_, lean_object* v_libFile_7779_, lean_object* v_linker_7780_, lean_object* v___y_7781_, uint8_t v_linkDeps_7782_, lean_object* v_linkLibs_7783_, lean_object* v___y_7784_, lean_object* v___y_7785_, lean_object* v___y_7786_, lean_object* v___y_7787_, lean_object* v___y_7788_, lean_object* v___y_7789_){
_start:
{
lean_object* v_libs_7792_; lean_object* v___y_7793_; 
if (v_linkDeps_7782_ == 0)
{
lean_object* v___x_7830_; 
v___x_7830_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7792_ = v___x_7830_;
v___y_7793_ = v___y_7789_;
goto v___jp_7791_;
}
else
{
lean_object* v___x_7831_; 
v___x_7831_ = l_Lake_mkLinkOrder___redArg(v_linkLibs_7783_, v___y_7789_);
if (lean_obj_tag(v___x_7831_) == 0)
{
lean_object* v_a_7832_; lean_object* v_a_7833_; 
v_a_7832_ = lean_ctor_get(v___x_7831_, 0);
lean_inc(v_a_7832_);
v_a_7833_ = lean_ctor_get(v___x_7831_, 1);
lean_inc(v_a_7833_);
lean_dec_ref_known(v___x_7831_, 2);
v_libs_7792_ = v_a_7832_;
v___y_7793_ = v_a_7833_;
goto v___jp_7791_;
}
else
{
lean_object* v_a_7834_; lean_object* v_a_7835_; lean_object* v___x_7837_; uint8_t v_isShared_7838_; uint8_t v_isSharedCheck_7842_; 
lean_dec(v___y_7781_);
lean_dec_ref(v_linker_7780_);
lean_dec_ref(v_libFile_7779_);
v_a_7834_ = lean_ctor_get(v___x_7831_, 0);
v_a_7835_ = lean_ctor_get(v___x_7831_, 1);
v_isSharedCheck_7842_ = !lean_is_exclusive(v___x_7831_);
if (v_isSharedCheck_7842_ == 0)
{
v___x_7837_ = v___x_7831_;
v_isShared_7838_ = v_isSharedCheck_7842_;
goto v_resetjp_7836_;
}
else
{
lean_inc(v_a_7835_);
lean_inc(v_a_7834_);
lean_dec(v___x_7831_);
v___x_7837_ = lean_box(0);
v_isShared_7838_ = v_isSharedCheck_7842_;
goto v_resetjp_7836_;
}
v_resetjp_7836_:
{
lean_object* v___x_7840_; 
if (v_isShared_7838_ == 0)
{
v___x_7840_ = v___x_7837_;
goto v_reusejp_7839_;
}
else
{
lean_object* v_reuseFailAlloc_7841_; 
v_reuseFailAlloc_7841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7841_, 0, v_a_7834_);
lean_ctor_set(v_reuseFailAlloc_7841_, 1, v_a_7835_);
v___x_7840_ = v_reuseFailAlloc_7841_;
goto v_reusejp_7839_;
}
v_reusejp_7839_:
{
return v___x_7840_;
}
}
}
}
v___jp_7791_:
{
lean_object* v_log_7794_; uint8_t v_action_7795_; uint8_t v_wantsRebuild_7796_; lean_object* v_trace_7797_; lean_object* v_buildTime_7798_; lean_object* v___x_7800_; uint8_t v_isShared_7801_; uint8_t v_isSharedCheck_7829_; 
v_log_7794_ = lean_ctor_get(v___y_7793_, 0);
v_action_7795_ = lean_ctor_get_uint8(v___y_7793_, sizeof(void*)*3);
v_wantsRebuild_7796_ = lean_ctor_get_uint8(v___y_7793_, sizeof(void*)*3 + 1);
v_trace_7797_ = lean_ctor_get(v___y_7793_, 1);
v_buildTime_7798_ = lean_ctor_get(v___y_7793_, 2);
v_isSharedCheck_7829_ = !lean_is_exclusive(v___y_7793_);
if (v_isSharedCheck_7829_ == 0)
{
v___x_7800_ = v___y_7793_;
v_isShared_7801_ = v_isSharedCheck_7829_;
goto v_resetjp_7799_;
}
else
{
lean_inc(v_buildTime_7798_);
lean_inc(v_trace_7797_);
lean_inc(v_log_7794_);
lean_dec(v___y_7793_);
v___x_7800_ = lean_box(0);
v_isShared_7801_ = v_isSharedCheck_7829_;
goto v_resetjp_7799_;
}
v_resetjp_7799_:
{
lean_object* v___x_7802_; lean_object* v___x_7803_; lean_object* v___x_7804_; 
v___x_7802_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_linkObjs_7777_, v_libs_7792_);
lean_dec_ref(v_libs_7792_);
v___x_7803_ = l_Array_append___redArg(v___x_7802_, v_args_7778_);
v___x_7804_ = l_Lake_compileSharedLib(v_libFile_7779_, v___x_7803_, v_linker_7780_, v___y_7781_, v_log_7794_);
lean_dec_ref(v___x_7803_);
if (lean_obj_tag(v___x_7804_) == 0)
{
lean_object* v_a_7805_; lean_object* v_a_7806_; lean_object* v___x_7808_; uint8_t v_isShared_7809_; uint8_t v_isSharedCheck_7816_; 
v_a_7805_ = lean_ctor_get(v___x_7804_, 0);
v_a_7806_ = lean_ctor_get(v___x_7804_, 1);
v_isSharedCheck_7816_ = !lean_is_exclusive(v___x_7804_);
if (v_isSharedCheck_7816_ == 0)
{
v___x_7808_ = v___x_7804_;
v_isShared_7809_ = v_isSharedCheck_7816_;
goto v_resetjp_7807_;
}
else
{
lean_inc(v_a_7806_);
lean_inc(v_a_7805_);
lean_dec(v___x_7804_);
v___x_7808_ = lean_box(0);
v_isShared_7809_ = v_isSharedCheck_7816_;
goto v_resetjp_7807_;
}
v_resetjp_7807_:
{
lean_object* v___x_7811_; 
if (v_isShared_7801_ == 0)
{
lean_ctor_set(v___x_7800_, 0, v_a_7806_);
v___x_7811_ = v___x_7800_;
goto v_reusejp_7810_;
}
else
{
lean_object* v_reuseFailAlloc_7815_; 
v_reuseFailAlloc_7815_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7815_, 0, v_a_7806_);
lean_ctor_set(v_reuseFailAlloc_7815_, 1, v_trace_7797_);
lean_ctor_set(v_reuseFailAlloc_7815_, 2, v_buildTime_7798_);
lean_ctor_set_uint8(v_reuseFailAlloc_7815_, sizeof(void*)*3, v_action_7795_);
lean_ctor_set_uint8(v_reuseFailAlloc_7815_, sizeof(void*)*3 + 1, v_wantsRebuild_7796_);
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
v_reuseFailAlloc_7814_ = lean_alloc_ctor(0, 2, 0);
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
else
{
lean_object* v_a_7817_; lean_object* v_a_7818_; lean_object* v___x_7820_; uint8_t v_isShared_7821_; uint8_t v_isSharedCheck_7828_; 
v_a_7817_ = lean_ctor_get(v___x_7804_, 0);
v_a_7818_ = lean_ctor_get(v___x_7804_, 1);
v_isSharedCheck_7828_ = !lean_is_exclusive(v___x_7804_);
if (v_isSharedCheck_7828_ == 0)
{
v___x_7820_ = v___x_7804_;
v_isShared_7821_ = v_isSharedCheck_7828_;
goto v_resetjp_7819_;
}
else
{
lean_inc(v_a_7818_);
lean_inc(v_a_7817_);
lean_dec(v___x_7804_);
v___x_7820_ = lean_box(0);
v_isShared_7821_ = v_isSharedCheck_7828_;
goto v_resetjp_7819_;
}
v_resetjp_7819_:
{
lean_object* v___x_7823_; 
if (v_isShared_7801_ == 0)
{
lean_ctor_set(v___x_7800_, 0, v_a_7818_);
v___x_7823_ = v___x_7800_;
goto v_reusejp_7822_;
}
else
{
lean_object* v_reuseFailAlloc_7827_; 
v_reuseFailAlloc_7827_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7827_, 0, v_a_7818_);
lean_ctor_set(v_reuseFailAlloc_7827_, 1, v_trace_7797_);
lean_ctor_set(v_reuseFailAlloc_7827_, 2, v_buildTime_7798_);
lean_ctor_set_uint8(v_reuseFailAlloc_7827_, sizeof(void*)*3, v_action_7795_);
lean_ctor_set_uint8(v_reuseFailAlloc_7827_, sizeof(void*)*3 + 1, v_wantsRebuild_7796_);
v___x_7823_ = v_reuseFailAlloc_7827_;
goto v_reusejp_7822_;
}
v_reusejp_7822_:
{
lean_object* v___x_7825_; 
if (v_isShared_7821_ == 0)
{
lean_ctor_set(v___x_7820_, 1, v___x_7823_);
v___x_7825_ = v___x_7820_;
goto v_reusejp_7824_;
}
else
{
lean_object* v_reuseFailAlloc_7826_; 
v_reuseFailAlloc_7826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7826_, 0, v_a_7817_);
lean_ctor_set(v_reuseFailAlloc_7826_, 1, v___x_7823_);
v___x_7825_ = v_reuseFailAlloc_7826_;
goto v_reusejp_7824_;
}
v_reusejp_7824_:
{
return v___x_7825_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync___lam__0___boxed(lean_object* v_linkObjs_7843_, lean_object* v_args_7844_, lean_object* v_libFile_7845_, lean_object* v_linker_7846_, lean_object* v___y_7847_, lean_object* v_linkDeps_7848_, lean_object* v_linkLibs_7849_, lean_object* v___y_7850_, lean_object* v___y_7851_, lean_object* v___y_7852_, lean_object* v___y_7853_, lean_object* v___y_7854_, lean_object* v___y_7855_, lean_object* v___y_7856_){
_start:
{
uint8_t v_linkDeps_boxed_7857_; lean_object* v_res_7858_; 
v_linkDeps_boxed_7857_ = lean_unbox(v_linkDeps_7848_);
v_res_7858_ = l_Lake_buildSharedLibSync___lam__0(v_linkObjs_7843_, v_args_7844_, v_libFile_7845_, v_linker_7846_, v___y_7847_, v_linkDeps_boxed_7857_, v_linkLibs_7849_, v___y_7850_, v___y_7851_, v___y_7852_, v___y_7853_, v___y_7854_, v___y_7855_);
lean_dec_ref(v___y_7854_);
lean_dec(v___y_7853_);
lean_dec(v___y_7852_);
lean_dec(v___y_7851_);
lean_dec_ref(v___y_7850_);
lean_dec_ref(v_linkLibs_7849_);
lean_dec_ref(v_args_7844_);
lean_dec_ref(v_linkObjs_7843_);
return v_res_7858_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync(lean_object* v_libName_7860_, lean_object* v_libFile_7861_, lean_object* v_linkObjs_7862_, lean_object* v_linkLibs_7863_, lean_object* v_args_7864_, lean_object* v_linker_7865_, uint8_t v_plugin_7866_, uint8_t v_linkDeps_7867_, lean_object* v_macosxDeploymentTarget_x3f_7868_, lean_object* v_a_7869_, lean_object* v_a_7870_, lean_object* v_a_7871_, lean_object* v_a_7872_, lean_object* v_a_7873_, lean_object* v_a_7874_){
_start:
{
lean_object* v___y_7877_; lean_object* v___y_7878_; lean_object* v___y_7879_; lean_object* v___y_7880_; lean_object* v___y_7881_; lean_object* v___y_7882_; lean_object* v___y_7883_; lean_object* v_log_7909_; uint8_t v_action_7910_; uint8_t v_wantsRebuild_7911_; lean_object* v_trace_7912_; lean_object* v_buildTime_7913_; lean_object* v___x_7915_; uint8_t v_isShared_7916_; uint8_t v_isSharedCheck_7943_; 
v_log_7909_ = lean_ctor_get(v_a_7874_, 0);
v_action_7910_ = lean_ctor_get_uint8(v_a_7874_, sizeof(void*)*3);
v_wantsRebuild_7911_ = lean_ctor_get_uint8(v_a_7874_, sizeof(void*)*3 + 1);
v_trace_7912_ = lean_ctor_get(v_a_7874_, 1);
v_buildTime_7913_ = lean_ctor_get(v_a_7874_, 2);
v_isSharedCheck_7943_ = !lean_is_exclusive(v_a_7874_);
if (v_isSharedCheck_7943_ == 0)
{
v___x_7915_ = v_a_7874_;
v_isShared_7916_ = v_isSharedCheck_7943_;
goto v_resetjp_7914_;
}
else
{
lean_inc(v_buildTime_7913_);
lean_inc(v_trace_7912_);
lean_inc(v_log_7909_);
lean_dec(v_a_7874_);
v___x_7915_ = lean_box(0);
v_isShared_7916_ = v_isSharedCheck_7943_;
goto v_resetjp_7914_;
}
v___jp_7876_:
{
uint8_t v___x_7884_; lean_object* v___x_7885_; uint8_t v___x_7886_; lean_object* v___x_7887_; 
v___x_7884_ = 0;
v___x_7885_ = l_Lake_sharedLibExt;
v___x_7886_ = 1;
v___x_7887_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_7861_, v___y_7877_, v___x_7884_, v___x_7885_, v___x_7886_, v___x_7884_, v___x_7884_, v___y_7878_, v___y_7879_, v___y_7880_, v___y_7881_, v___y_7882_, v___y_7883_);
if (lean_obj_tag(v___x_7887_) == 0)
{
lean_object* v_a_7888_; lean_object* v_a_7889_; lean_object* v___x_7891_; uint8_t v_isShared_7892_; uint8_t v_isSharedCheck_7899_; 
v_a_7888_ = lean_ctor_get(v___x_7887_, 0);
v_a_7889_ = lean_ctor_get(v___x_7887_, 1);
v_isSharedCheck_7899_ = !lean_is_exclusive(v___x_7887_);
if (v_isSharedCheck_7899_ == 0)
{
v___x_7891_ = v___x_7887_;
v_isShared_7892_ = v_isSharedCheck_7899_;
goto v_resetjp_7890_;
}
else
{
lean_inc(v_a_7889_);
lean_inc(v_a_7888_);
lean_dec(v___x_7887_);
v___x_7891_ = lean_box(0);
v_isShared_7892_ = v_isSharedCheck_7899_;
goto v_resetjp_7890_;
}
v_resetjp_7890_:
{
lean_object* v_path_7893_; lean_object* v___x_7894_; lean_object* v___x_7895_; lean_object* v___x_7897_; 
v_path_7893_ = lean_ctor_get(v_a_7888_, 1);
lean_inc_ref(v_path_7893_);
lean_dec(v_a_7888_);
v___x_7894_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v___x_7895_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_7895_, 0, v_path_7893_);
lean_ctor_set(v___x_7895_, 1, v_libName_7860_);
lean_ctor_set(v___x_7895_, 2, v_linkLibs_7863_);
lean_ctor_set(v___x_7895_, 3, v___x_7894_);
lean_ctor_set_uint8(v___x_7895_, sizeof(void*)*4, v_plugin_7866_);
if (v_isShared_7892_ == 0)
{
lean_ctor_set(v___x_7891_, 0, v___x_7895_);
v___x_7897_ = v___x_7891_;
goto v_reusejp_7896_;
}
else
{
lean_object* v_reuseFailAlloc_7898_; 
v_reuseFailAlloc_7898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7898_, 0, v___x_7895_);
lean_ctor_set(v_reuseFailAlloc_7898_, 1, v_a_7889_);
v___x_7897_ = v_reuseFailAlloc_7898_;
goto v_reusejp_7896_;
}
v_reusejp_7896_:
{
return v___x_7897_;
}
}
}
else
{
lean_object* v_a_7900_; lean_object* v_a_7901_; lean_object* v___x_7903_; uint8_t v_isShared_7904_; uint8_t v_isSharedCheck_7908_; 
lean_dec_ref(v_linkLibs_7863_);
lean_dec_ref(v_libName_7860_);
v_a_7900_ = lean_ctor_get(v___x_7887_, 0);
v_a_7901_ = lean_ctor_get(v___x_7887_, 1);
v_isSharedCheck_7908_ = !lean_is_exclusive(v___x_7887_);
if (v_isSharedCheck_7908_ == 0)
{
v___x_7903_ = v___x_7887_;
v_isShared_7904_ = v_isSharedCheck_7908_;
goto v_resetjp_7902_;
}
else
{
lean_inc(v_a_7901_);
lean_inc(v_a_7900_);
lean_dec(v___x_7887_);
v___x_7903_ = lean_box(0);
v_isShared_7904_ = v_isSharedCheck_7908_;
goto v_resetjp_7902_;
}
v_resetjp_7902_:
{
lean_object* v___x_7906_; 
if (v_isShared_7904_ == 0)
{
v___x_7906_ = v___x_7903_;
goto v_reusejp_7905_;
}
else
{
lean_object* v_reuseFailAlloc_7907_; 
v_reuseFailAlloc_7907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7907_, 0, v_a_7900_);
lean_ctor_set(v_reuseFailAlloc_7907_, 1, v_a_7901_);
v___x_7906_ = v_reuseFailAlloc_7907_;
goto v_reusejp_7905_;
}
v_reusejp_7905_:
{
return v___x_7906_;
}
}
}
}
v_resetjp_7914_:
{
lean_object* v___x_7917_; lean_object* v___x_7918_; lean_object* v___x_7920_; 
v___x_7917_ = l_Lake_platformTrace;
v___x_7918_ = l_Lake_BuildTrace_mix(v_trace_7912_, v___x_7917_);
lean_inc(v_buildTime_7913_);
lean_inc_ref(v___x_7918_);
lean_inc_ref(v_log_7909_);
if (v_isShared_7916_ == 0)
{
lean_ctor_set(v___x_7915_, 1, v___x_7918_);
v___x_7920_ = v___x_7915_;
goto v_reusejp_7919_;
}
else
{
lean_object* v_reuseFailAlloc_7942_; 
v_reuseFailAlloc_7942_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7942_, 0, v_log_7909_);
lean_ctor_set(v_reuseFailAlloc_7942_, 1, v___x_7918_);
lean_ctor_set(v_reuseFailAlloc_7942_, 2, v_buildTime_7913_);
lean_ctor_set_uint8(v_reuseFailAlloc_7942_, sizeof(void*)*3, v_action_7910_);
lean_ctor_set_uint8(v_reuseFailAlloc_7942_, sizeof(void*)*3 + 1, v_wantsRebuild_7911_);
v___x_7920_ = v_reuseFailAlloc_7942_;
goto v_reusejp_7919_;
}
v_reusejp_7919_:
{
lean_object* v___y_7922_; lean_object* v_val_7923_; 
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_7868_) == 0)
{
lean_object* v_toBuildConfig_7936_; lean_object* v_macosxDeploymentTarget_x3f_7937_; lean_object* v___x_7938_; lean_object* v___f_7939_; 
v_toBuildConfig_7936_ = lean_ctor_get(v_a_7873_, 0);
v_macosxDeploymentTarget_x3f_7937_ = lean_ctor_get(v_toBuildConfig_7936_, 3);
v___x_7938_ = lean_box(v_linkDeps_7867_);
lean_inc_ref(v_linkLibs_7863_);
lean_inc(v_macosxDeploymentTarget_x3f_7937_);
lean_inc_ref(v_linker_7865_);
lean_inc_ref(v_libFile_7861_);
lean_inc_ref(v_args_7864_);
lean_inc_ref(v_linkObjs_7862_);
v___f_7939_ = lean_alloc_closure((void*)(l_Lake_buildSharedLibSync___lam__0___boxed), 14, 7);
lean_closure_set(v___f_7939_, 0, v_linkObjs_7862_);
lean_closure_set(v___f_7939_, 1, v_args_7864_);
lean_closure_set(v___f_7939_, 2, v_libFile_7861_);
lean_closure_set(v___f_7939_, 3, v_linker_7865_);
lean_closure_set(v___f_7939_, 4, v_macosxDeploymentTarget_x3f_7937_);
lean_closure_set(v___f_7939_, 5, v___x_7938_);
lean_closure_set(v___f_7939_, 6, v_linkLibs_7863_);
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_7937_) == 1)
{
lean_object* v_val_7940_; 
lean_dec_ref(v___f_7939_);
lean_dec_ref(v___x_7920_);
v_val_7940_ = lean_ctor_get(v_macosxDeploymentTarget_x3f_7937_, 0);
lean_inc(v_val_7940_);
lean_inc_ref(v_macosxDeploymentTarget_x3f_7937_);
v___y_7922_ = v_macosxDeploymentTarget_x3f_7937_;
v_val_7923_ = v_val_7940_;
goto v___jp_7921_;
}
else
{
lean_dec_ref(v___x_7918_);
lean_dec(v_buildTime_7913_);
lean_dec_ref(v_log_7909_);
lean_dec_ref(v_linker_7865_);
lean_dec_ref(v_args_7864_);
lean_dec_ref(v_linkObjs_7862_);
v___y_7877_ = v___f_7939_;
v___y_7878_ = v_a_7869_;
v___y_7879_ = v_a_7870_;
v___y_7880_ = v_a_7871_;
v___y_7881_ = v_a_7872_;
v___y_7882_ = v_a_7873_;
v___y_7883_ = v___x_7920_;
goto v___jp_7876_;
}
}
else
{
lean_object* v_val_7941_; 
lean_dec_ref(v___x_7920_);
v_val_7941_ = lean_ctor_get(v_macosxDeploymentTarget_x3f_7868_, 0);
lean_inc(v_val_7941_);
v___y_7922_ = v_macosxDeploymentTarget_x3f_7868_;
v_val_7923_ = v_val_7941_;
goto v___jp_7921_;
}
v___jp_7921_:
{
lean_object* v___x_7924_; lean_object* v___f_7925_; uint64_t v___x_7926_; uint64_t v___x_7927_; uint64_t v___x_7928_; lean_object* v___x_7929_; lean_object* v___x_7930_; lean_object* v___x_7931_; lean_object* v___x_7932_; lean_object* v___x_7933_; lean_object* v___x_7934_; lean_object* v___x_7935_; 
v___x_7924_ = lean_box(v_linkDeps_7867_);
lean_inc_ref(v_linkLibs_7863_);
lean_inc_ref(v_libFile_7861_);
v___f_7925_ = lean_alloc_closure((void*)(l_Lake_buildSharedLibSync___lam__0___boxed), 14, 7);
lean_closure_set(v___f_7925_, 0, v_linkObjs_7862_);
lean_closure_set(v___f_7925_, 1, v_args_7864_);
lean_closure_set(v___f_7925_, 2, v_libFile_7861_);
lean_closure_set(v___f_7925_, 3, v_linker_7865_);
lean_closure_set(v___f_7925_, 4, v___y_7922_);
lean_closure_set(v___f_7925_, 5, v___x_7924_);
lean_closure_set(v___f_7925_, 6, v_linkLibs_7863_);
v___x_7926_ = l_Lake_Hash_nil;
v___x_7927_ = lean_string_hash(v_val_7923_);
v___x_7928_ = lean_uint64_mix_hash(v___x_7926_, v___x_7927_);
v___x_7929_ = ((lean_object*)(l_Lake_buildSharedLibSync___closed__0));
v___x_7930_ = lean_string_append(v___x_7929_, v_val_7923_);
lean_dec_ref(v_val_7923_);
v___x_7931_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_7932_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_7933_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_7933_, 0, v___x_7930_);
lean_ctor_set(v___x_7933_, 1, v___x_7931_);
lean_ctor_set(v___x_7933_, 2, v___x_7932_);
lean_ctor_set_uint64(v___x_7933_, sizeof(void*)*3, v___x_7928_);
v___x_7934_ = l_Lake_BuildTrace_mix(v___x_7918_, v___x_7933_);
v___x_7935_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_7935_, 0, v_log_7909_);
lean_ctor_set(v___x_7935_, 1, v___x_7934_);
lean_ctor_set(v___x_7935_, 2, v_buildTime_7913_);
lean_ctor_set_uint8(v___x_7935_, sizeof(void*)*3, v_action_7910_);
lean_ctor_set_uint8(v___x_7935_, sizeof(void*)*3 + 1, v_wantsRebuild_7911_);
v___y_7877_ = v___f_7925_;
v___y_7878_ = v_a_7869_;
v___y_7879_ = v_a_7870_;
v___y_7880_ = v_a_7871_;
v___y_7881_ = v_a_7872_;
v___y_7882_ = v_a_7873_;
v___y_7883_ = v___x_7935_;
goto v___jp_7876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync___boxed(lean_object* v_libName_7944_, lean_object* v_libFile_7945_, lean_object* v_linkObjs_7946_, lean_object* v_linkLibs_7947_, lean_object* v_args_7948_, lean_object* v_linker_7949_, lean_object* v_plugin_7950_, lean_object* v_linkDeps_7951_, lean_object* v_macosxDeploymentTarget_x3f_7952_, lean_object* v_a_7953_, lean_object* v_a_7954_, lean_object* v_a_7955_, lean_object* v_a_7956_, lean_object* v_a_7957_, lean_object* v_a_7958_, lean_object* v_a_7959_){
_start:
{
uint8_t v_plugin_boxed_7960_; uint8_t v_linkDeps_boxed_7961_; lean_object* v_res_7962_; 
v_plugin_boxed_7960_ = lean_unbox(v_plugin_7950_);
v_linkDeps_boxed_7961_ = lean_unbox(v_linkDeps_7951_);
v_res_7962_ = l_Lake_buildSharedLibSync(v_libName_7944_, v_libFile_7945_, v_linkObjs_7946_, v_linkLibs_7947_, v_args_7948_, v_linker_7949_, v_plugin_boxed_7960_, v_linkDeps_boxed_7961_, v_macosxDeploymentTarget_x3f_7952_, v_a_7953_, v_a_7954_, v_a_7955_, v_a_7956_, v_a_7957_, v_a_7958_);
lean_dec_ref(v_a_7957_);
lean_dec(v_a_7956_);
lean_dec(v_a_7955_);
lean_dec(v_a_7954_);
return v_res_7962_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0(lean_object* v_extraDepTrace_7963_, lean_object* v_traceArgs_7964_, lean_object* v_weakArgs_7965_, lean_object* v_libName_7966_, lean_object* v_libFile_7967_, lean_object* v_objs_7968_, lean_object* v_linker_7969_, uint8_t v_plugin_7970_, uint8_t v_linkDeps_7971_, lean_object* v_macosxDeploymentTarget_x3f_7972_, lean_object* v_libs_7973_, lean_object* v___y_7974_, lean_object* v___y_7975_, lean_object* v___y_7976_, lean_object* v___y_7977_, lean_object* v___y_7978_, lean_object* v___y_7979_){
_start:
{
lean_object* v___x_7981_; 
lean_inc_ref(v___y_7978_);
lean_inc(v___y_7977_);
lean_inc(v___y_7976_);
lean_inc(v___y_7975_);
lean_inc_ref(v___y_7974_);
v___x_7981_ = lean_apply_7(v_extraDepTrace_7963_, v___y_7974_, v___y_7975_, v___y_7976_, v___y_7977_, v___y_7978_, v___y_7979_, lean_box(0));
if (lean_obj_tag(v___x_7981_) == 0)
{
lean_object* v_a_7982_; lean_object* v_a_7983_; lean_object* v_log_7984_; uint8_t v_action_7985_; uint8_t v_wantsRebuild_7986_; lean_object* v_trace_7987_; lean_object* v_buildTime_7988_; lean_object* v___x_7990_; uint8_t v_isShared_7991_; uint8_t v_isSharedCheck_8017_; 
v_a_7982_ = lean_ctor_get(v___x_7981_, 1);
lean_inc(v_a_7982_);
v_a_7983_ = lean_ctor_get(v___x_7981_, 0);
lean_inc(v_a_7983_);
lean_dec_ref_known(v___x_7981_, 2);
v_log_7984_ = lean_ctor_get(v_a_7982_, 0);
v_action_7985_ = lean_ctor_get_uint8(v_a_7982_, sizeof(void*)*3);
v_wantsRebuild_7986_ = lean_ctor_get_uint8(v_a_7982_, sizeof(void*)*3 + 1);
v_trace_7987_ = lean_ctor_get(v_a_7982_, 1);
v_buildTime_7988_ = lean_ctor_get(v_a_7982_, 2);
v_isSharedCheck_8017_ = !lean_is_exclusive(v_a_7982_);
if (v_isSharedCheck_8017_ == 0)
{
v___x_7990_ = v_a_7982_;
v_isShared_7991_ = v_isSharedCheck_8017_;
goto v_resetjp_7989_;
}
else
{
lean_inc(v_buildTime_7988_);
lean_inc(v_trace_7987_);
lean_inc(v_log_7984_);
lean_dec(v_a_7982_);
v___x_7990_ = lean_box(0);
v_isShared_7991_ = v_isSharedCheck_8017_;
goto v_resetjp_7989_;
}
v_resetjp_7989_:
{
lean_object* v___x_7992_; uint64_t v___y_7994_; uint64_t v___x_8010_; lean_object* v___x_8011_; lean_object* v___x_8012_; uint8_t v___x_8013_; 
v___x_7992_ = l_Lake_BuildTrace_mix(v_trace_7987_, v_a_7983_);
v___x_8010_ = l_Lake_Hash_nil;
v___x_8011_ = lean_unsigned_to_nat(0u);
v___x_8012_ = lean_array_get_size(v_traceArgs_7964_);
v___x_8013_ = lean_nat_dec_lt(v___x_8011_, v___x_8012_);
if (v___x_8013_ == 0)
{
v___y_7994_ = v___x_8010_;
goto v___jp_7993_;
}
else
{
size_t v___x_8014_; size_t v___x_8015_; uint64_t v___x_8016_; 
v___x_8014_ = ((size_t)0ULL);
v___x_8015_ = lean_usize_of_nat(v___x_8012_);
v___x_8016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Internal_buildLeanO_spec__1(v_traceArgs_7964_, v___x_8014_, v___x_8015_, v___x_8010_);
v___y_7994_ = v___x_8016_;
goto v___jp_7993_;
}
v___jp_7993_:
{
lean_object* v___x_7995_; lean_object* v___x_7996_; lean_object* v___x_7997_; lean_object* v___x_7998_; lean_object* v___x_7999_; lean_object* v___x_8000_; lean_object* v___x_8001_; lean_object* v___x_8002_; lean_object* v___x_8003_; lean_object* v___x_8004_; lean_object* v___x_8006_; 
v___x_7995_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_7996_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_7964_);
v___x_7997_ = lean_array_to_list(v_traceArgs_7964_);
v___x_7998_ = l_List_toString___at___00Lake_Internal_buildLeanO_spec__0(v___x_7997_);
lean_dec(v___x_7997_);
v___x_7999_ = lean_string_append(v___x_7996_, v___x_7998_);
lean_dec_ref(v___x_7998_);
v___x_8000_ = lean_string_append(v___x_7995_, v___x_7999_);
lean_dec_ref(v___x_7999_);
v___x_8001_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_8002_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_8003_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_8003_, 0, v___x_8000_);
lean_ctor_set(v___x_8003_, 1, v___x_8001_);
lean_ctor_set(v___x_8003_, 2, v___x_8002_);
lean_ctor_set_uint64(v___x_8003_, sizeof(void*)*3, v___y_7994_);
v___x_8004_ = l_Lake_BuildTrace_mix(v___x_7992_, v___x_8003_);
if (v_isShared_7991_ == 0)
{
lean_ctor_set(v___x_7990_, 1, v___x_8004_);
v___x_8006_ = v___x_7990_;
goto v_reusejp_8005_;
}
else
{
lean_object* v_reuseFailAlloc_8009_; 
v_reuseFailAlloc_8009_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8009_, 0, v_log_7984_);
lean_ctor_set(v_reuseFailAlloc_8009_, 1, v___x_8004_);
lean_ctor_set(v_reuseFailAlloc_8009_, 2, v_buildTime_7988_);
lean_ctor_set_uint8(v_reuseFailAlloc_8009_, sizeof(void*)*3, v_action_7985_);
lean_ctor_set_uint8(v_reuseFailAlloc_8009_, sizeof(void*)*3 + 1, v_wantsRebuild_7986_);
v___x_8006_ = v_reuseFailAlloc_8009_;
goto v_reusejp_8005_;
}
v_reusejp_8005_:
{
lean_object* v___x_8007_; lean_object* v___x_8008_; 
v___x_8007_ = l_Array_append___redArg(v_weakArgs_7965_, v_traceArgs_7964_);
lean_dec_ref(v_traceArgs_7964_);
v___x_8008_ = l_Lake_buildSharedLibSync(v_libName_7966_, v_libFile_7967_, v_objs_7968_, v_libs_7973_, v___x_8007_, v_linker_7969_, v_plugin_7970_, v_linkDeps_7971_, v_macosxDeploymentTarget_x3f_7972_, v___y_7974_, v___y_7975_, v___y_7976_, v___y_7977_, v___y_7978_, v___x_8006_);
return v___x_8008_;
}
}
}
}
else
{
lean_object* v_a_8018_; lean_object* v_a_8019_; lean_object* v___x_8021_; uint8_t v_isShared_8022_; uint8_t v_isSharedCheck_8026_; 
lean_dec_ref(v___y_7974_);
lean_dec_ref(v_libs_7973_);
lean_dec(v_macosxDeploymentTarget_x3f_7972_);
lean_dec_ref(v_linker_7969_);
lean_dec_ref(v_objs_7968_);
lean_dec_ref(v_libFile_7967_);
lean_dec_ref(v_libName_7966_);
lean_dec_ref(v_weakArgs_7965_);
lean_dec_ref(v_traceArgs_7964_);
v_a_8018_ = lean_ctor_get(v___x_7981_, 0);
v_a_8019_ = lean_ctor_get(v___x_7981_, 1);
v_isSharedCheck_8026_ = !lean_is_exclusive(v___x_7981_);
if (v_isSharedCheck_8026_ == 0)
{
v___x_8021_ = v___x_7981_;
v_isShared_8022_ = v_isSharedCheck_8026_;
goto v_resetjp_8020_;
}
else
{
lean_inc(v_a_8019_);
lean_inc(v_a_8018_);
lean_dec(v___x_7981_);
v___x_8021_ = lean_box(0);
v_isShared_8022_ = v_isSharedCheck_8026_;
goto v_resetjp_8020_;
}
v_resetjp_8020_:
{
lean_object* v___x_8024_; 
if (v_isShared_8022_ == 0)
{
v___x_8024_ = v___x_8021_;
goto v_reusejp_8023_;
}
else
{
lean_object* v_reuseFailAlloc_8025_; 
v_reuseFailAlloc_8025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8025_, 0, v_a_8018_);
lean_ctor_set(v_reuseFailAlloc_8025_, 1, v_a_8019_);
v___x_8024_ = v_reuseFailAlloc_8025_;
goto v_reusejp_8023_;
}
v_reusejp_8023_:
{
return v___x_8024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object** _args){
lean_object* v_extraDepTrace_8027_ = _args[0];
lean_object* v_traceArgs_8028_ = _args[1];
lean_object* v_weakArgs_8029_ = _args[2];
lean_object* v_libName_8030_ = _args[3];
lean_object* v_libFile_8031_ = _args[4];
lean_object* v_objs_8032_ = _args[5];
lean_object* v_linker_8033_ = _args[6];
lean_object* v_plugin_8034_ = _args[7];
lean_object* v_linkDeps_8035_ = _args[8];
lean_object* v_macosxDeploymentTarget_x3f_8036_ = _args[9];
lean_object* v_libs_8037_ = _args[10];
lean_object* v___y_8038_ = _args[11];
lean_object* v___y_8039_ = _args[12];
lean_object* v___y_8040_ = _args[13];
lean_object* v___y_8041_ = _args[14];
lean_object* v___y_8042_ = _args[15];
lean_object* v___y_8043_ = _args[16];
lean_object* v___y_8044_ = _args[17];
_start:
{
uint8_t v_plugin_boxed_8045_; uint8_t v_linkDeps_boxed_8046_; lean_object* v_res_8047_; 
v_plugin_boxed_8045_ = lean_unbox(v_plugin_8034_);
v_linkDeps_boxed_8046_ = lean_unbox(v_linkDeps_8035_);
v_res_8047_ = l_Lake_buildSharedLib___lam__0(v_extraDepTrace_8027_, v_traceArgs_8028_, v_weakArgs_8029_, v_libName_8030_, v_libFile_8031_, v_objs_8032_, v_linker_8033_, v_plugin_boxed_8045_, v_linkDeps_boxed_8046_, v_macosxDeploymentTarget_x3f_8036_, v_libs_8037_, v___y_8038_, v___y_8039_, v___y_8040_, v___y_8041_, v___y_8042_, v___y_8043_);
lean_dec_ref(v___y_8042_);
lean_dec(v___y_8041_);
lean_dec(v___y_8040_);
lean_dec(v___y_8039_);
return v_res_8047_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1(lean_object* v_extraDepTrace_8049_, lean_object* v_traceArgs_8050_, lean_object* v_weakArgs_8051_, lean_object* v_libName_8052_, lean_object* v_libFile_8053_, lean_object* v_linker_8054_, uint8_t v_plugin_8055_, uint8_t v_linkDeps_8056_, lean_object* v_macosxDeploymentTarget_x3f_8057_, lean_object* v_linkLibs_8058_, lean_object* v___x_8059_, lean_object* v_objs_8060_, lean_object* v___y_8061_, lean_object* v___y_8062_, lean_object* v___y_8063_, lean_object* v___y_8064_, lean_object* v___y_8065_, lean_object* v___y_8066_){
_start:
{
lean_object* v_trace_8068_; lean_object* v___x_8069_; lean_object* v___x_8070_; lean_object* v___f_8071_; lean_object* v___x_8072_; lean_object* v___x_8073_; lean_object* v___x_8074_; uint8_t v___x_8075_; lean_object* v___x_8076_; lean_object* v___x_8077_; 
v_trace_8068_ = lean_ctor_get(v___y_8066_, 1);
v___x_8069_ = lean_box(v_plugin_8055_);
v___x_8070_ = lean_box(v_linkDeps_8056_);
v___f_8071_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__0___boxed), 18, 10);
lean_closure_set(v___f_8071_, 0, v_extraDepTrace_8049_);
lean_closure_set(v___f_8071_, 1, v_traceArgs_8050_);
lean_closure_set(v___f_8071_, 2, v_weakArgs_8051_);
lean_closure_set(v___f_8071_, 3, v_libName_8052_);
lean_closure_set(v___f_8071_, 4, v_libFile_8053_);
lean_closure_set(v___f_8071_, 5, v_objs_8060_);
lean_closure_set(v___f_8071_, 6, v_linker_8054_);
lean_closure_set(v___f_8071_, 7, v___x_8069_);
lean_closure_set(v___f_8071_, 8, v___x_8070_);
lean_closure_set(v___f_8071_, 9, v_macosxDeploymentTarget_x3f_8057_);
v___x_8072_ = ((lean_object*)(l_Lake_buildSharedLib___lam__1___closed__0));
v___x_8073_ = l_Lake_Job_collectArray___redArg(v_linkLibs_8058_, v___x_8072_);
v___x_8074_ = lean_unsigned_to_nat(0u);
v___x_8075_ = 0;
v___x_8076_ = l_Lake_Job_mapM___redArg(v___x_8059_, v___x_8073_, v___f_8071_, v___x_8074_, v___x_8075_, v___y_8061_, v___y_8062_, v___y_8063_, v___y_8064_, v___y_8065_, v_trace_8068_);
v___x_8077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8077_, 0, v___x_8076_);
lean_ctor_set(v___x_8077_, 1, v___y_8066_);
return v___x_8077_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1___boxed(lean_object** _args){
lean_object* v_extraDepTrace_8078_ = _args[0];
lean_object* v_traceArgs_8079_ = _args[1];
lean_object* v_weakArgs_8080_ = _args[2];
lean_object* v_libName_8081_ = _args[3];
lean_object* v_libFile_8082_ = _args[4];
lean_object* v_linker_8083_ = _args[5];
lean_object* v_plugin_8084_ = _args[6];
lean_object* v_linkDeps_8085_ = _args[7];
lean_object* v_macosxDeploymentTarget_x3f_8086_ = _args[8];
lean_object* v_linkLibs_8087_ = _args[9];
lean_object* v___x_8088_ = _args[10];
lean_object* v_objs_8089_ = _args[11];
lean_object* v___y_8090_ = _args[12];
lean_object* v___y_8091_ = _args[13];
lean_object* v___y_8092_ = _args[14];
lean_object* v___y_8093_ = _args[15];
lean_object* v___y_8094_ = _args[16];
lean_object* v___y_8095_ = _args[17];
lean_object* v___y_8096_ = _args[18];
_start:
{
uint8_t v_plugin_boxed_8097_; uint8_t v_linkDeps_boxed_8098_; lean_object* v_res_8099_; 
v_plugin_boxed_8097_ = lean_unbox(v_plugin_8084_);
v_linkDeps_boxed_8098_ = lean_unbox(v_linkDeps_8085_);
v_res_8099_ = l_Lake_buildSharedLib___lam__1(v_extraDepTrace_8078_, v_traceArgs_8079_, v_weakArgs_8080_, v_libName_8081_, v_libFile_8082_, v_linker_8083_, v_plugin_boxed_8097_, v_linkDeps_boxed_8098_, v_macosxDeploymentTarget_x3f_8086_, v_linkLibs_8087_, v___x_8088_, v_objs_8089_, v___y_8090_, v___y_8091_, v___y_8092_, v___y_8093_, v___y_8094_, v___y_8095_);
lean_dec_ref(v___y_8094_);
lean_dec(v___y_8093_);
lean_dec(v___y_8092_);
lean_dec(v___y_8091_);
lean_dec_ref(v_linkLibs_8087_);
return v_res_8099_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib(lean_object* v_libName_8101_, lean_object* v_libFile_8102_, lean_object* v_linkObjs_8103_, lean_object* v_linkLibs_8104_, lean_object* v_weakArgs_8105_, lean_object* v_traceArgs_8106_, lean_object* v_linker_8107_, lean_object* v_extraDepTrace_8108_, uint8_t v_plugin_8109_, uint8_t v_linkDeps_8110_, lean_object* v_macosxDeploymentTarget_x3f_8111_, lean_object* v_a_8112_, lean_object* v_a_8113_, lean_object* v_a_8114_, lean_object* v_a_8115_, lean_object* v_a_8116_, lean_object* v_a_8117_){
_start:
{
lean_object* v___x_8119_; lean_object* v___x_8120_; lean_object* v___x_8121_; lean_object* v___f_8122_; lean_object* v___x_8123_; lean_object* v___x_8124_; lean_object* v___x_8125_; uint8_t v___x_8126_; lean_object* v___x_8127_; 
v___x_8119_ = l_Lake_instDataKindDynlib;
v___x_8120_ = lean_box(v_plugin_8109_);
v___x_8121_ = lean_box(v_linkDeps_8110_);
v___f_8122_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__1___boxed), 19, 11);
lean_closure_set(v___f_8122_, 0, v_extraDepTrace_8108_);
lean_closure_set(v___f_8122_, 1, v_traceArgs_8106_);
lean_closure_set(v___f_8122_, 2, v_weakArgs_8105_);
lean_closure_set(v___f_8122_, 3, v_libName_8101_);
lean_closure_set(v___f_8122_, 4, v_libFile_8102_);
lean_closure_set(v___f_8122_, 5, v_linker_8107_);
lean_closure_set(v___f_8122_, 6, v___x_8120_);
lean_closure_set(v___f_8122_, 7, v___x_8121_);
lean_closure_set(v___f_8122_, 8, v_macosxDeploymentTarget_x3f_8111_);
lean_closure_set(v___f_8122_, 9, v_linkLibs_8104_);
lean_closure_set(v___f_8122_, 10, v___x_8119_);
v___x_8123_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8124_ = l_Lake_Job_collectArray___redArg(v_linkObjs_8103_, v___x_8123_);
v___x_8125_ = lean_unsigned_to_nat(0u);
v___x_8126_ = 1;
v___x_8127_ = l_Lake_Job_bindM___redArg(v___x_8119_, v___x_8124_, v___f_8122_, v___x_8125_, v___x_8126_, v_a_8112_, v_a_8113_, v_a_8114_, v_a_8115_, v_a_8116_, v_a_8117_);
return v___x_8127_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___boxed(lean_object** _args){
lean_object* v_libName_8128_ = _args[0];
lean_object* v_libFile_8129_ = _args[1];
lean_object* v_linkObjs_8130_ = _args[2];
lean_object* v_linkLibs_8131_ = _args[3];
lean_object* v_weakArgs_8132_ = _args[4];
lean_object* v_traceArgs_8133_ = _args[5];
lean_object* v_linker_8134_ = _args[6];
lean_object* v_extraDepTrace_8135_ = _args[7];
lean_object* v_plugin_8136_ = _args[8];
lean_object* v_linkDeps_8137_ = _args[9];
lean_object* v_macosxDeploymentTarget_x3f_8138_ = _args[10];
lean_object* v_a_8139_ = _args[11];
lean_object* v_a_8140_ = _args[12];
lean_object* v_a_8141_ = _args[13];
lean_object* v_a_8142_ = _args[14];
lean_object* v_a_8143_ = _args[15];
lean_object* v_a_8144_ = _args[16];
lean_object* v_a_8145_ = _args[17];
_start:
{
uint8_t v_plugin_boxed_8146_; uint8_t v_linkDeps_boxed_8147_; lean_object* v_res_8148_; 
v_plugin_boxed_8146_ = lean_unbox(v_plugin_8136_);
v_linkDeps_boxed_8147_ = lean_unbox(v_linkDeps_8137_);
v_res_8148_ = l_Lake_buildSharedLib(v_libName_8128_, v_libFile_8129_, v_linkObjs_8130_, v_linkLibs_8131_, v_weakArgs_8132_, v_traceArgs_8133_, v_linker_8134_, v_extraDepTrace_8135_, v_plugin_boxed_8146_, v_linkDeps_boxed_8147_, v_macosxDeploymentTarget_x3f_8138_, v_a_8139_, v_a_8140_, v_a_8141_, v_a_8142_, v_a_8143_, v_a_8144_);
lean_dec_ref(v_a_8144_);
lean_dec_ref(v_a_8143_);
lean_dec(v_a_8142_);
lean_dec(v_a_8141_);
lean_dec(v_a_8140_);
lean_dec_ref(v_linkObjs_8130_);
return v_res_8148_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync___lam__0(lean_object* v_linkObjs_8149_, lean_object* v_args_8150_, uint8_t v___x_8151_, lean_object* v_libFile_8152_, lean_object* v_macosxDeploymentTarget_x3f_8153_, uint8_t v_linkDeps_8154_, lean_object* v_linkLibs_8155_, lean_object* v___y_8156_, lean_object* v___y_8157_, lean_object* v___y_8158_, lean_object* v___y_8159_, lean_object* v___y_8160_, lean_object* v___y_8161_){
_start:
{
lean_object* v_toContext_8163_; lean_object* v_lakeEnv_8164_; lean_object* v_lean_8165_; lean_object* v_libs_8167_; lean_object* v___y_8168_; 
v_toContext_8163_ = lean_ctor_get(v___y_8160_, 1);
v_lakeEnv_8164_ = lean_ctor_get(v_toContext_8163_, 0);
v_lean_8165_ = lean_ctor_get(v_lakeEnv_8164_, 1);
if (v_linkDeps_8154_ == 0)
{
lean_object* v___x_8214_; 
v___x_8214_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_8167_ = v___x_8214_;
v___y_8168_ = v___y_8161_;
goto v___jp_8166_;
}
else
{
lean_object* v___x_8215_; 
v___x_8215_ = l_Lake_mkLinkOrder___redArg(v_linkLibs_8155_, v___y_8161_);
if (lean_obj_tag(v___x_8215_) == 0)
{
lean_object* v_a_8216_; lean_object* v_a_8217_; 
v_a_8216_ = lean_ctor_get(v___x_8215_, 0);
lean_inc(v_a_8216_);
v_a_8217_ = lean_ctor_get(v___x_8215_, 1);
lean_inc(v_a_8217_);
lean_dec_ref_known(v___x_8215_, 2);
v_libs_8167_ = v_a_8216_;
v___y_8168_ = v_a_8217_;
goto v___jp_8166_;
}
else
{
lean_object* v_a_8218_; lean_object* v_a_8219_; lean_object* v___x_8221_; uint8_t v_isShared_8222_; uint8_t v_isSharedCheck_8226_; 
lean_dec(v_macosxDeploymentTarget_x3f_8153_);
lean_dec_ref(v_libFile_8152_);
v_a_8218_ = lean_ctor_get(v___x_8215_, 0);
v_a_8219_ = lean_ctor_get(v___x_8215_, 1);
v_isSharedCheck_8226_ = !lean_is_exclusive(v___x_8215_);
if (v_isSharedCheck_8226_ == 0)
{
v___x_8221_ = v___x_8215_;
v_isShared_8222_ = v_isSharedCheck_8226_;
goto v_resetjp_8220_;
}
else
{
lean_inc(v_a_8219_);
lean_inc(v_a_8218_);
lean_dec(v___x_8215_);
v___x_8221_ = lean_box(0);
v_isShared_8222_ = v_isSharedCheck_8226_;
goto v_resetjp_8220_;
}
v_resetjp_8220_:
{
lean_object* v___x_8224_; 
if (v_isShared_8222_ == 0)
{
v___x_8224_ = v___x_8221_;
goto v_reusejp_8223_;
}
else
{
lean_object* v_reuseFailAlloc_8225_; 
v_reuseFailAlloc_8225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8225_, 0, v_a_8218_);
lean_ctor_set(v_reuseFailAlloc_8225_, 1, v_a_8219_);
v___x_8224_ = v_reuseFailAlloc_8225_;
goto v_reusejp_8223_;
}
v_reusejp_8223_:
{
return v___x_8224_;
}
}
}
}
v___jp_8166_:
{
lean_object* v_leanLibDir_8169_; lean_object* v_cc_8170_; lean_object* v_log_8171_; uint8_t v_action_8172_; uint8_t v_wantsRebuild_8173_; lean_object* v_trace_8174_; lean_object* v_buildTime_8175_; lean_object* v___x_8177_; uint8_t v_isShared_8178_; uint8_t v_isSharedCheck_8213_; 
v_leanLibDir_8169_ = lean_ctor_get(v_lean_8165_, 3);
v_cc_8170_ = lean_ctor_get(v_lean_8165_, 14);
v_log_8171_ = lean_ctor_get(v___y_8168_, 0);
v_action_8172_ = lean_ctor_get_uint8(v___y_8168_, sizeof(void*)*3);
v_wantsRebuild_8173_ = lean_ctor_get_uint8(v___y_8168_, sizeof(void*)*3 + 1);
v_trace_8174_ = lean_ctor_get(v___y_8168_, 1);
v_buildTime_8175_ = lean_ctor_get(v___y_8168_, 2);
v_isSharedCheck_8213_ = !lean_is_exclusive(v___y_8168_);
if (v_isSharedCheck_8213_ == 0)
{
v___x_8177_ = v___y_8168_;
v_isShared_8178_ = v_isSharedCheck_8213_;
goto v_resetjp_8176_;
}
else
{
lean_inc(v_buildTime_8175_);
lean_inc(v_trace_8174_);
lean_inc(v_log_8171_);
lean_dec(v___y_8168_);
v___x_8177_ = lean_box(0);
v_isShared_8178_ = v_isSharedCheck_8213_;
goto v_resetjp_8176_;
}
v_resetjp_8176_:
{
lean_object* v___x_8179_; lean_object* v___x_8180_; lean_object* v___x_8181_; lean_object* v___x_8182_; lean_object* v___x_8183_; lean_object* v___x_8184_; lean_object* v___x_8185_; lean_object* v___x_8186_; lean_object* v___x_8187_; lean_object* v___x_8188_; 
v___x_8179_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_linkObjs_8149_, v_libs_8167_);
lean_dec_ref(v_libs_8167_);
v___x_8180_ = l_Array_append___redArg(v___x_8179_, v_args_8150_);
v___x_8181_ = lean_unsigned_to_nat(2u);
v___x_8182_ = lean_mk_empty_array_with_capacity(v___x_8181_);
lean_dec_ref(v___x_8182_);
v___x_8183_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0);
lean_inc_ref(v_leanLibDir_8169_);
v___x_8184_ = lean_array_push(v___x_8183_, v_leanLibDir_8169_);
v___x_8185_ = l_Array_append___redArg(v___x_8180_, v___x_8184_);
lean_dec_ref(v___x_8184_);
v___x_8186_ = l_Lake_LeanInstall_ccLinkFlags(v___x_8151_, v_lean_8165_);
v___x_8187_ = l_Array_append___redArg(v___x_8185_, v___x_8186_);
lean_dec_ref(v___x_8186_);
lean_inc_ref(v_cc_8170_);
v___x_8188_ = l_Lake_compileSharedLib(v_libFile_8152_, v___x_8187_, v_cc_8170_, v_macosxDeploymentTarget_x3f_8153_, v_log_8171_);
lean_dec_ref(v___x_8187_);
if (lean_obj_tag(v___x_8188_) == 0)
{
lean_object* v_a_8189_; lean_object* v_a_8190_; lean_object* v___x_8192_; uint8_t v_isShared_8193_; uint8_t v_isSharedCheck_8200_; 
v_a_8189_ = lean_ctor_get(v___x_8188_, 0);
v_a_8190_ = lean_ctor_get(v___x_8188_, 1);
v_isSharedCheck_8200_ = !lean_is_exclusive(v___x_8188_);
if (v_isSharedCheck_8200_ == 0)
{
v___x_8192_ = v___x_8188_;
v_isShared_8193_ = v_isSharedCheck_8200_;
goto v_resetjp_8191_;
}
else
{
lean_inc(v_a_8190_);
lean_inc(v_a_8189_);
lean_dec(v___x_8188_);
v___x_8192_ = lean_box(0);
v_isShared_8193_ = v_isSharedCheck_8200_;
goto v_resetjp_8191_;
}
v_resetjp_8191_:
{
lean_object* v___x_8195_; 
if (v_isShared_8178_ == 0)
{
lean_ctor_set(v___x_8177_, 0, v_a_8190_);
v___x_8195_ = v___x_8177_;
goto v_reusejp_8194_;
}
else
{
lean_object* v_reuseFailAlloc_8199_; 
v_reuseFailAlloc_8199_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8199_, 0, v_a_8190_);
lean_ctor_set(v_reuseFailAlloc_8199_, 1, v_trace_8174_);
lean_ctor_set(v_reuseFailAlloc_8199_, 2, v_buildTime_8175_);
lean_ctor_set_uint8(v_reuseFailAlloc_8199_, sizeof(void*)*3, v_action_8172_);
lean_ctor_set_uint8(v_reuseFailAlloc_8199_, sizeof(void*)*3 + 1, v_wantsRebuild_8173_);
v___x_8195_ = v_reuseFailAlloc_8199_;
goto v_reusejp_8194_;
}
v_reusejp_8194_:
{
lean_object* v___x_8197_; 
if (v_isShared_8193_ == 0)
{
lean_ctor_set(v___x_8192_, 1, v___x_8195_);
v___x_8197_ = v___x_8192_;
goto v_reusejp_8196_;
}
else
{
lean_object* v_reuseFailAlloc_8198_; 
v_reuseFailAlloc_8198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8198_, 0, v_a_8189_);
lean_ctor_set(v_reuseFailAlloc_8198_, 1, v___x_8195_);
v___x_8197_ = v_reuseFailAlloc_8198_;
goto v_reusejp_8196_;
}
v_reusejp_8196_:
{
return v___x_8197_;
}
}
}
}
else
{
lean_object* v_a_8201_; lean_object* v_a_8202_; lean_object* v___x_8204_; uint8_t v_isShared_8205_; uint8_t v_isSharedCheck_8212_; 
v_a_8201_ = lean_ctor_get(v___x_8188_, 0);
v_a_8202_ = lean_ctor_get(v___x_8188_, 1);
v_isSharedCheck_8212_ = !lean_is_exclusive(v___x_8188_);
if (v_isSharedCheck_8212_ == 0)
{
v___x_8204_ = v___x_8188_;
v_isShared_8205_ = v_isSharedCheck_8212_;
goto v_resetjp_8203_;
}
else
{
lean_inc(v_a_8202_);
lean_inc(v_a_8201_);
lean_dec(v___x_8188_);
v___x_8204_ = lean_box(0);
v_isShared_8205_ = v_isSharedCheck_8212_;
goto v_resetjp_8203_;
}
v_resetjp_8203_:
{
lean_object* v___x_8207_; 
if (v_isShared_8178_ == 0)
{
lean_ctor_set(v___x_8177_, 0, v_a_8202_);
v___x_8207_ = v___x_8177_;
goto v_reusejp_8206_;
}
else
{
lean_object* v_reuseFailAlloc_8211_; 
v_reuseFailAlloc_8211_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8211_, 0, v_a_8202_);
lean_ctor_set(v_reuseFailAlloc_8211_, 1, v_trace_8174_);
lean_ctor_set(v_reuseFailAlloc_8211_, 2, v_buildTime_8175_);
lean_ctor_set_uint8(v_reuseFailAlloc_8211_, sizeof(void*)*3, v_action_8172_);
lean_ctor_set_uint8(v_reuseFailAlloc_8211_, sizeof(void*)*3 + 1, v_wantsRebuild_8173_);
v___x_8207_ = v_reuseFailAlloc_8211_;
goto v_reusejp_8206_;
}
v_reusejp_8206_:
{
lean_object* v___x_8209_; 
if (v_isShared_8205_ == 0)
{
lean_ctor_set(v___x_8204_, 1, v___x_8207_);
v___x_8209_ = v___x_8204_;
goto v_reusejp_8208_;
}
else
{
lean_object* v_reuseFailAlloc_8210_; 
v_reuseFailAlloc_8210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8210_, 0, v_a_8201_);
lean_ctor_set(v_reuseFailAlloc_8210_, 1, v___x_8207_);
v___x_8209_ = v_reuseFailAlloc_8210_;
goto v_reusejp_8208_;
}
v_reusejp_8208_:
{
return v___x_8209_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync___lam__0___boxed(lean_object* v_linkObjs_8227_, lean_object* v_args_8228_, lean_object* v___x_8229_, lean_object* v_libFile_8230_, lean_object* v_macosxDeploymentTarget_x3f_8231_, lean_object* v_linkDeps_8232_, lean_object* v_linkLibs_8233_, lean_object* v___y_8234_, lean_object* v___y_8235_, lean_object* v___y_8236_, lean_object* v___y_8237_, lean_object* v___y_8238_, lean_object* v___y_8239_, lean_object* v___y_8240_){
_start:
{
uint8_t v___x_34596__boxed_8241_; uint8_t v_linkDeps_boxed_8242_; lean_object* v_res_8243_; 
v___x_34596__boxed_8241_ = lean_unbox(v___x_8229_);
v_linkDeps_boxed_8242_ = lean_unbox(v_linkDeps_8232_);
v_res_8243_ = l_Lake_buildLeanSharedLibSync___lam__0(v_linkObjs_8227_, v_args_8228_, v___x_34596__boxed_8241_, v_libFile_8230_, v_macosxDeploymentTarget_x3f_8231_, v_linkDeps_boxed_8242_, v_linkLibs_8233_, v___y_8234_, v___y_8235_, v___y_8236_, v___y_8237_, v___y_8238_, v___y_8239_);
lean_dec_ref(v___y_8238_);
lean_dec(v___y_8237_);
lean_dec(v___y_8236_);
lean_dec(v___y_8235_);
lean_dec_ref(v___y_8234_);
lean_dec_ref(v_linkLibs_8233_);
lean_dec_ref(v_args_8228_);
lean_dec_ref(v_linkObjs_8227_);
return v_res_8243_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync(lean_object* v_libName_8244_, lean_object* v_libFile_8245_, lean_object* v_linkObjs_8246_, lean_object* v_linkLibs_8247_, lean_object* v_args_8248_, uint8_t v_plugin_8249_, uint8_t v_linkDeps_8250_, lean_object* v_macosxDeploymentTarget_x3f_8251_, lean_object* v_a_8252_, lean_object* v_a_8253_, lean_object* v_a_8254_, lean_object* v_a_8255_, lean_object* v_a_8256_, lean_object* v_a_8257_){
_start:
{
lean_object* v_log_8259_; uint8_t v_action_8260_; uint8_t v_wantsRebuild_8261_; lean_object* v_trace_8262_; lean_object* v_buildTime_8263_; lean_object* v___x_8265_; uint8_t v_isShared_8266_; uint8_t v_isSharedCheck_8302_; 
v_log_8259_ = lean_ctor_get(v_a_8257_, 0);
v_action_8260_ = lean_ctor_get_uint8(v_a_8257_, sizeof(void*)*3);
v_wantsRebuild_8261_ = lean_ctor_get_uint8(v_a_8257_, sizeof(void*)*3 + 1);
v_trace_8262_ = lean_ctor_get(v_a_8257_, 1);
v_buildTime_8263_ = lean_ctor_get(v_a_8257_, 2);
v_isSharedCheck_8302_ = !lean_is_exclusive(v_a_8257_);
if (v_isSharedCheck_8302_ == 0)
{
v___x_8265_ = v_a_8257_;
v_isShared_8266_ = v_isSharedCheck_8302_;
goto v_resetjp_8264_;
}
else
{
lean_inc(v_buildTime_8263_);
lean_inc(v_trace_8262_);
lean_inc(v_log_8259_);
lean_dec(v_a_8257_);
v___x_8265_ = lean_box(0);
v_isShared_8266_ = v_isSharedCheck_8302_;
goto v_resetjp_8264_;
}
v_resetjp_8264_:
{
lean_object* v_leanTrace_8267_; lean_object* v___x_8268_; lean_object* v___x_8269_; lean_object* v___x_8270_; lean_object* v___x_8272_; 
v_leanTrace_8267_ = lean_ctor_get(v_a_8256_, 2);
lean_inc_ref(v_leanTrace_8267_);
v___x_8268_ = l_Lake_BuildTrace_mix(v_trace_8262_, v_leanTrace_8267_);
v___x_8269_ = l_Lake_platformTrace;
v___x_8270_ = l_Lake_BuildTrace_mix(v___x_8268_, v___x_8269_);
if (v_isShared_8266_ == 0)
{
lean_ctor_set(v___x_8265_, 1, v___x_8270_);
v___x_8272_ = v___x_8265_;
goto v_reusejp_8271_;
}
else
{
lean_object* v_reuseFailAlloc_8301_; 
v_reuseFailAlloc_8301_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8301_, 0, v_log_8259_);
lean_ctor_set(v_reuseFailAlloc_8301_, 1, v___x_8270_);
lean_ctor_set(v_reuseFailAlloc_8301_, 2, v_buildTime_8263_);
lean_ctor_set_uint8(v_reuseFailAlloc_8301_, sizeof(void*)*3, v_action_8260_);
lean_ctor_set_uint8(v_reuseFailAlloc_8301_, sizeof(void*)*3 + 1, v_wantsRebuild_8261_);
v___x_8272_ = v_reuseFailAlloc_8301_;
goto v_reusejp_8271_;
}
v_reusejp_8271_:
{
uint8_t v___x_8273_; lean_object* v___x_8274_; lean_object* v___x_8275_; lean_object* v___f_8276_; uint8_t v___x_8277_; lean_object* v___x_8278_; lean_object* v___x_8279_; 
v___x_8273_ = 1;
v___x_8274_ = lean_box(v___x_8273_);
v___x_8275_ = lean_box(v_linkDeps_8250_);
lean_inc_ref(v_linkLibs_8247_);
lean_inc_ref(v_libFile_8245_);
v___f_8276_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibSync___lam__0___boxed), 14, 7);
lean_closure_set(v___f_8276_, 0, v_linkObjs_8246_);
lean_closure_set(v___f_8276_, 1, v_args_8248_);
lean_closure_set(v___f_8276_, 2, v___x_8274_);
lean_closure_set(v___f_8276_, 3, v_libFile_8245_);
lean_closure_set(v___f_8276_, 4, v_macosxDeploymentTarget_x3f_8251_);
lean_closure_set(v___f_8276_, 5, v___x_8275_);
lean_closure_set(v___f_8276_, 6, v_linkLibs_8247_);
v___x_8277_ = 0;
v___x_8278_ = l_Lake_sharedLibExt;
v___x_8279_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_8245_, v___f_8276_, v___x_8277_, v___x_8278_, v___x_8273_, v___x_8277_, v___x_8277_, v_a_8252_, v_a_8253_, v_a_8254_, v_a_8255_, v_a_8256_, v___x_8272_);
if (lean_obj_tag(v___x_8279_) == 0)
{
lean_object* v_a_8280_; lean_object* v_a_8281_; lean_object* v___x_8283_; uint8_t v_isShared_8284_; uint8_t v_isSharedCheck_8291_; 
v_a_8280_ = lean_ctor_get(v___x_8279_, 0);
v_a_8281_ = lean_ctor_get(v___x_8279_, 1);
v_isSharedCheck_8291_ = !lean_is_exclusive(v___x_8279_);
if (v_isSharedCheck_8291_ == 0)
{
v___x_8283_ = v___x_8279_;
v_isShared_8284_ = v_isSharedCheck_8291_;
goto v_resetjp_8282_;
}
else
{
lean_inc(v_a_8281_);
lean_inc(v_a_8280_);
lean_dec(v___x_8279_);
v___x_8283_ = lean_box(0);
v_isShared_8284_ = v_isSharedCheck_8291_;
goto v_resetjp_8282_;
}
v_resetjp_8282_:
{
lean_object* v_path_8285_; lean_object* v___x_8286_; lean_object* v___x_8287_; lean_object* v___x_8289_; 
v_path_8285_ = lean_ctor_get(v_a_8280_, 1);
lean_inc_ref(v_path_8285_);
lean_dec(v_a_8280_);
v___x_8286_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v___x_8287_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_8287_, 0, v_path_8285_);
lean_ctor_set(v___x_8287_, 1, v_libName_8244_);
lean_ctor_set(v___x_8287_, 2, v_linkLibs_8247_);
lean_ctor_set(v___x_8287_, 3, v___x_8286_);
lean_ctor_set_uint8(v___x_8287_, sizeof(void*)*4, v_plugin_8249_);
if (v_isShared_8284_ == 0)
{
lean_ctor_set(v___x_8283_, 0, v___x_8287_);
v___x_8289_ = v___x_8283_;
goto v_reusejp_8288_;
}
else
{
lean_object* v_reuseFailAlloc_8290_; 
v_reuseFailAlloc_8290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8290_, 0, v___x_8287_);
lean_ctor_set(v_reuseFailAlloc_8290_, 1, v_a_8281_);
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
lean_dec_ref(v_linkLibs_8247_);
lean_dec_ref(v_libName_8244_);
v_a_8292_ = lean_ctor_get(v___x_8279_, 0);
v_a_8293_ = lean_ctor_get(v___x_8279_, 1);
v_isSharedCheck_8300_ = !lean_is_exclusive(v___x_8279_);
if (v_isSharedCheck_8300_ == 0)
{
v___x_8295_ = v___x_8279_;
v_isShared_8296_ = v_isSharedCheck_8300_;
goto v_resetjp_8294_;
}
else
{
lean_inc(v_a_8293_);
lean_inc(v_a_8292_);
lean_dec(v___x_8279_);
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
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync___boxed(lean_object* v_libName_8303_, lean_object* v_libFile_8304_, lean_object* v_linkObjs_8305_, lean_object* v_linkLibs_8306_, lean_object* v_args_8307_, lean_object* v_plugin_8308_, lean_object* v_linkDeps_8309_, lean_object* v_macosxDeploymentTarget_x3f_8310_, lean_object* v_a_8311_, lean_object* v_a_8312_, lean_object* v_a_8313_, lean_object* v_a_8314_, lean_object* v_a_8315_, lean_object* v_a_8316_, lean_object* v_a_8317_){
_start:
{
uint8_t v_plugin_boxed_8318_; uint8_t v_linkDeps_boxed_8319_; lean_object* v_res_8320_; 
v_plugin_boxed_8318_ = lean_unbox(v_plugin_8308_);
v_linkDeps_boxed_8319_ = lean_unbox(v_linkDeps_8309_);
v_res_8320_ = l_Lake_buildLeanSharedLibSync(v_libName_8303_, v_libFile_8304_, v_linkObjs_8305_, v_linkLibs_8306_, v_args_8307_, v_plugin_boxed_8318_, v_linkDeps_boxed_8319_, v_macosxDeploymentTarget_x3f_8310_, v_a_8311_, v_a_8312_, v_a_8313_, v_a_8314_, v_a_8315_, v_a_8316_);
lean_dec_ref(v_a_8315_);
lean_dec(v_a_8314_);
lean_dec(v_a_8313_);
lean_dec(v_a_8312_);
return v_res_8320_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object* v_traceArgs_8321_, lean_object* v_weakArgs_8322_, lean_object* v_libName_8323_, lean_object* v_libFile_8324_, lean_object* v_objs_8325_, uint8_t v_plugin_8326_, uint8_t v_linkDeps_8327_, lean_object* v_macosxDeploymentTarget_x3f_8328_, lean_object* v_libs_8329_, lean_object* v___y_8330_, lean_object* v___y_8331_, lean_object* v___y_8332_, lean_object* v___y_8333_, lean_object* v___y_8334_, lean_object* v___y_8335_){
_start:
{
uint64_t v___y_8338_; uint64_t v___x_8363_; lean_object* v___x_8364_; lean_object* v___x_8365_; uint8_t v___x_8366_; 
v___x_8363_ = l_Lake_Hash_nil;
v___x_8364_ = lean_unsigned_to_nat(0u);
v___x_8365_ = lean_array_get_size(v_traceArgs_8321_);
v___x_8366_ = lean_nat_dec_lt(v___x_8364_, v___x_8365_);
if (v___x_8366_ == 0)
{
v___y_8338_ = v___x_8363_;
goto v___jp_8337_;
}
else
{
size_t v___x_8367_; size_t v___x_8368_; uint64_t v___x_8369_; 
v___x_8367_ = ((size_t)0ULL);
v___x_8368_ = lean_usize_of_nat(v___x_8365_);
v___x_8369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Internal_buildLeanO_spec__1(v_traceArgs_8321_, v___x_8367_, v___x_8368_, v___x_8363_);
v___y_8338_ = v___x_8369_;
goto v___jp_8337_;
}
v___jp_8337_:
{
lean_object* v_log_8339_; uint8_t v_action_8340_; uint8_t v_wantsRebuild_8341_; lean_object* v_trace_8342_; lean_object* v_buildTime_8343_; lean_object* v___x_8345_; uint8_t v_isShared_8346_; uint8_t v_isSharedCheck_8362_; 
v_log_8339_ = lean_ctor_get(v___y_8335_, 0);
v_action_8340_ = lean_ctor_get_uint8(v___y_8335_, sizeof(void*)*3);
v_wantsRebuild_8341_ = lean_ctor_get_uint8(v___y_8335_, sizeof(void*)*3 + 1);
v_trace_8342_ = lean_ctor_get(v___y_8335_, 1);
v_buildTime_8343_ = lean_ctor_get(v___y_8335_, 2);
v_isSharedCheck_8362_ = !lean_is_exclusive(v___y_8335_);
if (v_isSharedCheck_8362_ == 0)
{
v___x_8345_ = v___y_8335_;
v_isShared_8346_ = v_isSharedCheck_8362_;
goto v_resetjp_8344_;
}
else
{
lean_inc(v_buildTime_8343_);
lean_inc(v_trace_8342_);
lean_inc(v_log_8339_);
lean_dec(v___y_8335_);
v___x_8345_ = lean_box(0);
v_isShared_8346_ = v_isSharedCheck_8362_;
goto v_resetjp_8344_;
}
v_resetjp_8344_:
{
lean_object* v___x_8347_; lean_object* v___x_8348_; lean_object* v___x_8349_; lean_object* v___x_8350_; lean_object* v___x_8351_; lean_object* v___x_8352_; lean_object* v___x_8353_; lean_object* v___x_8354_; lean_object* v___x_8355_; lean_object* v___x_8356_; lean_object* v___x_8358_; 
v___x_8347_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_8348_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_8349_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_8321_);
v___x_8350_ = lean_array_to_list(v_traceArgs_8321_);
v___x_8351_ = l_List_toString___at___00Lake_Internal_buildLeanO_spec__0(v___x_8350_);
lean_dec(v___x_8350_);
v___x_8352_ = lean_string_append(v___x_8349_, v___x_8351_);
lean_dec_ref(v___x_8351_);
v___x_8353_ = lean_string_append(v___x_8348_, v___x_8352_);
lean_dec_ref(v___x_8352_);
v___x_8354_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_8355_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_8355_, 0, v___x_8353_);
lean_ctor_set(v___x_8355_, 1, v___x_8347_);
lean_ctor_set(v___x_8355_, 2, v___x_8354_);
lean_ctor_set_uint64(v___x_8355_, sizeof(void*)*3, v___y_8338_);
v___x_8356_ = l_Lake_BuildTrace_mix(v_trace_8342_, v___x_8355_);
if (v_isShared_8346_ == 0)
{
lean_ctor_set(v___x_8345_, 1, v___x_8356_);
v___x_8358_ = v___x_8345_;
goto v_reusejp_8357_;
}
else
{
lean_object* v_reuseFailAlloc_8361_; 
v_reuseFailAlloc_8361_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8361_, 0, v_log_8339_);
lean_ctor_set(v_reuseFailAlloc_8361_, 1, v___x_8356_);
lean_ctor_set(v_reuseFailAlloc_8361_, 2, v_buildTime_8343_);
lean_ctor_set_uint8(v_reuseFailAlloc_8361_, sizeof(void*)*3, v_action_8340_);
lean_ctor_set_uint8(v_reuseFailAlloc_8361_, sizeof(void*)*3 + 1, v_wantsRebuild_8341_);
v___x_8358_ = v_reuseFailAlloc_8361_;
goto v_reusejp_8357_;
}
v_reusejp_8357_:
{
lean_object* v___x_8359_; lean_object* v___x_8360_; 
v___x_8359_ = l_Array_append___redArg(v_weakArgs_8322_, v_traceArgs_8321_);
lean_dec_ref(v_traceArgs_8321_);
v___x_8360_ = l_Lake_buildLeanSharedLibSync(v_libName_8323_, v_libFile_8324_, v_objs_8325_, v_libs_8329_, v___x_8359_, v_plugin_8326_, v_linkDeps_8327_, v_macosxDeploymentTarget_x3f_8328_, v___y_8330_, v___y_8331_, v___y_8332_, v___y_8333_, v___y_8334_, v___x_8358_);
return v___x_8360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object* v_traceArgs_8370_, lean_object* v_weakArgs_8371_, lean_object* v_libName_8372_, lean_object* v_libFile_8373_, lean_object* v_objs_8374_, lean_object* v_plugin_8375_, lean_object* v_linkDeps_8376_, lean_object* v_macosxDeploymentTarget_x3f_8377_, lean_object* v_libs_8378_, lean_object* v___y_8379_, lean_object* v___y_8380_, lean_object* v___y_8381_, lean_object* v___y_8382_, lean_object* v___y_8383_, lean_object* v___y_8384_, lean_object* v___y_8385_){
_start:
{
uint8_t v_plugin_boxed_8386_; uint8_t v_linkDeps_boxed_8387_; lean_object* v_res_8388_; 
v_plugin_boxed_8386_ = lean_unbox(v_plugin_8375_);
v_linkDeps_boxed_8387_ = lean_unbox(v_linkDeps_8376_);
v_res_8388_ = l_Lake_buildLeanSharedLib___lam__0(v_traceArgs_8370_, v_weakArgs_8371_, v_libName_8372_, v_libFile_8373_, v_objs_8374_, v_plugin_boxed_8386_, v_linkDeps_boxed_8387_, v_macosxDeploymentTarget_x3f_8377_, v_libs_8378_, v___y_8379_, v___y_8380_, v___y_8381_, v___y_8382_, v___y_8383_, v___y_8384_);
lean_dec_ref(v___y_8383_);
lean_dec(v___y_8382_);
lean_dec(v___y_8381_);
lean_dec(v___y_8380_);
return v_res_8388_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object* v_traceArgs_8389_, lean_object* v_weakArgs_8390_, lean_object* v_libName_8391_, lean_object* v_libFile_8392_, uint8_t v_plugin_8393_, uint8_t v_linkDeps_8394_, lean_object* v_macosxDeploymentTarget_x3f_8395_, lean_object* v_linkLibs_8396_, lean_object* v___x_8397_, lean_object* v_objs_8398_, lean_object* v___y_8399_, lean_object* v___y_8400_, lean_object* v___y_8401_, lean_object* v___y_8402_, lean_object* v___y_8403_, lean_object* v___y_8404_){
_start:
{
lean_object* v_trace_8406_; lean_object* v___x_8407_; lean_object* v___x_8408_; lean_object* v___f_8409_; lean_object* v___x_8410_; lean_object* v___x_8411_; lean_object* v___x_8412_; uint8_t v___x_8413_; lean_object* v___x_8414_; lean_object* v___x_8415_; 
v_trace_8406_ = lean_ctor_get(v___y_8404_, 1);
v___x_8407_ = lean_box(v_plugin_8393_);
v___x_8408_ = lean_box(v_linkDeps_8394_);
v___f_8409_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__0___boxed), 16, 8);
lean_closure_set(v___f_8409_, 0, v_traceArgs_8389_);
lean_closure_set(v___f_8409_, 1, v_weakArgs_8390_);
lean_closure_set(v___f_8409_, 2, v_libName_8391_);
lean_closure_set(v___f_8409_, 3, v_libFile_8392_);
lean_closure_set(v___f_8409_, 4, v_objs_8398_);
lean_closure_set(v___f_8409_, 5, v___x_8407_);
lean_closure_set(v___f_8409_, 6, v___x_8408_);
lean_closure_set(v___f_8409_, 7, v_macosxDeploymentTarget_x3f_8395_);
v___x_8410_ = ((lean_object*)(l_Lake_buildSharedLib___lam__1___closed__0));
v___x_8411_ = l_Lake_Job_collectArray___redArg(v_linkLibs_8396_, v___x_8410_);
v___x_8412_ = lean_unsigned_to_nat(0u);
v___x_8413_ = 0;
v___x_8414_ = l_Lake_Job_mapM___redArg(v___x_8397_, v___x_8411_, v___f_8409_, v___x_8412_, v___x_8413_, v___y_8399_, v___y_8400_, v___y_8401_, v___y_8402_, v___y_8403_, v_trace_8406_);
v___x_8415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8415_, 0, v___x_8414_);
lean_ctor_set(v___x_8415_, 1, v___y_8404_);
return v___x_8415_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1___boxed(lean_object** _args){
lean_object* v_traceArgs_8416_ = _args[0];
lean_object* v_weakArgs_8417_ = _args[1];
lean_object* v_libName_8418_ = _args[2];
lean_object* v_libFile_8419_ = _args[3];
lean_object* v_plugin_8420_ = _args[4];
lean_object* v_linkDeps_8421_ = _args[5];
lean_object* v_macosxDeploymentTarget_x3f_8422_ = _args[6];
lean_object* v_linkLibs_8423_ = _args[7];
lean_object* v___x_8424_ = _args[8];
lean_object* v_objs_8425_ = _args[9];
lean_object* v___y_8426_ = _args[10];
lean_object* v___y_8427_ = _args[11];
lean_object* v___y_8428_ = _args[12];
lean_object* v___y_8429_ = _args[13];
lean_object* v___y_8430_ = _args[14];
lean_object* v___y_8431_ = _args[15];
lean_object* v___y_8432_ = _args[16];
_start:
{
uint8_t v_plugin_boxed_8433_; uint8_t v_linkDeps_boxed_8434_; lean_object* v_res_8435_; 
v_plugin_boxed_8433_ = lean_unbox(v_plugin_8420_);
v_linkDeps_boxed_8434_ = lean_unbox(v_linkDeps_8421_);
v_res_8435_ = l_Lake_buildLeanSharedLib___lam__1(v_traceArgs_8416_, v_weakArgs_8417_, v_libName_8418_, v_libFile_8419_, v_plugin_boxed_8433_, v_linkDeps_boxed_8434_, v_macosxDeploymentTarget_x3f_8422_, v_linkLibs_8423_, v___x_8424_, v_objs_8425_, v___y_8426_, v___y_8427_, v___y_8428_, v___y_8429_, v___y_8430_, v___y_8431_);
lean_dec_ref(v___y_8430_);
lean_dec(v___y_8429_);
lean_dec(v___y_8428_);
lean_dec(v___y_8427_);
lean_dec_ref(v_linkLibs_8423_);
return v_res_8435_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object* v_libName_8436_, lean_object* v_libFile_8437_, lean_object* v_linkObjs_8438_, lean_object* v_linkLibs_8439_, lean_object* v_weakArgs_8440_, lean_object* v_traceArgs_8441_, uint8_t v_plugin_8442_, uint8_t v_linkDeps_8443_, lean_object* v_macosxDeploymentTarget_x3f_8444_, lean_object* v_a_8445_, lean_object* v_a_8446_, lean_object* v_a_8447_, lean_object* v_a_8448_, lean_object* v_a_8449_, lean_object* v_a_8450_){
_start:
{
lean_object* v___x_8452_; lean_object* v___x_8453_; lean_object* v___x_8454_; lean_object* v___f_8455_; lean_object* v___x_8456_; lean_object* v___x_8457_; lean_object* v___x_8458_; uint8_t v___x_8459_; lean_object* v___x_8460_; 
v___x_8452_ = l_Lake_instDataKindDynlib;
v___x_8453_ = lean_box(v_plugin_8442_);
v___x_8454_ = lean_box(v_linkDeps_8443_);
v___f_8455_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__1___boxed), 17, 9);
lean_closure_set(v___f_8455_, 0, v_traceArgs_8441_);
lean_closure_set(v___f_8455_, 1, v_weakArgs_8440_);
lean_closure_set(v___f_8455_, 2, v_libName_8436_);
lean_closure_set(v___f_8455_, 3, v_libFile_8437_);
lean_closure_set(v___f_8455_, 4, v___x_8453_);
lean_closure_set(v___f_8455_, 5, v___x_8454_);
lean_closure_set(v___f_8455_, 6, v_macosxDeploymentTarget_x3f_8444_);
lean_closure_set(v___f_8455_, 7, v_linkLibs_8439_);
lean_closure_set(v___f_8455_, 8, v___x_8452_);
v___x_8456_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8457_ = l_Lake_Job_collectArray___redArg(v_linkObjs_8438_, v___x_8456_);
v___x_8458_ = lean_unsigned_to_nat(0u);
v___x_8459_ = 1;
v___x_8460_ = l_Lake_Job_bindM___redArg(v___x_8452_, v___x_8457_, v___f_8455_, v___x_8458_, v___x_8459_, v_a_8445_, v_a_8446_, v_a_8447_, v_a_8448_, v_a_8449_, v_a_8450_);
return v___x_8460_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object* v_libName_8461_, lean_object* v_libFile_8462_, lean_object* v_linkObjs_8463_, lean_object* v_linkLibs_8464_, lean_object* v_weakArgs_8465_, lean_object* v_traceArgs_8466_, lean_object* v_plugin_8467_, lean_object* v_linkDeps_8468_, lean_object* v_macosxDeploymentTarget_x3f_8469_, lean_object* v_a_8470_, lean_object* v_a_8471_, lean_object* v_a_8472_, lean_object* v_a_8473_, lean_object* v_a_8474_, lean_object* v_a_8475_, lean_object* v_a_8476_){
_start:
{
uint8_t v_plugin_boxed_8477_; uint8_t v_linkDeps_boxed_8478_; lean_object* v_res_8479_; 
v_plugin_boxed_8477_ = lean_unbox(v_plugin_8467_);
v_linkDeps_boxed_8478_ = lean_unbox(v_linkDeps_8468_);
v_res_8479_ = l_Lake_buildLeanSharedLib(v_libName_8461_, v_libFile_8462_, v_linkObjs_8463_, v_linkLibs_8464_, v_weakArgs_8465_, v_traceArgs_8466_, v_plugin_boxed_8477_, v_linkDeps_boxed_8478_, v_macosxDeploymentTarget_x3f_8469_, v_a_8470_, v_a_8471_, v_a_8472_, v_a_8473_, v_a_8474_, v_a_8475_);
lean_dec_ref(v_a_8475_);
lean_dec_ref(v_a_8474_);
lean_dec(v_a_8473_);
lean_dec(v_a_8472_);
lean_dec(v_a_8471_);
lean_dec_ref(v_linkObjs_8463_);
return v_res_8479_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync___lam__0(lean_object* v_linkLibs_8480_, lean_object* v_linkObjs_8481_, lean_object* v_args_8482_, uint8_t v_sharedLean_8483_, lean_object* v_exeFile_8484_, lean_object* v___y_8485_, lean_object* v___y_8486_, lean_object* v___y_8487_, lean_object* v___y_8488_, lean_object* v___y_8489_, lean_object* v___y_8490_, lean_object* v___y_8491_){
_start:
{
lean_object* v_toContext_8493_; lean_object* v_lakeEnv_8494_; lean_object* v_lean_8495_; lean_object* v___x_8496_; 
v_toContext_8493_ = lean_ctor_get(v___y_8490_, 1);
v_lakeEnv_8494_ = lean_ctor_get(v_toContext_8493_, 0);
v_lean_8495_ = lean_ctor_get(v_lakeEnv_8494_, 1);
v___x_8496_ = l_Lake_mkLinkOrder___redArg(v_linkLibs_8480_, v___y_8491_);
if (lean_obj_tag(v___x_8496_) == 0)
{
lean_object* v_a_8497_; lean_object* v_a_8498_; lean_object* v_leanLibDir_8499_; lean_object* v_cc_8500_; lean_object* v_log_8501_; uint8_t v_action_8502_; uint8_t v_wantsRebuild_8503_; lean_object* v_trace_8504_; lean_object* v_buildTime_8505_; lean_object* v___x_8507_; uint8_t v_isShared_8508_; uint8_t v_isSharedCheck_8543_; 
v_a_8497_ = lean_ctor_get(v___x_8496_, 1);
lean_inc(v_a_8497_);
v_a_8498_ = lean_ctor_get(v___x_8496_, 0);
lean_inc(v_a_8498_);
lean_dec_ref_known(v___x_8496_, 2);
v_leanLibDir_8499_ = lean_ctor_get(v_lean_8495_, 3);
v_cc_8500_ = lean_ctor_get(v_lean_8495_, 14);
v_log_8501_ = lean_ctor_get(v_a_8497_, 0);
v_action_8502_ = lean_ctor_get_uint8(v_a_8497_, sizeof(void*)*3);
v_wantsRebuild_8503_ = lean_ctor_get_uint8(v_a_8497_, sizeof(void*)*3 + 1);
v_trace_8504_ = lean_ctor_get(v_a_8497_, 1);
v_buildTime_8505_ = lean_ctor_get(v_a_8497_, 2);
v_isSharedCheck_8543_ = !lean_is_exclusive(v_a_8497_);
if (v_isSharedCheck_8543_ == 0)
{
v___x_8507_ = v_a_8497_;
v_isShared_8508_ = v_isSharedCheck_8543_;
goto v_resetjp_8506_;
}
else
{
lean_inc(v_buildTime_8505_);
lean_inc(v_trace_8504_);
lean_inc(v_log_8501_);
lean_dec(v_a_8497_);
v___x_8507_ = lean_box(0);
v_isShared_8508_ = v_isSharedCheck_8543_;
goto v_resetjp_8506_;
}
v_resetjp_8506_:
{
lean_object* v___x_8509_; lean_object* v___x_8510_; lean_object* v___x_8511_; lean_object* v___x_8512_; lean_object* v___x_8513_; lean_object* v___x_8514_; lean_object* v___x_8515_; lean_object* v___x_8516_; lean_object* v___x_8517_; lean_object* v___x_8518_; 
v___x_8509_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_linkObjs_8481_, v_a_8498_);
lean_dec(v_a_8498_);
v___x_8510_ = l_Array_append___redArg(v___x_8509_, v_args_8482_);
v___x_8511_ = lean_unsigned_to_nat(2u);
v___x_8512_ = lean_mk_empty_array_with_capacity(v___x_8511_);
lean_dec_ref(v___x_8512_);
v___x_8513_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0);
lean_inc_ref(v_leanLibDir_8499_);
v___x_8514_ = lean_array_push(v___x_8513_, v_leanLibDir_8499_);
v___x_8515_ = l_Array_append___redArg(v___x_8510_, v___x_8514_);
lean_dec_ref(v___x_8514_);
v___x_8516_ = l_Lake_LeanInstall_ccLinkFlags(v_sharedLean_8483_, v_lean_8495_);
v___x_8517_ = l_Array_append___redArg(v___x_8515_, v___x_8516_);
lean_dec_ref(v___x_8516_);
lean_inc_ref(v_cc_8500_);
v___x_8518_ = l_Lake_compileExe(v_exeFile_8484_, v___x_8517_, v_cc_8500_, v___y_8485_, v_log_8501_);
lean_dec_ref(v___x_8517_);
if (lean_obj_tag(v___x_8518_) == 0)
{
lean_object* v_a_8519_; lean_object* v_a_8520_; lean_object* v___x_8522_; uint8_t v_isShared_8523_; uint8_t v_isSharedCheck_8530_; 
v_a_8519_ = lean_ctor_get(v___x_8518_, 0);
v_a_8520_ = lean_ctor_get(v___x_8518_, 1);
v_isSharedCheck_8530_ = !lean_is_exclusive(v___x_8518_);
if (v_isSharedCheck_8530_ == 0)
{
v___x_8522_ = v___x_8518_;
v_isShared_8523_ = v_isSharedCheck_8530_;
goto v_resetjp_8521_;
}
else
{
lean_inc(v_a_8520_);
lean_inc(v_a_8519_);
lean_dec(v___x_8518_);
v___x_8522_ = lean_box(0);
v_isShared_8523_ = v_isSharedCheck_8530_;
goto v_resetjp_8521_;
}
v_resetjp_8521_:
{
lean_object* v___x_8525_; 
if (v_isShared_8508_ == 0)
{
lean_ctor_set(v___x_8507_, 0, v_a_8520_);
v___x_8525_ = v___x_8507_;
goto v_reusejp_8524_;
}
else
{
lean_object* v_reuseFailAlloc_8529_; 
v_reuseFailAlloc_8529_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8529_, 0, v_a_8520_);
lean_ctor_set(v_reuseFailAlloc_8529_, 1, v_trace_8504_);
lean_ctor_set(v_reuseFailAlloc_8529_, 2, v_buildTime_8505_);
lean_ctor_set_uint8(v_reuseFailAlloc_8529_, sizeof(void*)*3, v_action_8502_);
lean_ctor_set_uint8(v_reuseFailAlloc_8529_, sizeof(void*)*3 + 1, v_wantsRebuild_8503_);
v___x_8525_ = v_reuseFailAlloc_8529_;
goto v_reusejp_8524_;
}
v_reusejp_8524_:
{
lean_object* v___x_8527_; 
if (v_isShared_8523_ == 0)
{
lean_ctor_set(v___x_8522_, 1, v___x_8525_);
v___x_8527_ = v___x_8522_;
goto v_reusejp_8526_;
}
else
{
lean_object* v_reuseFailAlloc_8528_; 
v_reuseFailAlloc_8528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8528_, 0, v_a_8519_);
lean_ctor_set(v_reuseFailAlloc_8528_, 1, v___x_8525_);
v___x_8527_ = v_reuseFailAlloc_8528_;
goto v_reusejp_8526_;
}
v_reusejp_8526_:
{
return v___x_8527_;
}
}
}
}
else
{
lean_object* v_a_8531_; lean_object* v_a_8532_; lean_object* v___x_8534_; uint8_t v_isShared_8535_; uint8_t v_isSharedCheck_8542_; 
v_a_8531_ = lean_ctor_get(v___x_8518_, 0);
v_a_8532_ = lean_ctor_get(v___x_8518_, 1);
v_isSharedCheck_8542_ = !lean_is_exclusive(v___x_8518_);
if (v_isSharedCheck_8542_ == 0)
{
v___x_8534_ = v___x_8518_;
v_isShared_8535_ = v_isSharedCheck_8542_;
goto v_resetjp_8533_;
}
else
{
lean_inc(v_a_8532_);
lean_inc(v_a_8531_);
lean_dec(v___x_8518_);
v___x_8534_ = lean_box(0);
v_isShared_8535_ = v_isSharedCheck_8542_;
goto v_resetjp_8533_;
}
v_resetjp_8533_:
{
lean_object* v___x_8537_; 
if (v_isShared_8508_ == 0)
{
lean_ctor_set(v___x_8507_, 0, v_a_8532_);
v___x_8537_ = v___x_8507_;
goto v_reusejp_8536_;
}
else
{
lean_object* v_reuseFailAlloc_8541_; 
v_reuseFailAlloc_8541_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8541_, 0, v_a_8532_);
lean_ctor_set(v_reuseFailAlloc_8541_, 1, v_trace_8504_);
lean_ctor_set(v_reuseFailAlloc_8541_, 2, v_buildTime_8505_);
lean_ctor_set_uint8(v_reuseFailAlloc_8541_, sizeof(void*)*3, v_action_8502_);
lean_ctor_set_uint8(v_reuseFailAlloc_8541_, sizeof(void*)*3 + 1, v_wantsRebuild_8503_);
v___x_8537_ = v_reuseFailAlloc_8541_;
goto v_reusejp_8536_;
}
v_reusejp_8536_:
{
lean_object* v___x_8539_; 
if (v_isShared_8535_ == 0)
{
lean_ctor_set(v___x_8534_, 1, v___x_8537_);
v___x_8539_ = v___x_8534_;
goto v_reusejp_8538_;
}
else
{
lean_object* v_reuseFailAlloc_8540_; 
v_reuseFailAlloc_8540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8540_, 0, v_a_8531_);
lean_ctor_set(v_reuseFailAlloc_8540_, 1, v___x_8537_);
v___x_8539_ = v_reuseFailAlloc_8540_;
goto v_reusejp_8538_;
}
v_reusejp_8538_:
{
return v___x_8539_;
}
}
}
}
}
}
else
{
lean_object* v_a_8544_; lean_object* v_a_8545_; lean_object* v___x_8547_; uint8_t v_isShared_8548_; uint8_t v_isSharedCheck_8552_; 
lean_dec(v___y_8485_);
lean_dec_ref(v_exeFile_8484_);
v_a_8544_ = lean_ctor_get(v___x_8496_, 0);
v_a_8545_ = lean_ctor_get(v___x_8496_, 1);
v_isSharedCheck_8552_ = !lean_is_exclusive(v___x_8496_);
if (v_isSharedCheck_8552_ == 0)
{
v___x_8547_ = v___x_8496_;
v_isShared_8548_ = v_isSharedCheck_8552_;
goto v_resetjp_8546_;
}
else
{
lean_inc(v_a_8545_);
lean_inc(v_a_8544_);
lean_dec(v___x_8496_);
v___x_8547_ = lean_box(0);
v_isShared_8548_ = v_isSharedCheck_8552_;
goto v_resetjp_8546_;
}
v_resetjp_8546_:
{
lean_object* v___x_8550_; 
if (v_isShared_8548_ == 0)
{
v___x_8550_ = v___x_8547_;
goto v_reusejp_8549_;
}
else
{
lean_object* v_reuseFailAlloc_8551_; 
v_reuseFailAlloc_8551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8551_, 0, v_a_8544_);
lean_ctor_set(v_reuseFailAlloc_8551_, 1, v_a_8545_);
v___x_8550_ = v_reuseFailAlloc_8551_;
goto v_reusejp_8549_;
}
v_reusejp_8549_:
{
return v___x_8550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync___lam__0___boxed(lean_object* v_linkLibs_8553_, lean_object* v_linkObjs_8554_, lean_object* v_args_8555_, lean_object* v_sharedLean_8556_, lean_object* v_exeFile_8557_, lean_object* v___y_8558_, lean_object* v___y_8559_, lean_object* v___y_8560_, lean_object* v___y_8561_, lean_object* v___y_8562_, lean_object* v___y_8563_, lean_object* v___y_8564_, lean_object* v___y_8565_){
_start:
{
uint8_t v_sharedLean_boxed_8566_; lean_object* v_res_8567_; 
v_sharedLean_boxed_8566_ = lean_unbox(v_sharedLean_8556_);
v_res_8567_ = l_Lake_buildLeanExeSync___lam__0(v_linkLibs_8553_, v_linkObjs_8554_, v_args_8555_, v_sharedLean_boxed_8566_, v_exeFile_8557_, v___y_8558_, v___y_8559_, v___y_8560_, v___y_8561_, v___y_8562_, v___y_8563_, v___y_8564_);
lean_dec_ref(v___y_8563_);
lean_dec(v___y_8562_);
lean_dec(v___y_8561_);
lean_dec(v___y_8560_);
lean_dec_ref(v___y_8559_);
lean_dec_ref(v_args_8555_);
lean_dec_ref(v_linkObjs_8554_);
lean_dec_ref(v_linkLibs_8553_);
return v_res_8567_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync(lean_object* v_exeFile_8568_, lean_object* v_linkObjs_8569_, lean_object* v_linkLibs_8570_, lean_object* v_args_8571_, uint8_t v_sharedLean_8572_, lean_object* v_macosxDeploymentTarget_x3f_8573_, lean_object* v_a_8574_, lean_object* v_a_8575_, lean_object* v_a_8576_, lean_object* v_a_8577_, lean_object* v_a_8578_, lean_object* v_a_8579_){
_start:
{
lean_object* v___y_8582_; lean_object* v___y_8583_; lean_object* v___y_8584_; lean_object* v___y_8585_; lean_object* v___y_8586_; lean_object* v___y_8587_; lean_object* v___y_8588_; lean_object* v_log_8612_; uint8_t v_action_8613_; uint8_t v_wantsRebuild_8614_; lean_object* v_trace_8615_; lean_object* v_buildTime_8616_; lean_object* v___x_8618_; uint8_t v_isShared_8619_; uint8_t v_isSharedCheck_8648_; 
v_log_8612_ = lean_ctor_get(v_a_8579_, 0);
v_action_8613_ = lean_ctor_get_uint8(v_a_8579_, sizeof(void*)*3);
v_wantsRebuild_8614_ = lean_ctor_get_uint8(v_a_8579_, sizeof(void*)*3 + 1);
v_trace_8615_ = lean_ctor_get(v_a_8579_, 1);
v_buildTime_8616_ = lean_ctor_get(v_a_8579_, 2);
v_isSharedCheck_8648_ = !lean_is_exclusive(v_a_8579_);
if (v_isSharedCheck_8648_ == 0)
{
v___x_8618_ = v_a_8579_;
v_isShared_8619_ = v_isSharedCheck_8648_;
goto v_resetjp_8617_;
}
else
{
lean_inc(v_buildTime_8616_);
lean_inc(v_trace_8615_);
lean_inc(v_log_8612_);
lean_dec(v_a_8579_);
v___x_8618_ = lean_box(0);
v_isShared_8619_ = v_isSharedCheck_8648_;
goto v_resetjp_8617_;
}
v___jp_8581_:
{
uint8_t v___x_8589_; uint8_t v___x_8590_; lean_object* v___x_8591_; lean_object* v___x_8592_; 
v___x_8589_ = 1;
v___x_8590_ = 0;
v___x_8591_ = l_System_FilePath_exeExtension;
v___x_8592_ = l_Lake_buildArtifactUnlessUpToDate(v_exeFile_8568_, v___y_8582_, v___x_8590_, v___x_8591_, v___x_8589_, v___x_8589_, v___x_8590_, v___y_8583_, v___y_8584_, v___y_8585_, v___y_8586_, v___y_8587_, v___y_8588_);
if (lean_obj_tag(v___x_8592_) == 0)
{
lean_object* v_a_8593_; lean_object* v_a_8594_; lean_object* v___x_8596_; uint8_t v_isShared_8597_; uint8_t v_isSharedCheck_8602_; 
v_a_8593_ = lean_ctor_get(v___x_8592_, 0);
v_a_8594_ = lean_ctor_get(v___x_8592_, 1);
v_isSharedCheck_8602_ = !lean_is_exclusive(v___x_8592_);
if (v_isSharedCheck_8602_ == 0)
{
v___x_8596_ = v___x_8592_;
v_isShared_8597_ = v_isSharedCheck_8602_;
goto v_resetjp_8595_;
}
else
{
lean_inc(v_a_8594_);
lean_inc(v_a_8593_);
lean_dec(v___x_8592_);
v___x_8596_ = lean_box(0);
v_isShared_8597_ = v_isSharedCheck_8602_;
goto v_resetjp_8595_;
}
v_resetjp_8595_:
{
lean_object* v_path_8598_; lean_object* v___x_8600_; 
v_path_8598_ = lean_ctor_get(v_a_8593_, 1);
lean_inc_ref(v_path_8598_);
lean_dec(v_a_8593_);
if (v_isShared_8597_ == 0)
{
lean_ctor_set(v___x_8596_, 0, v_path_8598_);
v___x_8600_ = v___x_8596_;
goto v_reusejp_8599_;
}
else
{
lean_object* v_reuseFailAlloc_8601_; 
v_reuseFailAlloc_8601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8601_, 0, v_path_8598_);
lean_ctor_set(v_reuseFailAlloc_8601_, 1, v_a_8594_);
v___x_8600_ = v_reuseFailAlloc_8601_;
goto v_reusejp_8599_;
}
v_reusejp_8599_:
{
return v___x_8600_;
}
}
}
else
{
lean_object* v_a_8603_; lean_object* v_a_8604_; lean_object* v___x_8606_; uint8_t v_isShared_8607_; uint8_t v_isSharedCheck_8611_; 
v_a_8603_ = lean_ctor_get(v___x_8592_, 0);
v_a_8604_ = lean_ctor_get(v___x_8592_, 1);
v_isSharedCheck_8611_ = !lean_is_exclusive(v___x_8592_);
if (v_isSharedCheck_8611_ == 0)
{
v___x_8606_ = v___x_8592_;
v_isShared_8607_ = v_isSharedCheck_8611_;
goto v_resetjp_8605_;
}
else
{
lean_inc(v_a_8604_);
lean_inc(v_a_8603_);
lean_dec(v___x_8592_);
v___x_8606_ = lean_box(0);
v_isShared_8607_ = v_isSharedCheck_8611_;
goto v_resetjp_8605_;
}
v_resetjp_8605_:
{
lean_object* v___x_8609_; 
if (v_isShared_8607_ == 0)
{
v___x_8609_ = v___x_8606_;
goto v_reusejp_8608_;
}
else
{
lean_object* v_reuseFailAlloc_8610_; 
v_reuseFailAlloc_8610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8610_, 0, v_a_8603_);
lean_ctor_set(v_reuseFailAlloc_8610_, 1, v_a_8604_);
v___x_8609_ = v_reuseFailAlloc_8610_;
goto v_reusejp_8608_;
}
v_reusejp_8608_:
{
return v___x_8609_;
}
}
}
}
v_resetjp_8617_:
{
lean_object* v_toBuildConfig_8620_; lean_object* v_leanTrace_8621_; lean_object* v___x_8622_; lean_object* v___x_8623_; lean_object* v___x_8624_; lean_object* v___x_8626_; 
v_toBuildConfig_8620_ = lean_ctor_get(v_a_8578_, 0);
v_leanTrace_8621_ = lean_ctor_get(v_a_8578_, 2);
lean_inc_ref(v_leanTrace_8621_);
v___x_8622_ = l_Lake_BuildTrace_mix(v_trace_8615_, v_leanTrace_8621_);
v___x_8623_ = l_Lake_platformTrace;
v___x_8624_ = l_Lake_BuildTrace_mix(v___x_8622_, v___x_8623_);
lean_inc(v_buildTime_8616_);
lean_inc_ref(v___x_8624_);
lean_inc_ref(v_log_8612_);
if (v_isShared_8619_ == 0)
{
lean_ctor_set(v___x_8618_, 1, v___x_8624_);
v___x_8626_ = v___x_8618_;
goto v_reusejp_8625_;
}
else
{
lean_object* v_reuseFailAlloc_8647_; 
v_reuseFailAlloc_8647_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8647_, 0, v_log_8612_);
lean_ctor_set(v_reuseFailAlloc_8647_, 1, v___x_8624_);
lean_ctor_set(v_reuseFailAlloc_8647_, 2, v_buildTime_8616_);
lean_ctor_set_uint8(v_reuseFailAlloc_8647_, sizeof(void*)*3, v_action_8613_);
lean_ctor_set_uint8(v_reuseFailAlloc_8647_, sizeof(void*)*3 + 1, v_wantsRebuild_8614_);
v___x_8626_ = v_reuseFailAlloc_8647_;
goto v_reusejp_8625_;
}
v_reusejp_8625_:
{
lean_object* v___y_8628_; lean_object* v_val_8629_; 
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_8573_) == 0)
{
lean_object* v_macosxDeploymentTarget_x3f_8642_; lean_object* v___x_8643_; lean_object* v___f_8644_; 
v_macosxDeploymentTarget_x3f_8642_ = lean_ctor_get(v_toBuildConfig_8620_, 3);
v___x_8643_ = lean_box(v_sharedLean_8572_);
lean_inc(v_macosxDeploymentTarget_x3f_8642_);
lean_inc_ref(v_exeFile_8568_);
lean_inc_ref(v_args_8571_);
lean_inc_ref(v_linkObjs_8569_);
lean_inc_ref(v_linkLibs_8570_);
v___f_8644_ = lean_alloc_closure((void*)(l_Lake_buildLeanExeSync___lam__0___boxed), 13, 6);
lean_closure_set(v___f_8644_, 0, v_linkLibs_8570_);
lean_closure_set(v___f_8644_, 1, v_linkObjs_8569_);
lean_closure_set(v___f_8644_, 2, v_args_8571_);
lean_closure_set(v___f_8644_, 3, v___x_8643_);
lean_closure_set(v___f_8644_, 4, v_exeFile_8568_);
lean_closure_set(v___f_8644_, 5, v_macosxDeploymentTarget_x3f_8642_);
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_8642_) == 1)
{
lean_object* v_val_8645_; 
lean_dec_ref(v___f_8644_);
lean_dec_ref(v___x_8626_);
v_val_8645_ = lean_ctor_get(v_macosxDeploymentTarget_x3f_8642_, 0);
lean_inc(v_val_8645_);
lean_inc_ref(v_macosxDeploymentTarget_x3f_8642_);
v___y_8628_ = v_macosxDeploymentTarget_x3f_8642_;
v_val_8629_ = v_val_8645_;
goto v___jp_8627_;
}
else
{
lean_dec_ref(v___x_8624_);
lean_dec(v_buildTime_8616_);
lean_dec_ref(v_log_8612_);
lean_dec_ref(v_args_8571_);
lean_dec_ref(v_linkLibs_8570_);
lean_dec_ref(v_linkObjs_8569_);
v___y_8582_ = v___f_8644_;
v___y_8583_ = v_a_8574_;
v___y_8584_ = v_a_8575_;
v___y_8585_ = v_a_8576_;
v___y_8586_ = v_a_8577_;
v___y_8587_ = v_a_8578_;
v___y_8588_ = v___x_8626_;
goto v___jp_8581_;
}
}
else
{
lean_object* v_val_8646_; 
lean_dec_ref(v___x_8626_);
v_val_8646_ = lean_ctor_get(v_macosxDeploymentTarget_x3f_8573_, 0);
lean_inc(v_val_8646_);
v___y_8628_ = v_macosxDeploymentTarget_x3f_8573_;
v_val_8629_ = v_val_8646_;
goto v___jp_8627_;
}
v___jp_8627_:
{
lean_object* v___x_8630_; lean_object* v___f_8631_; uint64_t v___x_8632_; uint64_t v___x_8633_; uint64_t v___x_8634_; lean_object* v___x_8635_; lean_object* v___x_8636_; lean_object* v___x_8637_; lean_object* v___x_8638_; lean_object* v___x_8639_; lean_object* v___x_8640_; lean_object* v___x_8641_; 
v___x_8630_ = lean_box(v_sharedLean_8572_);
lean_inc_ref(v_exeFile_8568_);
v___f_8631_ = lean_alloc_closure((void*)(l_Lake_buildLeanExeSync___lam__0___boxed), 13, 6);
lean_closure_set(v___f_8631_, 0, v_linkLibs_8570_);
lean_closure_set(v___f_8631_, 1, v_linkObjs_8569_);
lean_closure_set(v___f_8631_, 2, v_args_8571_);
lean_closure_set(v___f_8631_, 3, v___x_8630_);
lean_closure_set(v___f_8631_, 4, v_exeFile_8568_);
lean_closure_set(v___f_8631_, 5, v___y_8628_);
v___x_8632_ = l_Lake_Hash_nil;
v___x_8633_ = lean_string_hash(v_val_8629_);
v___x_8634_ = lean_uint64_mix_hash(v___x_8632_, v___x_8633_);
v___x_8635_ = ((lean_object*)(l_Lake_buildSharedLibSync___closed__0));
v___x_8636_ = lean_string_append(v___x_8635_, v_val_8629_);
lean_dec_ref(v_val_8629_);
v___x_8637_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_8638_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_8639_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_8639_, 0, v___x_8636_);
lean_ctor_set(v___x_8639_, 1, v___x_8637_);
lean_ctor_set(v___x_8639_, 2, v___x_8638_);
lean_ctor_set_uint64(v___x_8639_, sizeof(void*)*3, v___x_8634_);
v___x_8640_ = l_Lake_BuildTrace_mix(v___x_8624_, v___x_8639_);
v___x_8641_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_8641_, 0, v_log_8612_);
lean_ctor_set(v___x_8641_, 1, v___x_8640_);
lean_ctor_set(v___x_8641_, 2, v_buildTime_8616_);
lean_ctor_set_uint8(v___x_8641_, sizeof(void*)*3, v_action_8613_);
lean_ctor_set_uint8(v___x_8641_, sizeof(void*)*3 + 1, v_wantsRebuild_8614_);
v___y_8582_ = v___f_8631_;
v___y_8583_ = v_a_8574_;
v___y_8584_ = v_a_8575_;
v___y_8585_ = v_a_8576_;
v___y_8586_ = v_a_8577_;
v___y_8587_ = v_a_8578_;
v___y_8588_ = v___x_8641_;
goto v___jp_8581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync___boxed(lean_object* v_exeFile_8649_, lean_object* v_linkObjs_8650_, lean_object* v_linkLibs_8651_, lean_object* v_args_8652_, lean_object* v_sharedLean_8653_, lean_object* v_macosxDeploymentTarget_x3f_8654_, lean_object* v_a_8655_, lean_object* v_a_8656_, lean_object* v_a_8657_, lean_object* v_a_8658_, lean_object* v_a_8659_, lean_object* v_a_8660_, lean_object* v_a_8661_){
_start:
{
uint8_t v_sharedLean_boxed_8662_; lean_object* v_res_8663_; 
v_sharedLean_boxed_8662_ = lean_unbox(v_sharedLean_8653_);
v_res_8663_ = l_Lake_buildLeanExeSync(v_exeFile_8649_, v_linkObjs_8650_, v_linkLibs_8651_, v_args_8652_, v_sharedLean_boxed_8662_, v_macosxDeploymentTarget_x3f_8654_, v_a_8655_, v_a_8656_, v_a_8657_, v_a_8658_, v_a_8659_, v_a_8660_);
lean_dec_ref(v_a_8659_);
lean_dec(v_a_8658_);
lean_dec(v_a_8657_);
lean_dec(v_a_8656_);
return v_res_8663_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0(lean_object* v_traceArgs_8664_, lean_object* v_weakArgs_8665_, lean_object* v_exeFile_8666_, lean_object* v_objs_8667_, uint8_t v_sharedLean_8668_, lean_object* v_macosxDeploymentTarget_x3f_8669_, lean_object* v_libs_8670_, lean_object* v___y_8671_, lean_object* v___y_8672_, lean_object* v___y_8673_, lean_object* v___y_8674_, lean_object* v___y_8675_, lean_object* v___y_8676_){
_start:
{
uint64_t v___y_8679_; uint64_t v___x_8704_; lean_object* v___x_8705_; lean_object* v___x_8706_; uint8_t v___x_8707_; 
v___x_8704_ = l_Lake_Hash_nil;
v___x_8705_ = lean_unsigned_to_nat(0u);
v___x_8706_ = lean_array_get_size(v_traceArgs_8664_);
v___x_8707_ = lean_nat_dec_lt(v___x_8705_, v___x_8706_);
if (v___x_8707_ == 0)
{
v___y_8679_ = v___x_8704_;
goto v___jp_8678_;
}
else
{
size_t v___x_8708_; size_t v___x_8709_; uint64_t v___x_8710_; 
v___x_8708_ = ((size_t)0ULL);
v___x_8709_ = lean_usize_of_nat(v___x_8706_);
v___x_8710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Internal_buildLeanO_spec__1(v_traceArgs_8664_, v___x_8708_, v___x_8709_, v___x_8704_);
v___y_8679_ = v___x_8710_;
goto v___jp_8678_;
}
v___jp_8678_:
{
lean_object* v_log_8680_; uint8_t v_action_8681_; uint8_t v_wantsRebuild_8682_; lean_object* v_trace_8683_; lean_object* v_buildTime_8684_; lean_object* v___x_8686_; uint8_t v_isShared_8687_; uint8_t v_isSharedCheck_8703_; 
v_log_8680_ = lean_ctor_get(v___y_8676_, 0);
v_action_8681_ = lean_ctor_get_uint8(v___y_8676_, sizeof(void*)*3);
v_wantsRebuild_8682_ = lean_ctor_get_uint8(v___y_8676_, sizeof(void*)*3 + 1);
v_trace_8683_ = lean_ctor_get(v___y_8676_, 1);
v_buildTime_8684_ = lean_ctor_get(v___y_8676_, 2);
v_isSharedCheck_8703_ = !lean_is_exclusive(v___y_8676_);
if (v_isSharedCheck_8703_ == 0)
{
v___x_8686_ = v___y_8676_;
v_isShared_8687_ = v_isSharedCheck_8703_;
goto v_resetjp_8685_;
}
else
{
lean_inc(v_buildTime_8684_);
lean_inc(v_trace_8683_);
lean_inc(v_log_8680_);
lean_dec(v___y_8676_);
v___x_8686_ = lean_box(0);
v_isShared_8687_ = v_isSharedCheck_8703_;
goto v_resetjp_8685_;
}
v_resetjp_8685_:
{
lean_object* v___x_8688_; lean_object* v___x_8689_; lean_object* v___x_8690_; lean_object* v___x_8691_; lean_object* v___x_8692_; lean_object* v___x_8693_; lean_object* v___x_8694_; lean_object* v___x_8695_; lean_object* v___x_8696_; lean_object* v___x_8697_; lean_object* v___x_8699_; 
v___x_8688_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_8689_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_8690_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_8664_);
v___x_8691_ = lean_array_to_list(v_traceArgs_8664_);
v___x_8692_ = l_List_toString___at___00Lake_Internal_buildLeanO_spec__0(v___x_8691_);
lean_dec(v___x_8691_);
v___x_8693_ = lean_string_append(v___x_8690_, v___x_8692_);
lean_dec_ref(v___x_8692_);
v___x_8694_ = lean_string_append(v___x_8689_, v___x_8693_);
lean_dec_ref(v___x_8693_);
v___x_8695_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_8696_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_8696_, 0, v___x_8694_);
lean_ctor_set(v___x_8696_, 1, v___x_8688_);
lean_ctor_set(v___x_8696_, 2, v___x_8695_);
lean_ctor_set_uint64(v___x_8696_, sizeof(void*)*3, v___y_8679_);
v___x_8697_ = l_Lake_BuildTrace_mix(v_trace_8683_, v___x_8696_);
if (v_isShared_8687_ == 0)
{
lean_ctor_set(v___x_8686_, 1, v___x_8697_);
v___x_8699_ = v___x_8686_;
goto v_reusejp_8698_;
}
else
{
lean_object* v_reuseFailAlloc_8702_; 
v_reuseFailAlloc_8702_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8702_, 0, v_log_8680_);
lean_ctor_set(v_reuseFailAlloc_8702_, 1, v___x_8697_);
lean_ctor_set(v_reuseFailAlloc_8702_, 2, v_buildTime_8684_);
lean_ctor_set_uint8(v_reuseFailAlloc_8702_, sizeof(void*)*3, v_action_8681_);
lean_ctor_set_uint8(v_reuseFailAlloc_8702_, sizeof(void*)*3 + 1, v_wantsRebuild_8682_);
v___x_8699_ = v_reuseFailAlloc_8702_;
goto v_reusejp_8698_;
}
v_reusejp_8698_:
{
lean_object* v___x_8700_; lean_object* v___x_8701_; 
v___x_8700_ = l_Array_append___redArg(v_weakArgs_8665_, v_traceArgs_8664_);
lean_dec_ref(v_traceArgs_8664_);
v___x_8701_ = l_Lake_buildLeanExeSync(v_exeFile_8666_, v_objs_8667_, v_libs_8670_, v___x_8700_, v_sharedLean_8668_, v_macosxDeploymentTarget_x3f_8669_, v___y_8671_, v___y_8672_, v___y_8673_, v___y_8674_, v___y_8675_, v___x_8699_);
return v___x_8701_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object* v_traceArgs_8711_, lean_object* v_weakArgs_8712_, lean_object* v_exeFile_8713_, lean_object* v_objs_8714_, lean_object* v_sharedLean_8715_, lean_object* v_macosxDeploymentTarget_x3f_8716_, lean_object* v_libs_8717_, lean_object* v___y_8718_, lean_object* v___y_8719_, lean_object* v___y_8720_, lean_object* v___y_8721_, lean_object* v___y_8722_, lean_object* v___y_8723_, lean_object* v___y_8724_){
_start:
{
uint8_t v_sharedLean_boxed_8725_; lean_object* v_res_8726_; 
v_sharedLean_boxed_8725_ = lean_unbox(v_sharedLean_8715_);
v_res_8726_ = l_Lake_buildLeanExe___lam__0(v_traceArgs_8711_, v_weakArgs_8712_, v_exeFile_8713_, v_objs_8714_, v_sharedLean_boxed_8725_, v_macosxDeploymentTarget_x3f_8716_, v_libs_8717_, v___y_8718_, v___y_8719_, v___y_8720_, v___y_8721_, v___y_8722_, v___y_8723_);
lean_dec_ref(v___y_8722_);
lean_dec(v___y_8721_);
lean_dec(v___y_8720_);
lean_dec(v___y_8719_);
return v_res_8726_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object* v_traceArgs_8727_, lean_object* v_weakArgs_8728_, lean_object* v_exeFile_8729_, uint8_t v_sharedLean_8730_, lean_object* v_macosxDeploymentTarget_x3f_8731_, lean_object* v_linkLibs_8732_, lean_object* v___x_8733_, lean_object* v_objs_8734_, lean_object* v___y_8735_, lean_object* v___y_8736_, lean_object* v___y_8737_, lean_object* v___y_8738_, lean_object* v___y_8739_, lean_object* v___y_8740_){
_start:
{
lean_object* v_trace_8742_; lean_object* v___x_8743_; lean_object* v___f_8744_; lean_object* v___x_8745_; lean_object* v___x_8746_; lean_object* v___x_8747_; uint8_t v___x_8748_; lean_object* v___x_8749_; lean_object* v___x_8750_; 
v_trace_8742_ = lean_ctor_get(v___y_8740_, 1);
v___x_8743_ = lean_box(v_sharedLean_8730_);
v___f_8744_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__0___boxed), 14, 6);
lean_closure_set(v___f_8744_, 0, v_traceArgs_8727_);
lean_closure_set(v___f_8744_, 1, v_weakArgs_8728_);
lean_closure_set(v___f_8744_, 2, v_exeFile_8729_);
lean_closure_set(v___f_8744_, 3, v_objs_8734_);
lean_closure_set(v___f_8744_, 4, v___x_8743_);
lean_closure_set(v___f_8744_, 5, v_macosxDeploymentTarget_x3f_8731_);
v___x_8745_ = ((lean_object*)(l_Lake_buildSharedLib___lam__1___closed__0));
v___x_8746_ = l_Lake_Job_collectArray___redArg(v_linkLibs_8732_, v___x_8745_);
v___x_8747_ = lean_unsigned_to_nat(0u);
v___x_8748_ = 0;
v___x_8749_ = l_Lake_Job_mapM___redArg(v___x_8733_, v___x_8746_, v___f_8744_, v___x_8747_, v___x_8748_, v___y_8735_, v___y_8736_, v___y_8737_, v___y_8738_, v___y_8739_, v_trace_8742_);
v___x_8750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8750_, 0, v___x_8749_);
lean_ctor_set(v___x_8750_, 1, v___y_8740_);
return v___x_8750_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object* v_traceArgs_8751_, lean_object* v_weakArgs_8752_, lean_object* v_exeFile_8753_, lean_object* v_sharedLean_8754_, lean_object* v_macosxDeploymentTarget_x3f_8755_, lean_object* v_linkLibs_8756_, lean_object* v___x_8757_, lean_object* v_objs_8758_, lean_object* v___y_8759_, lean_object* v___y_8760_, lean_object* v___y_8761_, lean_object* v___y_8762_, lean_object* v___y_8763_, lean_object* v___y_8764_, lean_object* v___y_8765_){
_start:
{
uint8_t v_sharedLean_boxed_8766_; lean_object* v_res_8767_; 
v_sharedLean_boxed_8766_ = lean_unbox(v_sharedLean_8754_);
v_res_8767_ = l_Lake_buildLeanExe___lam__1(v_traceArgs_8751_, v_weakArgs_8752_, v_exeFile_8753_, v_sharedLean_boxed_8766_, v_macosxDeploymentTarget_x3f_8755_, v_linkLibs_8756_, v___x_8757_, v_objs_8758_, v___y_8759_, v___y_8760_, v___y_8761_, v___y_8762_, v___y_8763_, v___y_8764_);
lean_dec_ref(v___y_8763_);
lean_dec(v___y_8762_);
lean_dec(v___y_8761_);
lean_dec(v___y_8760_);
lean_dec_ref(v_linkLibs_8756_);
return v_res_8767_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object* v_exeFile_8768_, lean_object* v_linkObjs_8769_, lean_object* v_linkLibs_8770_, lean_object* v_weakArgs_8771_, lean_object* v_traceArgs_8772_, uint8_t v_sharedLean_8773_, lean_object* v_macosxDeploymentTarget_x3f_8774_, lean_object* v_a_8775_, lean_object* v_a_8776_, lean_object* v_a_8777_, lean_object* v_a_8778_, lean_object* v_a_8779_, lean_object* v_a_8780_){
_start:
{
lean_object* v___x_8782_; lean_object* v___x_8783_; lean_object* v___f_8784_; lean_object* v___x_8785_; lean_object* v___x_8786_; lean_object* v___x_8787_; uint8_t v___x_8788_; lean_object* v___x_8789_; 
v___x_8782_ = l_Lake_instDataKindFilePath;
v___x_8783_ = lean_box(v_sharedLean_8773_);
v___f_8784_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__1___boxed), 15, 7);
lean_closure_set(v___f_8784_, 0, v_traceArgs_8772_);
lean_closure_set(v___f_8784_, 1, v_weakArgs_8771_);
lean_closure_set(v___f_8784_, 2, v_exeFile_8768_);
lean_closure_set(v___f_8784_, 3, v___x_8783_);
lean_closure_set(v___f_8784_, 4, v_macosxDeploymentTarget_x3f_8774_);
lean_closure_set(v___f_8784_, 5, v_linkLibs_8770_);
lean_closure_set(v___f_8784_, 6, v___x_8782_);
v___x_8785_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8786_ = l_Lake_Job_collectArray___redArg(v_linkObjs_8769_, v___x_8785_);
v___x_8787_ = lean_unsigned_to_nat(0u);
v___x_8788_ = 1;
v___x_8789_ = l_Lake_Job_bindM___redArg(v___x_8782_, v___x_8786_, v___f_8784_, v___x_8787_, v___x_8788_, v_a_8775_, v_a_8776_, v_a_8777_, v_a_8778_, v_a_8779_, v_a_8780_);
return v___x_8789_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object* v_exeFile_8790_, lean_object* v_linkObjs_8791_, lean_object* v_linkLibs_8792_, lean_object* v_weakArgs_8793_, lean_object* v_traceArgs_8794_, lean_object* v_sharedLean_8795_, lean_object* v_macosxDeploymentTarget_x3f_8796_, lean_object* v_a_8797_, lean_object* v_a_8798_, lean_object* v_a_8799_, lean_object* v_a_8800_, lean_object* v_a_8801_, lean_object* v_a_8802_, lean_object* v_a_8803_){
_start:
{
uint8_t v_sharedLean_boxed_8804_; lean_object* v_res_8805_; 
v_sharedLean_boxed_8804_ = lean_unbox(v_sharedLean_8795_);
v_res_8805_ = l_Lake_buildLeanExe(v_exeFile_8790_, v_linkObjs_8791_, v_linkLibs_8792_, v_weakArgs_8793_, v_traceArgs_8794_, v_sharedLean_boxed_8804_, v_macosxDeploymentTarget_x3f_8796_, v_a_8797_, v_a_8798_, v_a_8799_, v_a_8800_, v_a_8801_, v_a_8802_);
lean_dec_ref(v_a_8802_);
lean_dec_ref(v_a_8801_);
lean_dec(v_a_8800_);
lean_dec(v_a_8799_);
lean_dec(v_a_8798_);
lean_dec_ref(v_linkObjs_8791_);
return v_res_8805_;
}
}
lean_object* runtime_initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Actions(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Common(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
