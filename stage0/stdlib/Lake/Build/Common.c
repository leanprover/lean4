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
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
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
extern lean_object* l_System_FilePath_exeExtension;
lean_object* l_Lake_compileExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_System_FilePath_walkDir(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(uint8_t, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_1938_; lean_object* v_log_1939_; uint8_t v_action_1940_; uint8_t v_wantsRebuild_1941_; lean_object* v_trace_1942_; lean_object* v_buildTime_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1954_; 
v___x_1938_ = lean_io_mono_ms_now();
v_log_1939_ = lean_ctor_get(v___y_1936_, 0);
v_action_1940_ = lean_ctor_get_uint8(v___y_1936_, sizeof(void*)*3);
v_wantsRebuild_1941_ = lean_ctor_get_uint8(v___y_1936_, sizeof(void*)*3 + 1);
v_trace_1942_ = lean_ctor_get(v___y_1936_, 1);
v_buildTime_1943_ = lean_ctor_get(v___y_1936_, 2);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___y_1936_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1945_ = v___y_1936_;
v_isShared_1946_ = v_isSharedCheck_1954_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_buildTime_1943_);
lean_inc(v_trace_1942_);
lean_inc(v_log_1939_);
lean_dec(v___y_1936_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1954_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1951_; 
v___x_1947_ = lean_nat_sub(v___x_1938_, v_val_1934_);
lean_dec(v___x_1938_);
v___x_1948_ = lean_box(0);
v___x_1949_ = lean_nat_add(v_buildTime_1943_, v___x_1947_);
lean_dec(v___x_1947_);
lean_dec(v_buildTime_1943_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 2, v___x_1949_);
v___x_1951_ = v___x_1945_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_log_1939_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v_trace_1942_);
lean_ctor_set(v_reuseFailAlloc_1953_, 2, v___x_1949_);
lean_ctor_set_uint8(v_reuseFailAlloc_1953_, sizeof(void*)*3, v_action_1940_);
lean_ctor_set_uint8(v_reuseFailAlloc_1953_, sizeof(void*)*3 + 1, v_wantsRebuild_1941_);
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
lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2005_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_1993_);
if (v_isShared_2000_ == 0)
{
v___x_2007_ = v___x_1999_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_log_1993_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_trace_1996_);
lean_ctor_set(v_reuseFailAlloc_2087_, 2, v_buildTime_1997_);
lean_ctor_set_uint8(v_reuseFailAlloc_2087_, sizeof(void*)*3 + 1, v_wantsRebuild_1995_);
v___x_2007_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
lean_object* v___x_2008_; lean_object* v_a_2010_; lean_object* v_a_2011_; 
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*3, v___x_2002_);
lean_inc_ref(v_a_1974_);
lean_inc(v_a_1973_);
lean_inc(v_a_1972_);
lean_inc(v_a_1971_);
v___x_2008_ = lean_apply_7(v_build_1968_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v___x_2007_, lean_box(0));
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2015_; lean_object* v_a_2016_; lean_object* v_log_2017_; uint8_t v_action_2018_; uint8_t v_wantsRebuild_2019_; lean_object* v_trace_2020_; lean_object* v_buildTime_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v_a_2015_ = lean_ctor_get(v___x_2008_, 1);
lean_inc(v_a_2015_);
v_a_2016_ = lean_ctor_get(v___x_2008_, 0);
lean_inc_n(v_a_2016_, 2);
lean_dec_ref_known(v___x_2008_, 2);
v_log_2017_ = lean_ctor_get(v_a_2015_, 0);
v_action_2018_ = lean_ctor_get_uint8(v_a_2015_, sizeof(void*)*3);
v_wantsRebuild_2019_ = lean_ctor_get_uint8(v_a_2015_, sizeof(void*)*3 + 1);
v_trace_2020_ = lean_ctor_get(v_a_2015_, 1);
v_buildTime_2021_ = lean_ctor_get(v_a_2015_, 2);
v___x_2022_ = lean_array_get_size(v_log_1993_);
lean_dec_ref(v_log_1993_);
v___x_2023_ = lean_array_get_size(v_log_2017_);
v___x_2024_ = l_Array_extract___redArg(v_log_2017_, v___x_2022_, v___x_2023_);
v___x_2025_ = lean_apply_1(v_inst_1965_, v_a_2016_);
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
lean_inc(v_a_2016_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 0, v_a_2016_);
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2016_);
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
v___x_2039_ = l_Lake_buildAction___redArg___lam__0(v___x_2005_, v___x_2038_, v_a_2015_);
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
lean_ctor_set(v___x_2042_, 0, v_a_2016_);
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2016_);
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
lean_inc(v_buildTime_2021_);
lean_inc_ref(v_trace_2020_);
lean_inc_ref(v_log_2017_);
lean_del_object(v___x_2029_);
lean_dec(v_a_2016_);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_a_2015_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; lean_object* v_unused_2066_; lean_object* v_unused_2067_; 
v_unused_2065_ = lean_ctor_get(v_a_2015_, 2);
lean_dec(v_unused_2065_);
v_unused_2066_ = lean_ctor_get(v_a_2015_, 1);
lean_dec(v_unused_2066_);
v_unused_2067_ = lean_ctor_get(v_a_2015_, 0);
lean_dec(v_unused_2067_);
v___x_2054_ = v_a_2015_;
v_isShared_2055_ = v_isSharedCheck_2064_;
goto v_resetjp_2053_;
}
else
{
lean_dec(v_a_2015_);
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
v___x_2060_ = lean_array_push(v_log_2017_, v___x_2059_);
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
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_trace_2020_);
lean_ctor_set(v_reuseFailAlloc_2063_, 2, v_buildTime_2021_);
lean_ctor_set_uint8(v_reuseFailAlloc_2063_, sizeof(void*)*3, v_action_2018_);
lean_ctor_set_uint8(v_reuseFailAlloc_2063_, sizeof(void*)*3 + 1, v_wantsRebuild_2019_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
v_a_2010_ = v___x_2023_;
v_a_2011_ = v___x_2062_;
goto v___jp_2009_;
}
}
}
}
}
else
{
lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2081_; 
lean_inc(v_buildTime_2021_);
lean_inc_ref(v_trace_2020_);
lean_inc_ref(v_log_2017_);
lean_dec(v_a_2016_);
lean_dec_ref(v___x_2004_);
v_isSharedCheck_2081_ = !lean_is_exclusive(v_a_2015_);
if (v_isSharedCheck_2081_ == 0)
{
lean_object* v_unused_2082_; lean_object* v_unused_2083_; lean_object* v_unused_2084_; 
v_unused_2082_ = lean_ctor_get(v_a_2015_, 2);
lean_dec(v_unused_2082_);
v_unused_2083_ = lean_ctor_get(v_a_2015_, 1);
lean_dec(v_unused_2083_);
v_unused_2084_ = lean_ctor_get(v_a_2015_, 0);
lean_dec(v_unused_2084_);
v___x_2071_ = v_a_2015_;
v_isShared_2072_ = v_isSharedCheck_2081_;
goto v_resetjp_2070_;
}
else
{
lean_dec(v_a_2015_);
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
v___x_2077_ = lean_array_push(v_log_2017_, v___x_2076_);
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
lean_ctor_set(v_reuseFailAlloc_2080_, 1, v_trace_2020_);
lean_ctor_set(v_reuseFailAlloc_2080_, 2, v_buildTime_2021_);
lean_ctor_set_uint8(v_reuseFailAlloc_2080_, sizeof(void*)*3, v_action_2018_);
lean_ctor_set_uint8(v_reuseFailAlloc_2080_, sizeof(void*)*3 + 1, v_wantsRebuild_2019_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
v_a_2010_ = v___x_2023_;
v_a_2011_ = v___x_2079_;
goto v___jp_2009_;
}
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v_a_2086_; 
lean_dec_ref(v___x_2004_);
lean_dec_ref(v_log_1993_);
lean_dec_ref(v_traceFile_1967_);
lean_dec_ref(v_inst_1965_);
v_a_2085_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2085_);
v_a_2086_ = lean_ctor_get(v___x_2008_, 1);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2008_, 2);
v_a_2010_ = v_a_2085_;
v_a_2011_ = v_a_2086_;
goto v___jp_2009_;
}
v___jp_2009_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v_a_2014_; 
v___x_2012_ = lean_box(0);
v___x_2013_ = l_Lake_buildAction___redArg___lam__0(v___x_2005_, v___x_2012_, v_a_2011_);
lean_dec(v___x_2005_);
v_a_2014_ = lean_ctor_get(v___x_2013_, 1);
lean_inc(v_a_2014_);
lean_dec_ref(v___x_2013_);
v_a_1978_ = v_a_2010_;
v_a_1979_ = v_a_2014_;
goto v___jp_1977_;
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
lean_object* v___x_2170_; 
lean_inc_ref(v_traceFile_2151_);
v___x_2170_ = l_Lake_readTraceFile(v_traceFile_2151_, v_log_2162_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v_a_2172_; lean_object* v___x_2174_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
v_a_2172_ = lean_ctor_get(v___x_2170_, 1);
lean_inc(v_a_2172_);
lean_dec_ref_known(v___x_2170_, 2);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 0, v_a_2172_);
v___x_2174_ = v___x_2168_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2172_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_trace_2165_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v_buildTime_2166_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*3, v_action_2163_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*3 + 1, v_wantsRebuild_2164_);
v___x_2174_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2175_; 
v___x_2175_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2147_, v_inst_2148_, v_info_2149_, v_depTrace_2150_, v_a_2171_, v_oldTrace_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v___x_2174_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2212_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
v_a_2177_ = lean_ctor_get(v___x_2175_, 1);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2179_ = v___x_2175_;
v_isShared_2180_ = v_isSharedCheck_2212_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_inc(v_a_2176_);
lean_dec(v___x_2175_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2212_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
uint8_t v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; 
v___x_2181_ = lean_unbox(v_a_2176_);
lean_dec(v_a_2176_);
v___x_2182_ = l_Lake_OutputStatus_ctorIdx(v___x_2181_);
v___x_2183_ = lean_obj_once(&l_Lake_OutputStatus_isUpToDate___closed__0, &l_Lake_OutputStatus_isUpToDate___closed__0_once, _init_l_Lake_OutputStatus_isUpToDate___closed__0);
v___x_2184_ = lean_nat_dec_eq(v___x_2182_, v___x_2183_);
lean_dec(v___x_2182_);
if (v___x_2184_ == 0)
{
uint8_t v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2188_; 
lean_dec_ref(v_a_2155_);
lean_dec_ref(v_build_2152_);
lean_dec_ref(v_traceFile_2151_);
v___x_2185_ = 1;
v___x_2186_ = lean_box(v___x_2185_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v___x_2186_);
v___x_2188_ = v___x_2179_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2186_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_a_2177_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
else
{
lean_object* v___f_2190_; lean_object* v___x_2191_; 
lean_del_object(v___x_2179_);
v___f_2190_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2191_ = l_Lake_buildAction___redArg(v___f_2190_, v_depTrace_2150_, v_traceFile_2151_, v_build_2152_, v_action_2153_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2177_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2201_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 1);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2201_ == 0)
{
lean_object* v_unused_2202_; 
v_unused_2202_ = lean_ctor_get(v___x_2191_, 0);
lean_dec(v_unused_2202_);
v___x_2194_ = v___x_2191_;
v_isShared_2195_ = v_isSharedCheck_2201_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2191_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2201_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
uint8_t v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2199_; 
v___x_2196_ = 0;
v___x_2197_ = lean_box(v___x_2196_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v___x_2197_);
v___x_2199_ = v___x_2194_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_a_2192_);
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
v_a_2203_ = lean_ctor_get(v___x_2191_, 0);
v_a_2204_ = lean_ctor_get(v___x_2191_, 1);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2191_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_inc(v_a_2203_);
lean_dec(v___x_2191_);
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
v_a_2213_ = lean_ctor_get(v___x_2175_, 0);
v_a_2214_ = lean_ctor_get(v___x_2175_, 1);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2175_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_inc(v_a_2213_);
lean_dec(v___x_2175_);
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
v_a_2223_ = lean_ctor_get(v___x_2170_, 0);
v_a_2224_ = lean_ctor_get(v___x_2170_, 1);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2226_ = v___x_2170_;
v_isShared_2227_ = v_isSharedCheck_2234_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_inc(v_a_2223_);
lean_dec(v___x_2170_);
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
lean_object* v___x_2277_; 
lean_inc_ref(v_traceFile_2258_);
v___x_2277_ = l_Lake_readTraceFile(v_traceFile_2258_, v_log_2269_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; lean_object* v_a_2279_; lean_object* v___x_2281_; 
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_a_2278_);
v_a_2279_ = lean_ctor_get(v___x_2277_, 1);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2277_, 2);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 0, v_a_2279_);
v___x_2281_ = v___x_2275_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2279_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v_trace_2272_);
lean_ctor_set(v_reuseFailAlloc_2329_, 2, v_buildTime_2273_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*3, v_action_2270_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*3 + 1, v_wantsRebuild_2271_);
v___x_2281_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
lean_object* v___x_2282_; 
v___x_2282_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2254_, v_inst_2255_, v_info_2256_, v_depTrace_2257_, v_a_2278_, v_oldTrace_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v___x_2281_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2319_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
v_a_2284_ = lean_ctor_get(v___x_2282_, 1);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2286_ = v___x_2282_;
v_isShared_2287_ = v_isSharedCheck_2319_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_inc(v_a_2283_);
lean_dec(v___x_2282_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2319_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
uint8_t v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; 
v___x_2288_ = lean_unbox(v_a_2283_);
lean_dec(v_a_2283_);
v___x_2289_ = l_Lake_OutputStatus_ctorIdx(v___x_2288_);
v___x_2290_ = lean_obj_once(&l_Lake_OutputStatus_isUpToDate___closed__0, &l_Lake_OutputStatus_isUpToDate___closed__0_once, _init_l_Lake_OutputStatus_isUpToDate___closed__0);
v___x_2291_ = lean_nat_dec_eq(v___x_2289_, v___x_2290_);
lean_dec(v___x_2289_);
if (v___x_2291_ == 0)
{
uint8_t v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2295_; 
lean_dec_ref(v_a_2262_);
lean_dec_ref(v_build_2259_);
lean_dec_ref(v_traceFile_2258_);
v___x_2292_ = 1;
v___x_2293_ = lean_box(v___x_2292_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v___x_2293_);
v___x_2295_ = v___x_2286_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2293_);
lean_ctor_set(v_reuseFailAlloc_2296_, 1, v_a_2284_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
else
{
lean_object* v___f_2297_; lean_object* v___x_2298_; 
lean_del_object(v___x_2286_);
v___f_2297_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2298_ = l_Lake_buildAction___redArg(v___f_2297_, v_depTrace_2257_, v_traceFile_2258_, v_build_2259_, v_action_2260_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2284_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2308_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 1);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2308_ == 0)
{
lean_object* v_unused_2309_; 
v_unused_2309_ = lean_ctor_get(v___x_2298_, 0);
lean_dec(v_unused_2309_);
v___x_2301_ = v___x_2298_;
v_isShared_2302_ = v_isSharedCheck_2308_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2298_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2308_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
uint8_t v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2306_; 
v___x_2303_ = 0;
v___x_2304_ = lean_box(v___x_2303_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v___x_2304_);
v___x_2306_ = v___x_2301_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_a_2299_);
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
v_a_2310_ = lean_ctor_get(v___x_2298_, 0);
v_a_2311_ = lean_ctor_get(v___x_2298_, 1);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2298_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_inc(v_a_2310_);
lean_dec(v___x_2298_);
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
v_a_2320_ = lean_ctor_get(v___x_2282_, 0);
v_a_2321_ = lean_ctor_get(v___x_2282_, 1);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2282_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_inc(v_a_2320_);
lean_dec(v___x_2282_);
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
v_a_2330_ = lean_ctor_get(v___x_2277_, 0);
v_a_2331_ = lean_ctor_get(v___x_2277_, 1);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2333_ = v___x_2277_;
v_isShared_2334_ = v_isSharedCheck_2341_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_inc(v_a_2330_);
lean_dec(v___x_2277_);
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
lean_object* v_a_2377_; lean_object* v_a_2378_; lean_object* v_log_2380_; uint8_t v_action_2381_; uint8_t v_wantsRebuild_2382_; lean_object* v_trace_2383_; lean_object* v_buildTime_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2423_; 
v_log_2380_ = lean_ctor_get(v_a_2374_, 0);
v_action_2381_ = lean_ctor_get_uint8(v_a_2374_, sizeof(void*)*3);
v_wantsRebuild_2382_ = lean_ctor_get_uint8(v_a_2374_, sizeof(void*)*3 + 1);
v_trace_2383_ = lean_ctor_get(v_a_2374_, 1);
v_buildTime_2384_ = lean_ctor_get(v_a_2374_, 2);
v_isSharedCheck_2423_ = !lean_is_exclusive(v_a_2374_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2386_ = v_a_2374_;
v_isShared_2387_ = v_isSharedCheck_2423_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_buildTime_2384_);
lean_inc(v_trace_2383_);
lean_inc(v_log_2380_);
lean_dec(v_a_2374_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2423_;
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
lean_object* v___x_2388_; 
lean_inc_ref(v_traceFile_2365_);
v___x_2388_ = l_Lake_readTraceFile(v_traceFile_2365_, v_log_2380_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v_a_2390_; lean_object* v___x_2392_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2389_);
v_a_2390_ = lean_ctor_get(v___x_2388_, 1);
lean_inc(v_a_2390_);
lean_dec_ref_known(v___x_2388_, 2);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 0, v_a_2390_);
v___x_2392_ = v___x_2386_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2390_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v_trace_2383_);
lean_ctor_set(v_reuseFailAlloc_2417_, 2, v_buildTime_2384_);
lean_ctor_set_uint8(v_reuseFailAlloc_2417_, sizeof(void*)*3, v_action_2381_);
lean_ctor_set_uint8(v_reuseFailAlloc_2417_, sizeof(void*)*3 + 1, v_wantsRebuild_2382_);
v___x_2392_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
lean_object* v___x_2393_; 
v___x_2393_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2361_, v_inst_2362_, v_info_2363_, v_depTrace_2364_, v_a_2389_, v_oldTrace_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v___x_2392_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2414_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
v_a_2395_ = lean_ctor_get(v___x_2393_, 1);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2397_ = v___x_2393_;
v_isShared_2398_ = v_isSharedCheck_2414_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_inc(v_a_2394_);
lean_dec(v___x_2393_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2414_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2399_; lean_object* v_a_2401_; uint8_t v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; uint8_t v___x_2408_; 
v___x_2399_ = lean_box(0);
v___x_2405_ = lean_unbox(v_a_2394_);
lean_dec(v_a_2394_);
v___x_2406_ = l_Lake_OutputStatus_ctorIdx(v___x_2405_);
v___x_2407_ = lean_obj_once(&l_Lake_OutputStatus_isUpToDate___closed__0, &l_Lake_OutputStatus_isUpToDate___closed__0_once, _init_l_Lake_OutputStatus_isUpToDate___closed__0);
v___x_2408_ = lean_nat_dec_eq(v___x_2406_, v___x_2407_);
lean_dec(v___x_2406_);
if (v___x_2408_ == 0)
{
lean_dec_ref(v_a_2369_);
lean_dec_ref(v_build_2366_);
lean_dec_ref(v_traceFile_2365_);
v_a_2401_ = v_a_2395_;
goto v___jp_2400_;
}
else
{
lean_object* v___f_2409_; lean_object* v___x_2410_; 
v___f_2409_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2410_ = l_Lake_buildAction___redArg(v___f_2409_, v_depTrace_2364_, v_traceFile_2365_, v_build_2366_, v_action_2367_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2395_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 1);
lean_inc(v_a_2411_);
lean_dec_ref_known(v___x_2410_, 2);
v_a_2401_ = v_a_2411_;
goto v___jp_2400_;
}
else
{
lean_object* v_a_2412_; lean_object* v_a_2413_; 
lean_del_object(v___x_2397_);
v_a_2412_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_a_2412_);
v_a_2413_ = lean_ctor_get(v___x_2410_, 1);
lean_inc(v_a_2413_);
lean_dec_ref_known(v___x_2410_, 2);
v_a_2377_ = v_a_2412_;
v_a_2378_ = v_a_2413_;
goto v___jp_2376_;
}
}
v___jp_2400_:
{
lean_object* v___x_2403_; 
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 1, v_a_2401_);
lean_ctor_set(v___x_2397_, 0, v___x_2399_);
v___x_2403_ = v___x_2397_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2399_);
lean_ctor_set(v_reuseFailAlloc_2404_, 1, v_a_2401_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
else
{
lean_object* v_a_2415_; lean_object* v_a_2416_; 
lean_dec_ref(v_a_2369_);
lean_dec_ref(v_build_2366_);
lean_dec_ref(v_traceFile_2365_);
v_a_2415_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2415_);
v_a_2416_ = lean_ctor_get(v___x_2393_, 1);
lean_inc(v_a_2416_);
lean_dec_ref_known(v___x_2393_, 2);
v_a_2377_ = v_a_2415_;
v_a_2378_ = v_a_2416_;
goto v___jp_2376_;
}
}
}
else
{
lean_object* v_a_2418_; lean_object* v_a_2419_; lean_object* v___x_2421_; 
lean_dec_ref(v_a_2369_);
lean_dec_ref(v_build_2366_);
lean_dec_ref(v_traceFile_2365_);
lean_dec(v_info_2363_);
lean_dec_ref(v_inst_2362_);
lean_dec_ref(v_inst_2361_);
v_a_2418_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2418_);
v_a_2419_ = lean_ctor_get(v___x_2388_, 1);
lean_inc(v_a_2419_);
lean_dec_ref_known(v___x_2388_, 2);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 0, v_a_2419_);
v___x_2421_ = v___x_2386_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2419_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_trace_2383_);
lean_ctor_set(v_reuseFailAlloc_2422_, 2, v_buildTime_2384_);
lean_ctor_set_uint8(v_reuseFailAlloc_2422_, sizeof(void*)*3, v_action_2381_);
lean_ctor_set_uint8(v_reuseFailAlloc_2422_, sizeof(void*)*3 + 1, v_wantsRebuild_2382_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
v_a_2377_ = v_a_2418_;
v_a_2378_ = v___x_2421_;
goto v___jp_2376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg___boxed(lean_object* v_inst_2424_, lean_object* v_inst_2425_, lean_object* v_info_2426_, lean_object* v_depTrace_2427_, lean_object* v_traceFile_2428_, lean_object* v_build_2429_, lean_object* v_action_2430_, lean_object* v_oldTrace_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
uint8_t v_action_boxed_2439_; lean_object* v_res_2440_; 
v_action_boxed_2439_ = lean_unbox(v_action_2430_);
v_res_2440_ = l_Lake_buildUnlessUpToDate___redArg(v_inst_2424_, v_inst_2425_, v_info_2426_, v_depTrace_2427_, v_traceFile_2428_, v_build_2429_, v_action_boxed_2439_, v_oldTrace_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
lean_dec_ref(v_a_2436_);
lean_dec(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_oldTrace_2431_);
lean_dec_ref(v_depTrace_2427_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate(lean_object* v_00_u03b9_2441_, lean_object* v_inst_2442_, lean_object* v_inst_2443_, lean_object* v_info_2444_, lean_object* v_depTrace_2445_, lean_object* v_traceFile_2446_, lean_object* v_build_2447_, uint8_t v_action_2448_, lean_object* v_oldTrace_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v_a_2458_; lean_object* v_a_2459_; lean_object* v_log_2461_; uint8_t v_action_2462_; uint8_t v_wantsRebuild_2463_; lean_object* v_trace_2464_; lean_object* v_buildTime_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2504_; 
v_log_2461_ = lean_ctor_get(v_a_2455_, 0);
v_action_2462_ = lean_ctor_get_uint8(v_a_2455_, sizeof(void*)*3);
v_wantsRebuild_2463_ = lean_ctor_get_uint8(v_a_2455_, sizeof(void*)*3 + 1);
v_trace_2464_ = lean_ctor_get(v_a_2455_, 1);
v_buildTime_2465_ = lean_ctor_get(v_a_2455_, 2);
v_isSharedCheck_2504_ = !lean_is_exclusive(v_a_2455_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2467_ = v_a_2455_;
v_isShared_2468_ = v_isSharedCheck_2504_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_buildTime_2465_);
lean_inc(v_trace_2464_);
lean_inc(v_log_2461_);
lean_dec(v_a_2455_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2504_;
goto v_resetjp_2466_;
}
v___jp_2457_:
{
lean_object* v___x_2460_; 
v___x_2460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2460_, 0, v_a_2458_);
lean_ctor_set(v___x_2460_, 1, v_a_2459_);
return v___x_2460_;
}
v_resetjp_2466_:
{
lean_object* v___x_2469_; 
lean_inc_ref(v_traceFile_2446_);
v___x_2469_ = l_Lake_readTraceFile(v_traceFile_2446_, v_log_2461_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v_a_2470_; lean_object* v_a_2471_; lean_object* v___x_2473_; 
v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_a_2470_);
v_a_2471_ = lean_ctor_get(v___x_2469_, 1);
lean_inc(v_a_2471_);
lean_dec_ref_known(v___x_2469_, 2);
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 0, v_a_2471_);
v___x_2473_ = v___x_2467_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_a_2471_);
lean_ctor_set(v_reuseFailAlloc_2498_, 1, v_trace_2464_);
lean_ctor_set(v_reuseFailAlloc_2498_, 2, v_buildTime_2465_);
lean_ctor_set_uint8(v_reuseFailAlloc_2498_, sizeof(void*)*3, v_action_2462_);
lean_ctor_set_uint8(v_reuseFailAlloc_2498_, sizeof(void*)*3 + 1, v_wantsRebuild_2463_);
v___x_2473_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
lean_object* v___x_2474_; 
v___x_2474_ = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(v_inst_2442_, v_inst_2443_, v_info_2444_, v_depTrace_2445_, v_a_2470_, v_oldTrace_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v___x_2473_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2495_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
v_a_2476_ = lean_ctor_get(v___x_2474_, 1);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2478_ = v___x_2474_;
v_isShared_2479_ = v_isSharedCheck_2495_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_inc(v_a_2475_);
lean_dec(v___x_2474_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2495_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2480_; lean_object* v_a_2482_; uint8_t v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; 
v___x_2480_ = lean_box(0);
v___x_2486_ = lean_unbox(v_a_2475_);
lean_dec(v_a_2475_);
v___x_2487_ = l_Lake_OutputStatus_ctorIdx(v___x_2486_);
v___x_2488_ = lean_obj_once(&l_Lake_OutputStatus_isUpToDate___closed__0, &l_Lake_OutputStatus_isUpToDate___closed__0_once, _init_l_Lake_OutputStatus_isUpToDate___closed__0);
v___x_2489_ = lean_nat_dec_eq(v___x_2487_, v___x_2488_);
lean_dec(v___x_2487_);
if (v___x_2489_ == 0)
{
lean_dec_ref(v_a_2450_);
lean_dec_ref(v_build_2447_);
lean_dec_ref(v_traceFile_2446_);
v_a_2482_ = v_a_2476_;
goto v___jp_2481_;
}
else
{
lean_object* v___f_2490_; lean_object* v___x_2491_; 
v___f_2490_ = ((lean_object*)(l_Lake_instToOutputJsonPUnit___closed__0));
v___x_2491_ = l_Lake_buildAction___redArg(v___f_2490_, v_depTrace_2445_, v_traceFile_2446_, v_build_2447_, v_action_2448_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2476_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 1);
lean_inc(v_a_2492_);
lean_dec_ref_known(v___x_2491_, 2);
v_a_2482_ = v_a_2492_;
goto v___jp_2481_;
}
else
{
lean_object* v_a_2493_; lean_object* v_a_2494_; 
lean_del_object(v___x_2478_);
v_a_2493_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_a_2493_);
v_a_2494_ = lean_ctor_get(v___x_2491_, 1);
lean_inc(v_a_2494_);
lean_dec_ref_known(v___x_2491_, 2);
v_a_2458_ = v_a_2493_;
v_a_2459_ = v_a_2494_;
goto v___jp_2457_;
}
}
v___jp_2481_:
{
lean_object* v___x_2484_; 
if (v_isShared_2479_ == 0)
{
lean_ctor_set(v___x_2478_, 1, v_a_2482_);
lean_ctor_set(v___x_2478_, 0, v___x_2480_);
v___x_2484_ = v___x_2478_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2480_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v_a_2482_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
else
{
lean_object* v_a_2496_; lean_object* v_a_2497_; 
lean_dec_ref(v_a_2450_);
lean_dec_ref(v_build_2447_);
lean_dec_ref(v_traceFile_2446_);
v_a_2496_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_a_2496_);
v_a_2497_ = lean_ctor_get(v___x_2474_, 1);
lean_inc(v_a_2497_);
lean_dec_ref_known(v___x_2474_, 2);
v_a_2458_ = v_a_2496_;
v_a_2459_ = v_a_2497_;
goto v___jp_2457_;
}
}
}
else
{
lean_object* v_a_2499_; lean_object* v_a_2500_; lean_object* v___x_2502_; 
lean_dec_ref(v_a_2450_);
lean_dec_ref(v_build_2447_);
lean_dec_ref(v_traceFile_2446_);
lean_dec(v_info_2444_);
lean_dec_ref(v_inst_2443_);
lean_dec_ref(v_inst_2442_);
v_a_2499_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_a_2499_);
v_a_2500_ = lean_ctor_get(v___x_2469_, 1);
lean_inc(v_a_2500_);
lean_dec_ref_known(v___x_2469_, 2);
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 0, v_a_2500_);
v___x_2502_ = v___x_2467_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2500_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v_trace_2464_);
lean_ctor_set(v_reuseFailAlloc_2503_, 2, v_buildTime_2465_);
lean_ctor_set_uint8(v_reuseFailAlloc_2503_, sizeof(void*)*3, v_action_2462_);
lean_ctor_set_uint8(v_reuseFailAlloc_2503_, sizeof(void*)*3 + 1, v_wantsRebuild_2463_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
v_a_2458_ = v_a_2499_;
v_a_2459_ = v___x_2502_;
goto v___jp_2457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___boxed(lean_object* v_00_u03b9_2505_, lean_object* v_inst_2506_, lean_object* v_inst_2507_, lean_object* v_info_2508_, lean_object* v_depTrace_2509_, lean_object* v_traceFile_2510_, lean_object* v_build_2511_, lean_object* v_action_2512_, lean_object* v_oldTrace_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_){
_start:
{
uint8_t v_action_boxed_2521_; lean_object* v_res_2522_; 
v_action_boxed_2521_ = lean_unbox(v_action_2512_);
v_res_2522_ = l_Lake_buildUnlessUpToDate(v_00_u03b9_2505_, v_inst_2506_, v_inst_2507_, v_info_2508_, v_depTrace_2509_, v_traceFile_2510_, v_build_2511_, v_action_boxed_2521_, v_oldTrace_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_);
lean_dec_ref(v_a_2518_);
lean_dec(v_a_2517_);
lean_dec(v_a_2516_);
lean_dec(v_a_2515_);
lean_dec_ref(v_oldTrace_2513_);
lean_dec_ref(v_depTrace_2509_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFileHash(lean_object* v_file_2524_, uint64_t v_hash_2525_){
_start:
{
lean_object* v___x_2527_; lean_object* v_hashFile_2528_; lean_object* v___x_2529_; 
v___x_2527_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
v_hashFile_2528_ = lean_string_append(v_file_2524_, v___x_2527_);
lean_inc_ref(v_hashFile_2528_);
v___x_2529_ = l_Lake_createParentDirs(v_hashFile_2528_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
lean_dec_ref_known(v___x_2529_, 1);
v___x_2530_ = l_Lake_lowerHexUInt64(v_hash_2525_);
v___x_2531_ = l_IO_FS_writeFile(v_hashFile_2528_, v___x_2530_);
lean_dec_ref(v___x_2530_);
lean_dec_ref(v_hashFile_2528_);
return v___x_2531_;
}
else
{
lean_dec_ref(v_hashFile_2528_);
return v___x_2529_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_writeFileHash___boxed(lean_object* v_file_2532_, lean_object* v_hash_2533_, lean_object* v_a_2534_){
_start:
{
uint64_t v_hash_boxed_2535_; lean_object* v_res_2536_; 
v_hash_boxed_2535_ = lean_unbox_uint64(v_hash_2533_);
lean_dec_ref(v_hash_2533_);
v_res_2536_ = l_Lake_writeFileHash(v_file_2532_, v_hash_boxed_2535_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object* v_file_2537_, uint8_t v_text_2538_){
_start:
{
lean_object* v___y_2541_; 
if (v_text_2538_ == 0)
{
lean_object* v___x_2553_; 
v___x_2553_ = l_Lake_computeBinFileHash(v_file_2537_);
v___y_2541_ = v___x_2553_;
goto v___jp_2540_;
}
else
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Lake_computeTextFileHash(v_file_2537_);
v___y_2541_ = v___x_2554_;
goto v___jp_2540_;
}
v___jp_2540_:
{
if (lean_obj_tag(v___y_2541_) == 0)
{
lean_object* v_a_2542_; uint64_t v___x_2543_; lean_object* v___x_2544_; 
v_a_2542_ = lean_ctor_get(v___y_2541_, 0);
lean_inc(v_a_2542_);
lean_dec_ref_known(v___y_2541_, 1);
v___x_2543_ = lean_unbox_uint64(v_a_2542_);
lean_dec(v_a_2542_);
v___x_2544_ = l_Lake_writeFileHash(v_file_2537_, v___x_2543_);
return v___x_2544_;
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec_ref(v_file_2537_);
v_a_2545_ = lean_ctor_get(v___y_2541_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___y_2541_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___y_2541_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___y_2541_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash___boxed(lean_object* v_file_2555_, lean_object* v_text_2556_, lean_object* v_a_2557_){
_start:
{
uint8_t v_text_boxed_2558_; lean_object* v_res_2559_; 
v_text_boxed_2558_ = lean_unbox(v_text_2556_);
v_res_2559_ = l_Lake_cacheFileHash(v_file_2555_, v_text_boxed_2558_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lake_clearFileHash(lean_object* v_file_2560_){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2562_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
v___x_2563_ = lean_string_append(v_file_2560_, v___x_2562_);
v___x_2564_ = l_Lake_removeFileIfExists(v___x_2563_);
lean_dec_ref(v___x_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_Lake_clearFileHash___boxed(lean_object* v_file_2565_, lean_object* v_a_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l_Lake_clearFileHash(v_file_2565_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg(lean_object* v_file_2568_, uint8_t v_text_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_){
_start:
{
lean_object* v_toBuildConfig_2573_; uint8_t v_trustHash_2574_; lean_object* v___x_2575_; lean_object* v_hashFile_2576_; uint8_t v___y_2578_; uint8_t v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2616_; 
v_toBuildConfig_2573_ = lean_ctor_get(v_a_2570_, 0);
v_trustHash_2574_ = lean_ctor_get_uint8(v_toBuildConfig_2573_, sizeof(void*)*4 + 1);
v___x_2575_ = ((lean_object*)(l_Lake_writeFileHash___closed__0));
lean_inc_ref(v_file_2568_);
v_hashFile_2576_ = lean_string_append(v_file_2568_, v___x_2575_);
if (v_trustHash_2574_ == 0)
{
v___y_2616_ = v_a_2571_;
goto v___jp_2615_;
}
else
{
lean_object* v___x_2629_; 
v___x_2629_ = l_Lake_Hash_load_x3f(v_hashFile_2576_);
if (lean_obj_tag(v___x_2629_) == 1)
{
lean_object* v_val_2630_; lean_object* v___x_2631_; 
lean_dec_ref(v_hashFile_2576_);
lean_dec_ref(v_file_2568_);
v_val_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_val_2630_);
lean_dec_ref_known(v___x_2629_, 1);
v___x_2631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2631_, 0, v_val_2630_);
lean_ctor_set(v___x_2631_, 1, v_a_2571_);
return v___x_2631_;
}
else
{
lean_dec(v___x_2629_);
v___y_2616_ = v_a_2571_;
goto v___jp_2615_;
}
}
v___jp_2577_:
{
if (lean_obj_tag(v___y_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v___x_2585_; 
v_a_2584_ = lean_ctor_get(v___y_2583_, 0);
lean_inc(v_a_2584_);
lean_dec_ref_known(v___y_2583_, 1);
lean_inc_ref(v_hashFile_2576_);
v___x_2585_ = l_Lake_createParentDirs(v_hashFile_2576_);
if (lean_obj_tag(v___x_2585_) == 0)
{
uint64_t v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
lean_dec_ref_known(v___x_2585_, 1);
v___x_2586_ = lean_unbox_uint64(v_a_2584_);
v___x_2587_ = l_Lake_lowerHexUInt64(v___x_2586_);
v___x_2588_ = l_IO_FS_writeFile(v_hashFile_2576_, v___x_2587_);
lean_dec_ref(v___x_2587_);
lean_dec_ref(v_hashFile_2576_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v___x_2589_; lean_object* v___x_2590_; 
lean_dec_ref_known(v___x_2588_, 1);
v___x_2589_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2589_, 0, v___y_2581_);
lean_ctor_set(v___x_2589_, 1, v___y_2582_);
lean_ctor_set(v___x_2589_, 2, v___y_2580_);
lean_ctor_set_uint8(v___x_2589_, sizeof(void*)*3, v___y_2578_);
lean_ctor_set_uint8(v___x_2589_, sizeof(void*)*3 + 1, v___y_2579_);
v___x_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2590_, 0, v_a_2584_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
return v___x_2590_;
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
lean_dec(v_a_2584_);
v_a_2591_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2591_);
lean_dec_ref_known(v___x_2588_, 1);
v___x_2592_ = lean_io_error_to_string(v_a_2591_);
v___x_2593_ = 3;
v___x_2594_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2594_, 0, v___x_2592_);
lean_ctor_set_uint8(v___x_2594_, sizeof(void*)*1, v___x_2593_);
v___x_2595_ = lean_array_get_size(v___y_2581_);
v___x_2596_ = lean_array_push(v___y_2581_, v___x_2594_);
v___x_2597_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2597_, 0, v___x_2596_);
lean_ctor_set(v___x_2597_, 1, v___y_2582_);
lean_ctor_set(v___x_2597_, 2, v___y_2580_);
lean_ctor_set_uint8(v___x_2597_, sizeof(void*)*3, v___y_2578_);
lean_ctor_set_uint8(v___x_2597_, sizeof(void*)*3 + 1, v___y_2579_);
v___x_2598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2595_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
return v___x_2598_;
}
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2600_; uint8_t v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
lean_dec(v_a_2584_);
lean_dec_ref(v_hashFile_2576_);
v_a_2599_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_a_2599_);
lean_dec_ref_known(v___x_2585_, 1);
v___x_2600_ = lean_io_error_to_string(v_a_2599_);
v___x_2601_ = 3;
v___x_2602_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2602_, 0, v___x_2600_);
lean_ctor_set_uint8(v___x_2602_, sizeof(void*)*1, v___x_2601_);
v___x_2603_ = lean_array_get_size(v___y_2581_);
v___x_2604_ = lean_array_push(v___y_2581_, v___x_2602_);
v___x_2605_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2605_, 0, v___x_2604_);
lean_ctor_set(v___x_2605_, 1, v___y_2582_);
lean_ctor_set(v___x_2605_, 2, v___y_2580_);
lean_ctor_set_uint8(v___x_2605_, sizeof(void*)*3, v___y_2578_);
lean_ctor_set_uint8(v___x_2605_, sizeof(void*)*3 + 1, v___y_2579_);
v___x_2606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2603_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
return v___x_2606_;
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2608_; uint8_t v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
lean_dec_ref(v_hashFile_2576_);
v_a_2607_ = lean_ctor_get(v___y_2583_, 0);
lean_inc(v_a_2607_);
lean_dec_ref_known(v___y_2583_, 1);
v___x_2608_ = lean_io_error_to_string(v_a_2607_);
v___x_2609_ = 3;
v___x_2610_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2610_, 0, v___x_2608_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*1, v___x_2609_);
v___x_2611_ = lean_array_get_size(v___y_2581_);
v___x_2612_ = lean_array_push(v___y_2581_, v___x_2610_);
v___x_2613_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2613_, 0, v___x_2612_);
lean_ctor_set(v___x_2613_, 1, v___y_2582_);
lean_ctor_set(v___x_2613_, 2, v___y_2580_);
lean_ctor_set_uint8(v___x_2613_, sizeof(void*)*3, v___y_2578_);
lean_ctor_set_uint8(v___x_2613_, sizeof(void*)*3 + 1, v___y_2579_);
v___x_2614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2611_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
return v___x_2614_;
}
}
v___jp_2615_:
{
if (v_text_2569_ == 0)
{
lean_object* v_log_2617_; uint8_t v_action_2618_; uint8_t v_wantsRebuild_2619_; lean_object* v_trace_2620_; lean_object* v_buildTime_2621_; lean_object* v___x_2622_; 
v_log_2617_ = lean_ctor_get(v___y_2616_, 0);
lean_inc_ref(v_log_2617_);
v_action_2618_ = lean_ctor_get_uint8(v___y_2616_, sizeof(void*)*3);
v_wantsRebuild_2619_ = lean_ctor_get_uint8(v___y_2616_, sizeof(void*)*3 + 1);
v_trace_2620_ = lean_ctor_get(v___y_2616_, 1);
lean_inc_ref(v_trace_2620_);
v_buildTime_2621_ = lean_ctor_get(v___y_2616_, 2);
lean_inc(v_buildTime_2621_);
lean_dec_ref(v___y_2616_);
v___x_2622_ = l_Lake_computeBinFileHash(v_file_2568_);
lean_dec_ref(v_file_2568_);
v___y_2578_ = v_action_2618_;
v___y_2579_ = v_wantsRebuild_2619_;
v___y_2580_ = v_buildTime_2621_;
v___y_2581_ = v_log_2617_;
v___y_2582_ = v_trace_2620_;
v___y_2583_ = v___x_2622_;
goto v___jp_2577_;
}
else
{
lean_object* v_log_2623_; uint8_t v_action_2624_; uint8_t v_wantsRebuild_2625_; lean_object* v_trace_2626_; lean_object* v_buildTime_2627_; lean_object* v___x_2628_; 
v_log_2623_ = lean_ctor_get(v___y_2616_, 0);
lean_inc_ref(v_log_2623_);
v_action_2624_ = lean_ctor_get_uint8(v___y_2616_, sizeof(void*)*3);
v_wantsRebuild_2625_ = lean_ctor_get_uint8(v___y_2616_, sizeof(void*)*3 + 1);
v_trace_2626_ = lean_ctor_get(v___y_2616_, 1);
lean_inc_ref(v_trace_2626_);
v_buildTime_2627_ = lean_ctor_get(v___y_2616_, 2);
lean_inc(v_buildTime_2627_);
lean_dec_ref(v___y_2616_);
v___x_2628_ = l_Lake_computeTextFileHash(v_file_2568_);
lean_dec_ref(v_file_2568_);
v___y_2578_ = v_action_2624_;
v___y_2579_ = v_wantsRebuild_2625_;
v___y_2580_ = v_buildTime_2627_;
v___y_2581_ = v_log_2623_;
v___y_2582_ = v_trace_2626_;
v___y_2583_ = v___x_2628_;
goto v___jp_2577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg___boxed(lean_object* v_file_2632_, lean_object* v_text_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_){
_start:
{
uint8_t v_text_boxed_2637_; lean_object* v_res_2638_; 
v_text_boxed_2637_ = lean_unbox(v_text_2633_);
v_res_2638_ = l_Lake_fetchFileHash___redArg(v_file_2632_, v_text_boxed_2637_, v_a_2634_, v_a_2635_);
lean_dec_ref(v_a_2634_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash(lean_object* v_file_2639_, uint8_t v_text_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Lake_fetchFileHash___redArg(v_file_2639_, v_text_2640_, v_a_2645_, v_a_2646_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___boxed(lean_object* v_file_2649_, lean_object* v_text_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_){
_start:
{
uint8_t v_text_boxed_2658_; lean_object* v_res_2659_; 
v_text_boxed_2658_ = lean_unbox(v_text_2650_);
v_res_2659_ = l_Lake_fetchFileHash(v_file_2649_, v_text_boxed_2658_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_);
lean_dec_ref(v_a_2655_);
lean_dec(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg(lean_object* v_file_2660_, uint8_t v_text_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_){
_start:
{
lean_object* v___x_2665_; 
lean_inc_ref(v_file_2660_);
v___x_2665_ = l_Lake_fetchFileHash___redArg(v_file_2660_, v_text_2661_, v_a_2662_, v_a_2663_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2704_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 1);
v_a_2667_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2669_ = v___x_2665_;
v_isShared_2670_ = v_isSharedCheck_2704_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2666_);
lean_inc(v_a_2667_);
lean_dec(v___x_2665_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2704_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v_log_2671_; uint8_t v_action_2672_; uint8_t v_wantsRebuild_2673_; lean_object* v_trace_2674_; lean_object* v_buildTime_2675_; lean_object* v___x_2676_; 
v_log_2671_ = lean_ctor_get(v_a_2666_, 0);
v_action_2672_ = lean_ctor_get_uint8(v_a_2666_, sizeof(void*)*3);
v_wantsRebuild_2673_ = lean_ctor_get_uint8(v_a_2666_, sizeof(void*)*3 + 1);
v_trace_2674_ = lean_ctor_get(v_a_2666_, 1);
v_buildTime_2675_ = lean_ctor_get(v_a_2666_, 2);
v___x_2676_ = lean_io_metadata(v_file_2660_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; lean_object* v_modified_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; uint64_t v___x_2681_; lean_object* v___x_2683_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___x_2676_, 1);
v_modified_2678_ = lean_ctor_get(v_a_2677_, 1);
lean_inc_ref(v_modified_2678_);
lean_dec(v_a_2677_);
v___x_2679_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_2680_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_2680_, 0, v_file_2660_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
lean_ctor_set(v___x_2680_, 2, v_modified_2678_);
v___x_2681_ = lean_unbox_uint64(v_a_2667_);
lean_dec(v_a_2667_);
lean_ctor_set_uint64(v___x_2680_, sizeof(void*)*3, v___x_2681_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v___x_2680_);
v___x_2683_ = v___x_2669_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2680_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_a_2666_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
else
{
lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2700_; 
lean_inc(v_buildTime_2675_);
lean_inc_ref(v_trace_2674_);
lean_inc_ref(v_log_2671_);
lean_dec(v_a_2667_);
lean_dec_ref(v_file_2660_);
v_isSharedCheck_2700_ = !lean_is_exclusive(v_a_2666_);
if (v_isSharedCheck_2700_ == 0)
{
lean_object* v_unused_2701_; lean_object* v_unused_2702_; lean_object* v_unused_2703_; 
v_unused_2701_ = lean_ctor_get(v_a_2666_, 2);
lean_dec(v_unused_2701_);
v_unused_2702_ = lean_ctor_get(v_a_2666_, 1);
lean_dec(v_unused_2702_);
v_unused_2703_ = lean_ctor_get(v_a_2666_, 0);
lean_dec(v_unused_2703_);
v___x_2686_ = v_a_2666_;
v_isShared_2687_ = v_isSharedCheck_2700_;
goto v_resetjp_2685_;
}
else
{
lean_dec(v_a_2666_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2700_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v_a_2688_; lean_object* v___x_2689_; uint8_t v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2695_; 
v_a_2688_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2688_);
lean_dec_ref_known(v___x_2676_, 1);
v___x_2689_ = lean_io_error_to_string(v_a_2688_);
v___x_2690_ = 3;
v___x_2691_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2691_, 0, v___x_2689_);
lean_ctor_set_uint8(v___x_2691_, sizeof(void*)*1, v___x_2690_);
v___x_2692_ = lean_array_get_size(v_log_2671_);
v___x_2693_ = lean_array_push(v_log_2671_, v___x_2691_);
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v___x_2693_);
v___x_2695_ = v___x_2686_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2693_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v_trace_2674_);
lean_ctor_set(v_reuseFailAlloc_2699_, 2, v_buildTime_2675_);
lean_ctor_set_uint8(v_reuseFailAlloc_2699_, sizeof(void*)*3, v_action_2672_);
lean_ctor_set_uint8(v_reuseFailAlloc_2699_, sizeof(void*)*3 + 1, v_wantsRebuild_2673_);
v___x_2695_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
lean_object* v___x_2697_; 
if (v_isShared_2670_ == 0)
{
lean_ctor_set_tag(v___x_2669_, 1);
lean_ctor_set(v___x_2669_, 1, v___x_2695_);
lean_ctor_set(v___x_2669_, 0, v___x_2692_);
v___x_2697_ = v___x_2669_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2692_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v___x_2695_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
}
}
else
{
lean_object* v_a_2705_; lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_dec_ref(v_file_2660_);
v_a_2705_ = lean_ctor_get(v___x_2665_, 0);
v_a_2706_ = lean_ctor_get(v___x_2665_, 1);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2665_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_inc(v_a_2705_);
lean_dec(v___x_2665_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2705_);
lean_ctor_set(v_reuseFailAlloc_2712_, 1, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg___boxed(lean_object* v_file_2714_, lean_object* v_text_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_){
_start:
{
uint8_t v_text_boxed_2719_; lean_object* v_res_2720_; 
v_text_boxed_2719_ = lean_unbox(v_text_2715_);
v_res_2720_ = l_Lake_fetchFileTrace___redArg(v_file_2714_, v_text_boxed_2719_, v_a_2716_, v_a_2717_);
lean_dec_ref(v_a_2716_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object* v_file_2721_, uint8_t v_text_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_){
_start:
{
lean_object* v___x_2730_; 
v___x_2730_ = l_Lake_fetchFileTrace___redArg(v_file_2721_, v_text_2722_, v_a_2727_, v_a_2728_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object* v_file_2731_, lean_object* v_text_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_){
_start:
{
uint8_t v_text_boxed_2740_; lean_object* v_res_2741_; 
v_text_boxed_2740_ = lean_unbox(v_text_2732_);
v_res_2741_ = l_Lake_fetchFileTrace(v_file_2731_, v_text_boxed_2740_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_);
lean_dec_ref(v_a_2737_);
lean_dec(v_a_2736_);
lean_dec(v_a_2735_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(lean_object* v_val_2742_, lean_object* v_a_x3f_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v___x_2746_; lean_object* v_log_2747_; uint8_t v_action_2748_; uint8_t v_wantsRebuild_2749_; lean_object* v_trace_2750_; lean_object* v_buildTime_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2762_; 
v___x_2746_ = lean_io_mono_ms_now();
v_log_2747_ = lean_ctor_get(v___y_2744_, 0);
v_action_2748_ = lean_ctor_get_uint8(v___y_2744_, sizeof(void*)*3);
v_wantsRebuild_2749_ = lean_ctor_get_uint8(v___y_2744_, sizeof(void*)*3 + 1);
v_trace_2750_ = lean_ctor_get(v___y_2744_, 1);
v_buildTime_2751_ = lean_ctor_get(v___y_2744_, 2);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___y_2744_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2753_ = v___y_2744_;
v_isShared_2754_ = v_isSharedCheck_2762_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_buildTime_2751_);
lean_inc(v_trace_2750_);
lean_inc(v_log_2747_);
lean_dec(v___y_2744_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2762_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2759_; 
v___x_2755_ = lean_nat_sub(v___x_2746_, v_val_2742_);
lean_dec(v___x_2746_);
v___x_2756_ = lean_box(0);
v___x_2757_ = lean_nat_add(v_buildTime_2751_, v___x_2755_);
lean_dec(v___x_2755_);
lean_dec(v_buildTime_2751_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 2, v___x_2757_);
v___x_2759_ = v___x_2753_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_log_2747_);
lean_ctor_set(v_reuseFailAlloc_2761_, 1, v_trace_2750_);
lean_ctor_set(v_reuseFailAlloc_2761_, 2, v___x_2757_);
lean_ctor_set_uint8(v_reuseFailAlloc_2761_, sizeof(void*)*3, v_action_2748_);
lean_ctor_set_uint8(v_reuseFailAlloc_2761_, sizeof(void*)*3 + 1, v_wantsRebuild_2749_);
v___x_2759_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
lean_object* v___x_2760_; 
v___x_2760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2756_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
return v___x_2760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0___boxed(lean_object* v_val_2763_, lean_object* v_a_x3f_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v_val_2763_, v_a_x3f_2764_, v___y_2765_);
lean_dec(v_a_x3f_2764_);
lean_dec(v_val_2763_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(lean_object* v_build_2768_, lean_object* v_file_2769_, lean_object* v_a_2770_, lean_object* v_depTrace_2771_, lean_object* v_traceFile_2772_, uint8_t v_action_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_){
_start:
{
lean_object* v_a_2781_; lean_object* v_a_2782_; lean_object* v_log_2785_; uint8_t v_action_2786_; uint8_t v_wantsRebuild_2787_; lean_object* v_trace_2788_; lean_object* v_buildTime_2789_; lean_object* v_toBuildConfig_2795_; lean_object* v_log_2796_; uint8_t v_action_2797_; uint8_t v_wantsRebuild_2798_; lean_object* v_trace_2799_; lean_object* v_buildTime_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2923_; 
v_toBuildConfig_2795_ = lean_ctor_get(v_a_2777_, 0);
v_log_2796_ = lean_ctor_get(v_a_2778_, 0);
v_action_2797_ = lean_ctor_get_uint8(v_a_2778_, sizeof(void*)*3);
v_wantsRebuild_2798_ = lean_ctor_get_uint8(v_a_2778_, sizeof(void*)*3 + 1);
v_trace_2799_ = lean_ctor_get(v_a_2778_, 1);
v_buildTime_2800_ = lean_ctor_get(v_a_2778_, 2);
v_isSharedCheck_2923_ = !lean_is_exclusive(v_a_2778_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2802_ = v_a_2778_;
v_isShared_2803_ = v_isSharedCheck_2923_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_buildTime_2800_);
lean_inc(v_trace_2799_);
lean_inc(v_log_2796_);
lean_dec(v_a_2778_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2923_;
goto v_resetjp_2801_;
}
v___jp_2780_:
{
lean_object* v___x_2783_; 
v___x_2783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2783_, 0, v_a_2781_);
lean_ctor_set(v___x_2783_, 1, v_a_2782_);
return v___x_2783_;
}
v___jp_2784_:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2790_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_2791_ = lean_array_get_size(v_log_2785_);
v___x_2792_ = lean_array_push(v_log_2785_, v___x_2790_);
v___x_2793_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
lean_ctor_set(v___x_2793_, 1, v_trace_2788_);
lean_ctor_set(v___x_2793_, 2, v_buildTime_2789_);
lean_ctor_set_uint8(v___x_2793_, sizeof(void*)*3, v_action_2786_);
lean_ctor_set_uint8(v___x_2793_, sizeof(void*)*3 + 1, v_wantsRebuild_2787_);
v___x_2794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2791_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
return v___x_2794_;
}
v_resetjp_2801_:
{
uint8_t v_noBuild_2804_; uint8_t v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v_noBuild_2804_ = lean_ctor_get_uint8(v_toBuildConfig_2795_, sizeof(void*)*4 + 2);
v___x_2805_ = l_Lake_JobAction_merge(v_action_2797_, v_action_2773_);
v___x_2806_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_2772_);
v___x_2807_ = l_System_FilePath_addExtension(v_traceFile_2772_, v___x_2806_);
if (v_noBuild_2804_ == 0)
{
lean_object* v___x_2808_; lean_object* v___x_2810_; 
v___x_2808_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_2796_);
if (v_isShared_2803_ == 0)
{
v___x_2810_ = v___x_2802_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_log_2796_);
lean_ctor_set(v_reuseFailAlloc_2907_, 1, v_trace_2799_);
lean_ctor_set(v_reuseFailAlloc_2907_, 2, v_buildTime_2800_);
lean_ctor_set_uint8(v_reuseFailAlloc_2907_, sizeof(void*)*3 + 1, v_wantsRebuild_2798_);
v___x_2810_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
lean_object* v___x_2811_; lean_object* v_a_2813_; lean_object* v_a_2814_; 
lean_ctor_set_uint8(v___x_2810_, sizeof(void*)*3, v___x_2805_);
lean_inc_ref(v_a_2777_);
lean_inc(v_a_2776_);
lean_inc(v_a_2775_);
lean_inc(v_a_2774_);
v___x_2811_ = lean_apply_7(v_build_2768_, v_a_2770_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v___x_2810_, lean_box(0));
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2818_; lean_object* v_log_2819_; uint8_t v_action_2820_; uint8_t v_wantsRebuild_2821_; lean_object* v_trace_2822_; lean_object* v_buildTime_2823_; lean_object* v___x_2824_; 
v_a_2818_ = lean_ctor_get(v___x_2811_, 1);
lean_inc(v_a_2818_);
lean_dec_ref_known(v___x_2811_, 2);
v_log_2819_ = lean_ctor_get(v_a_2818_, 0);
v_action_2820_ = lean_ctor_get_uint8(v_a_2818_, sizeof(void*)*3);
v_wantsRebuild_2821_ = lean_ctor_get_uint8(v_a_2818_, sizeof(void*)*3 + 1);
v_trace_2822_ = lean_ctor_get(v_a_2818_, 1);
v_buildTime_2823_ = lean_ctor_get(v_a_2818_, 2);
v___x_2824_ = l_Lake_clearFileHash(v_file_2769_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_a_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2825_);
lean_dec_ref_known(v___x_2824_, 1);
v___x_2826_ = lean_array_get_size(v_log_2796_);
lean_dec_ref(v_log_2796_);
v___x_2827_ = lean_array_get_size(v_log_2819_);
v___x_2828_ = l_Array_extract___redArg(v_log_2819_, v___x_2826_, v___x_2827_);
v___x_2829_ = lean_box(0);
v___x_2830_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_2771_, v___x_2829_, v___x_2828_);
v___x_2831_ = l_Lake_BuildMetadata_writeFile(v_traceFile_2772_, v___x_2830_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2872_; 
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2872_ == 0)
{
lean_object* v_unused_2873_; 
v_unused_2873_ = lean_ctor_get(v___x_2831_, 0);
lean_dec(v_unused_2873_);
v___x_2833_ = v___x_2831_;
v_isShared_2834_ = v_isSharedCheck_2872_;
goto v_resetjp_2832_;
}
else
{
lean_dec(v___x_2831_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2872_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2835_; 
v___x_2835_ = l_Lake_removeFileIfExists(v___x_2807_);
lean_dec_ref(v___x_2807_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2855_; 
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2855_ == 0)
{
lean_object* v_unused_2856_; 
v_unused_2856_ = lean_ctor_get(v___x_2835_, 0);
lean_dec(v_unused_2856_);
v___x_2837_ = v___x_2835_;
v_isShared_2838_ = v_isSharedCheck_2855_;
goto v_resetjp_2836_;
}
else
{
lean_dec(v___x_2835_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2855_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
lean_inc(v_a_2825_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 0, v_a_2825_);
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2825_);
v___x_2840_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
lean_object* v___x_2842_; 
if (v_isShared_2834_ == 0)
{
lean_ctor_set_tag(v___x_2833_, 1);
lean_ctor_set(v___x_2833_, 0, v___x_2840_);
v___x_2842_ = v___x_2833_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2840_);
v___x_2842_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
lean_object* v___x_2843_; lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2851_; 
v___x_2843_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v___x_2808_, v___x_2842_, v_a_2818_);
lean_dec_ref(v___x_2842_);
lean_dec(v___x_2808_);
v_a_2844_ = lean_ctor_get(v___x_2843_, 1);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2851_ == 0)
{
lean_object* v_unused_2852_; 
v_unused_2852_ = lean_ctor_get(v___x_2843_, 0);
lean_dec(v_unused_2852_);
v___x_2846_ = v___x_2843_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2843_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2849_; 
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 0, v_a_2825_);
v___x_2849_ = v___x_2846_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2825_);
lean_ctor_set(v_reuseFailAlloc_2850_, 1, v_a_2844_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
}
}
}
else
{
lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2868_; 
lean_inc(v_buildTime_2823_);
lean_inc_ref(v_trace_2822_);
lean_inc_ref(v_log_2819_);
lean_del_object(v___x_2833_);
lean_dec(v_a_2825_);
v_isSharedCheck_2868_ = !lean_is_exclusive(v_a_2818_);
if (v_isSharedCheck_2868_ == 0)
{
lean_object* v_unused_2869_; lean_object* v_unused_2870_; lean_object* v_unused_2871_; 
v_unused_2869_ = lean_ctor_get(v_a_2818_, 2);
lean_dec(v_unused_2869_);
v_unused_2870_ = lean_ctor_get(v_a_2818_, 1);
lean_dec(v_unused_2870_);
v_unused_2871_ = lean_ctor_get(v_a_2818_, 0);
lean_dec(v_unused_2871_);
v___x_2858_ = v_a_2818_;
v_isShared_2859_ = v_isSharedCheck_2868_;
goto v_resetjp_2857_;
}
else
{
lean_dec(v_a_2818_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2868_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v_a_2860_; lean_object* v___x_2861_; uint8_t v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2866_; 
v_a_2860_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2860_);
lean_dec_ref_known(v___x_2835_, 1);
v___x_2861_ = lean_io_error_to_string(v_a_2860_);
v___x_2862_ = 3;
v___x_2863_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2863_, 0, v___x_2861_);
lean_ctor_set_uint8(v___x_2863_, sizeof(void*)*1, v___x_2862_);
v___x_2864_ = lean_array_push(v_log_2819_, v___x_2863_);
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 0, v___x_2864_);
v___x_2866_ = v___x_2858_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v___x_2864_);
lean_ctor_set(v_reuseFailAlloc_2867_, 1, v_trace_2822_);
lean_ctor_set(v_reuseFailAlloc_2867_, 2, v_buildTime_2823_);
lean_ctor_set_uint8(v_reuseFailAlloc_2867_, sizeof(void*)*3, v_action_2820_);
lean_ctor_set_uint8(v_reuseFailAlloc_2867_, sizeof(void*)*3 + 1, v_wantsRebuild_2821_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
v_a_2813_ = v___x_2827_;
v_a_2814_ = v___x_2866_;
goto v___jp_2812_;
}
}
}
}
}
else
{
lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2885_; 
lean_inc(v_buildTime_2823_);
lean_inc_ref(v_trace_2822_);
lean_inc_ref(v_log_2819_);
lean_dec(v_a_2825_);
lean_dec_ref(v___x_2807_);
v_isSharedCheck_2885_ = !lean_is_exclusive(v_a_2818_);
if (v_isSharedCheck_2885_ == 0)
{
lean_object* v_unused_2886_; lean_object* v_unused_2887_; lean_object* v_unused_2888_; 
v_unused_2886_ = lean_ctor_get(v_a_2818_, 2);
lean_dec(v_unused_2886_);
v_unused_2887_ = lean_ctor_get(v_a_2818_, 1);
lean_dec(v_unused_2887_);
v_unused_2888_ = lean_ctor_get(v_a_2818_, 0);
lean_dec(v_unused_2888_);
v___x_2875_ = v_a_2818_;
v_isShared_2876_ = v_isSharedCheck_2885_;
goto v_resetjp_2874_;
}
else
{
lean_dec(v_a_2818_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2885_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v_a_2877_; lean_object* v___x_2878_; uint8_t v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2883_; 
v_a_2877_ = lean_ctor_get(v___x_2831_, 0);
lean_inc(v_a_2877_);
lean_dec_ref_known(v___x_2831_, 1);
v___x_2878_ = lean_io_error_to_string(v_a_2877_);
v___x_2879_ = 3;
v___x_2880_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2880_, 0, v___x_2878_);
lean_ctor_set_uint8(v___x_2880_, sizeof(void*)*1, v___x_2879_);
v___x_2881_ = lean_array_push(v_log_2819_, v___x_2880_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 0, v___x_2881_);
v___x_2883_ = v___x_2875_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2881_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v_trace_2822_);
lean_ctor_set(v_reuseFailAlloc_2884_, 2, v_buildTime_2823_);
lean_ctor_set_uint8(v_reuseFailAlloc_2884_, sizeof(void*)*3, v_action_2820_);
lean_ctor_set_uint8(v_reuseFailAlloc_2884_, sizeof(void*)*3 + 1, v_wantsRebuild_2821_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
v_a_2813_ = v___x_2827_;
v_a_2814_ = v___x_2883_;
goto v___jp_2812_;
}
}
}
}
else
{
lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2901_; 
lean_inc(v_buildTime_2823_);
lean_inc_ref(v_trace_2822_);
lean_inc_ref(v_log_2819_);
lean_dec_ref(v___x_2807_);
lean_dec_ref(v_log_2796_);
lean_dec_ref(v_traceFile_2772_);
v_isSharedCheck_2901_ = !lean_is_exclusive(v_a_2818_);
if (v_isSharedCheck_2901_ == 0)
{
lean_object* v_unused_2902_; lean_object* v_unused_2903_; lean_object* v_unused_2904_; 
v_unused_2902_ = lean_ctor_get(v_a_2818_, 2);
lean_dec(v_unused_2902_);
v_unused_2903_ = lean_ctor_get(v_a_2818_, 1);
lean_dec(v_unused_2903_);
v_unused_2904_ = lean_ctor_get(v_a_2818_, 0);
lean_dec(v_unused_2904_);
v___x_2890_ = v_a_2818_;
v_isShared_2891_ = v_isSharedCheck_2901_;
goto v_resetjp_2889_;
}
else
{
lean_dec(v_a_2818_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2901_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v_a_2892_; lean_object* v___x_2893_; uint8_t v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2899_; 
v_a_2892_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2892_);
lean_dec_ref_known(v___x_2824_, 1);
v___x_2893_ = lean_io_error_to_string(v_a_2892_);
v___x_2894_ = 3;
v___x_2895_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2895_, 0, v___x_2893_);
lean_ctor_set_uint8(v___x_2895_, sizeof(void*)*1, v___x_2894_);
v___x_2896_ = lean_array_get_size(v_log_2819_);
v___x_2897_ = lean_array_push(v_log_2819_, v___x_2895_);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 0, v___x_2897_);
v___x_2899_ = v___x_2890_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2897_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v_trace_2822_);
lean_ctor_set(v_reuseFailAlloc_2900_, 2, v_buildTime_2823_);
lean_ctor_set_uint8(v_reuseFailAlloc_2900_, sizeof(void*)*3, v_action_2820_);
lean_ctor_set_uint8(v_reuseFailAlloc_2900_, sizeof(void*)*3 + 1, v_wantsRebuild_2821_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
v_a_2813_ = v___x_2896_;
v_a_2814_ = v___x_2899_;
goto v___jp_2812_;
}
}
}
}
else
{
lean_object* v_a_2905_; lean_object* v_a_2906_; 
lean_dec_ref(v___x_2807_);
lean_dec_ref(v_log_2796_);
lean_dec_ref(v_traceFile_2772_);
lean_dec_ref(v_file_2769_);
v_a_2905_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2905_);
v_a_2906_ = lean_ctor_get(v___x_2811_, 1);
lean_inc(v_a_2906_);
lean_dec_ref_known(v___x_2811_, 2);
v_a_2813_ = v_a_2905_;
v_a_2814_ = v_a_2906_;
goto v___jp_2812_;
}
v___jp_2812_:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v_a_2817_; 
v___x_2815_ = lean_box(0);
v___x_2816_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(v___x_2808_, v___x_2815_, v_a_2814_);
lean_dec(v___x_2808_);
v_a_2817_ = lean_ctor_get(v___x_2816_, 1);
lean_inc(v_a_2817_);
lean_dec_ref(v___x_2816_);
v_a_2781_ = v_a_2813_;
v_a_2782_ = v_a_2817_;
goto v___jp_2780_;
}
}
}
else
{
uint8_t v___x_2908_; 
lean_dec_ref(v_a_2770_);
lean_dec_ref(v_file_2769_);
lean_dec_ref(v_build_2768_);
v___x_2908_ = l_System_FilePath_pathExists(v_traceFile_2772_);
lean_dec_ref(v_traceFile_2772_);
if (v___x_2908_ == 0)
{
lean_dec_ref(v___x_2807_);
lean_del_object(v___x_2802_);
v_log_2785_ = v_log_2796_;
v_action_2786_ = v___x_2805_;
v_wantsRebuild_2787_ = v_noBuild_2804_;
v_trace_2788_ = v_trace_2799_;
v_buildTime_2789_ = v_buildTime_2800_;
goto v___jp_2784_;
}
else
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2909_ = lean_box(0);
v___x_2910_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_2911_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_2771_, v___x_2909_, v___x_2910_);
v___x_2912_ = l_Lake_BuildMetadata_writeFile(v___x_2807_, v___x_2911_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_dec_ref_known(v___x_2912_, 1);
lean_del_object(v___x_2802_);
v_log_2785_ = v_log_2796_;
v_action_2786_ = v___x_2805_;
v_wantsRebuild_2787_ = v_noBuild_2804_;
v_trace_2788_ = v_trace_2799_;
v_buildTime_2789_ = v_buildTime_2800_;
goto v___jp_2784_;
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2914_; uint8_t v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2920_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_a_2913_);
lean_dec_ref_known(v___x_2912_, 1);
v___x_2914_ = lean_io_error_to_string(v_a_2913_);
v___x_2915_ = 3;
v___x_2916_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2916_, 0, v___x_2914_);
lean_ctor_set_uint8(v___x_2916_, sizeof(void*)*1, v___x_2915_);
v___x_2917_ = lean_array_get_size(v_log_2796_);
v___x_2918_ = lean_array_push(v_log_2796_, v___x_2916_);
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v___x_2918_);
v___x_2920_ = v___x_2802_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v___x_2918_);
lean_ctor_set(v_reuseFailAlloc_2922_, 1, v_trace_2799_);
lean_ctor_set(v_reuseFailAlloc_2922_, 2, v_buildTime_2800_);
v___x_2920_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v___x_2921_; 
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3, v___x_2805_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 1, v_noBuild_2804_);
v___x_2921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2917_);
lean_ctor_set(v___x_2921_, 1, v___x_2920_);
return v___x_2921_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___boxed(lean_object* v_build_2924_, lean_object* v_file_2925_, lean_object* v_a_2926_, lean_object* v_depTrace_2927_, lean_object* v_traceFile_2928_, lean_object* v_action_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_){
_start:
{
uint8_t v_action_boxed_2936_; lean_object* v_res_2937_; 
v_action_boxed_2936_ = lean_unbox(v_action_2929_);
v_res_2937_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(v_build_2924_, v_file_2925_, v_a_2926_, v_depTrace_2927_, v_traceFile_2928_, v_action_boxed_2936_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_);
lean_dec_ref(v_a_2933_);
lean_dec(v_a_2932_);
lean_dec(v_a_2931_);
lean_dec(v_a_2930_);
lean_dec_ref(v_depTrace_2927_);
return v_res_2937_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(lean_object* v_info_2938_, lean_object* v_self_2939_){
_start:
{
lean_object* v___x_2941_; 
v___x_2941_ = lean_io_metadata(v_info_2938_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_a_2942_; lean_object* v_modified_2943_; uint8_t v___x_2944_; 
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_a_2942_);
lean_dec_ref_known(v___x_2941_, 1);
v_modified_2943_ = lean_ctor_get(v_a_2942_, 1);
lean_inc_ref(v_modified_2943_);
lean_dec(v_a_2942_);
v___x_2944_ = l_IO_FS_instOrdSystemTime_ord(v_self_2939_, v_modified_2943_);
lean_dec_ref(v_modified_2943_);
if (v___x_2944_ == 0)
{
uint8_t v___x_2945_; 
v___x_2945_ = 1;
return v___x_2945_;
}
else
{
uint8_t v___x_2946_; 
v___x_2946_ = 0;
return v___x_2946_;
}
}
else
{
uint8_t v___x_2947_; 
lean_dec_ref_known(v___x_2941_, 1);
v___x_2947_ = 0;
return v___x_2947_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___boxed(lean_object* v_info_2948_, lean_object* v_self_2949_, lean_object* v_a_2950_){
_start:
{
uint8_t v_res_2951_; lean_object* v_r_2952_; 
v_res_2951_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_2948_, v_self_2949_);
lean_dec_ref(v_self_2949_);
lean_dec_ref(v_info_2948_);
v_r_2952_ = lean_box(v_res_2951_);
return v_r_2952_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(lean_object* v_x_2953_, lean_object* v_x_2954_){
_start:
{
if (lean_obj_tag(v_x_2953_) == 0)
{
if (lean_obj_tag(v_x_2954_) == 0)
{
uint8_t v___x_2955_; 
v___x_2955_ = 1;
return v___x_2955_;
}
else
{
uint8_t v___x_2956_; 
v___x_2956_ = 0;
return v___x_2956_;
}
}
else
{
if (lean_obj_tag(v_x_2954_) == 0)
{
uint8_t v___x_2957_; 
v___x_2957_ = 0;
return v___x_2957_;
}
else
{
lean_object* v_val_2958_; lean_object* v_val_2959_; uint64_t v___x_2960_; uint64_t v___x_2961_; uint8_t v___x_2962_; 
v_val_2958_ = lean_ctor_get(v_x_2953_, 0);
v_val_2959_ = lean_ctor_get(v_x_2954_, 0);
v___x_2960_ = lean_unbox_uint64(v_val_2958_);
v___x_2961_ = lean_unbox_uint64(v_val_2959_);
v___x_2962_ = lean_uint64_dec_eq(v___x_2960_, v___x_2961_);
return v___x_2962_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2963_, lean_object* v_x_2964_){
_start:
{
uint8_t v_res_2965_; lean_object* v_r_2966_; 
v_res_2965_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(v_x_2963_, v_x_2964_);
lean_dec(v_x_2964_);
lean_dec(v_x_2963_);
v_r_2966_ = lean_box(v_res_2965_);
return v_r_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(lean_object* v_info_2967_, lean_object* v_depTrace_2968_, lean_object* v_depHash_2969_, lean_object* v_oldTrace_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_){
_start:
{
uint64_t v_hash_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; uint8_t v___x_2977_; 
v_hash_2974_ = lean_ctor_get_uint64(v_depTrace_2968_, sizeof(void*)*3);
v___x_2975_ = lean_box_uint64(v_hash_2974_);
v___x_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
v___x_2977_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(v___x_2976_, v_depHash_2969_);
lean_dec_ref_known(v___x_2976_, 1);
if (v___x_2977_ == 0)
{
lean_object* v_toBuildConfig_2978_; uint8_t v_oldMode_2979_; 
v_toBuildConfig_2978_ = lean_ctor_get(v_a_2971_, 0);
v_oldMode_2979_ = lean_ctor_get_uint8(v_toBuildConfig_2978_, sizeof(void*)*4);
if (v_oldMode_2979_ == 0)
{
uint8_t v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2980_ = 0;
v___x_2981_ = lean_box(v___x_2980_);
v___x_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2981_);
lean_ctor_set(v___x_2982_, 1, v_a_2972_);
return v___x_2982_;
}
else
{
uint8_t v___x_2983_; 
v___x_2983_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_2967_, v_oldTrace_2970_);
if (v___x_2983_ == 0)
{
uint8_t v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2984_ = 0;
v___x_2985_ = lean_box(v___x_2984_);
v___x_2986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2985_);
lean_ctor_set(v___x_2986_, 1, v_a_2972_);
return v___x_2986_;
}
else
{
uint8_t v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2987_ = 1;
v___x_2988_ = lean_box(v___x_2987_);
v___x_2989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2988_);
lean_ctor_set(v___x_2989_, 1, v_a_2972_);
return v___x_2989_;
}
}
}
else
{
uint8_t v___x_2990_; 
v___x_2990_ = l_System_FilePath_pathExists(v_info_2967_);
if (v___x_2990_ == 0)
{
uint8_t v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2991_ = 0;
v___x_2992_ = lean_box(v___x_2991_);
v___x_2993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2992_);
lean_ctor_set(v___x_2993_, 1, v_a_2972_);
return v___x_2993_;
}
else
{
uint8_t v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2994_ = 2;
v___x_2995_ = lean_box(v___x_2994_);
v___x_2996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2995_);
lean_ctor_set(v___x_2996_, 1, v_a_2972_);
return v___x_2996_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg___boxed(lean_object* v_info_2997_, lean_object* v_depTrace_2998_, lean_object* v_depHash_2999_, lean_object* v_oldTrace_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_2997_, v_depTrace_2998_, v_depHash_2999_, v_oldTrace_3000_, v_a_3001_, v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec_ref(v_oldTrace_3000_);
lean_dec(v_depHash_2999_);
lean_dec_ref(v_depTrace_2998_);
lean_dec_ref(v_info_2997_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(lean_object* v_a_3005_, lean_object* v_info_3006_, lean_object* v_depTrace_3007_, lean_object* v_savedTrace_3008_, lean_object* v_oldTrace_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_){
_start:
{
if (lean_obj_tag(v_savedTrace_3008_) == 2)
{
lean_object* v_data_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3067_; 
v_data_3016_ = lean_ctor_get(v_savedTrace_3008_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v_savedTrace_3008_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3018_ = v_savedTrace_3008_;
v_isShared_3019_ = v_isSharedCheck_3067_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_data_3016_);
lean_dec(v_savedTrace_3008_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3067_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
uint64_t v_depHash_3020_; lean_object* v_log_3021_; lean_object* v___x_3022_; lean_object* v___x_3024_; 
v_depHash_3020_ = lean_ctor_get_uint64(v_data_3016_, sizeof(void*)*3);
v_log_3021_ = lean_ctor_get(v_data_3016_, 2);
lean_inc_ref(v_log_3021_);
lean_dec_ref(v_data_3016_);
v___x_3022_ = lean_box_uint64(v_depHash_3020_);
if (v_isShared_3019_ == 0)
{
lean_ctor_set_tag(v___x_3018_, 1);
lean_ctor_set(v___x_3018_, 0, v___x_3022_);
v___x_3024_ = v___x_3018_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3022_);
v___x_3024_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
lean_object* v___x_3025_; lean_object* v_a_3026_; lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3065_; 
v___x_3025_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_3006_, v_depTrace_3007_, v___x_3024_, v_oldTrace_3009_, v_a_3013_, v_a_3014_);
lean_dec_ref(v___x_3024_);
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
v_a_3027_ = lean_ctor_get(v___x_3025_, 1);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3029_ = v___x_3025_;
v_isShared_3030_ = v_isSharedCheck_3065_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_inc(v_a_3026_);
lean_dec(v___x_3025_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3065_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___y_3032_; uint8_t v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; uint8_t v___x_3039_; 
v___x_3036_ = lean_unbox(v_a_3026_);
v___x_3037_ = l_Lake_OutputStatus_ctorIdx(v___x_3036_);
v___x_3038_ = lean_obj_once(&l_Lake_OutputStatus_isUpToDate___closed__0, &l_Lake_OutputStatus_isUpToDate___closed__0_once, _init_l_Lake_OutputStatus_isUpToDate___closed__0);
v___x_3039_ = lean_nat_dec_eq(v___x_3037_, v___x_3038_);
lean_dec(v___x_3037_);
if (v___x_3039_ == 0)
{
lean_object* v_log_3040_; uint8_t v_action_3041_; uint8_t v_wantsRebuild_3042_; lean_object* v_trace_3043_; lean_object* v_buildTime_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3064_; 
v_log_3040_ = lean_ctor_get(v_a_3027_, 0);
v_action_3041_ = lean_ctor_get_uint8(v_a_3027_, sizeof(void*)*3);
v_wantsRebuild_3042_ = lean_ctor_get_uint8(v_a_3027_, sizeof(void*)*3 + 1);
v_trace_3043_ = lean_ctor_get(v_a_3027_, 1);
v_buildTime_3044_ = lean_ctor_get(v_a_3027_, 2);
v_isSharedCheck_3064_ = !lean_is_exclusive(v_a_3027_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3046_ = v_a_3027_;
v_isShared_3047_ = v_isSharedCheck_3064_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_buildTime_3044_);
lean_inc(v_trace_3043_);
lean_inc(v_log_3040_);
lean_dec(v_a_3027_);
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
v___x_3052_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_3021_, v_a_3005_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v___x_3051_);
lean_dec_ref(v_log_3021_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 1);
lean_inc(v_a_3053_);
lean_dec_ref_known(v___x_3052_, 2);
v___y_3032_ = v_a_3053_;
goto v___jp_3031_;
}
else
{
lean_object* v_a_3054_; lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_del_object(v___x_3029_);
lean_dec(v_a_3026_);
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
lean_dec_ref(v_log_3021_);
v___y_3032_ = v_a_3027_;
goto v___jp_3031_;
}
v___jp_3031_:
{
lean_object* v___x_3034_; 
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 1, v___y_3032_);
v___x_3034_ = v___x_3029_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3026_);
lean_ctor_set(v_reuseFailAlloc_3035_, 1, v___y_3032_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
}
}
else
{
lean_object* v_toBuildConfig_3068_; uint8_t v_oldMode_3069_; 
lean_dec(v_savedTrace_3008_);
v_toBuildConfig_3068_ = lean_ctor_get(v_a_3013_, 0);
v_oldMode_3069_ = lean_ctor_get_uint8(v_toBuildConfig_3068_, sizeof(void*)*4);
if (v_oldMode_3069_ == 0)
{
uint8_t v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3070_ = 0;
v___x_3071_ = lean_box(v___x_3070_);
v___x_3072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
lean_ctor_set(v___x_3072_, 1, v_a_3014_);
return v___x_3072_;
}
else
{
uint8_t v___x_3073_; 
v___x_3073_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(v_info_3006_, v_oldTrace_3009_);
if (v___x_3073_ == 0)
{
uint8_t v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = 0;
v___x_3075_ = lean_box(v___x_3074_);
v___x_3076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
lean_ctor_set(v___x_3076_, 1, v_a_3014_);
return v___x_3076_;
}
else
{
uint8_t v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3077_ = 1;
v___x_3078_ = lean_box(v___x_3077_);
v___x_3079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
lean_ctor_set(v___x_3079_, 1, v_a_3014_);
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
lean_object* v_a_3104_; lean_object* v_a_3105_; lean_object* v_a_3108_; lean_object* v_log_3141_; uint8_t v_action_3142_; uint8_t v_wantsRebuild_3143_; lean_object* v_trace_3144_; lean_object* v_buildTime_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3177_; 
v_log_3141_ = lean_ctor_get(v_a_3101_, 0);
v_action_3142_ = lean_ctor_get_uint8(v_a_3101_, sizeof(void*)*3);
v_wantsRebuild_3143_ = lean_ctor_get_uint8(v_a_3101_, sizeof(void*)*3 + 1);
v_trace_3144_ = lean_ctor_get(v_a_3101_, 1);
v_buildTime_3145_ = lean_ctor_get(v_a_3101_, 2);
v_isSharedCheck_3177_ = !lean_is_exclusive(v_a_3101_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3147_ = v_a_3101_;
v_isShared_3148_ = v_isSharedCheck_3177_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_buildTime_3145_);
lean_inc(v_trace_3144_);
lean_inc(v_log_3141_);
lean_dec(v_a_3101_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3177_;
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
lean_dec_ref_known(v___x_3151_, 2);
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
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_a_3153_);
lean_ctor_set(v_reuseFailAlloc_3171_, 1, v_trace_3144_);
lean_ctor_set(v_reuseFailAlloc_3171_, 2, v_buildTime_3145_);
lean_ctor_set_uint8(v_reuseFailAlloc_3171_, sizeof(void*)*3, v_action_3142_);
lean_ctor_set_uint8(v_reuseFailAlloc_3171_, sizeof(void*)*3 + 1, v_wantsRebuild_3143_);
v___x_3156_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
lean_object* v___x_3157_; 
v___x_3157_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_3096_, v_file_3093_, v_trace_3144_, v_a_3152_, v_mtime_3154_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v___x_3156_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3158_; lean_object* v_a_3159_; uint8_t v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; uint8_t v___x_3163_; 
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_a_3158_);
v_a_3159_ = lean_ctor_get(v___x_3157_, 1);
lean_inc(v_a_3159_);
lean_dec_ref_known(v___x_3157_, 2);
v___x_3160_ = lean_unbox(v_a_3158_);
lean_dec(v_a_3158_);
v___x_3161_ = l_Lake_OutputStatus_ctorIdx(v___x_3160_);
v___x_3162_ = lean_obj_once(&l_Lake_OutputStatus_isUpToDate___closed__0, &l_Lake_OutputStatus_isUpToDate___closed__0_once, _init_l_Lake_OutputStatus_isUpToDate___closed__0);
v___x_3163_ = lean_nat_dec_eq(v___x_3161_, v___x_3162_);
lean_dec(v___x_3161_);
if (v___x_3163_ == 0)
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
uint8_t v___x_3164_; lean_object* v___x_3165_; 
v___x_3164_ = 5;
lean_inc_ref(v_file_3093_);
v___x_3165_ = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(v_build_3094_, v_file_3093_, v_a_3096_, v_trace_3144_, v_traceFile_3150_, v___x_3164_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3159_);
lean_dec_ref(v_trace_3144_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_object* v_a_3166_; 
v_a_3166_ = lean_ctor_get(v___x_3165_, 1);
lean_inc(v_a_3166_);
lean_dec_ref_known(v___x_3165_, 2);
v_a_3108_ = v_a_3166_;
goto v___jp_3107_;
}
else
{
lean_object* v_a_3167_; lean_object* v_a_3168_; 
lean_dec_ref(v_file_3093_);
v_a_3167_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_a_3167_);
v_a_3168_ = lean_ctor_get(v___x_3165_, 1);
lean_inc(v_a_3168_);
lean_dec_ref_known(v___x_3165_, 2);
v_a_3104_ = v_a_3167_;
v_a_3105_ = v_a_3168_;
goto v___jp_3103_;
}
}
}
else
{
lean_object* v_a_3169_; lean_object* v_a_3170_; 
lean_dec_ref(v_traceFile_3150_);
lean_dec_ref(v_trace_3144_);
lean_dec_ref(v_a_3096_);
lean_dec_ref(v_build_3094_);
lean_dec_ref(v_file_3093_);
v_a_3169_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_a_3169_);
v_a_3170_ = lean_ctor_get(v___x_3157_, 1);
lean_inc(v_a_3170_);
lean_dec_ref_known(v___x_3157_, 2);
v_a_3104_ = v_a_3169_;
v_a_3105_ = v_a_3170_;
goto v___jp_3103_;
}
}
}
else
{
lean_object* v_a_3172_; lean_object* v_a_3173_; lean_object* v___x_3175_; 
lean_dec_ref(v_traceFile_3150_);
lean_dec_ref(v_a_3096_);
lean_dec_ref(v_build_3094_);
lean_dec_ref(v_file_3093_);
v_a_3172_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3172_);
v_a_3173_ = lean_ctor_get(v___x_3151_, 1);
lean_inc(v_a_3173_);
lean_dec_ref_known(v___x_3151_, 2);
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 0, v_a_3173_);
v___x_3175_ = v___x_3147_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3173_);
lean_ctor_set(v_reuseFailAlloc_3176_, 1, v_trace_3144_);
lean_ctor_set(v_reuseFailAlloc_3176_, 2, v_buildTime_3145_);
lean_ctor_set_uint8(v_reuseFailAlloc_3176_, sizeof(void*)*3, v_action_3142_);
lean_ctor_set_uint8(v_reuseFailAlloc_3176_, sizeof(void*)*3 + 1, v_wantsRebuild_3143_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
v_a_3104_ = v_a_3172_;
v_a_3105_ = v___x_3175_;
goto v___jp_3103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27___boxed(lean_object* v_file_3178_, lean_object* v_build_3179_, lean_object* v_text_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_){
_start:
{
uint8_t v_text_boxed_3188_; lean_object* v_res_3189_; 
v_text_boxed_3188_ = lean_unbox(v_text_3180_);
v_res_3189_ = l_Lake_buildFileUnlessUpToDate_x27(v_file_3178_, v_build_3179_, v_text_boxed_3188_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_);
lean_dec_ref(v_a_3185_);
lean_dec(v_a_3184_);
lean_dec(v_a_3183_);
lean_dec(v_a_3182_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(lean_object* v_a_3190_, lean_object* v_info_3191_, lean_object* v_depTrace_3192_, lean_object* v_depHash_3193_, lean_object* v_oldTrace_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_){
_start:
{
lean_object* v___x_3201_; 
v___x_3201_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(v_info_3191_, v_depTrace_3192_, v_depHash_3193_, v_oldTrace_3194_, v_a_3198_, v_a_3199_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___boxed(lean_object* v_a_3202_, lean_object* v_info_3203_, lean_object* v_depTrace_3204_, lean_object* v_depHash_3205_, lean_object* v_oldTrace_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(v_a_3202_, v_info_3203_, v_depTrace_3204_, v_depHash_3205_, v_oldTrace_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_);
lean_dec_ref(v_a_3210_);
lean_dec(v_a_3209_);
lean_dec(v_a_3208_);
lean_dec(v_a_3207_);
lean_dec_ref(v_oldTrace_3206_);
lean_dec(v_depHash_3205_);
lean_dec_ref(v_depTrace_3204_);
lean_dec_ref(v_info_3203_);
lean_dec_ref(v_a_3202_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0(lean_object* v___x_3214_, lean_object* v___x_3215_, lean_object* v_file_3216_, uint64_t v___x_3217_, lean_object* v___x_3218_, uint8_t v_useLocalFile_3219_, lean_object* v_____r_3220_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = l_IO_setAccessRights(v___x_3214_, v___x_3215_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v___x_3223_; 
lean_dec_ref_known(v___x_3222_, 1);
lean_inc_ref(v_file_3216_);
v___x_3223_ = l_Lake_writeFileHash(v_file_3216_, v___x_3217_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v___x_3224_; 
lean_dec_ref_known(v___x_3223_, 1);
v___x_3224_ = lean_io_metadata(v___x_3214_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3237_; 
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3227_ = v___x_3224_;
v_isShared_3228_ = v_isSharedCheck_3237_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_3224_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3237_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v_modified_3229_; lean_object* v___y_3231_; 
v_modified_3229_ = lean_ctor_get(v_a_3225_, 1);
lean_inc_ref(v_modified_3229_);
lean_dec(v_a_3225_);
if (v_useLocalFile_3219_ == 0)
{
v___y_3231_ = v___x_3214_;
goto v___jp_3230_;
}
else
{
lean_dec_ref(v___x_3214_);
lean_inc_ref(v_file_3216_);
v___y_3231_ = v_file_3216_;
goto v___jp_3230_;
}
v___jp_3230_:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3235_; 
v___x_3232_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3218_);
lean_ctor_set(v___x_3232_, 1, v___y_3231_);
lean_ctor_set(v___x_3232_, 2, v_file_3216_);
lean_ctor_set(v___x_3232_, 3, v_modified_3229_);
v___x_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3232_);
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 0, v___x_3233_);
v___x_3235_ = v___x_3227_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v___x_3233_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
else
{
lean_object* v_a_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3245_; 
lean_dec_ref(v___x_3218_);
lean_dec_ref(v_file_3216_);
lean_dec_ref(v___x_3214_);
v_a_3238_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3240_ = v___x_3224_;
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_a_3238_);
lean_dec(v___x_3224_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3243_; 
if (v_isShared_3241_ == 0)
{
v___x_3243_ = v___x_3240_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_a_3238_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
}
}
else
{
lean_object* v_a_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3253_; 
lean_dec_ref(v___x_3218_);
lean_dec_ref(v_file_3216_);
lean_dec_ref(v___x_3214_);
v_a_3246_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3248_ = v___x_3223_;
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_a_3246_);
lean_dec(v___x_3223_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3251_; 
if (v_isShared_3249_ == 0)
{
v___x_3251_ = v___x_3248_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_a_3246_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
}
else
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3261_; 
lean_dec_ref(v___x_3218_);
lean_dec_ref(v_file_3216_);
lean_dec_ref(v___x_3214_);
v_a_3254_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3256_ = v___x_3222_;
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3222_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3259_; 
if (v_isShared_3257_ == 0)
{
v___x_3259_ = v___x_3256_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3254_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___lam__0___boxed(lean_object* v___x_3262_, lean_object* v___x_3263_, lean_object* v_file_3264_, lean_object* v___x_3265_, lean_object* v___x_3266_, lean_object* v_useLocalFile_3267_, lean_object* v_____r_3268_, lean_object* v___y_3269_){
_start:
{
uint64_t v___x_2111__boxed_3270_; uint8_t v_useLocalFile_boxed_3271_; lean_object* v_res_3272_; 
v___x_2111__boxed_3270_ = lean_unbox_uint64(v___x_3265_);
lean_dec_ref(v___x_3265_);
v_useLocalFile_boxed_3271_ = lean_unbox(v_useLocalFile_3267_);
v_res_3272_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3262_, v___x_3263_, v_file_3264_, v___x_2111__boxed_3270_, v___x_3266_, v_useLocalFile_boxed_3271_, v_____r_3268_);
lean_dec_ref(v___x_3263_);
return v_res_3272_;
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
lean_object* v_a_3308_; uint64_t v___x_3309_; uint64_t v___x_3310_; uint64_t v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___y_3316_; lean_object* v___x_3337_; lean_object* v___x_3338_; uint8_t v___x_3339_; 
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_a_3308_);
lean_dec_ref_known(v___x_3307_, 1);
v___x_3309_ = l_Lake_Hash_nil;
v___x_3310_ = lean_byte_array_hash(v_a_3308_);
v___x_3311_ = lean_uint64_mix_hash(v___x_3309_, v___x_3310_);
lean_inc_ref(v_ext_3282_);
v___x_3312_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3312_, 0, v_ext_3282_);
lean_ctor_set_uint64(v___x_3312_, sizeof(void*)*1, v___x_3311_);
v___x_3313_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
v___x_3314_ = l_System_FilePath_join(v_cache_3280_, v___x_3313_);
v___x_3337_ = lean_string_utf8_byte_size(v_ext_3282_);
v___x_3338_ = lean_unsigned_to_nat(0u);
v___x_3339_ = lean_nat_dec_eq(v___x_3337_, v___x_3338_);
if (v___x_3339_ == 0)
{
lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3340_ = l_Lake_lowerHexUInt64(v___x_3311_);
v___x_3341_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_3342_ = lean_string_append(v___x_3340_, v___x_3341_);
v___x_3343_ = lean_string_append(v___x_3342_, v_ext_3282_);
lean_dec_ref(v_ext_3282_);
v___y_3316_ = v___x_3343_;
goto v___jp_3315_;
}
else
{
lean_object* v___x_3344_; 
lean_dec_ref(v_ext_3282_);
v___x_3344_ = l_Lake_lowerHexUInt64(v___x_3311_);
v___y_3316_ = v___x_3344_;
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
lean_dec_ref_known(v___x_3319_, 1);
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
lean_dec_ref_known(v___x_3322_, 1);
v___x_3323_ = lean_io_hard_link(v_file_3281_, v___x_3320_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
lean_dec_ref_known(v___x_3323_, 1);
lean_dec(v_a_3308_);
v___x_3324_ = lean_box(0);
v___x_3325_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3320_, v___x_3318_, v_file_3281_, v___x_3311_, v___x_3312_, v_useLocalFile_3285_, v___x_3324_);
lean_dec_ref_known(v___x_3318_, 3);
v___y_3295_ = v___x_3325_;
goto v___jp_3294_;
}
else
{
lean_object* v_a_3326_; 
v_a_3326_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3326_);
lean_dec_ref_known(v___x_3323_, 1);
if (lean_obj_tag(v_a_3326_) == 0)
{
lean_object* v___x_3327_; lean_object* v___x_3328_; 
lean_dec_ref_known(v_a_3326_, 2);
lean_dec(v_a_3308_);
v___x_3327_ = lean_box(0);
v___x_3328_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3320_, v___x_3318_, v_file_3281_, v___x_3311_, v___x_3312_, v_useLocalFile_3285_, v___x_3327_);
lean_dec_ref_known(v___x_3318_, 3);
v___y_3295_ = v___x_3328_;
goto v___jp_3294_;
}
else
{
lean_object* v___x_3329_; 
lean_dec(v_a_3326_);
v___x_3329_ = l_Lake_writeBinFileIfNew(v___x_3320_, v_a_3308_);
lean_dec(v_a_3308_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v_a_3330_; lean_object* v___x_3331_; 
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_a_3330_);
lean_dec_ref_known(v___x_3329_, 1);
v___x_3331_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3320_, v___x_3318_, v_file_3281_, v___x_3311_, v___x_3312_, v_useLocalFile_3285_, v_a_3330_);
lean_dec_ref_known(v___x_3318_, 3);
v___y_3295_ = v___x_3331_;
goto v___jp_3294_;
}
else
{
lean_object* v_a_3332_; 
lean_dec_ref(v___x_3320_);
lean_dec_ref_known(v___x_3318_, 3);
lean_dec_ref_known(v___x_3312_, 1);
lean_dec_ref(v_file_3281_);
v_a_3332_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_a_3332_);
lean_dec_ref_known(v___x_3329_, 1);
v_a_3288_ = v_a_3332_;
goto v___jp_3287_;
}
}
}
}
else
{
lean_object* v_a_3333_; 
lean_dec_ref(v___x_3320_);
lean_dec_ref_known(v___x_3318_, 3);
lean_dec_ref_known(v___x_3312_, 1);
lean_dec(v_a_3308_);
lean_dec_ref(v_file_3281_);
v_a_3333_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3333_);
lean_dec_ref_known(v___x_3322_, 1);
v_a_3288_ = v_a_3333_;
goto v___jp_3287_;
}
}
else
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
lean_dec(v_a_3308_);
v___x_3334_ = lean_box(0);
v___x_3335_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3320_, v___x_3318_, v_file_3281_, v___x_3311_, v___x_3312_, v_useLocalFile_3285_, v___x_3334_);
lean_dec_ref_known(v___x_3318_, 3);
v___y_3295_ = v___x_3335_;
goto v___jp_3294_;
}
}
else
{
lean_object* v_a_3336_; 
lean_dec_ref_known(v___x_3318_, 3);
lean_dec_ref(v___y_3316_);
lean_dec_ref(v___x_3314_);
lean_dec_ref_known(v___x_3312_, 1);
lean_dec(v_a_3308_);
lean_dec_ref(v_file_3281_);
v_a_3336_ = lean_ctor_get(v___x_3319_, 0);
lean_inc(v_a_3336_);
lean_dec_ref_known(v___x_3319_, 1);
v_a_3288_ = v_a_3336_;
goto v___jp_3287_;
}
}
}
else
{
lean_object* v_a_3345_; 
lean_dec_ref(v_ext_3282_);
lean_dec_ref(v_file_3281_);
lean_dec_ref(v_cache_3280_);
v_a_3345_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_a_3345_);
lean_dec_ref_known(v___x_3307_, 1);
v_a_3288_ = v_a_3345_;
goto v___jp_3287_;
}
}
else
{
lean_object* v___x_3346_; 
v___x_3346_ = l_IO_FS_readFile(v_file_3281_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_a_3347_; lean_object* v___x_3348_; uint64_t v___x_3349_; uint64_t v___x_3350_; uint64_t v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___y_3356_; lean_object* v___x_3370_; lean_object* v___x_3371_; uint8_t v___x_3372_; 
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_a_3347_);
lean_dec_ref_known(v___x_3346_, 1);
v___x_3348_ = l_String_crlfToLf(v_a_3347_);
lean_dec(v_a_3347_);
v___x_3349_ = l_Lake_Hash_nil;
v___x_3350_ = lean_string_hash(v___x_3348_);
v___x_3351_ = lean_uint64_mix_hash(v___x_3349_, v___x_3350_);
lean_inc_ref(v_ext_3282_);
v___x_3352_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3352_, 0, v_ext_3282_);
lean_ctor_set_uint64(v___x_3352_, sizeof(void*)*1, v___x_3351_);
v___x_3353_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
v___x_3354_ = l_System_FilePath_join(v_cache_3280_, v___x_3353_);
v___x_3370_ = lean_string_utf8_byte_size(v_ext_3282_);
v___x_3371_ = lean_unsigned_to_nat(0u);
v___x_3372_ = lean_nat_dec_eq(v___x_3370_, v___x_3371_);
if (v___x_3372_ == 0)
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3373_ = l_Lake_lowerHexUInt64(v___x_3351_);
v___x_3374_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_3375_ = lean_string_append(v___x_3373_, v___x_3374_);
v___x_3376_ = lean_string_append(v___x_3375_, v_ext_3282_);
lean_dec_ref(v_ext_3282_);
v___y_3356_ = v___x_3376_;
goto v___jp_3355_;
}
else
{
lean_object* v___x_3377_; 
lean_dec_ref(v_ext_3282_);
v___x_3377_ = l_Lake_lowerHexUInt64(v___x_3351_);
v___y_3356_ = v___x_3377_;
goto v___jp_3355_;
}
v___jp_3355_:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3357_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__3));
v___x_3358_ = l_IO_setAccessRights(v_file_3281_, v___x_3357_);
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_object* v___x_3359_; uint8_t v___x_3360_; 
lean_dec_ref_known(v___x_3358_, 1);
v___x_3359_ = l_Lake_joinRelative(v___x_3354_, v___y_3356_);
v___x_3360_ = l_System_FilePath_pathExists(v___x_3359_);
if (v___x_3360_ == 0)
{
lean_object* v___x_3361_; 
lean_inc_ref(v___x_3359_);
v___x_3361_ = l_Lake_createParentDirs(v___x_3359_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v___x_3362_; 
lean_dec_ref_known(v___x_3361_, 1);
v___x_3362_ = l_Lake_writeFileIfNew(v___x_3359_, v___x_3348_);
lean_dec_ref(v___x_3348_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3364_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v___x_3362_, 1);
v___x_3364_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3359_, v___x_3357_, v_file_3281_, v___x_3351_, v___x_3352_, v_useLocalFile_3285_, v_a_3363_);
v___y_3295_ = v___x_3364_;
goto v___jp_3294_;
}
else
{
lean_object* v_a_3365_; 
lean_dec_ref(v___x_3359_);
lean_dec_ref_known(v___x_3352_, 1);
lean_dec_ref(v_file_3281_);
v_a_3365_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3365_);
lean_dec_ref_known(v___x_3362_, 1);
v_a_3288_ = v_a_3365_;
goto v___jp_3287_;
}
}
else
{
lean_object* v_a_3366_; 
lean_dec_ref(v___x_3359_);
lean_dec_ref_known(v___x_3352_, 1);
lean_dec_ref(v___x_3348_);
lean_dec_ref(v_file_3281_);
v_a_3366_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3366_);
lean_dec_ref_known(v___x_3361_, 1);
v_a_3288_ = v_a_3366_;
goto v___jp_3287_;
}
}
else
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
lean_dec_ref(v___x_3348_);
v___x_3367_ = lean_box(0);
v___x_3368_ = l_Lake_Cache_saveArtifact___lam__0(v___x_3359_, v___x_3357_, v_file_3281_, v___x_3351_, v___x_3352_, v_useLocalFile_3285_, v___x_3367_);
v___y_3295_ = v___x_3368_;
goto v___jp_3294_;
}
}
else
{
lean_object* v_a_3369_; 
lean_dec_ref(v___y_3356_);
lean_dec_ref(v___x_3354_);
lean_dec_ref_known(v___x_3352_, 1);
lean_dec_ref(v___x_3348_);
lean_dec_ref(v_file_3281_);
v_a_3369_ = lean_ctor_get(v___x_3358_, 0);
lean_inc(v_a_3369_);
lean_dec_ref_known(v___x_3358_, 1);
v_a_3288_ = v_a_3369_;
goto v___jp_3287_;
}
}
}
else
{
lean_object* v_a_3378_; 
lean_dec_ref(v_ext_3282_);
lean_dec_ref(v_file_3281_);
lean_dec_ref(v_cache_3280_);
v_a_3378_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_a_3378_);
lean_dec_ref_known(v___x_3346_, 1);
v_a_3288_ = v_a_3378_;
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
lean_dec_ref_known(v___y_3295_, 1);
v_a_3288_ = v_a_3305_;
goto v___jp_3287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___boxed(lean_object* v_cache_3379_, lean_object* v_file_3380_, lean_object* v_ext_3381_, lean_object* v_text_3382_, lean_object* v_exe_3383_, lean_object* v_useLocalFile_3384_, lean_object* v_a_3385_){
_start:
{
uint8_t v_text_boxed_3386_; uint8_t v_exe_boxed_3387_; uint8_t v_useLocalFile_boxed_3388_; lean_object* v_res_3389_; 
v_text_boxed_3386_ = lean_unbox(v_text_3382_);
v_exe_boxed_3387_ = lean_unbox(v_exe_3383_);
v_useLocalFile_boxed_3388_ = lean_unbox(v_useLocalFile_3384_);
v_res_3389_ = l_Lake_Cache_saveArtifact(v_cache_3379_, v_file_3380_, v_ext_3381_, v_text_boxed_3386_, v_exe_boxed_3387_, v_useLocalFile_boxed_3388_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0(lean_object* v_x_3390_){
_start:
{
lean_object* v_lakeCache_3391_; 
v_lakeCache_3391_ = lean_ctor_get(v_x_3390_, 2);
lean_inc_ref(v_lakeCache_3391_);
return v_lakeCache_3391_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0___boxed(lean_object* v_x_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l_Lake_cacheArtifact___redArg___lam__0(v_x_3392_);
lean_dec_ref(v_x_3392_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1(lean_object* v_file_3394_, lean_object* v_ext_3395_, uint8_t v_text_3396_, uint8_t v_exe_3397_, uint8_t v_useLocalFile_3398_, lean_object* v_inst_3399_, lean_object* v_____do__lift_3400_){
_start:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3401_ = lean_box(v_text_3396_);
v___x_3402_ = lean_box(v_exe_3397_);
v___x_3403_ = lean_box(v_useLocalFile_3398_);
v___x_3404_ = lean_alloc_closure((void*)(l_Lake_Cache_saveArtifact___boxed), 7, 6);
lean_closure_set(v___x_3404_, 0, v_____do__lift_3400_);
lean_closure_set(v___x_3404_, 1, v_file_3394_);
lean_closure_set(v___x_3404_, 2, v_ext_3395_);
lean_closure_set(v___x_3404_, 3, v___x_3401_);
lean_closure_set(v___x_3404_, 4, v___x_3402_);
lean_closure_set(v___x_3404_, 5, v___x_3403_);
v___x_3405_ = lean_apply_2(v_inst_3399_, lean_box(0), v___x_3404_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1___boxed(lean_object* v_file_3406_, lean_object* v_ext_3407_, lean_object* v_text_3408_, lean_object* v_exe_3409_, lean_object* v_useLocalFile_3410_, lean_object* v_inst_3411_, lean_object* v_____do__lift_3412_){
_start:
{
uint8_t v_text_boxed_3413_; uint8_t v_exe_boxed_3414_; uint8_t v_useLocalFile_boxed_3415_; lean_object* v_res_3416_; 
v_text_boxed_3413_ = lean_unbox(v_text_3408_);
v_exe_boxed_3414_ = lean_unbox(v_exe_3409_);
v_useLocalFile_boxed_3415_ = lean_unbox(v_useLocalFile_3410_);
v_res_3416_ = l_Lake_cacheArtifact___redArg___lam__1(v_file_3406_, v_ext_3407_, v_text_boxed_3413_, v_exe_boxed_3414_, v_useLocalFile_boxed_3415_, v_inst_3411_, v_____do__lift_3412_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg(lean_object* v_inst_3418_, lean_object* v_inst_3419_, lean_object* v_inst_3420_, lean_object* v_file_3421_, lean_object* v_ext_3422_, uint8_t v_text_3423_, uint8_t v_exe_3424_, uint8_t v_useLocalFile_3425_){
_start:
{
lean_object* v_toApplicative_3426_; lean_object* v_toFunctor_3427_; lean_object* v_toBind_3428_; lean_object* v_map_3429_; lean_object* v___f_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___f_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v_toApplicative_3426_ = lean_ctor_get(v_inst_3420_, 0);
v_toFunctor_3427_ = lean_ctor_get(v_toApplicative_3426_, 0);
lean_inc_ref(v_toFunctor_3427_);
v_toBind_3428_ = lean_ctor_get(v_inst_3420_, 1);
lean_inc(v_toBind_3428_);
lean_dec_ref(v_inst_3420_);
v_map_3429_ = lean_ctor_get(v_toFunctor_3427_, 0);
lean_inc(v_map_3429_);
lean_dec_ref(v_toFunctor_3427_);
v___f_3430_ = ((lean_object*)(l_Lake_cacheArtifact___redArg___closed__0));
v___x_3431_ = lean_box(v_text_3423_);
v___x_3432_ = lean_box(v_exe_3424_);
v___x_3433_ = lean_box(v_useLocalFile_3425_);
v___f_3434_ = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_3434_, 0, v_file_3421_);
lean_closure_set(v___f_3434_, 1, v_ext_3422_);
lean_closure_set(v___f_3434_, 2, v___x_3431_);
lean_closure_set(v___f_3434_, 3, v___x_3432_);
lean_closure_set(v___f_3434_, 4, v___x_3433_);
lean_closure_set(v___f_3434_, 5, v_inst_3419_);
v___x_3435_ = lean_apply_4(v_map_3429_, lean_box(0), lean_box(0), v___f_3430_, v_inst_3418_);
v___x_3436_ = lean_apply_4(v_toBind_3428_, lean_box(0), lean_box(0), v___x_3435_, v___f_3434_);
return v___x_3436_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___boxed(lean_object* v_inst_3437_, lean_object* v_inst_3438_, lean_object* v_inst_3439_, lean_object* v_file_3440_, lean_object* v_ext_3441_, lean_object* v_text_3442_, lean_object* v_exe_3443_, lean_object* v_useLocalFile_3444_){
_start:
{
uint8_t v_text_boxed_3445_; uint8_t v_exe_boxed_3446_; uint8_t v_useLocalFile_boxed_3447_; lean_object* v_res_3448_; 
v_text_boxed_3445_ = lean_unbox(v_text_3442_);
v_exe_boxed_3446_ = lean_unbox(v_exe_3443_);
v_useLocalFile_boxed_3447_ = lean_unbox(v_useLocalFile_3444_);
v_res_3448_ = l_Lake_cacheArtifact___redArg(v_inst_3437_, v_inst_3438_, v_inst_3439_, v_file_3440_, v_ext_3441_, v_text_boxed_3445_, v_exe_boxed_3446_, v_useLocalFile_boxed_3447_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact(lean_object* v_m_3449_, lean_object* v_inst_3450_, lean_object* v_inst_3451_, lean_object* v_inst_3452_, lean_object* v_file_3453_, lean_object* v_ext_3454_, uint8_t v_text_3455_, uint8_t v_exe_3456_, uint8_t v_useLocalFile_3457_){
_start:
{
lean_object* v_toApplicative_3458_; lean_object* v_toFunctor_3459_; lean_object* v_toBind_3460_; lean_object* v_map_3461_; lean_object* v___f_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___f_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v_toApplicative_3458_ = lean_ctor_get(v_inst_3452_, 0);
v_toFunctor_3459_ = lean_ctor_get(v_toApplicative_3458_, 0);
lean_inc_ref(v_toFunctor_3459_);
v_toBind_3460_ = lean_ctor_get(v_inst_3452_, 1);
lean_inc(v_toBind_3460_);
lean_dec_ref(v_inst_3452_);
v_map_3461_ = lean_ctor_get(v_toFunctor_3459_, 0);
lean_inc(v_map_3461_);
lean_dec_ref(v_toFunctor_3459_);
v___f_3462_ = ((lean_object*)(l_Lake_cacheArtifact___redArg___closed__0));
v___x_3463_ = lean_box(v_text_3455_);
v___x_3464_ = lean_box(v_exe_3456_);
v___x_3465_ = lean_box(v_useLocalFile_3457_);
v___f_3466_ = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_3466_, 0, v_file_3453_);
lean_closure_set(v___f_3466_, 1, v_ext_3454_);
lean_closure_set(v___f_3466_, 2, v___x_3463_);
lean_closure_set(v___f_3466_, 3, v___x_3464_);
lean_closure_set(v___f_3466_, 4, v___x_3465_);
lean_closure_set(v___f_3466_, 5, v_inst_3451_);
v___x_3467_ = lean_apply_4(v_map_3461_, lean_box(0), lean_box(0), v___f_3462_, v_inst_3450_);
v___x_3468_ = lean_apply_4(v_toBind_3460_, lean_box(0), lean_box(0), v___x_3467_, v___f_3466_);
return v___x_3468_;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___boxed(lean_object* v_m_3469_, lean_object* v_inst_3470_, lean_object* v_inst_3471_, lean_object* v_inst_3472_, lean_object* v_file_3473_, lean_object* v_ext_3474_, lean_object* v_text_3475_, lean_object* v_exe_3476_, lean_object* v_useLocalFile_3477_){
_start:
{
uint8_t v_text_boxed_3478_; uint8_t v_exe_boxed_3479_; uint8_t v_useLocalFile_boxed_3480_; lean_object* v_res_3481_; 
v_text_boxed_3478_ = lean_unbox(v_text_3475_);
v_exe_boxed_3479_ = lean_unbox(v_exe_3476_);
v_useLocalFile_boxed_3480_ = lean_unbox(v_useLocalFile_3477_);
v_res_3481_ = l_Lake_cacheArtifact(v_m_3469_, v_inst_3470_, v_inst_3471_, v_inst_3472_, v_file_3473_, v_ext_3474_, v_text_boxed_3478_, v_exe_boxed_3479_, v_useLocalFile_boxed_3480_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0(lean_object* v_x1_3483_, lean_object* v_x2_3484_){
_start:
{
lean_object* v_message_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v_message_3485_ = lean_ctor_get(v_x2_3484_, 0);
v___x_3486_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0));
v___x_3487_ = lean_string_append(v_x1_3483_, v___x_3486_);
v___x_3488_ = lean_string_append(v___x_3487_, v_message_3485_);
return v___x_3488_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___boxed(lean_object* v_x1_3489_, lean_object* v_x2_3490_){
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0(v_x1_3489_, v_x2_3490_);
lean_dec_ref(v_x2_3490_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(lean_object* v_inst_3495_, uint64_t v_inputHash_3496_, lean_object* v_pkg_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_){
_start:
{
lean_object* v_r_3506_; lean_object* v___y_3507_; uint8_t v___y_3510_; lean_object* v___y_3511_; uint8_t v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v_toContext_3521_; lean_object* v_log_3522_; uint8_t v_action_3523_; uint8_t v_wantsRebuild_3524_; lean_object* v_trace_3525_; lean_object* v_buildTime_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3592_; 
v_toContext_3521_ = lean_ctor_get(v_a_3502_, 1);
v_log_3522_ = lean_ctor_get(v_a_3503_, 0);
v_action_3523_ = lean_ctor_get_uint8(v_a_3503_, sizeof(void*)*3);
v_wantsRebuild_3524_ = lean_ctor_get_uint8(v_a_3503_, sizeof(void*)*3 + 1);
v_trace_3525_ = lean_ctor_get(v_a_3503_, 1);
v_buildTime_3526_ = lean_ctor_get(v_a_3503_, 2);
v_isSharedCheck_3592_ = !lean_is_exclusive(v_a_3503_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3528_ = v_a_3503_;
v_isShared_3529_ = v_isSharedCheck_3592_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_buildTime_3526_);
lean_inc(v_trace_3525_);
lean_inc(v_log_3522_);
lean_dec(v_a_3503_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3592_;
goto v_resetjp_3527_;
}
v___jp_3505_:
{
lean_object* v___x_3508_; 
v___x_3508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3508_, 0, v_r_3506_);
lean_ctor_set(v___x_3508_, 1, v___y_3507_);
return v___x_3508_;
}
v___jp_3509_:
{
uint8_t v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3516_ = 0;
v___x_3517_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3517_, 0, v___y_3515_);
lean_ctor_set_uint8(v___x_3517_, sizeof(void*)*1, v___x_3516_);
v___x_3518_ = lean_array_push(v___y_3514_, v___x_3517_);
v___x_3519_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3519_, 0, v___x_3518_);
lean_ctor_set(v___x_3519_, 1, v___y_3513_);
lean_ctor_set(v___x_3519_, 2, v___y_3511_);
lean_ctor_set_uint8(v___x_3519_, sizeof(void*)*3, v___y_3510_);
lean_ctor_set_uint8(v___x_3519_, sizeof(void*)*3 + 1, v___y_3512_);
v___x_3520_ = lean_box(0);
v_r_3506_ = v___x_3520_;
v___y_3507_ = v___x_3519_;
goto v___jp_3505_;
}
v_resetjp_3527_:
{
lean_object* v_lakeCache_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___f_3533_; lean_object* v_a_3535_; lean_object* v_log_3536_; uint8_t v_action_3537_; uint8_t v_wantsRebuild_3538_; lean_object* v_trace_3539_; lean_object* v_buildTime_3540_; 
v_lakeCache_3530_ = lean_ctor_get(v_toContext_3521_, 2);
v___x_3531_ = l_Lake_Package_cacheScope(v_pkg_3497_);
lean_inc_ref(v_lakeCache_3530_);
v___x_3532_ = l_Lake_Cache_readOutputs_x3f(v_lakeCache_3530_, v___x_3531_, v_inputHash_3496_, v_log_3522_);
v___f_3533_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__0));
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_a_3566_; lean_object* v_a_3567_; lean_object* v___x_3569_; 
v_a_3566_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_a_3566_);
v_a_3567_ = lean_ctor_get(v___x_3532_, 1);
lean_inc(v_a_3567_);
lean_dec_ref_known(v___x_3532_, 2);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v_a_3567_);
v___x_3569_ = v___x_3528_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3567_);
lean_ctor_set(v_reuseFailAlloc_3589_, 1, v_trace_3525_);
lean_ctor_set(v_reuseFailAlloc_3589_, 2, v_buildTime_3526_);
lean_ctor_set_uint8(v_reuseFailAlloc_3589_, sizeof(void*)*3, v_action_3523_);
lean_ctor_set_uint8(v_reuseFailAlloc_3589_, sizeof(void*)*3 + 1, v_wantsRebuild_3524_);
v___x_3569_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
if (lean_obj_tag(v_a_3566_) == 0)
{
lean_object* v___x_3570_; 
lean_dec_ref(v_a_3498_);
lean_dec_ref(v_inst_3495_);
v___x_3570_ = lean_box(0);
v_r_3506_ = v___x_3570_;
v___y_3507_ = v___x_3569_;
goto v___jp_3505_;
}
else
{
lean_object* v_val_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3588_; 
v_val_3571_ = lean_ctor_get(v_a_3566_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v_a_3566_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3573_ = v_a_3566_;
v_isShared_3574_ = v_isSharedCheck_3588_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_val_3571_);
lean_dec(v_a_3566_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3588_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3575_; 
lean_inc_ref(v_a_3502_);
lean_inc(v_a_3501_);
lean_inc(v_a_3500_);
lean_inc(v_a_3499_);
v___x_3575_ = lean_apply_8(v_inst_3495_, v_val_3571_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v___x_3569_, lean_box(0));
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v_a_3576_; lean_object* v_a_3577_; lean_object* v___x_3579_; 
v_a_3576_ = lean_ctor_get(v___x_3575_, 0);
lean_inc(v_a_3576_);
v_a_3577_ = lean_ctor_get(v___x_3575_, 1);
lean_inc(v_a_3577_);
lean_dec_ref_known(v___x_3575_, 2);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 0, v_a_3576_);
v___x_3579_ = v___x_3573_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_a_3576_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
v_r_3506_ = v___x_3579_;
v___y_3507_ = v_a_3577_;
goto v___jp_3505_;
}
}
else
{
lean_object* v_a_3581_; lean_object* v_a_3582_; lean_object* v_log_3583_; uint8_t v_action_3584_; uint8_t v_wantsRebuild_3585_; lean_object* v_trace_3586_; lean_object* v_buildTime_3587_; 
lean_del_object(v___x_3573_);
v_a_3581_ = lean_ctor_get(v___x_3575_, 1);
lean_inc(v_a_3581_);
v_a_3582_ = lean_ctor_get(v___x_3575_, 0);
lean_inc(v_a_3582_);
lean_dec_ref_known(v___x_3575_, 2);
v_log_3583_ = lean_ctor_get(v_a_3581_, 0);
lean_inc_ref(v_log_3583_);
v_action_3584_ = lean_ctor_get_uint8(v_a_3581_, sizeof(void*)*3);
v_wantsRebuild_3585_ = lean_ctor_get_uint8(v_a_3581_, sizeof(void*)*3 + 1);
v_trace_3586_ = lean_ctor_get(v_a_3581_, 1);
lean_inc_ref(v_trace_3586_);
v_buildTime_3587_ = lean_ctor_get(v_a_3581_, 2);
lean_inc(v_buildTime_3587_);
lean_dec(v_a_3581_);
v_a_3535_ = v_a_3582_;
v_log_3536_ = v_log_3583_;
v_action_3537_ = v_action_3584_;
v_wantsRebuild_3538_ = v_wantsRebuild_3585_;
v_trace_3539_ = v_trace_3586_;
v_buildTime_3540_ = v_buildTime_3587_;
goto v___jp_3534_;
}
}
}
}
}
else
{
lean_object* v_a_3590_; lean_object* v_a_3591_; 
lean_del_object(v___x_3528_);
lean_dec_ref(v_a_3498_);
lean_dec_ref(v_inst_3495_);
v_a_3590_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_a_3590_);
v_a_3591_ = lean_ctor_get(v___x_3532_, 1);
lean_inc(v_a_3591_);
lean_dec_ref_known(v___x_3532_, 2);
v_a_3535_ = v_a_3590_;
v_log_3536_ = v_a_3591_;
v_action_3537_ = v_action_3523_;
v_wantsRebuild_3538_ = v_wantsRebuild_3524_;
v_trace_3539_ = v_trace_3525_;
v_buildTime_3540_ = v_buildTime_3526_;
goto v___jp_3534_;
}
v___jp_3534_:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; uint8_t v___x_3558_; 
v___x_3541_ = lean_array_get_size(v_log_3536_);
lean_inc(v_a_3535_);
v___x_3542_ = l_Array_extract___redArg(v_log_3536_, v_a_3535_, v___x_3541_);
v___x_3543_ = l_Array_shrink___redArg(v_log_3536_, v_a_3535_);
lean_dec(v_a_3535_);
v___x_3544_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1));
v___x_3545_ = l_Lake_lowerHexUInt64(v_inputHash_3496_);
v___x_3546_ = lean_unsigned_to_nat(7u);
v___x_3547_ = lean_unsigned_to_nat(0u);
v___x_3548_ = lean_string_utf8_byte_size(v___x_3545_);
lean_inc_ref(v___x_3545_);
v___x_3549_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3545_);
lean_ctor_set(v___x_3549_, 1, v___x_3547_);
lean_ctor_set(v___x_3549_, 2, v___x_3548_);
v___x_3550_ = l_String_Slice_Pos_nextn(v___x_3549_, v___x_3547_, v___x_3546_);
lean_dec_ref_known(v___x_3549_, 3);
v___x_3551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3545_);
lean_ctor_set(v___x_3551_, 1, v___x_3547_);
lean_ctor_set(v___x_3551_, 2, v___x_3550_);
v___x_3552_ = l_String_Slice_toString(v___x_3551_);
lean_dec_ref_known(v___x_3551_, 3);
v___x_3553_ = lean_string_append(v___x_3544_, v___x_3552_);
lean_dec_ref(v___x_3552_);
v___x_3554_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__2));
v___x_3555_ = lean_string_append(v___x_3553_, v___x_3554_);
v___x_3556_ = lean_array_get_size(v___x_3542_);
v___x_3557_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__9));
v___x_3558_ = lean_nat_dec_lt(v___x_3547_, v___x_3556_);
if (v___x_3558_ == 0)
{
lean_dec_ref(v___x_3542_);
v___y_3510_ = v_action_3537_;
v___y_3511_ = v_buildTime_3540_;
v___y_3512_ = v_wantsRebuild_3538_;
v___y_3513_ = v_trace_3539_;
v___y_3514_ = v___x_3543_;
v___y_3515_ = v___x_3555_;
goto v___jp_3509_;
}
else
{
uint8_t v___x_3559_; 
v___x_3559_ = lean_nat_dec_le(v___x_3556_, v___x_3556_);
if (v___x_3559_ == 0)
{
if (v___x_3558_ == 0)
{
lean_dec_ref(v___x_3542_);
v___y_3510_ = v_action_3537_;
v___y_3511_ = v_buildTime_3540_;
v___y_3512_ = v_wantsRebuild_3538_;
v___y_3513_ = v_trace_3539_;
v___y_3514_ = v___x_3543_;
v___y_3515_ = v___x_3555_;
goto v___jp_3509_;
}
else
{
size_t v___x_3560_; size_t v___x_3561_; lean_object* v___x_3562_; 
v___x_3560_ = ((size_t)0ULL);
v___x_3561_ = lean_usize_of_nat(v___x_3556_);
v___x_3562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3557_, v___f_3533_, v___x_3542_, v___x_3560_, v___x_3561_, v___x_3555_);
v___y_3510_ = v_action_3537_;
v___y_3511_ = v_buildTime_3540_;
v___y_3512_ = v_wantsRebuild_3538_;
v___y_3513_ = v_trace_3539_;
v___y_3514_ = v___x_3543_;
v___y_3515_ = v___x_3562_;
goto v___jp_3509_;
}
}
else
{
size_t v___x_3563_; size_t v___x_3564_; lean_object* v___x_3565_; 
v___x_3563_ = ((size_t)0ULL);
v___x_3564_ = lean_usize_of_nat(v___x_3556_);
v___x_3565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3557_, v___f_3533_, v___x_3542_, v___x_3563_, v___x_3564_, v___x_3555_);
v___y_3510_ = v_action_3537_;
v___y_3511_ = v_buildTime_3540_;
v___y_3512_ = v_wantsRebuild_3538_;
v___y_3513_ = v_trace_3539_;
v___y_3514_ = v___x_3543_;
v___y_3515_ = v___x_3565_;
goto v___jp_3509_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___boxed(lean_object* v_inst_3593_, lean_object* v_inputHash_3594_, lean_object* v_pkg_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_){
_start:
{
uint64_t v_inputHash_boxed_3603_; lean_object* v_res_3604_; 
v_inputHash_boxed_3603_ = lean_unbox_uint64(v_inputHash_3594_);
lean_dec_ref(v_inputHash_3594_);
v_res_3604_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3593_, v_inputHash_boxed_3603_, v_pkg_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_);
lean_dec_ref(v_a_3600_);
lean_dec(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec(v_a_3597_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f(lean_object* v_00_u03b1_3605_, lean_object* v_inst_3606_, uint64_t v_inputHash_3607_, lean_object* v_pkg_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_){
_start:
{
lean_object* v___x_3616_; 
v___x_3616_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3606_, v_inputHash_3607_, v_pkg_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___boxed(lean_object* v_00_u03b1_3617_, lean_object* v_inst_3618_, lean_object* v_inputHash_3619_, lean_object* v_pkg_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_){
_start:
{
uint64_t v_inputHash_boxed_3628_; lean_object* v_res_3629_; 
v_inputHash_boxed_3628_ = lean_unbox_uint64(v_inputHash_3619_);
lean_dec_ref(v_inputHash_3619_);
v_res_3629_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f(v_00_u03b1_3617_, v_inst_3618_, v_inputHash_boxed_3628_, v_pkg_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_);
lean_dec_ref(v_a_3625_);
lean_dec(v_a_3624_);
lean_dec(v_a_3623_);
lean_dec(v_a_3622_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(lean_object* v_a_3630_, lean_object* v_____r_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3639_, 0, v_a_3630_);
v___x_3640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3640_, 0, v___x_3639_);
v___x_3641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3640_);
lean_ctor_set(v___x_3641_, 1, v___y_3637_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0___boxed(lean_object* v_a_3642_, lean_object* v_____r_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3642_, v_____r_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec(v___y_3647_);
lean_dec(v___y_3646_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg(lean_object* v_inst_3653_, uint64_t v_inputHash_3654_, lean_object* v_savedTrace_3655_, lean_object* v_pkg_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_){
_start:
{
lean_object* v___y_3665_; lean_object* v_a_3669_; lean_object* v_a_3670_; lean_object* v___y_3685_; 
if (lean_obj_tag(v_savedTrace_3655_) == 2)
{
lean_object* v_data_3700_; uint64_t v_depHash_3701_; lean_object* v_outputs_x3f_3702_; uint8_t v___x_3703_; 
v_data_3700_ = lean_ctor_get(v_savedTrace_3655_, 0);
lean_inc_ref(v_data_3700_);
lean_dec_ref_known(v_savedTrace_3655_, 1);
v_depHash_3701_ = lean_ctor_get_uint64(v_data_3700_, sizeof(void*)*3);
v_outputs_x3f_3702_ = lean_ctor_get(v_data_3700_, 1);
lean_inc(v_outputs_x3f_3702_);
lean_dec_ref(v_data_3700_);
v___x_3703_ = lean_uint64_dec_eq(v_depHash_3701_, v_inputHash_3654_);
if (v___x_3703_ == 0)
{
lean_dec(v_outputs_x3f_3702_);
lean_dec_ref(v_a_3657_);
lean_dec_ref(v_pkg_3656_);
lean_dec_ref(v_inst_3653_);
v___y_3665_ = v_a_3662_;
goto v___jp_3664_;
}
else
{
if (lean_obj_tag(v_outputs_x3f_3702_) == 1)
{
lean_object* v_val_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v_val_3704_ = lean_ctor_get(v_outputs_x3f_3702_, 0);
lean_inc_n(v_val_3704_, 2);
lean_dec_ref_known(v_outputs_x3f_3702_, 1);
v___x_3705_ = lean_box(0);
v___x_3706_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3706_, 0, v_val_3704_);
lean_ctor_set(v___x_3706_, 1, v___x_3705_);
lean_ctor_set(v___x_3706_, 2, v___x_3705_);
lean_inc_ref(v_a_3661_);
lean_inc(v_a_3660_);
lean_inc(v_a_3659_);
lean_inc(v_a_3658_);
lean_inc_ref(v_a_3657_);
v___x_3707_ = lean_apply_8(v_inst_3653_, v___x_3706_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, lean_box(0));
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_config_3708_; lean_object* v_a_3709_; lean_object* v_a_3710_; lean_object* v_enableArtifactCache_x3f_3711_; lean_object* v_a_3713_; uint8_t v_a_3717_; lean_object* v_a_3718_; 
v_config_3708_ = lean_ctor_get(v_pkg_3656_, 6);
v_a_3709_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_a_3709_);
v_a_3710_ = lean_ctor_get(v___x_3707_, 1);
lean_inc(v_a_3710_);
lean_dec_ref_known(v___x_3707_, 2);
v_enableArtifactCache_x3f_3711_ = lean_ctor_get(v_config_3708_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_3711_) == 0)
{
lean_object* v_toContext_3750_; lean_object* v_lakeEnv_3751_; lean_object* v_enableArtifactCache_x3f_3752_; 
v_toContext_3750_ = lean_ctor_get(v_a_3661_, 1);
v_lakeEnv_3751_ = lean_ctor_get(v_toContext_3750_, 0);
v_enableArtifactCache_x3f_3752_ = lean_ctor_get(v_lakeEnv_3751_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_3752_) == 0)
{
lean_object* v_packages_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v_config_3756_; lean_object* v_enableArtifactCache_x3f_3757_; 
v_packages_3753_ = lean_ctor_get(v_toContext_3750_, 4);
v___x_3754_ = lean_unsigned_to_nat(0u);
v___x_3755_ = lean_array_fget_borrowed(v_packages_3753_, v___x_3754_);
v_config_3756_ = lean_ctor_get(v___x_3755_, 6);
v_enableArtifactCache_x3f_3757_ = lean_ctor_get(v_config_3756_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_3757_) == 0)
{
lean_dec(v_val_3704_);
lean_dec_ref(v_pkg_3656_);
v_a_3713_ = v_a_3710_;
goto v___jp_3712_;
}
else
{
lean_object* v_val_3758_; uint8_t v___x_3759_; 
v_val_3758_ = lean_ctor_get(v_enableArtifactCache_x3f_3757_, 0);
v___x_3759_ = lean_unbox(v_val_3758_);
v_a_3717_ = v___x_3759_;
v_a_3718_ = v_a_3710_;
goto v___jp_3716_;
}
}
else
{
lean_object* v_val_3760_; uint8_t v___x_3761_; 
v_val_3760_ = lean_ctor_get(v_enableArtifactCache_x3f_3752_, 0);
v___x_3761_ = lean_unbox(v_val_3760_);
v_a_3717_ = v___x_3761_;
v_a_3718_ = v_a_3710_;
goto v___jp_3716_;
}
}
else
{
lean_object* v_val_3762_; uint8_t v___x_3763_; 
v_val_3762_ = lean_ctor_get(v_enableArtifactCache_x3f_3711_, 0);
v___x_3763_ = lean_unbox(v_val_3762_);
v_a_3717_ = v___x_3763_;
v_a_3718_ = v_a_3710_;
goto v___jp_3716_;
}
v___jp_3712_:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3714_ = lean_box(0);
v___x_3715_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3709_, v___x_3714_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3713_);
lean_dec_ref(v_a_3657_);
v___y_3685_ = v___x_3715_;
goto v___jp_3684_;
}
v___jp_3716_:
{
if (v_a_3717_ == 0)
{
lean_dec(v_val_3704_);
lean_dec_ref(v_pkg_3656_);
v_a_3713_ = v_a_3718_;
goto v___jp_3712_;
}
else
{
lean_object* v_toContext_3719_; lean_object* v_log_3720_; uint8_t v_action_3721_; uint8_t v_wantsRebuild_3722_; lean_object* v_trace_3723_; lean_object* v_buildTime_3724_; lean_object* v_lakeCache_3725_; lean_object* v___x_3726_; uint8_t v___x_3727_; lean_object* v___x_3728_; 
v_toContext_3719_ = lean_ctor_get(v_a_3661_, 1);
v_log_3720_ = lean_ctor_get(v_a_3718_, 0);
v_action_3721_ = lean_ctor_get_uint8(v_a_3718_, sizeof(void*)*3);
v_wantsRebuild_3722_ = lean_ctor_get_uint8(v_a_3718_, sizeof(void*)*3 + 1);
v_trace_3723_ = lean_ctor_get(v_a_3718_, 1);
v_buildTime_3724_ = lean_ctor_get(v_a_3718_, 2);
v_lakeCache_3725_ = lean_ctor_get(v_toContext_3719_, 2);
v___x_3726_ = l_Lake_Package_cacheScope(v_pkg_3656_);
v___x_3727_ = 0;
lean_inc_ref(v_lakeCache_3725_);
v___x_3728_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_3725_, v___x_3726_, v_inputHash_3654_, v_val_3704_, v___x_3705_, v___x_3705_, v___x_3727_);
if (lean_obj_tag(v___x_3728_) == 0)
{
lean_object* v___x_3729_; lean_object* v___x_3730_; 
lean_dec_ref_known(v___x_3728_, 1);
v___x_3729_ = lean_box(0);
v___x_3730_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3709_, v___x_3729_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3718_);
lean_dec_ref(v_a_3657_);
v___y_3685_ = v___x_3730_;
goto v___jp_3684_;
}
else
{
lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3746_; 
lean_inc(v_buildTime_3724_);
lean_inc_ref(v_trace_3723_);
lean_inc_ref(v_log_3720_);
v_isSharedCheck_3746_ = !lean_is_exclusive(v_a_3718_);
if (v_isSharedCheck_3746_ == 0)
{
lean_object* v_unused_3747_; lean_object* v_unused_3748_; lean_object* v_unused_3749_; 
v_unused_3747_ = lean_ctor_get(v_a_3718_, 2);
lean_dec(v_unused_3747_);
v_unused_3748_ = lean_ctor_get(v_a_3718_, 1);
lean_dec(v_unused_3748_);
v_unused_3749_ = lean_ctor_get(v_a_3718_, 0);
lean_dec(v_unused_3749_);
v___x_3732_ = v_a_3718_;
v_isShared_3733_ = v_isSharedCheck_3746_;
goto v_resetjp_3731_;
}
else
{
lean_dec(v_a_3718_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3746_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v_a_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; uint8_t v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3743_; 
v_a_3734_ = lean_ctor_get(v___x_3728_, 0);
lean_inc(v_a_3734_);
lean_dec_ref_known(v___x_3728_, 1);
v___x_3735_ = ((lean_object*)(l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0));
v___x_3736_ = lean_io_error_to_string(v_a_3734_);
v___x_3737_ = lean_string_append(v___x_3735_, v___x_3736_);
lean_dec_ref(v___x_3736_);
v___x_3738_ = 2;
v___x_3739_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3739_, 0, v___x_3737_);
lean_ctor_set_uint8(v___x_3739_, sizeof(void*)*1, v___x_3738_);
v___x_3740_ = lean_box(0);
v___x_3741_ = lean_array_push(v_log_3720_, v___x_3739_);
if (v_isShared_3733_ == 0)
{
lean_ctor_set(v___x_3732_, 0, v___x_3741_);
v___x_3743_ = v___x_3732_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v___x_3741_);
lean_ctor_set(v_reuseFailAlloc_3745_, 1, v_trace_3723_);
lean_ctor_set(v_reuseFailAlloc_3745_, 2, v_buildTime_3724_);
lean_ctor_set_uint8(v_reuseFailAlloc_3745_, sizeof(void*)*3, v_action_3721_);
lean_ctor_set_uint8(v_reuseFailAlloc_3745_, sizeof(void*)*3 + 1, v_wantsRebuild_3722_);
v___x_3743_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
lean_object* v___x_3744_; 
v___x_3744_ = l_Lake_getArtifactsUsingTrace_x3f___redArg___lam__0(v_a_3709_, v___x_3740_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v___x_3743_);
lean_dec_ref(v_a_3657_);
v___y_3685_ = v___x_3744_;
goto v___jp_3684_;
}
}
}
}
}
}
else
{
lean_object* v_a_3764_; lean_object* v_a_3765_; 
lean_dec(v_val_3704_);
lean_dec_ref(v_a_3657_);
lean_dec_ref(v_pkg_3656_);
v_a_3764_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_a_3764_);
v_a_3765_ = lean_ctor_get(v___x_3707_, 1);
lean_inc(v_a_3765_);
lean_dec_ref_known(v___x_3707_, 2);
v_a_3669_ = v_a_3764_;
v_a_3670_ = v_a_3765_;
goto v___jp_3668_;
}
}
else
{
lean_dec(v_outputs_x3f_3702_);
lean_dec_ref(v_a_3657_);
lean_dec_ref(v_pkg_3656_);
lean_dec_ref(v_inst_3653_);
v___y_3665_ = v_a_3662_;
goto v___jp_3664_;
}
}
}
else
{
lean_dec_ref(v_a_3657_);
lean_dec_ref(v_pkg_3656_);
lean_dec(v_savedTrace_3655_);
lean_dec_ref(v_inst_3653_);
v___y_3665_ = v_a_3662_;
goto v___jp_3664_;
}
v___jp_3664_:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3666_ = lean_box(0);
v___x_3667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3666_);
lean_ctor_set(v___x_3667_, 1, v___y_3665_);
return v___x_3667_;
}
v___jp_3668_:
{
lean_object* v_log_3671_; uint8_t v_action_3672_; uint8_t v_wantsRebuild_3673_; lean_object* v_trace_3674_; lean_object* v_buildTime_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3683_; 
v_log_3671_ = lean_ctor_get(v_a_3670_, 0);
v_action_3672_ = lean_ctor_get_uint8(v_a_3670_, sizeof(void*)*3);
v_wantsRebuild_3673_ = lean_ctor_get_uint8(v_a_3670_, sizeof(void*)*3 + 1);
v_trace_3674_ = lean_ctor_get(v_a_3670_, 1);
v_buildTime_3675_ = lean_ctor_get(v_a_3670_, 2);
v_isSharedCheck_3683_ = !lean_is_exclusive(v_a_3670_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3677_ = v_a_3670_;
v_isShared_3678_ = v_isSharedCheck_3683_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_buildTime_3675_);
lean_inc(v_trace_3674_);
lean_inc(v_log_3671_);
lean_dec(v_a_3670_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3683_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3679_; lean_object* v___x_3681_; 
v___x_3679_ = l_Array_shrink___redArg(v_log_3671_, v_a_3669_);
lean_dec(v_a_3669_);
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 0, v___x_3679_);
v___x_3681_ = v___x_3677_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v___x_3679_);
lean_ctor_set(v_reuseFailAlloc_3682_, 1, v_trace_3674_);
lean_ctor_set(v_reuseFailAlloc_3682_, 2, v_buildTime_3675_);
lean_ctor_set_uint8(v_reuseFailAlloc_3682_, sizeof(void*)*3, v_action_3672_);
lean_ctor_set_uint8(v_reuseFailAlloc_3682_, sizeof(void*)*3 + 1, v_wantsRebuild_3673_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
v___y_3665_ = v___x_3681_;
goto v___jp_3664_;
}
}
}
v___jp_3684_:
{
if (lean_obj_tag(v___y_3685_) == 0)
{
lean_object* v_a_3686_; 
v_a_3686_ = lean_ctor_get(v___y_3685_, 0);
if (lean_obj_tag(v_a_3686_) == 0)
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3695_; 
lean_inc_ref(v_a_3686_);
v_a_3687_ = lean_ctor_get(v___y_3685_, 1);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___y_3685_);
if (v_isSharedCheck_3695_ == 0)
{
lean_object* v_unused_3696_; 
v_unused_3696_ = lean_ctor_get(v___y_3685_, 0);
lean_dec(v_unused_3696_);
v___x_3689_ = v___y_3685_;
v_isShared_3690_ = v_isSharedCheck_3695_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___y_3685_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3695_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v_a_3691_; lean_object* v___x_3693_; 
v_a_3691_ = lean_ctor_get(v_a_3686_, 0);
lean_inc(v_a_3691_);
lean_dec_ref_known(v_a_3686_, 1);
if (v_isShared_3690_ == 0)
{
lean_ctor_set(v___x_3689_, 0, v_a_3691_);
v___x_3693_ = v___x_3689_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_a_3691_);
lean_ctor_set(v_reuseFailAlloc_3694_, 1, v_a_3687_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
else
{
lean_object* v_a_3697_; 
v_a_3697_ = lean_ctor_get(v___y_3685_, 1);
lean_inc(v_a_3697_);
lean_dec_ref_known(v___y_3685_, 2);
v___y_3665_ = v_a_3697_;
goto v___jp_3664_;
}
}
else
{
lean_object* v_a_3698_; lean_object* v_a_3699_; 
v_a_3698_ = lean_ctor_get(v___y_3685_, 0);
lean_inc(v_a_3698_);
v_a_3699_ = lean_ctor_get(v___y_3685_, 1);
lean_inc(v_a_3699_);
lean_dec_ref_known(v___y_3685_, 2);
v_a_3669_ = v_a_3698_;
v_a_3670_ = v_a_3699_;
goto v___jp_3668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___redArg___boxed(lean_object* v_inst_3766_, lean_object* v_inputHash_3767_, lean_object* v_savedTrace_3768_, lean_object* v_pkg_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_){
_start:
{
uint64_t v_inputHash_boxed_3777_; lean_object* v_res_3778_; 
v_inputHash_boxed_3777_ = lean_unbox_uint64(v_inputHash_3767_);
lean_dec_ref(v_inputHash_3767_);
v_res_3778_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3766_, v_inputHash_boxed_3777_, v_savedTrace_3768_, v_pkg_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_);
lean_dec_ref(v_a_3774_);
lean_dec(v_a_3773_);
lean_dec(v_a_3772_);
lean_dec(v_a_3771_);
return v_res_3778_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f(lean_object* v_00_u03b1_3779_, lean_object* v_inst_3780_, uint64_t v_inputHash_3781_, lean_object* v_savedTrace_3782_, lean_object* v_pkg_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_){
_start:
{
lean_object* v___x_3791_; 
v___x_3791_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3780_, v_inputHash_3781_, v_savedTrace_3782_, v_pkg_3783_, v_a_3784_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_, v_a_3789_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___boxed(lean_object* v_00_u03b1_3792_, lean_object* v_inst_3793_, lean_object* v_inputHash_3794_, lean_object* v_savedTrace_3795_, lean_object* v_pkg_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_){
_start:
{
uint64_t v_inputHash_boxed_3804_; lean_object* v_res_3805_; 
v_inputHash_boxed_3804_ = lean_unbox_uint64(v_inputHash_3794_);
lean_dec_ref(v_inputHash_3794_);
v_res_3805_ = l_Lake_getArtifactsUsingTrace_x3f(v_00_u03b1_3792_, v_inst_3793_, v_inputHash_boxed_3804_, v_savedTrace_3795_, v_pkg_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_);
lean_dec_ref(v_a_3801_);
lean_dec(v_a_3800_);
lean_dec(v_a_3799_);
lean_dec(v_a_3798_);
return v_res_3805_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg(lean_object* v_inst_3806_, uint64_t v_inputHash_3807_, lean_object* v_savedTrace_3808_, lean_object* v_pkg_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_){
_start:
{
lean_object* v_a_3818_; lean_object* v___y_3819_; lean_object* v___x_3822_; lean_object* v_a_3823_; 
lean_inc_ref(v_a_3810_);
lean_inc_ref(v_pkg_3809_);
lean_inc_ref(v_inst_3806_);
v___x_3822_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3806_, v_inputHash_3807_, v_savedTrace_3808_, v_pkg_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_);
v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
lean_inc(v_a_3823_);
if (lean_obj_tag(v_a_3823_) == 1)
{
lean_object* v_a_3824_; lean_object* v_val_3825_; 
lean_dec_ref(v_a_3810_);
lean_dec_ref(v_pkg_3809_);
lean_dec_ref(v_inst_3806_);
v_a_3824_ = lean_ctor_get(v___x_3822_, 1);
lean_inc(v_a_3824_);
lean_dec_ref(v___x_3822_);
v_val_3825_ = lean_ctor_get(v_a_3823_, 0);
lean_inc(v_val_3825_);
lean_dec_ref_known(v_a_3823_, 1);
v_a_3818_ = v_val_3825_;
v___y_3819_ = v_a_3824_;
goto v___jp_3817_;
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3827_; lean_object* v_a_3828_; 
lean_dec(v_a_3823_);
v_a_3826_ = lean_ctor_get(v___x_3822_, 1);
lean_inc(v_a_3826_);
lean_dec_ref(v___x_3822_);
v___x_3827_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3806_, v_inputHash_3807_, v_pkg_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3826_);
v_a_3828_ = lean_ctor_get(v___x_3827_, 0);
lean_inc(v_a_3828_);
if (lean_obj_tag(v_a_3828_) == 1)
{
lean_object* v_a_3829_; lean_object* v_val_3830_; 
v_a_3829_ = lean_ctor_get(v___x_3827_, 1);
lean_inc(v_a_3829_);
lean_dec_ref(v___x_3827_);
v_val_3830_ = lean_ctor_get(v_a_3828_, 0);
lean_inc(v_val_3830_);
lean_dec_ref_known(v_a_3828_, 1);
v_a_3818_ = v_val_3830_;
v___y_3819_ = v_a_3829_;
goto v___jp_3817_;
}
else
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3839_; 
lean_dec(v_a_3828_);
v_a_3831_ = lean_ctor_get(v___x_3827_, 1);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3839_ == 0)
{
lean_object* v_unused_3840_; 
v_unused_3840_ = lean_ctor_get(v___x_3827_, 0);
lean_dec(v_unused_3840_);
v___x_3833_ = v___x_3827_;
v_isShared_3834_ = v_isSharedCheck_3839_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v___x_3827_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3839_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3835_; lean_object* v___x_3837_; 
v___x_3835_ = lean_box(0);
if (v_isShared_3834_ == 0)
{
lean_ctor_set(v___x_3833_, 0, v___x_3835_);
v___x_3837_ = v___x_3833_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v___x_3835_);
lean_ctor_set(v_reuseFailAlloc_3838_, 1, v_a_3831_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
}
v___jp_3817_:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3820_, 0, v_a_3818_);
v___x_3821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3820_);
lean_ctor_set(v___x_3821_, 1, v___y_3819_);
return v___x_3821_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___boxed(lean_object* v_inst_3841_, lean_object* v_inputHash_3842_, lean_object* v_savedTrace_3843_, lean_object* v_pkg_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_){
_start:
{
uint64_t v_inputHash_boxed_3852_; lean_object* v_res_3853_; 
v_inputHash_boxed_3852_ = lean_unbox_uint64(v_inputHash_3842_);
lean_dec_ref(v_inputHash_3842_);
v_res_3853_ = l_Lake_getArtifacts_x3f___redArg(v_inst_3841_, v_inputHash_boxed_3852_, v_savedTrace_3843_, v_pkg_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_);
lean_dec_ref(v_a_3849_);
lean_dec(v_a_3848_);
lean_dec(v_a_3847_);
lean_dec(v_a_3846_);
return v_res_3853_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f(lean_object* v_00_u03b1_3854_, lean_object* v_inst_3855_, uint64_t v_inputHash_3856_, lean_object* v_savedTrace_3857_, lean_object* v_pkg_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_){
_start:
{
lean_object* v_a_3867_; lean_object* v___y_3868_; lean_object* v___x_3871_; lean_object* v_a_3872_; 
lean_inc_ref(v_a_3859_);
lean_inc_ref(v_pkg_3858_);
lean_inc_ref(v_inst_3855_);
v___x_3871_ = l_Lake_getArtifactsUsingTrace_x3f___redArg(v_inst_3855_, v_inputHash_3856_, v_savedTrace_3857_, v_pkg_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_);
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_a_3872_);
if (lean_obj_tag(v_a_3872_) == 1)
{
lean_object* v_a_3873_; lean_object* v_val_3874_; 
lean_dec_ref(v_a_3859_);
lean_dec_ref(v_pkg_3858_);
lean_dec_ref(v_inst_3855_);
v_a_3873_ = lean_ctor_get(v___x_3871_, 1);
lean_inc(v_a_3873_);
lean_dec_ref(v___x_3871_);
v_val_3874_ = lean_ctor_get(v_a_3872_, 0);
lean_inc(v_val_3874_);
lean_dec_ref_known(v_a_3872_, 1);
v_a_3867_ = v_val_3874_;
v___y_3868_ = v_a_3873_;
goto v___jp_3866_;
}
else
{
lean_object* v_a_3875_; lean_object* v___x_3876_; lean_object* v_a_3877_; 
lean_dec(v_a_3872_);
v_a_3875_ = lean_ctor_get(v___x_3871_, 1);
lean_inc(v_a_3875_);
lean_dec_ref(v___x_3871_);
v___x_3876_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg(v_inst_3855_, v_inputHash_3856_, v_pkg_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3875_);
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_a_3877_);
if (lean_obj_tag(v_a_3877_) == 1)
{
lean_object* v_a_3878_; lean_object* v_val_3879_; 
v_a_3878_ = lean_ctor_get(v___x_3876_, 1);
lean_inc(v_a_3878_);
lean_dec_ref(v___x_3876_);
v_val_3879_ = lean_ctor_get(v_a_3877_, 0);
lean_inc(v_val_3879_);
lean_dec_ref_known(v_a_3877_, 1);
v_a_3867_ = v_val_3879_;
v___y_3868_ = v_a_3878_;
goto v___jp_3866_;
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3888_; 
lean_dec(v_a_3877_);
v_a_3880_ = lean_ctor_get(v___x_3876_, 1);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3888_ == 0)
{
lean_object* v_unused_3889_; 
v_unused_3889_ = lean_ctor_get(v___x_3876_, 0);
lean_dec(v_unused_3889_);
v___x_3882_ = v___x_3876_;
v_isShared_3883_ = v_isSharedCheck_3888_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3876_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3888_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3884_; lean_object* v___x_3886_; 
v___x_3884_ = lean_box(0);
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 0, v___x_3884_);
v___x_3886_ = v___x_3882_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3884_);
lean_ctor_set(v_reuseFailAlloc_3887_, 1, v_a_3880_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
}
v___jp_3866_:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3869_, 0, v_a_3867_);
v___x_3870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3869_);
lean_ctor_set(v___x_3870_, 1, v___y_3868_);
return v___x_3870_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___boxed(lean_object* v_00_u03b1_3890_, lean_object* v_inst_3891_, lean_object* v_inputHash_3892_, lean_object* v_savedTrace_3893_, lean_object* v_pkg_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_){
_start:
{
uint64_t v_inputHash_boxed_3902_; lean_object* v_res_3903_; 
v_inputHash_boxed_3902_ = lean_unbox_uint64(v_inputHash_3892_);
lean_dec_ref(v_inputHash_3892_);
v_res_3903_ = l_Lake_getArtifacts_x3f(v_00_u03b1_3890_, v_inst_3891_, v_inputHash_boxed_3902_, v_savedTrace_3893_, v_pkg_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_);
lean_dec_ref(v_a_3899_);
lean_dec(v_a_3898_);
lean_dec(v_a_3897_);
lean_dec(v_a_3896_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__0(lean_object* v_descr_3904_, lean_object* v___x_3905_, lean_object* v_mtime_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_){
_start:
{
lean_object* v___x_3914_; lean_object* v___x_3915_; 
lean_inc_ref(v___x_3905_);
v___x_3914_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3914_, 0, v_descr_3904_);
lean_ctor_set(v___x_3914_, 1, v___x_3905_);
lean_ctor_set(v___x_3914_, 2, v___x_3905_);
lean_ctor_set(v___x_3914_, 3, v_mtime_3906_);
v___x_3915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3914_);
lean_ctor_set(v___x_3915_, 1, v___y_3912_);
return v___x_3915_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__0___boxed(lean_object* v_descr_3916_, lean_object* v___x_3917_, lean_object* v_mtime_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_){
_start:
{
lean_object* v_res_3926_; 
v_res_3926_ = l_Lake_resolveArtifact___lam__0(v_descr_3916_, v___x_3917_, v_mtime_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_);
lean_dec_ref(v___y_3923_);
lean_dec(v___y_3922_);
lean_dec(v___y_3921_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
return v_res_3926_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__1(lean_object* v___x_3928_, lean_object* v___f_3929_, lean_object* v_____r_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_){
_start:
{
lean_object* v_log_3938_; uint8_t v_action_3939_; uint8_t v_wantsRebuild_3940_; lean_object* v_trace_3941_; lean_object* v_buildTime_3942_; lean_object* v___x_3943_; 
v_log_3938_ = lean_ctor_get(v___y_3936_, 0);
v_action_3939_ = lean_ctor_get_uint8(v___y_3936_, sizeof(void*)*3);
v_wantsRebuild_3940_ = lean_ctor_get_uint8(v___y_3936_, sizeof(void*)*3 + 1);
v_trace_3941_ = lean_ctor_get(v___y_3936_, 1);
v_buildTime_3942_ = lean_ctor_get(v___y_3936_, 2);
v___x_3943_ = lean_io_metadata(v___x_3928_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; lean_object* v_modified_3945_; lean_object* v___x_3946_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3944_);
lean_dec_ref_known(v___x_3943_, 1);
v_modified_3945_ = lean_ctor_get(v_a_3944_, 1);
lean_inc_ref(v_modified_3945_);
lean_dec(v_a_3944_);
lean_inc_ref(v___y_3935_);
lean_inc(v___y_3934_);
lean_inc(v___y_3933_);
lean_inc(v___y_3932_);
v___x_3946_ = lean_apply_8(v___f_3929_, v_modified_3945_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, lean_box(0));
return v___x_3946_;
}
else
{
lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3962_; 
lean_inc(v_buildTime_3942_);
lean_inc_ref(v_trace_3941_);
lean_inc_ref(v_log_3938_);
lean_dec_ref(v___y_3931_);
lean_dec_ref(v___f_3929_);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___y_3936_);
if (v_isSharedCheck_3962_ == 0)
{
lean_object* v_unused_3963_; lean_object* v_unused_3964_; lean_object* v_unused_3965_; 
v_unused_3963_ = lean_ctor_get(v___y_3936_, 2);
lean_dec(v_unused_3963_);
v_unused_3964_ = lean_ctor_get(v___y_3936_, 1);
lean_dec(v_unused_3964_);
v_unused_3965_ = lean_ctor_get(v___y_3936_, 0);
lean_dec(v_unused_3965_);
v___x_3948_ = v___y_3936_;
v_isShared_3949_ = v_isSharedCheck_3962_;
goto v_resetjp_3947_;
}
else
{
lean_dec(v___y_3936_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3962_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v_a_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; uint8_t v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3959_; 
v_a_3950_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3950_);
lean_dec_ref_known(v___x_3943_, 1);
v___x_3951_ = ((lean_object*)(l_Lake_resolveArtifact___lam__1___closed__0));
v___x_3952_ = lean_io_error_to_string(v_a_3950_);
v___x_3953_ = lean_string_append(v___x_3951_, v___x_3952_);
lean_dec_ref(v___x_3952_);
v___x_3954_ = 3;
v___x_3955_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3955_, 0, v___x_3953_);
lean_ctor_set_uint8(v___x_3955_, sizeof(void*)*1, v___x_3954_);
v___x_3956_ = lean_array_get_size(v_log_3938_);
v___x_3957_ = lean_array_push(v_log_3938_, v___x_3955_);
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 0, v___x_3957_);
v___x_3959_ = v___x_3948_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v___x_3957_);
lean_ctor_set(v_reuseFailAlloc_3961_, 1, v_trace_3941_);
lean_ctor_set(v_reuseFailAlloc_3961_, 2, v_buildTime_3942_);
lean_ctor_set_uint8(v_reuseFailAlloc_3961_, sizeof(void*)*3, v_action_3939_);
lean_ctor_set_uint8(v_reuseFailAlloc_3961_, sizeof(void*)*3 + 1, v_wantsRebuild_3940_);
v___x_3959_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
lean_object* v___x_3960_; 
v___x_3960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3956_);
lean_ctor_set(v___x_3960_, 1, v___x_3959_);
return v___x_3960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___lam__1___boxed(lean_object* v___x_3966_, lean_object* v___f_3967_, lean_object* v_____r_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l_Lake_resolveArtifact___lam__1(v___x_3966_, v___f_3967_, v_____r_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_);
lean_dec_ref(v___y_3973_);
lean_dec(v___y_3972_);
lean_dec(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec_ref(v___x_3966_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact(lean_object* v_descr_3988_, lean_object* v_service_x3f_3989_, lean_object* v_scope_x3f_3990_, uint8_t v_exe_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_){
_start:
{
lean_object* v___y_4000_; lean_object* v_a_4001_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v_toContext_4007_; lean_object* v_log_4008_; uint8_t v_action_4009_; uint8_t v_wantsRebuild_4010_; lean_object* v_trace_4011_; lean_object* v_buildTime_4012_; lean_object* v_lakeConfig_4013_; lean_object* v_lakeCache_4014_; uint64_t v_hash_4015_; lean_object* v_ext_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___y_4020_; lean_object* v___x_4118_; lean_object* v___x_4119_; uint8_t v___x_4120_; 
v_toContext_4007_ = lean_ctor_get(v_a_3996_, 1);
v_log_4008_ = lean_ctor_get(v_a_3997_, 0);
v_action_4009_ = lean_ctor_get_uint8(v_a_3997_, sizeof(void*)*3);
v_wantsRebuild_4010_ = lean_ctor_get_uint8(v_a_3997_, sizeof(void*)*3 + 1);
v_trace_4011_ = lean_ctor_get(v_a_3997_, 1);
v_buildTime_4012_ = lean_ctor_get(v_a_3997_, 2);
v_lakeConfig_4013_ = lean_ctor_get(v_toContext_4007_, 1);
v_lakeCache_4014_ = lean_ctor_get(v_toContext_4007_, 2);
v_hash_4015_ = lean_ctor_get_uint64(v_descr_3988_, sizeof(void*)*1);
v_ext_4016_ = lean_ctor_get(v_descr_3988_, 0);
v___x_4017_ = ((lean_object*)(l_Lake_Cache_saveArtifact___closed__1));
lean_inc_ref(v_lakeCache_4014_);
v___x_4018_ = l_System_FilePath_join(v_lakeCache_4014_, v___x_4017_);
v___x_4118_ = lean_string_utf8_byte_size(v_ext_4016_);
v___x_4119_ = lean_unsigned_to_nat(0u);
v___x_4120_ = lean_nat_dec_eq(v___x_4118_, v___x_4119_);
if (v___x_4120_ == 0)
{
lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4121_ = l_Lake_lowerHexUInt64(v_hash_4015_);
v___x_4122_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_4123_ = lean_string_append(v___x_4121_, v___x_4122_);
v___x_4124_ = lean_string_append(v___x_4123_, v_ext_4016_);
v___y_4020_ = v___x_4124_;
goto v___jp_4019_;
}
else
{
lean_object* v___x_4125_; 
v___x_4125_ = l_Lake_lowerHexUInt64(v_hash_4015_);
v___y_4020_ = v___x_4125_;
goto v___jp_4019_;
}
v___jp_3999_:
{
lean_object* v___x_4002_; 
v___x_4002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4002_, 0, v___y_4000_);
lean_ctor_set(v___x_4002_, 1, v_a_4001_);
return v___x_4002_;
}
v___jp_4003_:
{
if (lean_obj_tag(v___y_4005_) == 0)
{
lean_dec(v___y_4004_);
return v___y_4005_;
}
else
{
lean_object* v_a_4006_; 
v_a_4006_ = lean_ctor_get(v___y_4005_, 1);
lean_inc(v_a_4006_);
lean_dec_ref_known(v___y_4005_, 2);
v___y_4000_ = v___y_4004_;
v_a_4001_ = v_a_4006_;
goto v___jp_3999_;
}
}
v___jp_4019_:
{
lean_object* v___x_4021_; lean_object* v___f_4022_; lean_object* v___x_4023_; 
v___x_4021_ = l_Lake_joinRelative(v___x_4018_, v___y_4020_);
lean_inc_ref(v___x_4021_);
lean_inc_ref(v_descr_3988_);
v___f_4022_ = lean_alloc_closure((void*)(l_Lake_resolveArtifact___lam__0___boxed), 10, 2);
lean_closure_set(v___f_4022_, 0, v_descr_3988_);
lean_closure_set(v___f_4022_, 1, v___x_4021_);
v___x_4023_ = lean_io_metadata(v___x_4021_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_object* v_a_4024_; lean_object* v_modified_4025_; lean_object* v___x_4026_; 
lean_dec_ref(v___f_4022_);
lean_dec(v_scope_x3f_3990_);
lean_dec(v_service_x3f_3989_);
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
lean_inc(v_a_4024_);
lean_dec_ref_known(v___x_4023_, 1);
v_modified_4025_ = lean_ctor_get(v_a_4024_, 1);
lean_inc_ref(v_modified_4025_);
lean_dec(v_a_4024_);
v___x_4026_ = l_Lake_resolveArtifact___lam__0(v_descr_3988_, v___x_4021_, v_modified_4025_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_);
lean_dec_ref(v_a_3992_);
return v___x_4026_;
}
else
{
lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4114_; 
lean_inc(v_buildTime_4012_);
lean_inc_ref(v_trace_4011_);
lean_inc_ref(v_log_4008_);
lean_dec_ref(v_descr_3988_);
v_isSharedCheck_4114_ = !lean_is_exclusive(v_a_3997_);
if (v_isSharedCheck_4114_ == 0)
{
lean_object* v_unused_4115_; lean_object* v_unused_4116_; lean_object* v_unused_4117_; 
v_unused_4115_ = lean_ctor_get(v_a_3997_, 2);
lean_dec(v_unused_4115_);
v_unused_4116_ = lean_ctor_get(v_a_3997_, 1);
lean_dec(v_unused_4116_);
v_unused_4117_ = lean_ctor_get(v_a_3997_, 0);
lean_dec(v_unused_4117_);
v___x_4028_ = v_a_3997_;
v_isShared_4029_ = v_isSharedCheck_4114_;
goto v_resetjp_4027_;
}
else
{
lean_dec(v_a_3997_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4114_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v_a_4030_; 
v_a_4030_ = lean_ctor_get(v___x_4023_, 0);
lean_inc(v_a_4030_);
lean_dec_ref_known(v___x_4023_, 1);
if (lean_obj_tag(v_a_4030_) == 11)
{
lean_object* v___x_4031_; 
lean_dec_ref_known(v_a_4030_, 2);
v___x_4031_ = lean_array_get_size(v_log_4008_);
if (lean_obj_tag(v_service_x3f_3989_) == 1)
{
lean_object* v_val_4032_; lean_object* v_cacheServices_4033_; uint8_t v___x_4034_; uint8_t v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; 
v_val_4032_ = lean_ctor_get(v_service_x3f_3989_, 0);
lean_inc_n(v_val_4032_, 2);
lean_dec_ref_known(v_service_x3f_3989_, 1);
v_cacheServices_4033_ = lean_ctor_get(v_lakeConfig_4013_, 3);
v___x_4034_ = 4;
v___x_4035_ = l_Lake_JobAction_merge(v_action_4009_, v___x_4034_);
v___x_4036_ = lean_box(0);
v___x_4037_ = l_Lean_Name_str___override(v___x_4036_, v_val_4032_);
v___x_4038_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_cacheServices_4033_, v___x_4037_);
lean_dec(v___x_4037_);
if (lean_obj_tag(v___x_4038_) == 1)
{
lean_dec(v_val_4032_);
if (lean_obj_tag(v_scope_x3f_3990_) == 1)
{
lean_object* v_val_4039_; lean_object* v_val_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; uint8_t v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
v_val_4039_ = lean_ctor_get(v___x_4038_, 0);
lean_inc(v_val_4039_);
lean_dec_ref_known(v___x_4038_, 1);
v_val_4040_ = lean_ctor_get(v_scope_x3f_3990_, 0);
lean_inc(v_val_4040_);
lean_dec_ref_known(v_scope_x3f_3990_, 1);
v___x_4041_ = l_Lake_CacheService_artifactUrl(v_hash_4015_, v_val_4039_, v_val_4040_);
v___x_4042_ = ((lean_object*)(l_Lake_resolveArtifact___closed__0));
v___x_4043_ = l_Lake_lowerHexUInt64(v_hash_4015_);
v___x_4044_ = lean_string_append(v___x_4042_, v___x_4043_);
lean_dec_ref(v___x_4043_);
v___x_4045_ = ((lean_object*)(l_Lake_resolveArtifact___closed__1));
v___x_4046_ = lean_string_append(v___x_4044_, v___x_4045_);
v___x_4047_ = lean_string_append(v___x_4046_, v___x_4021_);
v___x_4048_ = ((lean_object*)(l_Lake_resolveArtifact___closed__2));
v___x_4049_ = lean_string_append(v___x_4047_, v___x_4048_);
v___x_4050_ = lean_string_append(v___x_4049_, v___x_4041_);
v___x_4051_ = 0;
v___x_4052_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4052_, 0, v___x_4050_);
lean_ctor_set_uint8(v___x_4052_, sizeof(void*)*1, v___x_4051_);
v___x_4053_ = lean_array_push(v_log_4008_, v___x_4052_);
lean_inc_ref(v___x_4021_);
v___x_4054_ = l_Lake_downloadArtifactCore(v_hash_4015_, v___x_4041_, v___x_4021_, v___x_4053_);
if (lean_obj_tag(v___x_4054_) == 0)
{
lean_object* v_a_4055_; uint8_t v___x_4056_; uint8_t v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v_a_4055_ = lean_ctor_get(v___x_4054_, 1);
lean_inc(v_a_4055_);
lean_dec_ref_known(v___x_4054_, 2);
v___x_4056_ = 1;
v___x_4057_ = 0;
v___x_4058_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4058_, 0, v___x_4056_);
lean_ctor_set_uint8(v___x_4058_, 1, v___x_4057_);
lean_ctor_set_uint8(v___x_4058_, 2, v_exe_3991_);
lean_inc_ref_n(v___x_4058_, 2);
v___x_4059_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4058_);
lean_ctor_set(v___x_4059_, 1, v___x_4058_);
lean_ctor_set(v___x_4059_, 2, v___x_4058_);
v___x_4060_ = l_IO_setAccessRights(v___x_4021_, v___x_4059_);
lean_dec_ref_known(v___x_4059_, 3);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v___x_4062_; 
lean_dec_ref_known(v___x_4060_, 1);
if (v_isShared_4029_ == 0)
{
lean_ctor_set(v___x_4028_, 0, v_a_4055_);
v___x_4062_ = v___x_4028_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_a_4055_);
lean_ctor_set(v_reuseFailAlloc_4065_, 1, v_trace_4011_);
lean_ctor_set(v_reuseFailAlloc_4065_, 2, v_buildTime_4012_);
lean_ctor_set_uint8(v_reuseFailAlloc_4065_, sizeof(void*)*3 + 1, v_wantsRebuild_4010_);
v___x_4062_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; 
lean_ctor_set_uint8(v___x_4062_, sizeof(void*)*3, v___x_4035_);
v___x_4063_ = lean_box(0);
v___x_4064_ = l_Lake_resolveArtifact___lam__1(v___x_4021_, v___f_4022_, v___x_4063_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_, v___x_4062_);
lean_dec_ref(v___x_4021_);
v___y_4004_ = v___x_4031_;
v___y_4005_ = v___x_4064_;
goto v___jp_4003_;
}
}
else
{
lean_object* v_a_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; uint8_t v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4075_; 
v_a_4066_ = lean_ctor_get(v___x_4060_, 0);
lean_inc(v_a_4066_);
lean_dec_ref_known(v___x_4060_, 1);
v___x_4067_ = ((lean_object*)(l_Lake_resolveArtifact___closed__3));
v___x_4068_ = lean_io_error_to_string(v_a_4066_);
v___x_4069_ = lean_string_append(v___x_4067_, v___x_4068_);
lean_dec_ref(v___x_4068_);
v___x_4070_ = 2;
v___x_4071_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4071_, 0, v___x_4069_);
lean_ctor_set_uint8(v___x_4071_, sizeof(void*)*1, v___x_4070_);
v___x_4072_ = lean_box(0);
v___x_4073_ = lean_array_push(v_a_4055_, v___x_4071_);
if (v_isShared_4029_ == 0)
{
lean_ctor_set(v___x_4028_, 0, v___x_4073_);
v___x_4075_ = v___x_4028_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v___x_4073_);
lean_ctor_set(v_reuseFailAlloc_4077_, 1, v_trace_4011_);
lean_ctor_set(v_reuseFailAlloc_4077_, 2, v_buildTime_4012_);
lean_ctor_set_uint8(v_reuseFailAlloc_4077_, sizeof(void*)*3 + 1, v_wantsRebuild_4010_);
v___x_4075_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
lean_object* v___x_4076_; 
lean_ctor_set_uint8(v___x_4075_, sizeof(void*)*3, v___x_4035_);
v___x_4076_ = l_Lake_resolveArtifact___lam__1(v___x_4021_, v___f_4022_, v___x_4072_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_, v___x_4075_);
lean_dec_ref(v___x_4021_);
v___y_4004_ = v___x_4031_;
v___y_4005_ = v___x_4076_;
goto v___jp_4003_;
}
}
}
else
{
lean_object* v_a_4078_; lean_object* v___x_4080_; 
lean_dec_ref(v___f_4022_);
lean_dec_ref(v___x_4021_);
lean_dec_ref(v_a_3992_);
v_a_4078_ = lean_ctor_get(v___x_4054_, 1);
lean_inc(v_a_4078_);
lean_dec_ref_known(v___x_4054_, 2);
if (v_isShared_4029_ == 0)
{
lean_ctor_set(v___x_4028_, 0, v_a_4078_);
v___x_4080_ = v___x_4028_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_a_4078_);
lean_ctor_set(v_reuseFailAlloc_4081_, 1, v_trace_4011_);
lean_ctor_set(v_reuseFailAlloc_4081_, 2, v_buildTime_4012_);
lean_ctor_set_uint8(v_reuseFailAlloc_4081_, sizeof(void*)*3 + 1, v_wantsRebuild_4010_);
v___x_4080_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
lean_ctor_set_uint8(v___x_4080_, sizeof(void*)*3, v___x_4035_);
v___y_4000_ = v___x_4031_;
v_a_4001_ = v___x_4080_;
goto v___jp_3999_;
}
}
}
else
{
lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4085_; 
lean_dec_ref_known(v___x_4038_, 1);
lean_dec_ref(v___f_4022_);
lean_dec_ref(v___x_4021_);
lean_dec_ref(v_a_3992_);
lean_dec(v_scope_x3f_3990_);
v___x_4082_ = ((lean_object*)(l_Lake_resolveArtifact___closed__5));
v___x_4083_ = lean_array_push(v_log_4008_, v___x_4082_);
if (v_isShared_4029_ == 0)
{
lean_ctor_set(v___x_4028_, 0, v___x_4083_);
v___x_4085_ = v___x_4028_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v___x_4083_);
lean_ctor_set(v_reuseFailAlloc_4086_, 1, v_trace_4011_);
lean_ctor_set(v_reuseFailAlloc_4086_, 2, v_buildTime_4012_);
lean_ctor_set_uint8(v_reuseFailAlloc_4086_, sizeof(void*)*3 + 1, v_wantsRebuild_4010_);
v___x_4085_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
lean_ctor_set_uint8(v___x_4085_, sizeof(void*)*3, v___x_4035_);
v___y_4000_ = v___x_4031_;
v_a_4001_ = v___x_4085_;
goto v___jp_3999_;
}
}
}
else
{
lean_object* v___x_4087_; lean_object* v___x_4088_; uint8_t v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4093_; 
lean_dec(v___x_4038_);
lean_dec_ref(v___f_4022_);
lean_dec_ref(v___x_4021_);
lean_dec_ref(v_a_3992_);
lean_dec(v_scope_x3f_3990_);
v___x_4087_ = ((lean_object*)(l_Lake_resolveArtifact___closed__6));
v___x_4088_ = lean_string_append(v___x_4087_, v_val_4032_);
lean_dec(v_val_4032_);
v___x_4089_ = 3;
v___x_4090_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4090_, 0, v___x_4088_);
lean_ctor_set_uint8(v___x_4090_, sizeof(void*)*1, v___x_4089_);
v___x_4091_ = lean_array_push(v_log_4008_, v___x_4090_);
if (v_isShared_4029_ == 0)
{
lean_ctor_set(v___x_4028_, 0, v___x_4091_);
v___x_4093_ = v___x_4028_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v___x_4091_);
lean_ctor_set(v_reuseFailAlloc_4094_, 1, v_trace_4011_);
lean_ctor_set(v_reuseFailAlloc_4094_, 2, v_buildTime_4012_);
lean_ctor_set_uint8(v_reuseFailAlloc_4094_, sizeof(void*)*3 + 1, v_wantsRebuild_4010_);
v___x_4093_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
lean_ctor_set_uint8(v___x_4093_, sizeof(void*)*3, v___x_4035_);
v___y_4000_ = v___x_4031_;
v_a_4001_ = v___x_4093_;
goto v___jp_3999_;
}
}
}
else
{
lean_object* v___x_4095_; lean_object* v___x_4096_; uint8_t v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4101_; 
lean_dec_ref(v___f_4022_);
lean_dec_ref(v_a_3992_);
lean_dec(v_scope_x3f_3990_);
lean_dec(v_service_x3f_3989_);
v___x_4095_ = ((lean_object*)(l_Lake_resolveArtifact___closed__7));
v___x_4096_ = lean_string_append(v___x_4095_, v___x_4021_);
lean_dec_ref(v___x_4021_);
v___x_4097_ = 3;
v___x_4098_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4098_, 0, v___x_4096_);
lean_ctor_set_uint8(v___x_4098_, sizeof(void*)*1, v___x_4097_);
v___x_4099_ = lean_array_push(v_log_4008_, v___x_4098_);
if (v_isShared_4029_ == 0)
{
lean_ctor_set(v___x_4028_, 0, v___x_4099_);
v___x_4101_ = v___x_4028_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v___x_4099_);
lean_ctor_set(v_reuseFailAlloc_4102_, 1, v_trace_4011_);
lean_ctor_set(v_reuseFailAlloc_4102_, 2, v_buildTime_4012_);
lean_ctor_set_uint8(v_reuseFailAlloc_4102_, sizeof(void*)*3, v_action_4009_);
lean_ctor_set_uint8(v_reuseFailAlloc_4102_, sizeof(void*)*3 + 1, v_wantsRebuild_4010_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
v___y_4000_ = v___x_4031_;
v_a_4001_ = v___x_4101_;
goto v___jp_3999_;
}
}
}
else
{
lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; uint8_t v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4111_; 
lean_dec_ref(v___f_4022_);
lean_dec_ref(v___x_4021_);
lean_dec_ref(v_a_3992_);
lean_dec(v_scope_x3f_3990_);
lean_dec(v_service_x3f_3989_);
v___x_4103_ = ((lean_object*)(l_Lake_resolveArtifact___closed__8));
v___x_4104_ = lean_io_error_to_string(v_a_4030_);
v___x_4105_ = lean_string_append(v___x_4103_, v___x_4104_);
lean_dec_ref(v___x_4104_);
v___x_4106_ = 3;
v___x_4107_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4107_, 0, v___x_4105_);
lean_ctor_set_uint8(v___x_4107_, sizeof(void*)*1, v___x_4106_);
v___x_4108_ = lean_array_get_size(v_log_4008_);
v___x_4109_ = lean_array_push(v_log_4008_, v___x_4107_);
if (v_isShared_4029_ == 0)
{
lean_ctor_set(v___x_4028_, 0, v___x_4109_);
v___x_4111_ = v___x_4028_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v___x_4109_);
lean_ctor_set(v_reuseFailAlloc_4113_, 1, v_trace_4011_);
lean_ctor_set(v_reuseFailAlloc_4113_, 2, v_buildTime_4012_);
lean_ctor_set_uint8(v_reuseFailAlloc_4113_, sizeof(void*)*3, v_action_4009_);
lean_ctor_set_uint8(v_reuseFailAlloc_4113_, sizeof(void*)*3 + 1, v_wantsRebuild_4010_);
v___x_4111_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
lean_object* v___x_4112_; 
v___x_4112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4112_, 0, v___x_4108_);
lean_ctor_set(v___x_4112_, 1, v___x_4111_);
return v___x_4112_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifact___boxed(lean_object* v_descr_4126_, lean_object* v_service_x3f_4127_, lean_object* v_scope_x3f_4128_, lean_object* v_exe_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_){
_start:
{
uint8_t v_exe_boxed_4137_; lean_object* v_res_4138_; 
v_exe_boxed_4137_ = lean_unbox(v_exe_4129_);
v_res_4138_ = l_Lake_resolveArtifact(v_descr_4126_, v_service_x3f_4127_, v_scope_x3f_4128_, v_exe_boxed_4137_, v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_);
lean_dec_ref(v_a_4134_);
lean_dec(v_a_4133_);
lean_dec(v_a_4132_);
lean_dec(v_a_4131_);
return v_res_4138_;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput(lean_object* v_out_4141_, uint8_t v_exe_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_){
_start:
{
lean_object* v_data_4150_; lean_object* v_service_x3f_4151_; lean_object* v_scope_x3f_4152_; lean_object* v___x_4153_; 
v_data_4150_ = lean_ctor_get(v_out_4141_, 0);
lean_inc_n(v_data_4150_, 2);
v_service_x3f_4151_ = lean_ctor_get(v_out_4141_, 1);
lean_inc(v_service_x3f_4151_);
v_scope_x3f_4152_ = lean_ctor_get(v_out_4141_, 2);
lean_inc(v_scope_x3f_4152_);
lean_dec_ref(v_out_4141_);
v___x_4153_ = l_Lake_ArtifactDescr_fromJson_x3f(v_data_4150_);
if (lean_obj_tag(v___x_4153_) == 0)
{
lean_object* v_a_4154_; lean_object* v_log_4155_; uint8_t v_action_4156_; uint8_t v_wantsRebuild_4157_; lean_object* v_trace_4158_; lean_object* v_buildTime_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4181_; 
lean_dec(v_scope_x3f_4152_);
lean_dec(v_service_x3f_4151_);
lean_dec_ref(v_a_4143_);
v_a_4154_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4154_);
lean_dec_ref_known(v___x_4153_, 1);
v_log_4155_ = lean_ctor_get(v_a_4148_, 0);
v_action_4156_ = lean_ctor_get_uint8(v_a_4148_, sizeof(void*)*3);
v_wantsRebuild_4157_ = lean_ctor_get_uint8(v_a_4148_, sizeof(void*)*3 + 1);
v_trace_4158_ = lean_ctor_get(v_a_4148_, 1);
v_buildTime_4159_ = lean_ctor_get(v_a_4148_, 2);
v_isSharedCheck_4181_ = !lean_is_exclusive(v_a_4148_);
if (v_isSharedCheck_4181_ == 0)
{
v___x_4161_ = v_a_4148_;
v_isShared_4162_ = v_isSharedCheck_4181_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_buildTime_4159_);
lean_inc(v_trace_4158_);
lean_inc(v_log_4155_);
lean_dec(v_a_4148_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4181_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; uint8_t v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4178_; 
v___x_4163_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__0));
v___x_4164_ = l_Lean_Json_render(v_data_4150_);
v___x_4165_ = lean_unsigned_to_nat(80u);
v___x_4166_ = lean_unsigned_to_nat(2u);
v___x_4167_ = lean_unsigned_to_nat(0u);
v___x_4168_ = l_Std_Format_pretty(v___x_4164_, v___x_4165_, v___x_4166_, v___x_4167_);
v___x_4169_ = lean_string_append(v___x_4163_, v___x_4168_);
lean_dec_ref(v___x_4168_);
v___x_4170_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__1));
v___x_4171_ = lean_string_append(v___x_4169_, v___x_4170_);
v___x_4172_ = lean_string_append(v___x_4171_, v_a_4154_);
lean_dec(v_a_4154_);
v___x_4173_ = 3;
v___x_4174_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4174_, 0, v___x_4172_);
lean_ctor_set_uint8(v___x_4174_, sizeof(void*)*1, v___x_4173_);
v___x_4175_ = lean_array_get_size(v_log_4155_);
v___x_4176_ = lean_array_push(v_log_4155_, v___x_4174_);
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 0, v___x_4176_);
v___x_4178_ = v___x_4161_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v___x_4176_);
lean_ctor_set(v_reuseFailAlloc_4180_, 1, v_trace_4158_);
lean_ctor_set(v_reuseFailAlloc_4180_, 2, v_buildTime_4159_);
lean_ctor_set_uint8(v_reuseFailAlloc_4180_, sizeof(void*)*3, v_action_4156_);
lean_ctor_set_uint8(v_reuseFailAlloc_4180_, sizeof(void*)*3 + 1, v_wantsRebuild_4157_);
v___x_4178_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
lean_object* v___x_4179_; 
v___x_4179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4175_);
lean_ctor_set(v___x_4179_, 1, v___x_4178_);
return v___x_4179_;
}
}
}
else
{
lean_object* v_a_4182_; lean_object* v___x_4183_; 
lean_dec(v_data_4150_);
v_a_4182_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4182_);
lean_dec_ref_known(v___x_4153_, 1);
v___x_4183_ = l_Lake_resolveArtifact(v_a_4182_, v_service_x3f_4151_, v_scope_x3f_4152_, v_exe_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_);
return v___x_4183_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactOutput___boxed(lean_object* v_out_4184_, lean_object* v_exe_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_){
_start:
{
uint8_t v_exe_boxed_4193_; lean_object* v_res_4194_; 
v_exe_boxed_4193_ = lean_unbox(v_exe_4185_);
v_res_4194_ = l_Lake_resolveArtifactOutput(v_out_4184_, v_exe_boxed_4193_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_);
lean_dec_ref(v_a_4190_);
lean_dec(v_a_4189_);
lean_dec(v_a_4188_);
lean_dec(v_a_4187_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(uint8_t v_exe_4195_, lean_object* v_out_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_){
_start:
{
lean_object* v___x_4204_; 
v___x_4204_ = l_Lake_resolveArtifactOutput(v_out_4196_, v_exe_4195_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed(lean_object* v_exe_4205_, lean_object* v_out_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_){
_start:
{
uint8_t v_exe_boxed_4214_; lean_object* v_res_4215_; 
v_exe_boxed_4214_ = lean_unbox(v_exe_4205_);
v_res_4215_ = l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0(v_exe_boxed_4214_, v_out_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec(v___y_4208_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(uint8_t v_exe_4216_){
_start:
{
lean_object* v___x_4217_; lean_object* v___f_4218_; 
v___x_4217_ = lean_box(v_exe_4216_);
v___f_4218_ = lean_alloc_closure((void*)(l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4218_, 0, v___x_4217_);
return v___f_4218_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact___boxed(lean_object* v_exe_4219_){
_start:
{
uint8_t v_exe_boxed_4220_; lean_object* v_res_4221_; 
v_exe_boxed_4220_ = lean_unbox(v_exe_4219_);
v_res_4221_ = l___private_Lake_Build_Common_0__Lake_instResolveOutputsXArtifact(v_exe_boxed_4220_);
return v_res_4221_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg(lean_object* v_path_4222_, lean_object* v_ext_4223_, uint8_t v_text_4224_, lean_object* v_a_4225_, lean_object* v_a_4226_){
_start:
{
lean_object* v___x_4228_; 
lean_inc_ref(v_path_4222_);
v___x_4228_ = l_Lake_fetchFileHash___redArg(v_path_4222_, v_text_4224_, v_a_4225_, v_a_4226_);
if (lean_obj_tag(v___x_4228_) == 0)
{
lean_object* v_a_4229_; lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4247_; 
v_a_4229_ = lean_ctor_get(v___x_4228_, 0);
v_a_4230_ = lean_ctor_get(v___x_4228_, 1);
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4228_);
if (v_isSharedCheck_4247_ == 0)
{
v___x_4232_ = v___x_4228_;
v_isShared_4233_ = v_isSharedCheck_4247_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_a_4230_);
lean_inc(v_a_4229_);
lean_dec(v___x_4228_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4247_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___x_4243_; 
v___x_4243_ = lean_io_metadata(v_path_4222_);
if (lean_obj_tag(v___x_4243_) == 0)
{
lean_object* v_a_4244_; lean_object* v_modified_4245_; 
v_a_4244_ = lean_ctor_get(v___x_4243_, 0);
lean_inc(v_a_4244_);
lean_dec_ref_known(v___x_4243_, 1);
v_modified_4245_ = lean_ctor_get(v_a_4244_, 1);
lean_inc_ref(v_modified_4245_);
lean_dec(v_a_4244_);
v___y_4235_ = v_a_4230_;
v___y_4236_ = v_modified_4245_;
goto v___jp_4234_;
}
else
{
lean_object* v___x_4246_; 
lean_dec_ref_known(v___x_4243_, 1);
v___x_4246_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___y_4235_ = v_a_4230_;
v___y_4236_ = v___x_4246_;
goto v___jp_4234_;
}
v___jp_4234_:
{
lean_object* v___x_4237_; uint64_t v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4241_; 
v___x_4237_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4237_, 0, v_ext_4223_);
v___x_4238_ = lean_unbox_uint64(v_a_4229_);
lean_dec(v_a_4229_);
lean_ctor_set_uint64(v___x_4237_, sizeof(void*)*1, v___x_4238_);
lean_inc_ref(v_path_4222_);
v___x_4239_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4237_);
lean_ctor_set(v___x_4239_, 1, v_path_4222_);
lean_ctor_set(v___x_4239_, 2, v_path_4222_);
lean_ctor_set(v___x_4239_, 3, v___y_4236_);
if (v_isShared_4233_ == 0)
{
lean_ctor_set(v___x_4232_, 1, v___y_4235_);
lean_ctor_set(v___x_4232_, 0, v___x_4239_);
v___x_4241_ = v___x_4232_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v___x_4239_);
lean_ctor_set(v_reuseFailAlloc_4242_, 1, v___y_4235_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
}
}
}
}
else
{
lean_object* v_a_4248_; lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4256_; 
lean_dec_ref(v_ext_4223_);
lean_dec_ref(v_path_4222_);
v_a_4248_ = lean_ctor_get(v___x_4228_, 0);
v_a_4249_ = lean_ctor_get(v___x_4228_, 1);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4228_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4251_ = v___x_4228_;
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_inc(v_a_4248_);
lean_dec(v___x_4228_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4254_; 
if (v_isShared_4252_ == 0)
{
v___x_4254_ = v___x_4251_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v_a_4248_);
lean_ctor_set(v_reuseFailAlloc_4255_, 1, v_a_4249_);
v___x_4254_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
return v___x_4254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg___boxed(lean_object* v_path_4257_, lean_object* v_ext_4258_, lean_object* v_text_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_){
_start:
{
uint8_t v_text_boxed_4263_; lean_object* v_res_4264_; 
v_text_boxed_4263_ = lean_unbox(v_text_4259_);
v_res_4264_ = l_Lake_computeArtifact___redArg(v_path_4257_, v_ext_4258_, v_text_boxed_4263_, v_a_4260_, v_a_4261_);
lean_dec_ref(v_a_4260_);
return v_res_4264_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact(lean_object* v_path_4265_, lean_object* v_ext_4266_, uint8_t v_text_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_){
_start:
{
lean_object* v___x_4275_; 
v___x_4275_ = l_Lake_computeArtifact___redArg(v_path_4265_, v_ext_4266_, v_text_4267_, v_a_4272_, v_a_4273_);
return v___x_4275_;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___boxed(lean_object* v_path_4276_, lean_object* v_ext_4277_, lean_object* v_text_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_){
_start:
{
uint8_t v_text_boxed_4286_; lean_object* v_res_4287_; 
v_text_boxed_4286_ = lean_unbox(v_text_4278_);
v_res_4287_ = l_Lake_computeArtifact(v_path_4276_, v_ext_4277_, v_text_boxed_4286_, v_a_4279_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_);
lean_dec_ref(v_a_4283_);
lean_dec(v_a_4282_);
lean_dec(v_a_4281_);
lean_dec(v_a_4280_);
lean_dec_ref(v_a_4279_);
return v_res_4287_;
}
}
LEAN_EXPORT lean_object* l_Lake_restoreArtifact(lean_object* v_file_4291_, lean_object* v_art_4292_, uint8_t v_exe_4293_, lean_object* v_a_4294_){
_start:
{
lean_object* v___y_4297_; uint8_t v___x_4310_; 
v___x_4310_ = l_System_FilePath_pathExists(v_file_4291_);
if (v___x_4310_ == 0)
{
lean_object* v_descr_4311_; lean_object* v_path_4312_; lean_object* v___y_4314_; lean_object* v___x_4329_; lean_object* v___x_4330_; uint8_t v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; 
v_descr_4311_ = lean_ctor_get(v_art_4292_, 0);
v_path_4312_ = lean_ctor_get(v_art_4292_, 1);
v___x_4329_ = ((lean_object*)(l_Lake_restoreArtifact___closed__1));
v___x_4330_ = lean_string_append(v___x_4329_, v_path_4312_);
v___x_4331_ = 0;
v___x_4332_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4332_, 0, v___x_4330_);
lean_ctor_set_uint8(v___x_4332_, sizeof(void*)*1, v___x_4331_);
v___x_4333_ = lean_array_push(v_a_4294_, v___x_4332_);
lean_inc_ref(v_file_4291_);
v___x_4334_ = l_Lake_createParentDirs(v_file_4291_);
if (lean_obj_tag(v___x_4334_) == 0)
{
uint8_t v___x_4335_; lean_object* v___x_4336_; 
lean_dec_ref_known(v___x_4334_, 1);
v___x_4335_ = 1;
v___x_4336_ = lean_io_hard_link(v_path_4312_, v_file_4291_);
if (lean_obj_tag(v___x_4336_) == 0)
{
lean_dec_ref_known(v___x_4336_, 1);
if (v_exe_4293_ == 0)
{
v___y_4314_ = v___x_4333_;
goto v___jp_4313_;
}
else
{
lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; 
v___x_4337_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4337_, 0, v___x_4335_);
lean_ctor_set_uint8(v___x_4337_, 1, v___x_4310_);
lean_ctor_set_uint8(v___x_4337_, 2, v_exe_4293_);
lean_inc_ref_n(v___x_4337_, 2);
v___x_4338_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4337_);
lean_ctor_set(v___x_4338_, 1, v___x_4337_);
lean_ctor_set(v___x_4338_, 2, v___x_4337_);
v___x_4339_ = l_IO_setAccessRights(v_file_4291_, v___x_4338_);
lean_dec_ref_known(v___x_4338_, 3);
if (lean_obj_tag(v___x_4339_) == 0)
{
lean_dec_ref_known(v___x_4339_, 1);
v___y_4314_ = v___x_4333_;
goto v___jp_4313_;
}
else
{
lean_object* v_a_4340_; lean_object* v___x_4341_; uint8_t v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
lean_dec_ref(v_art_4292_);
lean_dec_ref(v_file_4291_);
v_a_4340_ = lean_ctor_get(v___x_4339_, 0);
lean_inc(v_a_4340_);
lean_dec_ref_known(v___x_4339_, 1);
v___x_4341_ = lean_io_error_to_string(v_a_4340_);
v___x_4342_ = 3;
v___x_4343_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4343_, 0, v___x_4341_);
lean_ctor_set_uint8(v___x_4343_, sizeof(void*)*1, v___x_4342_);
v___x_4344_ = lean_array_get_size(v___x_4333_);
v___x_4345_ = lean_array_push(v___x_4333_, v___x_4343_);
v___x_4346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4346_, 0, v___x_4344_);
lean_ctor_set(v___x_4346_, 1, v___x_4345_);
return v___x_4346_;
}
}
}
else
{
lean_object* v_a_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; 
v_a_4347_ = lean_ctor_get(v___x_4336_, 0);
lean_inc(v_a_4347_);
lean_dec_ref_known(v___x_4336_, 1);
v___x_4348_ = ((lean_object*)(l_Lake_restoreArtifact___closed__2));
v___x_4349_ = lean_io_error_to_string(v_a_4347_);
v___x_4350_ = lean_string_append(v___x_4348_, v___x_4349_);
lean_dec_ref(v___x_4349_);
v___x_4351_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4351_, 0, v___x_4350_);
lean_ctor_set_uint8(v___x_4351_, sizeof(void*)*1, v___x_4331_);
v___x_4352_ = lean_array_push(v___x_4333_, v___x_4351_);
v___x_4353_ = l_Lake_copyFile(v_path_4312_, v_file_4291_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; 
lean_dec_ref_known(v___x_4353_, 1);
v___x_4354_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4354_, 0, v___x_4335_);
lean_ctor_set_uint8(v___x_4354_, 1, v___x_4310_);
lean_ctor_set_uint8(v___x_4354_, 2, v_exe_4293_);
lean_inc_ref_n(v___x_4354_, 2);
v___x_4355_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4355_, 0, v___x_4354_);
lean_ctor_set(v___x_4355_, 1, v___x_4354_);
lean_ctor_set(v___x_4355_, 2, v___x_4354_);
v___x_4356_ = l_IO_setAccessRights(v_file_4291_, v___x_4355_);
lean_dec_ref_known(v___x_4355_, 3);
if (lean_obj_tag(v___x_4356_) == 0)
{
lean_dec_ref_known(v___x_4356_, 1);
v___y_4314_ = v___x_4352_;
goto v___jp_4313_;
}
else
{
lean_object* v_a_4357_; lean_object* v___x_4358_; uint8_t v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; 
lean_dec_ref(v_art_4292_);
lean_dec_ref(v_file_4291_);
v_a_4357_ = lean_ctor_get(v___x_4356_, 0);
lean_inc(v_a_4357_);
lean_dec_ref_known(v___x_4356_, 1);
v___x_4358_ = lean_io_error_to_string(v_a_4357_);
v___x_4359_ = 3;
v___x_4360_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4360_, 0, v___x_4358_);
lean_ctor_set_uint8(v___x_4360_, sizeof(void*)*1, v___x_4359_);
v___x_4361_ = lean_array_get_size(v___x_4352_);
v___x_4362_ = lean_array_push(v___x_4352_, v___x_4360_);
v___x_4363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4363_, 0, v___x_4361_);
lean_ctor_set(v___x_4363_, 1, v___x_4362_);
return v___x_4363_;
}
}
else
{
lean_object* v_a_4364_; lean_object* v___x_4365_; uint8_t v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; 
lean_dec_ref(v_art_4292_);
lean_dec_ref(v_file_4291_);
v_a_4364_ = lean_ctor_get(v___x_4353_, 0);
lean_inc(v_a_4364_);
lean_dec_ref_known(v___x_4353_, 1);
v___x_4365_ = lean_io_error_to_string(v_a_4364_);
v___x_4366_ = 3;
v___x_4367_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4367_, 0, v___x_4365_);
lean_ctor_set_uint8(v___x_4367_, sizeof(void*)*1, v___x_4366_);
v___x_4368_ = lean_array_get_size(v___x_4352_);
v___x_4369_ = lean_array_push(v___x_4352_, v___x_4367_);
v___x_4370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4370_, 0, v___x_4368_);
lean_ctor_set(v___x_4370_, 1, v___x_4369_);
return v___x_4370_;
}
}
}
else
{
lean_object* v_a_4371_; lean_object* v___x_4372_; uint8_t v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; 
lean_dec_ref(v_art_4292_);
lean_dec_ref(v_file_4291_);
v_a_4371_ = lean_ctor_get(v___x_4334_, 0);
lean_inc(v_a_4371_);
lean_dec_ref_known(v___x_4334_, 1);
v___x_4372_ = lean_io_error_to_string(v_a_4371_);
v___x_4373_ = 3;
v___x_4374_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4374_, 0, v___x_4372_);
lean_ctor_set_uint8(v___x_4374_, sizeof(void*)*1, v___x_4373_);
v___x_4375_ = lean_array_get_size(v___x_4333_);
v___x_4376_ = lean_array_push(v___x_4333_, v___x_4374_);
v___x_4377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4377_, 0, v___x_4375_);
lean_ctor_set(v___x_4377_, 1, v___x_4376_);
return v___x_4377_;
}
v___jp_4313_:
{
uint64_t v_hash_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; uint8_t v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; 
v_hash_4315_ = lean_ctor_get_uint64(v_descr_4311_, sizeof(void*)*1);
v___x_4316_ = ((lean_object*)(l_Lake_restoreArtifact___closed__0));
v___x_4317_ = lean_string_append(v___x_4316_, v_file_4291_);
v___x_4318_ = 0;
v___x_4319_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4319_, 0, v___x_4317_);
lean_ctor_set_uint8(v___x_4319_, sizeof(void*)*1, v___x_4318_);
v___x_4320_ = lean_array_push(v___y_4314_, v___x_4319_);
lean_inc_ref(v_file_4291_);
v___x_4321_ = l_Lake_writeFileHash(v_file_4291_, v_hash_4315_);
if (lean_obj_tag(v___x_4321_) == 0)
{
lean_dec_ref_known(v___x_4321_, 1);
v___y_4297_ = v___x_4320_;
goto v___jp_4296_;
}
else
{
lean_object* v_a_4322_; lean_object* v___x_4323_; uint8_t v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; 
lean_dec_ref(v_art_4292_);
lean_dec_ref(v_file_4291_);
v_a_4322_ = lean_ctor_get(v___x_4321_, 0);
lean_inc(v_a_4322_);
lean_dec_ref_known(v___x_4321_, 1);
v___x_4323_ = lean_io_error_to_string(v_a_4322_);
v___x_4324_ = 3;
v___x_4325_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4325_, 0, v___x_4323_);
lean_ctor_set_uint8(v___x_4325_, sizeof(void*)*1, v___x_4324_);
v___x_4326_ = lean_array_get_size(v___x_4320_);
v___x_4327_ = lean_array_push(v___x_4320_, v___x_4325_);
v___x_4328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4328_, 0, v___x_4326_);
lean_ctor_set(v___x_4328_, 1, v___x_4327_);
return v___x_4328_;
}
}
}
else
{
v___y_4297_ = v_a_4294_;
goto v___jp_4296_;
}
v___jp_4296_:
{
lean_object* v_descr_4298_; lean_object* v_mtime_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4307_; 
v_descr_4298_ = lean_ctor_get(v_art_4292_, 0);
v_mtime_4299_ = lean_ctor_get(v_art_4292_, 3);
v_isSharedCheck_4307_ = !lean_is_exclusive(v_art_4292_);
if (v_isSharedCheck_4307_ == 0)
{
lean_object* v_unused_4308_; lean_object* v_unused_4309_; 
v_unused_4308_ = lean_ctor_get(v_art_4292_, 2);
lean_dec(v_unused_4308_);
v_unused_4309_ = lean_ctor_get(v_art_4292_, 1);
lean_dec(v_unused_4309_);
v___x_4301_ = v_art_4292_;
v_isShared_4302_ = v_isSharedCheck_4307_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_mtime_4299_);
lean_inc(v_descr_4298_);
lean_dec(v_art_4292_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4307_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4304_; 
lean_inc_ref(v_file_4291_);
if (v_isShared_4302_ == 0)
{
lean_ctor_set(v___x_4301_, 2, v_file_4291_);
lean_ctor_set(v___x_4301_, 1, v_file_4291_);
v___x_4304_ = v___x_4301_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_descr_4298_);
lean_ctor_set(v_reuseFailAlloc_4306_, 1, v_file_4291_);
lean_ctor_set(v_reuseFailAlloc_4306_, 2, v_file_4291_);
lean_ctor_set(v_reuseFailAlloc_4306_, 3, v_mtime_4299_);
v___x_4304_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
lean_object* v___x_4305_; 
v___x_4305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4304_);
lean_ctor_set(v___x_4305_, 1, v___y_4297_);
return v___x_4305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_restoreArtifact___boxed(lean_object* v_file_4378_, lean_object* v_art_4379_, lean_object* v_exe_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_){
_start:
{
uint8_t v_exe_boxed_4383_; lean_object* v_res_4384_; 
v_exe_boxed_4383_ = lean_unbox(v_exe_4380_);
v_res_4384_ = l_Lake_restoreArtifact(v_file_4378_, v_art_4379_, v_exe_boxed_4383_, v_a_4381_);
return v_res_4384_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(lean_object* v_val_4385_, lean_object* v_a_x3f_4386_, lean_object* v___y_4387_){
_start:
{
lean_object* v___x_4389_; lean_object* v_log_4390_; uint8_t v_action_4391_; uint8_t v_wantsRebuild_4392_; lean_object* v_trace_4393_; lean_object* v_buildTime_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4405_; 
v___x_4389_ = lean_io_mono_ms_now();
v_log_4390_ = lean_ctor_get(v___y_4387_, 0);
v_action_4391_ = lean_ctor_get_uint8(v___y_4387_, sizeof(void*)*3);
v_wantsRebuild_4392_ = lean_ctor_get_uint8(v___y_4387_, sizeof(void*)*3 + 1);
v_trace_4393_ = lean_ctor_get(v___y_4387_, 1);
v_buildTime_4394_ = lean_ctor_get(v___y_4387_, 2);
v_isSharedCheck_4405_ = !lean_is_exclusive(v___y_4387_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4396_ = v___y_4387_;
v_isShared_4397_ = v_isSharedCheck_4405_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_buildTime_4394_);
lean_inc(v_trace_4393_);
lean_inc(v_log_4390_);
lean_dec(v___y_4387_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4405_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4402_; 
v___x_4398_ = lean_nat_sub(v___x_4389_, v_val_4385_);
lean_dec(v___x_4389_);
v___x_4399_ = lean_box(0);
v___x_4400_ = lean_nat_add(v_buildTime_4394_, v___x_4398_);
lean_dec(v___x_4398_);
lean_dec(v_buildTime_4394_);
if (v_isShared_4397_ == 0)
{
lean_ctor_set(v___x_4396_, 2, v___x_4400_);
v___x_4402_ = v___x_4396_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_log_4390_);
lean_ctor_set(v_reuseFailAlloc_4404_, 1, v_trace_4393_);
lean_ctor_set(v_reuseFailAlloc_4404_, 2, v___x_4400_);
lean_ctor_set_uint8(v_reuseFailAlloc_4404_, sizeof(void*)*3, v_action_4391_);
lean_ctor_set_uint8(v_reuseFailAlloc_4404_, sizeof(void*)*3 + 1, v_wantsRebuild_4392_);
v___x_4402_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
lean_object* v___x_4403_; 
v___x_4403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4403_, 0, v___x_4399_);
lean_ctor_set(v___x_4403_, 1, v___x_4402_);
return v___x_4403_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0___boxed(lean_object* v_val_4406_, lean_object* v_a_x3f_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_){
_start:
{
lean_object* v_res_4410_; 
v_res_4410_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v_val_4406_, v_a_x3f_4407_, v___y_4408_);
lean_dec(v_a_x3f_4407_);
lean_dec(v_val_4406_);
return v_res_4410_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(lean_object* v_file_4411_, lean_object* v_build_4412_, lean_object* v_traceFile_4413_, lean_object* v_ext_4414_, uint8_t v_text_4415_, lean_object* v_a_4416_, lean_object* v_depTrace_4417_, lean_object* v_traceFile_4418_, uint8_t v_action_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_){
_start:
{
lean_object* v_a_4427_; lean_object* v_a_4428_; lean_object* v_log_4431_; uint8_t v_action_4432_; uint8_t v_wantsRebuild_4433_; lean_object* v_trace_4434_; lean_object* v_buildTime_4435_; lean_object* v_toBuildConfig_4441_; lean_object* v_log_4442_; uint8_t v_action_4443_; uint8_t v_wantsRebuild_4444_; lean_object* v_trace_4445_; lean_object* v_buildTime_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4625_; 
v_toBuildConfig_4441_ = lean_ctor_get(v_a_4423_, 0);
v_log_4442_ = lean_ctor_get(v_a_4424_, 0);
v_action_4443_ = lean_ctor_get_uint8(v_a_4424_, sizeof(void*)*3);
v_wantsRebuild_4444_ = lean_ctor_get_uint8(v_a_4424_, sizeof(void*)*3 + 1);
v_trace_4445_ = lean_ctor_get(v_a_4424_, 1);
v_buildTime_4446_ = lean_ctor_get(v_a_4424_, 2);
v_isSharedCheck_4625_ = !lean_is_exclusive(v_a_4424_);
if (v_isSharedCheck_4625_ == 0)
{
v___x_4448_ = v_a_4424_;
v_isShared_4449_ = v_isSharedCheck_4625_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_buildTime_4446_);
lean_inc(v_trace_4445_);
lean_inc(v_log_4442_);
lean_dec(v_a_4424_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4625_;
goto v_resetjp_4447_;
}
v___jp_4426_:
{
lean_object* v___x_4429_; 
v___x_4429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4429_, 0, v_a_4427_);
lean_ctor_set(v___x_4429_, 1, v_a_4428_);
return v___x_4429_;
}
v___jp_4430_:
{
lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; 
v___x_4436_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__1));
v___x_4437_ = lean_array_get_size(v_log_4431_);
v___x_4438_ = lean_array_push(v_log_4431_, v___x_4436_);
v___x_4439_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4439_, 0, v___x_4438_);
lean_ctor_set(v___x_4439_, 1, v_trace_4434_);
lean_ctor_set(v___x_4439_, 2, v_buildTime_4435_);
lean_ctor_set_uint8(v___x_4439_, sizeof(void*)*3, v_action_4432_);
lean_ctor_set_uint8(v___x_4439_, sizeof(void*)*3 + 1, v_wantsRebuild_4433_);
v___x_4440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4437_);
lean_ctor_set(v___x_4440_, 1, v___x_4439_);
return v___x_4440_;
}
v_resetjp_4447_:
{
uint8_t v_noBuild_4450_; uint8_t v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; 
v_noBuild_4450_ = lean_ctor_get_uint8(v_toBuildConfig_4441_, sizeof(void*)*4 + 2);
v___x_4451_ = l_Lake_JobAction_merge(v_action_4443_, v_action_4419_);
v___x_4452_ = ((lean_object*)(l_Lake_buildAction___redArg___closed__2));
lean_inc_ref(v_traceFile_4418_);
v___x_4453_ = l_System_FilePath_addExtension(v_traceFile_4418_, v___x_4452_);
if (v_noBuild_4450_ == 0)
{
lean_object* v___x_4454_; lean_object* v_a_4456_; lean_object* v_a_4457_; lean_object* v___x_4461_; 
v___x_4454_ = lean_io_mono_ms_now();
v___x_4461_ = l_Lake_removeFileIfExists(v_file_4411_);
if (lean_obj_tag(v___x_4461_) == 0)
{
lean_object* v___x_4463_; 
lean_dec_ref_known(v___x_4461_, 1);
lean_inc_ref(v_log_4442_);
if (v_isShared_4449_ == 0)
{
v___x_4463_ = v___x_4448_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4600_; 
v_reuseFailAlloc_4600_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4600_, 0, v_log_4442_);
lean_ctor_set(v_reuseFailAlloc_4600_, 1, v_trace_4445_);
lean_ctor_set(v_reuseFailAlloc_4600_, 2, v_buildTime_4446_);
lean_ctor_set_uint8(v_reuseFailAlloc_4600_, sizeof(void*)*3 + 1, v_wantsRebuild_4444_);
v___x_4463_ = v_reuseFailAlloc_4600_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
lean_object* v___x_4464_; 
lean_ctor_set_uint8(v___x_4463_, sizeof(void*)*3, v___x_4451_);
lean_inc_ref(v_a_4423_);
lean_inc(v_a_4422_);
lean_inc(v_a_4421_);
lean_inc(v_a_4420_);
v___x_4464_ = lean_apply_7(v_build_4412_, v_a_4416_, v_a_4420_, v_a_4421_, v_a_4422_, v_a_4423_, v___x_4463_, lean_box(0));
if (lean_obj_tag(v___x_4464_) == 0)
{
lean_object* v_a_4465_; lean_object* v_log_4466_; uint8_t v_action_4467_; uint8_t v_wantsRebuild_4468_; lean_object* v_trace_4469_; lean_object* v_buildTime_4470_; lean_object* v___x_4471_; 
v_a_4465_ = lean_ctor_get(v___x_4464_, 1);
lean_inc(v_a_4465_);
lean_dec_ref_known(v___x_4464_, 2);
v_log_4466_ = lean_ctor_get(v_a_4465_, 0);
v_action_4467_ = lean_ctor_get_uint8(v_a_4465_, sizeof(void*)*3);
v_wantsRebuild_4468_ = lean_ctor_get_uint8(v_a_4465_, sizeof(void*)*3 + 1);
v_trace_4469_ = lean_ctor_get(v_a_4465_, 1);
v_buildTime_4470_ = lean_ctor_get(v_a_4465_, 2);
lean_inc_ref(v_file_4411_);
v___x_4471_ = l_Lake_clearFileHash(v_file_4411_);
if (lean_obj_tag(v___x_4471_) == 0)
{
lean_object* v___x_4472_; 
lean_dec_ref_known(v___x_4471_, 1);
v___x_4472_ = l_Lake_removeFileIfExists(v_traceFile_4413_);
if (lean_obj_tag(v___x_4472_) == 0)
{
lean_object* v___x_4474_; uint8_t v_isShared_4475_; uint8_t v_isSharedCheck_4564_; 
v_isSharedCheck_4564_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4564_ == 0)
{
lean_object* v_unused_4565_; 
v_unused_4565_ = lean_ctor_get(v___x_4472_, 0);
lean_dec(v_unused_4565_);
v___x_4474_ = v___x_4472_;
v_isShared_4475_ = v_isSharedCheck_4564_;
goto v_resetjp_4473_;
}
else
{
lean_dec(v___x_4472_);
v___x_4474_ = lean_box(0);
v_isShared_4475_ = v_isSharedCheck_4564_;
goto v_resetjp_4473_;
}
v_resetjp_4473_:
{
lean_object* v___x_4476_; 
v___x_4476_ = l_Lake_computeArtifact___redArg(v_file_4411_, v_ext_4414_, v_text_4415_, v_a_4423_, v_a_4465_);
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_object* v_a_4477_; lean_object* v_a_4478_; lean_object* v_descr_4479_; lean_object* v_log_4480_; uint8_t v_action_4481_; uint8_t v_wantsRebuild_4482_; lean_object* v_trace_4483_; lean_object* v_buildTime_4484_; uint64_t v_hash_4485_; lean_object* v_ext_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___y_4491_; lean_object* v___x_4554_; lean_object* v___x_4555_; uint8_t v___x_4556_; 
v_a_4477_ = lean_ctor_get(v___x_4476_, 1);
lean_inc(v_a_4477_);
v_a_4478_ = lean_ctor_get(v___x_4476_, 0);
lean_inc(v_a_4478_);
lean_dec_ref_known(v___x_4476_, 2);
v_descr_4479_ = lean_ctor_get(v_a_4478_, 0);
v_log_4480_ = lean_ctor_get(v_a_4477_, 0);
v_action_4481_ = lean_ctor_get_uint8(v_a_4477_, sizeof(void*)*3);
v_wantsRebuild_4482_ = lean_ctor_get_uint8(v_a_4477_, sizeof(void*)*3 + 1);
v_trace_4483_ = lean_ctor_get(v_a_4477_, 1);
v_buildTime_4484_ = lean_ctor_get(v_a_4477_, 2);
v_hash_4485_ = lean_ctor_get_uint64(v_descr_4479_, sizeof(void*)*1);
v_ext_4486_ = lean_ctor_get(v_descr_4479_, 0);
v___x_4487_ = lean_array_get_size(v_log_4442_);
lean_dec_ref(v_log_4442_);
v___x_4488_ = lean_array_get_size(v_log_4480_);
v___x_4489_ = l_Array_extract___redArg(v_log_4480_, v___x_4487_, v___x_4488_);
v___x_4554_ = lean_string_utf8_byte_size(v_ext_4486_);
v___x_4555_ = lean_unsigned_to_nat(0u);
v___x_4556_ = lean_nat_dec_eq(v___x_4554_, v___x_4555_);
if (v___x_4556_ == 0)
{
lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
v___x_4557_ = l_Lake_lowerHexUInt64(v_hash_4485_);
v___x_4558_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_4559_ = lean_string_append(v___x_4557_, v___x_4558_);
v___x_4560_ = lean_string_append(v___x_4559_, v_ext_4486_);
v___y_4491_ = v___x_4560_;
goto v___jp_4490_;
}
else
{
lean_object* v___x_4561_; 
v___x_4561_ = l_Lake_lowerHexUInt64(v_hash_4485_);
v___y_4491_ = v___x_4561_;
goto v___jp_4490_;
}
v___jp_4490_:
{
lean_object* v___x_4493_; 
if (v_isShared_4475_ == 0)
{
lean_ctor_set_tag(v___x_4474_, 3);
lean_ctor_set(v___x_4474_, 0, v___y_4491_);
v___x_4493_ = v___x_4474_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v___y_4491_);
v___x_4493_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
lean_object* v___x_4494_; lean_object* v___x_4495_; 
v___x_4494_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_4417_, v___x_4493_, v___x_4489_);
v___x_4495_ = l_Lake_BuildMetadata_writeFile(v_traceFile_4418_, v___x_4494_);
if (lean_obj_tag(v___x_4495_) == 0)
{
lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4536_; 
v_isSharedCheck_4536_ = !lean_is_exclusive(v___x_4495_);
if (v_isSharedCheck_4536_ == 0)
{
lean_object* v_unused_4537_; 
v_unused_4537_ = lean_ctor_get(v___x_4495_, 0);
lean_dec(v_unused_4537_);
v___x_4497_ = v___x_4495_;
v_isShared_4498_ = v_isSharedCheck_4536_;
goto v_resetjp_4496_;
}
else
{
lean_dec(v___x_4495_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4536_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4499_; 
v___x_4499_ = l_Lake_removeFileIfExists(v___x_4453_);
lean_dec_ref(v___x_4453_);
if (lean_obj_tag(v___x_4499_) == 0)
{
lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4519_; 
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4519_ == 0)
{
lean_object* v_unused_4520_; 
v_unused_4520_ = lean_ctor_get(v___x_4499_, 0);
lean_dec(v_unused_4520_);
v___x_4501_ = v___x_4499_;
v_isShared_4502_ = v_isSharedCheck_4519_;
goto v_resetjp_4500_;
}
else
{
lean_dec(v___x_4499_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4519_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v___x_4504_; 
lean_inc(v_a_4478_);
if (v_isShared_4502_ == 0)
{
lean_ctor_set(v___x_4501_, 0, v_a_4478_);
v___x_4504_ = v___x_4501_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_a_4478_);
v___x_4504_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
lean_object* v___x_4506_; 
if (v_isShared_4498_ == 0)
{
lean_ctor_set_tag(v___x_4497_, 1);
lean_ctor_set(v___x_4497_, 0, v___x_4504_);
v___x_4506_ = v___x_4497_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v___x_4504_);
v___x_4506_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
lean_object* v___x_4507_; lean_object* v_a_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4515_; 
v___x_4507_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v___x_4454_, v___x_4506_, v_a_4477_);
lean_dec_ref(v___x_4506_);
lean_dec(v___x_4454_);
v_a_4508_ = lean_ctor_get(v___x_4507_, 1);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4507_);
if (v_isSharedCheck_4515_ == 0)
{
lean_object* v_unused_4516_; 
v_unused_4516_ = lean_ctor_get(v___x_4507_, 0);
lean_dec(v_unused_4516_);
v___x_4510_ = v___x_4507_;
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_a_4508_);
lean_dec(v___x_4507_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v___x_4513_; 
if (v_isShared_4511_ == 0)
{
lean_ctor_set(v___x_4510_, 0, v_a_4478_);
v___x_4513_ = v___x_4510_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_a_4478_);
lean_ctor_set(v_reuseFailAlloc_4514_, 1, v_a_4508_);
v___x_4513_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
return v___x_4513_;
}
}
}
}
}
}
else
{
lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4532_; 
lean_inc(v_buildTime_4484_);
lean_inc_ref(v_trace_4483_);
lean_inc_ref(v_log_4480_);
lean_del_object(v___x_4497_);
lean_dec(v_a_4478_);
v_isSharedCheck_4532_ = !lean_is_exclusive(v_a_4477_);
if (v_isSharedCheck_4532_ == 0)
{
lean_object* v_unused_4533_; lean_object* v_unused_4534_; lean_object* v_unused_4535_; 
v_unused_4533_ = lean_ctor_get(v_a_4477_, 2);
lean_dec(v_unused_4533_);
v_unused_4534_ = lean_ctor_get(v_a_4477_, 1);
lean_dec(v_unused_4534_);
v_unused_4535_ = lean_ctor_get(v_a_4477_, 0);
lean_dec(v_unused_4535_);
v___x_4522_ = v_a_4477_;
v_isShared_4523_ = v_isSharedCheck_4532_;
goto v_resetjp_4521_;
}
else
{
lean_dec(v_a_4477_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4532_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v_a_4524_; lean_object* v___x_4525_; uint8_t v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4530_; 
v_a_4524_ = lean_ctor_get(v___x_4499_, 0);
lean_inc(v_a_4524_);
lean_dec_ref_known(v___x_4499_, 1);
v___x_4525_ = lean_io_error_to_string(v_a_4524_);
v___x_4526_ = 3;
v___x_4527_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4527_, 0, v___x_4525_);
lean_ctor_set_uint8(v___x_4527_, sizeof(void*)*1, v___x_4526_);
v___x_4528_ = lean_array_push(v_log_4480_, v___x_4527_);
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
lean_ctor_set(v_reuseFailAlloc_4531_, 1, v_trace_4483_);
lean_ctor_set(v_reuseFailAlloc_4531_, 2, v_buildTime_4484_);
lean_ctor_set_uint8(v_reuseFailAlloc_4531_, sizeof(void*)*3, v_action_4481_);
lean_ctor_set_uint8(v_reuseFailAlloc_4531_, sizeof(void*)*3 + 1, v_wantsRebuild_4482_);
v___x_4530_ = v_reuseFailAlloc_4531_;
goto v_reusejp_4529_;
}
v_reusejp_4529_:
{
v_a_4456_ = v___x_4488_;
v_a_4457_ = v___x_4530_;
goto v___jp_4455_;
}
}
}
}
}
else
{
lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4549_; 
lean_inc(v_buildTime_4484_);
lean_inc_ref(v_trace_4483_);
lean_inc_ref(v_log_4480_);
lean_dec(v_a_4478_);
lean_dec_ref(v___x_4453_);
v_isSharedCheck_4549_ = !lean_is_exclusive(v_a_4477_);
if (v_isSharedCheck_4549_ == 0)
{
lean_object* v_unused_4550_; lean_object* v_unused_4551_; lean_object* v_unused_4552_; 
v_unused_4550_ = lean_ctor_get(v_a_4477_, 2);
lean_dec(v_unused_4550_);
v_unused_4551_ = lean_ctor_get(v_a_4477_, 1);
lean_dec(v_unused_4551_);
v_unused_4552_ = lean_ctor_get(v_a_4477_, 0);
lean_dec(v_unused_4552_);
v___x_4539_ = v_a_4477_;
v_isShared_4540_ = v_isSharedCheck_4549_;
goto v_resetjp_4538_;
}
else
{
lean_dec(v_a_4477_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4549_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v_a_4541_; lean_object* v___x_4542_; uint8_t v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4547_; 
v_a_4541_ = lean_ctor_get(v___x_4495_, 0);
lean_inc(v_a_4541_);
lean_dec_ref_known(v___x_4495_, 1);
v___x_4542_ = lean_io_error_to_string(v_a_4541_);
v___x_4543_ = 3;
v___x_4544_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4544_, 0, v___x_4542_);
lean_ctor_set_uint8(v___x_4544_, sizeof(void*)*1, v___x_4543_);
v___x_4545_ = lean_array_push(v_log_4480_, v___x_4544_);
if (v_isShared_4540_ == 0)
{
lean_ctor_set(v___x_4539_, 0, v___x_4545_);
v___x_4547_ = v___x_4539_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v___x_4545_);
lean_ctor_set(v_reuseFailAlloc_4548_, 1, v_trace_4483_);
lean_ctor_set(v_reuseFailAlloc_4548_, 2, v_buildTime_4484_);
lean_ctor_set_uint8(v_reuseFailAlloc_4548_, sizeof(void*)*3, v_action_4481_);
lean_ctor_set_uint8(v_reuseFailAlloc_4548_, sizeof(void*)*3 + 1, v_wantsRebuild_4482_);
v___x_4547_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
v_a_4456_ = v___x_4488_;
v_a_4457_ = v___x_4547_;
goto v___jp_4455_;
}
}
}
}
}
}
else
{
lean_object* v_a_4562_; lean_object* v_a_4563_; 
lean_del_object(v___x_4474_);
lean_dec_ref(v___x_4453_);
lean_dec_ref(v_log_4442_);
lean_dec_ref(v_traceFile_4418_);
v_a_4562_ = lean_ctor_get(v___x_4476_, 0);
lean_inc(v_a_4562_);
v_a_4563_ = lean_ctor_get(v___x_4476_, 1);
lean_inc(v_a_4563_);
lean_dec_ref_known(v___x_4476_, 2);
v_a_4456_ = v_a_4562_;
v_a_4457_ = v_a_4563_;
goto v___jp_4455_;
}
}
}
else
{
lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4578_; 
lean_inc(v_buildTime_4470_);
lean_inc_ref(v_trace_4469_);
lean_inc_ref(v_log_4466_);
lean_dec_ref(v___x_4453_);
lean_dec_ref(v_log_4442_);
lean_dec_ref(v_traceFile_4418_);
lean_dec_ref(v_ext_4414_);
lean_dec_ref(v_file_4411_);
v_isSharedCheck_4578_ = !lean_is_exclusive(v_a_4465_);
if (v_isSharedCheck_4578_ == 0)
{
lean_object* v_unused_4579_; lean_object* v_unused_4580_; lean_object* v_unused_4581_; 
v_unused_4579_ = lean_ctor_get(v_a_4465_, 2);
lean_dec(v_unused_4579_);
v_unused_4580_ = lean_ctor_get(v_a_4465_, 1);
lean_dec(v_unused_4580_);
v_unused_4581_ = lean_ctor_get(v_a_4465_, 0);
lean_dec(v_unused_4581_);
v___x_4567_ = v_a_4465_;
v_isShared_4568_ = v_isSharedCheck_4578_;
goto v_resetjp_4566_;
}
else
{
lean_dec(v_a_4465_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4578_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
lean_object* v_a_4569_; lean_object* v___x_4570_; uint8_t v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4576_; 
v_a_4569_ = lean_ctor_get(v___x_4472_, 0);
lean_inc(v_a_4569_);
lean_dec_ref_known(v___x_4472_, 1);
v___x_4570_ = lean_io_error_to_string(v_a_4569_);
v___x_4571_ = 3;
v___x_4572_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4572_, 0, v___x_4570_);
lean_ctor_set_uint8(v___x_4572_, sizeof(void*)*1, v___x_4571_);
v___x_4573_ = lean_array_get_size(v_log_4466_);
v___x_4574_ = lean_array_push(v_log_4466_, v___x_4572_);
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 0, v___x_4574_);
v___x_4576_ = v___x_4567_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v___x_4574_);
lean_ctor_set(v_reuseFailAlloc_4577_, 1, v_trace_4469_);
lean_ctor_set(v_reuseFailAlloc_4577_, 2, v_buildTime_4470_);
lean_ctor_set_uint8(v_reuseFailAlloc_4577_, sizeof(void*)*3, v_action_4467_);
lean_ctor_set_uint8(v_reuseFailAlloc_4577_, sizeof(void*)*3 + 1, v_wantsRebuild_4468_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
v_a_4456_ = v___x_4573_;
v_a_4457_ = v___x_4576_;
goto v___jp_4455_;
}
}
}
}
else
{
lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4594_; 
lean_inc(v_buildTime_4470_);
lean_inc_ref(v_trace_4469_);
lean_inc_ref(v_log_4466_);
lean_dec_ref(v___x_4453_);
lean_dec_ref(v_log_4442_);
lean_dec_ref(v_traceFile_4418_);
lean_dec_ref(v_ext_4414_);
lean_dec_ref(v_file_4411_);
v_isSharedCheck_4594_ = !lean_is_exclusive(v_a_4465_);
if (v_isSharedCheck_4594_ == 0)
{
lean_object* v_unused_4595_; lean_object* v_unused_4596_; lean_object* v_unused_4597_; 
v_unused_4595_ = lean_ctor_get(v_a_4465_, 2);
lean_dec(v_unused_4595_);
v_unused_4596_ = lean_ctor_get(v_a_4465_, 1);
lean_dec(v_unused_4596_);
v_unused_4597_ = lean_ctor_get(v_a_4465_, 0);
lean_dec(v_unused_4597_);
v___x_4583_ = v_a_4465_;
v_isShared_4584_ = v_isSharedCheck_4594_;
goto v_resetjp_4582_;
}
else
{
lean_dec(v_a_4465_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4594_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v_a_4585_; lean_object* v___x_4586_; uint8_t v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4592_; 
v_a_4585_ = lean_ctor_get(v___x_4471_, 0);
lean_inc(v_a_4585_);
lean_dec_ref_known(v___x_4471_, 1);
v___x_4586_ = lean_io_error_to_string(v_a_4585_);
v___x_4587_ = 3;
v___x_4588_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4588_, 0, v___x_4586_);
lean_ctor_set_uint8(v___x_4588_, sizeof(void*)*1, v___x_4587_);
v___x_4589_ = lean_array_get_size(v_log_4466_);
v___x_4590_ = lean_array_push(v_log_4466_, v___x_4588_);
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 0, v___x_4590_);
v___x_4592_ = v___x_4583_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v___x_4590_);
lean_ctor_set(v_reuseFailAlloc_4593_, 1, v_trace_4469_);
lean_ctor_set(v_reuseFailAlloc_4593_, 2, v_buildTime_4470_);
lean_ctor_set_uint8(v_reuseFailAlloc_4593_, sizeof(void*)*3, v_action_4467_);
lean_ctor_set_uint8(v_reuseFailAlloc_4593_, sizeof(void*)*3 + 1, v_wantsRebuild_4468_);
v___x_4592_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
v_a_4456_ = v___x_4589_;
v_a_4457_ = v___x_4592_;
goto v___jp_4455_;
}
}
}
}
else
{
lean_object* v_a_4598_; lean_object* v_a_4599_; 
lean_dec_ref(v___x_4453_);
lean_dec_ref(v_log_4442_);
lean_dec_ref(v_traceFile_4418_);
lean_dec_ref(v_ext_4414_);
lean_dec_ref(v_file_4411_);
v_a_4598_ = lean_ctor_get(v___x_4464_, 0);
lean_inc(v_a_4598_);
v_a_4599_ = lean_ctor_get(v___x_4464_, 1);
lean_inc(v_a_4599_);
lean_dec_ref_known(v___x_4464_, 2);
v_a_4456_ = v_a_4598_;
v_a_4457_ = v_a_4599_;
goto v___jp_4455_;
}
}
}
else
{
lean_object* v_a_4601_; lean_object* v___x_4602_; uint8_t v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4608_; 
lean_dec_ref(v___x_4453_);
lean_dec_ref(v_traceFile_4418_);
lean_dec_ref(v_a_4416_);
lean_dec_ref(v_ext_4414_);
lean_dec_ref(v_build_4412_);
lean_dec_ref(v_file_4411_);
v_a_4601_ = lean_ctor_get(v___x_4461_, 0);
lean_inc(v_a_4601_);
lean_dec_ref_known(v___x_4461_, 1);
v___x_4602_ = lean_io_error_to_string(v_a_4601_);
v___x_4603_ = 3;
v___x_4604_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4604_, 0, v___x_4602_);
lean_ctor_set_uint8(v___x_4604_, sizeof(void*)*1, v___x_4603_);
v___x_4605_ = lean_array_get_size(v_log_4442_);
v___x_4606_ = lean_array_push(v_log_4442_, v___x_4604_);
if (v_isShared_4449_ == 0)
{
lean_ctor_set(v___x_4448_, 0, v___x_4606_);
v___x_4608_ = v___x_4448_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v___x_4606_);
lean_ctor_set(v_reuseFailAlloc_4609_, 1, v_trace_4445_);
lean_ctor_set(v_reuseFailAlloc_4609_, 2, v_buildTime_4446_);
lean_ctor_set_uint8(v_reuseFailAlloc_4609_, sizeof(void*)*3 + 1, v_wantsRebuild_4444_);
v___x_4608_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
lean_ctor_set_uint8(v___x_4608_, sizeof(void*)*3, v___x_4451_);
v_a_4456_ = v___x_4605_;
v_a_4457_ = v___x_4608_;
goto v___jp_4455_;
}
}
v___jp_4455_:
{
lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v_a_4460_; 
v___x_4458_ = lean_box(0);
v___x_4459_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(v___x_4454_, v___x_4458_, v_a_4457_);
lean_dec(v___x_4454_);
v_a_4460_ = lean_ctor_get(v___x_4459_, 1);
lean_inc(v_a_4460_);
lean_dec_ref(v___x_4459_);
v_a_4427_ = v_a_4456_;
v_a_4428_ = v_a_4460_;
goto v___jp_4426_;
}
}
else
{
uint8_t v___x_4610_; 
lean_dec_ref(v_a_4416_);
lean_dec_ref(v_ext_4414_);
lean_dec_ref(v_build_4412_);
lean_dec_ref(v_file_4411_);
v___x_4610_ = l_System_FilePath_pathExists(v_traceFile_4418_);
lean_dec_ref(v_traceFile_4418_);
if (v___x_4610_ == 0)
{
lean_dec_ref(v___x_4453_);
lean_del_object(v___x_4448_);
v_log_4431_ = v_log_4442_;
v_action_4432_ = v___x_4451_;
v_wantsRebuild_4433_ = v_noBuild_4450_;
v_trace_4434_ = v_trace_4445_;
v_buildTime_4435_ = v_buildTime_4446_;
goto v___jp_4430_;
}
else
{
lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; 
v___x_4611_ = lean_box(0);
v___x_4612_ = ((lean_object*)(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1));
v___x_4613_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_4417_, v___x_4611_, v___x_4612_);
v___x_4614_ = l_Lake_BuildMetadata_writeFile(v___x_4453_, v___x_4613_);
if (lean_obj_tag(v___x_4614_) == 0)
{
lean_dec_ref_known(v___x_4614_, 1);
lean_del_object(v___x_4448_);
v_log_4431_ = v_log_4442_;
v_action_4432_ = v___x_4451_;
v_wantsRebuild_4433_ = v_noBuild_4450_;
v_trace_4434_ = v_trace_4445_;
v_buildTime_4435_ = v_buildTime_4446_;
goto v___jp_4430_;
}
else
{
lean_object* v_a_4615_; lean_object* v___x_4616_; uint8_t v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4622_; 
v_a_4615_ = lean_ctor_get(v___x_4614_, 0);
lean_inc(v_a_4615_);
lean_dec_ref_known(v___x_4614_, 1);
v___x_4616_ = lean_io_error_to_string(v_a_4615_);
v___x_4617_ = 3;
v___x_4618_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4618_, 0, v___x_4616_);
lean_ctor_set_uint8(v___x_4618_, sizeof(void*)*1, v___x_4617_);
v___x_4619_ = lean_array_get_size(v_log_4442_);
v___x_4620_ = lean_array_push(v_log_4442_, v___x_4618_);
if (v_isShared_4449_ == 0)
{
lean_ctor_set(v___x_4448_, 0, v___x_4620_);
v___x_4622_ = v___x_4448_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v___x_4620_);
lean_ctor_set(v_reuseFailAlloc_4624_, 1, v_trace_4445_);
lean_ctor_set(v_reuseFailAlloc_4624_, 2, v_buildTime_4446_);
v___x_4622_ = v_reuseFailAlloc_4624_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
lean_object* v___x_4623_; 
lean_ctor_set_uint8(v___x_4622_, sizeof(void*)*3, v___x_4451_);
lean_ctor_set_uint8(v___x_4622_, sizeof(void*)*3 + 1, v_noBuild_4450_);
v___x_4623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4623_, 0, v___x_4619_);
lean_ctor_set(v___x_4623_, 1, v___x_4622_);
return v___x_4623_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___boxed(lean_object* v_file_4626_, lean_object* v_build_4627_, lean_object* v_traceFile_4628_, lean_object* v_ext_4629_, lean_object* v_text_4630_, lean_object* v_a_4631_, lean_object* v_depTrace_4632_, lean_object* v_traceFile_4633_, lean_object* v_action_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_){
_start:
{
uint8_t v_text_boxed_4641_; uint8_t v_action_boxed_4642_; lean_object* v_res_4643_; 
v_text_boxed_4641_ = lean_unbox(v_text_4630_);
v_action_boxed_4642_ = lean_unbox(v_action_4634_);
v_res_4643_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(v_file_4626_, v_build_4627_, v_traceFile_4628_, v_ext_4629_, v_text_boxed_4641_, v_a_4631_, v_depTrace_4632_, v_traceFile_4633_, v_action_boxed_4642_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_);
lean_dec_ref(v_a_4638_);
lean_dec(v_a_4637_);
lean_dec(v_a_4636_);
lean_dec(v_a_4635_);
lean_dec_ref(v_depTrace_4632_);
lean_dec_ref(v_traceFile_4628_);
return v_res_4643_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(lean_object* v_file_4644_, lean_object* v_build_4645_, uint8_t v_text_4646_, lean_object* v_ext_4647_, lean_object* v_depTrace_4648_, lean_object* v_traceFile_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_){
_start:
{
uint8_t v___x_4657_; lean_object* v___x_4658_; 
v___x_4657_ = 5;
lean_inc_ref(v_traceFile_4649_);
v___x_4658_ = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(v_file_4644_, v_build_4645_, v_traceFile_4649_, v_ext_4647_, v_text_4646_, v_a_4650_, v_depTrace_4648_, v_traceFile_4649_, v___x_4657_, v_a_4651_, v_a_4652_, v_a_4653_, v_a_4654_, v_a_4655_);
lean_dec_ref(v_traceFile_4649_);
return v___x_4658_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild___boxed(lean_object* v_file_4659_, lean_object* v_build_4660_, lean_object* v_text_4661_, lean_object* v_ext_4662_, lean_object* v_depTrace_4663_, lean_object* v_traceFile_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_){
_start:
{
uint8_t v_text_boxed_4672_; lean_object* v_res_4673_; 
v_text_boxed_4672_ = lean_unbox(v_text_4661_);
v_res_4673_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_4659_, v_build_4660_, v_text_boxed_4672_, v_ext_4662_, v_depTrace_4663_, v_traceFile_4664_, v_a_4665_, v_a_4666_, v_a_4667_, v_a_4668_, v_a_4669_, v_a_4670_);
lean_dec_ref(v_a_4669_);
lean_dec(v_a_4668_);
lean_dec(v_a_4667_);
lean_dec(v_a_4666_);
lean_dec_ref(v_depTrace_4663_);
return v_res_4673_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(lean_object* v_art_4675_, lean_object* v_traceFile_4676_, lean_object* v_a_4677_){
_start:
{
lean_object* v_log_4679_; uint8_t v_action_4680_; uint8_t v_wantsRebuild_4681_; lean_object* v_trace_4682_; lean_object* v_buildTime_4683_; lean_object* v___x_4684_; 
v_log_4679_ = lean_ctor_get(v_a_4677_, 0);
v_action_4680_ = lean_ctor_get_uint8(v_a_4677_, sizeof(void*)*3);
v_wantsRebuild_4681_ = lean_ctor_get_uint8(v_a_4677_, sizeof(void*)*3 + 1);
v_trace_4682_ = lean_ctor_get(v_a_4677_, 1);
v_buildTime_4683_ = lean_ctor_get(v_a_4677_, 2);
v___x_4684_ = lean_io_metadata(v_traceFile_4676_);
if (lean_obj_tag(v___x_4684_) == 0)
{
lean_object* v_a_4685_; lean_object* v_modified_4686_; lean_object* v_descr_4687_; lean_object* v_path_4688_; lean_object* v_name_4689_; lean_object* v___x_4691_; uint8_t v_isShared_4692_; uint8_t v_isSharedCheck_4697_; 
v_a_4685_ = lean_ctor_get(v___x_4684_, 0);
lean_inc(v_a_4685_);
lean_dec_ref_known(v___x_4684_, 1);
v_modified_4686_ = lean_ctor_get(v_a_4685_, 1);
lean_inc_ref(v_modified_4686_);
lean_dec(v_a_4685_);
v_descr_4687_ = lean_ctor_get(v_art_4675_, 0);
v_path_4688_ = lean_ctor_get(v_art_4675_, 1);
v_name_4689_ = lean_ctor_get(v_art_4675_, 2);
v_isSharedCheck_4697_ = !lean_is_exclusive(v_art_4675_);
if (v_isSharedCheck_4697_ == 0)
{
lean_object* v_unused_4698_; 
v_unused_4698_ = lean_ctor_get(v_art_4675_, 3);
lean_dec(v_unused_4698_);
v___x_4691_ = v_art_4675_;
v_isShared_4692_ = v_isSharedCheck_4697_;
goto v_resetjp_4690_;
}
else
{
lean_inc(v_name_4689_);
lean_inc(v_path_4688_);
lean_inc(v_descr_4687_);
lean_dec(v_art_4675_);
v___x_4691_ = lean_box(0);
v_isShared_4692_ = v_isSharedCheck_4697_;
goto v_resetjp_4690_;
}
v_resetjp_4690_:
{
lean_object* v___x_4694_; 
if (v_isShared_4692_ == 0)
{
lean_ctor_set(v___x_4691_, 3, v_modified_4686_);
v___x_4694_ = v___x_4691_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v_descr_4687_);
lean_ctor_set(v_reuseFailAlloc_4696_, 1, v_path_4688_);
lean_ctor_set(v_reuseFailAlloc_4696_, 2, v_name_4689_);
lean_ctor_set(v_reuseFailAlloc_4696_, 3, v_modified_4686_);
v___x_4694_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4693_;
}
v_reusejp_4693_:
{
lean_object* v___x_4695_; 
v___x_4695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4695_, 0, v___x_4694_);
lean_ctor_set(v___x_4695_, 1, v_a_4677_);
return v___x_4695_;
}
}
}
else
{
lean_object* v_a_4699_; 
v_a_4699_ = lean_ctor_get(v___x_4684_, 0);
lean_inc(v_a_4699_);
lean_dec_ref_known(v___x_4684_, 1);
if (lean_obj_tag(v_a_4699_) == 11)
{
lean_object* v___x_4700_; 
lean_dec_ref_known(v_a_4699_, 2);
v___x_4700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4700_, 0, v_art_4675_);
lean_ctor_set(v___x_4700_, 1, v_a_4677_);
return v___x_4700_;
}
else
{
lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4715_; 
lean_inc(v_buildTime_4683_);
lean_inc_ref(v_trace_4682_);
lean_inc_ref(v_log_4679_);
lean_dec_ref(v_art_4675_);
v_isSharedCheck_4715_ = !lean_is_exclusive(v_a_4677_);
if (v_isSharedCheck_4715_ == 0)
{
lean_object* v_unused_4716_; lean_object* v_unused_4717_; lean_object* v_unused_4718_; 
v_unused_4716_ = lean_ctor_get(v_a_4677_, 2);
lean_dec(v_unused_4716_);
v_unused_4717_ = lean_ctor_get(v_a_4677_, 1);
lean_dec(v_unused_4717_);
v_unused_4718_ = lean_ctor_get(v_a_4677_, 0);
lean_dec(v_unused_4718_);
v___x_4702_ = v_a_4677_;
v_isShared_4703_ = v_isSharedCheck_4715_;
goto v_resetjp_4701_;
}
else
{
lean_dec(v_a_4677_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4715_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; uint8_t v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4712_; 
v___x_4704_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___closed__0));
v___x_4705_ = lean_io_error_to_string(v_a_4699_);
v___x_4706_ = lean_string_append(v___x_4704_, v___x_4705_);
lean_dec_ref(v___x_4705_);
v___x_4707_ = 3;
v___x_4708_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4708_, 0, v___x_4706_);
lean_ctor_set_uint8(v___x_4708_, sizeof(void*)*1, v___x_4707_);
v___x_4709_ = lean_array_get_size(v_log_4679_);
v___x_4710_ = lean_array_push(v_log_4679_, v___x_4708_);
if (v_isShared_4703_ == 0)
{
lean_ctor_set(v___x_4702_, 0, v___x_4710_);
v___x_4712_ = v___x_4702_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v___x_4710_);
lean_ctor_set(v_reuseFailAlloc_4714_, 1, v_trace_4682_);
lean_ctor_set(v_reuseFailAlloc_4714_, 2, v_buildTime_4683_);
lean_ctor_set_uint8(v_reuseFailAlloc_4714_, sizeof(void*)*3, v_action_4680_);
lean_ctor_set_uint8(v_reuseFailAlloc_4714_, sizeof(void*)*3 + 1, v_wantsRebuild_4681_);
v___x_4712_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
lean_object* v___x_4713_; 
v___x_4713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4713_, 0, v___x_4709_);
lean_ctor_set(v___x_4713_, 1, v___x_4712_);
return v___x_4713_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg___boxed(lean_object* v_art_4719_, lean_object* v_traceFile_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_){
_start:
{
lean_object* v_res_4723_; 
v_res_4723_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_4719_, v_traceFile_4720_, v_a_4721_);
lean_dec_ref(v_traceFile_4720_);
return v_res_4723_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(lean_object* v_art_4724_, lean_object* v_traceFile_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_){
_start:
{
lean_object* v___x_4733_; 
v___x_4733_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_4724_, v_traceFile_4725_, v_a_4731_);
return v___x_4733_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___boxed(lean_object* v_art_4734_, lean_object* v_traceFile_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_){
_start:
{
lean_object* v_res_4743_; 
v_res_4743_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime(v_art_4734_, v_traceFile_4735_, v_a_4736_, v_a_4737_, v_a_4738_, v_a_4739_, v_a_4740_, v_a_4741_);
lean_dec_ref(v_a_4740_);
lean_dec(v_a_4739_);
lean_dec(v_a_4738_);
lean_dec(v_a_4737_);
lean_dec_ref(v_a_4736_);
lean_dec_ref(v_traceFile_4735_);
return v_res_4743_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(lean_object* v_a_4744_, lean_object* v_____r_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_){
_start:
{
lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; 
v___x_4753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4753_, 0, v_a_4744_);
v___x_4754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4754_, 0, v___x_4753_);
v___x_4755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4755_, 0, v___x_4754_);
lean_ctor_set(v___x_4755_, 1, v___y_4751_);
return v___x_4755_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0___boxed(lean_object* v_a_4756_, lean_object* v_____r_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_){
_start:
{
lean_object* v_res_4765_; 
v_res_4765_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4756_, v_____r_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_);
lean_dec_ref(v___y_4762_);
lean_dec(v___y_4761_);
lean_dec(v___y_4760_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
return v_res_4765_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(uint8_t v_exe_4766_, lean_object* v___y_4767_, uint64_t v_inputHash_4768_, lean_object* v_savedTrace_4769_, lean_object* v_pkg_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_){
_start:
{
lean_object* v___y_4778_; lean_object* v_a_4782_; lean_object* v_a_4783_; lean_object* v___y_4798_; 
if (lean_obj_tag(v_savedTrace_4769_) == 2)
{
lean_object* v_data_4813_; uint64_t v_depHash_4814_; lean_object* v_outputs_x3f_4815_; uint8_t v___x_4816_; 
v_data_4813_ = lean_ctor_get(v_savedTrace_4769_, 0);
lean_inc_ref(v_data_4813_);
lean_dec_ref_known(v_savedTrace_4769_, 1);
v_depHash_4814_ = lean_ctor_get_uint64(v_data_4813_, sizeof(void*)*3);
v_outputs_x3f_4815_ = lean_ctor_get(v_data_4813_, 1);
lean_inc(v_outputs_x3f_4815_);
lean_dec_ref(v_data_4813_);
v___x_4816_ = lean_uint64_dec_eq(v_depHash_4814_, v_inputHash_4768_);
if (v___x_4816_ == 0)
{
lean_dec(v_outputs_x3f_4815_);
lean_dec_ref(v_pkg_4770_);
lean_dec_ref(v___y_4767_);
v___y_4778_ = v_a_4775_;
goto v___jp_4777_;
}
else
{
if (lean_obj_tag(v_outputs_x3f_4815_) == 1)
{
lean_object* v_val_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; 
v_val_4817_ = lean_ctor_get(v_outputs_x3f_4815_, 0);
lean_inc_n(v_val_4817_, 2);
lean_dec_ref_known(v_outputs_x3f_4815_, 1);
v___x_4818_ = lean_box(0);
v___x_4819_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4819_, 0, v_val_4817_);
lean_ctor_set(v___x_4819_, 1, v___x_4818_);
lean_ctor_set(v___x_4819_, 2, v___x_4818_);
lean_inc_ref(v___y_4767_);
v___x_4820_ = l_Lake_resolveArtifactOutput(v___x_4819_, v_exe_4766_, v___y_4767_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_);
if (lean_obj_tag(v___x_4820_) == 0)
{
lean_object* v_config_4821_; lean_object* v_a_4822_; lean_object* v_a_4823_; lean_object* v_enableArtifactCache_x3f_4824_; lean_object* v_a_4826_; uint8_t v_a_4830_; lean_object* v_a_4831_; 
v_config_4821_ = lean_ctor_get(v_pkg_4770_, 6);
v_a_4822_ = lean_ctor_get(v___x_4820_, 0);
lean_inc(v_a_4822_);
v_a_4823_ = lean_ctor_get(v___x_4820_, 1);
lean_inc(v_a_4823_);
lean_dec_ref_known(v___x_4820_, 2);
v_enableArtifactCache_x3f_4824_ = lean_ctor_get(v_config_4821_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_4824_) == 0)
{
lean_object* v_toContext_4863_; lean_object* v_lakeEnv_4864_; lean_object* v_enableArtifactCache_x3f_4865_; 
v_toContext_4863_ = lean_ctor_get(v_a_4774_, 1);
v_lakeEnv_4864_ = lean_ctor_get(v_toContext_4863_, 0);
v_enableArtifactCache_x3f_4865_ = lean_ctor_get(v_lakeEnv_4864_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_4865_) == 0)
{
lean_object* v_packages_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v_config_4869_; lean_object* v_enableArtifactCache_x3f_4870_; 
v_packages_4866_ = lean_ctor_get(v_toContext_4863_, 4);
v___x_4867_ = lean_unsigned_to_nat(0u);
v___x_4868_ = lean_array_fget_borrowed(v_packages_4866_, v___x_4867_);
v_config_4869_ = lean_ctor_get(v___x_4868_, 6);
v_enableArtifactCache_x3f_4870_ = lean_ctor_get(v_config_4869_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_4870_) == 0)
{
lean_dec(v_val_4817_);
lean_dec_ref(v_pkg_4770_);
v_a_4826_ = v_a_4823_;
goto v___jp_4825_;
}
else
{
lean_object* v_val_4871_; uint8_t v___x_4872_; 
v_val_4871_ = lean_ctor_get(v_enableArtifactCache_x3f_4870_, 0);
v___x_4872_ = lean_unbox(v_val_4871_);
v_a_4830_ = v___x_4872_;
v_a_4831_ = v_a_4823_;
goto v___jp_4829_;
}
}
else
{
lean_object* v_val_4873_; uint8_t v___x_4874_; 
v_val_4873_ = lean_ctor_get(v_enableArtifactCache_x3f_4865_, 0);
v___x_4874_ = lean_unbox(v_val_4873_);
v_a_4830_ = v___x_4874_;
v_a_4831_ = v_a_4823_;
goto v___jp_4829_;
}
}
else
{
lean_object* v_val_4875_; uint8_t v___x_4876_; 
v_val_4875_ = lean_ctor_get(v_enableArtifactCache_x3f_4824_, 0);
v___x_4876_ = lean_unbox(v_val_4875_);
v_a_4830_ = v___x_4876_;
v_a_4831_ = v_a_4823_;
goto v___jp_4829_;
}
v___jp_4825_:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; 
v___x_4827_ = lean_box(0);
v___x_4828_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4822_, v___x_4827_, v___y_4767_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4826_);
lean_dec_ref(v___y_4767_);
v___y_4798_ = v___x_4828_;
goto v___jp_4797_;
}
v___jp_4829_:
{
if (v_a_4830_ == 0)
{
lean_dec(v_val_4817_);
lean_dec_ref(v_pkg_4770_);
v_a_4826_ = v_a_4831_;
goto v___jp_4825_;
}
else
{
lean_object* v_toContext_4832_; lean_object* v_log_4833_; uint8_t v_action_4834_; uint8_t v_wantsRebuild_4835_; lean_object* v_trace_4836_; lean_object* v_buildTime_4837_; lean_object* v_lakeCache_4838_; lean_object* v___x_4839_; uint8_t v___x_4840_; lean_object* v___x_4841_; 
v_toContext_4832_ = lean_ctor_get(v_a_4774_, 1);
v_log_4833_ = lean_ctor_get(v_a_4831_, 0);
v_action_4834_ = lean_ctor_get_uint8(v_a_4831_, sizeof(void*)*3);
v_wantsRebuild_4835_ = lean_ctor_get_uint8(v_a_4831_, sizeof(void*)*3 + 1);
v_trace_4836_ = lean_ctor_get(v_a_4831_, 1);
v_buildTime_4837_ = lean_ctor_get(v_a_4831_, 2);
v_lakeCache_4838_ = lean_ctor_get(v_toContext_4832_, 2);
v___x_4839_ = l_Lake_Package_cacheScope(v_pkg_4770_);
v___x_4840_ = 0;
lean_inc_ref(v_lakeCache_4838_);
v___x_4841_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_4838_, v___x_4839_, v_inputHash_4768_, v_val_4817_, v___x_4818_, v___x_4818_, v___x_4840_);
if (lean_obj_tag(v___x_4841_) == 0)
{
lean_object* v___x_4842_; lean_object* v___x_4843_; 
lean_dec_ref_known(v___x_4841_, 1);
v___x_4842_ = lean_box(0);
v___x_4843_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4822_, v___x_4842_, v___y_4767_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4831_);
lean_dec_ref(v___y_4767_);
v___y_4798_ = v___x_4843_;
goto v___jp_4797_;
}
else
{
lean_object* v___x_4845_; uint8_t v_isShared_4846_; uint8_t v_isSharedCheck_4859_; 
lean_inc(v_buildTime_4837_);
lean_inc_ref(v_trace_4836_);
lean_inc_ref(v_log_4833_);
v_isSharedCheck_4859_ = !lean_is_exclusive(v_a_4831_);
if (v_isSharedCheck_4859_ == 0)
{
lean_object* v_unused_4860_; lean_object* v_unused_4861_; lean_object* v_unused_4862_; 
v_unused_4860_ = lean_ctor_get(v_a_4831_, 2);
lean_dec(v_unused_4860_);
v_unused_4861_ = lean_ctor_get(v_a_4831_, 1);
lean_dec(v_unused_4861_);
v_unused_4862_ = lean_ctor_get(v_a_4831_, 0);
lean_dec(v_unused_4862_);
v___x_4845_ = v_a_4831_;
v_isShared_4846_ = v_isSharedCheck_4859_;
goto v_resetjp_4844_;
}
else
{
lean_dec(v_a_4831_);
v___x_4845_ = lean_box(0);
v_isShared_4846_ = v_isSharedCheck_4859_;
goto v_resetjp_4844_;
}
v_resetjp_4844_:
{
lean_object* v_a_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; uint8_t v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4856_; 
v_a_4847_ = lean_ctor_get(v___x_4841_, 0);
lean_inc(v_a_4847_);
lean_dec_ref_known(v___x_4841_, 1);
v___x_4848_ = ((lean_object*)(l_Lake_getArtifactsUsingTrace_x3f___redArg___closed__0));
v___x_4849_ = lean_io_error_to_string(v_a_4847_);
v___x_4850_ = lean_string_append(v___x_4848_, v___x_4849_);
lean_dec_ref(v___x_4849_);
v___x_4851_ = 2;
v___x_4852_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4852_, 0, v___x_4850_);
lean_ctor_set_uint8(v___x_4852_, sizeof(void*)*1, v___x_4851_);
v___x_4853_ = lean_box(0);
v___x_4854_ = lean_array_push(v_log_4833_, v___x_4852_);
if (v_isShared_4846_ == 0)
{
lean_ctor_set(v___x_4845_, 0, v___x_4854_);
v___x_4856_ = v___x_4845_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v___x_4854_);
lean_ctor_set(v_reuseFailAlloc_4858_, 1, v_trace_4836_);
lean_ctor_set(v_reuseFailAlloc_4858_, 2, v_buildTime_4837_);
lean_ctor_set_uint8(v_reuseFailAlloc_4858_, sizeof(void*)*3, v_action_4834_);
lean_ctor_set_uint8(v_reuseFailAlloc_4858_, sizeof(void*)*3 + 1, v_wantsRebuild_4835_);
v___x_4856_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
lean_object* v___x_4857_; 
v___x_4857_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___lam__0(v_a_4822_, v___x_4853_, v___y_4767_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v___x_4856_);
lean_dec_ref(v___y_4767_);
v___y_4798_ = v___x_4857_;
goto v___jp_4797_;
}
}
}
}
}
}
else
{
lean_object* v_a_4877_; lean_object* v_a_4878_; 
lean_dec(v_val_4817_);
lean_dec_ref(v_pkg_4770_);
lean_dec_ref(v___y_4767_);
v_a_4877_ = lean_ctor_get(v___x_4820_, 0);
lean_inc(v_a_4877_);
v_a_4878_ = lean_ctor_get(v___x_4820_, 1);
lean_inc(v_a_4878_);
lean_dec_ref_known(v___x_4820_, 2);
v_a_4782_ = v_a_4877_;
v_a_4783_ = v_a_4878_;
goto v___jp_4781_;
}
}
else
{
lean_dec(v_outputs_x3f_4815_);
lean_dec_ref(v_pkg_4770_);
lean_dec_ref(v___y_4767_);
v___y_4778_ = v_a_4775_;
goto v___jp_4777_;
}
}
}
else
{
lean_dec_ref(v_pkg_4770_);
lean_dec(v_savedTrace_4769_);
lean_dec_ref(v___y_4767_);
v___y_4778_ = v_a_4775_;
goto v___jp_4777_;
}
v___jp_4777_:
{
lean_object* v___x_4779_; lean_object* v___x_4780_; 
v___x_4779_ = lean_box(0);
v___x_4780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4780_, 0, v___x_4779_);
lean_ctor_set(v___x_4780_, 1, v___y_4778_);
return v___x_4780_;
}
v___jp_4781_:
{
lean_object* v_log_4784_; uint8_t v_action_4785_; uint8_t v_wantsRebuild_4786_; lean_object* v_trace_4787_; lean_object* v_buildTime_4788_; lean_object* v___x_4790_; uint8_t v_isShared_4791_; uint8_t v_isSharedCheck_4796_; 
v_log_4784_ = lean_ctor_get(v_a_4783_, 0);
v_action_4785_ = lean_ctor_get_uint8(v_a_4783_, sizeof(void*)*3);
v_wantsRebuild_4786_ = lean_ctor_get_uint8(v_a_4783_, sizeof(void*)*3 + 1);
v_trace_4787_ = lean_ctor_get(v_a_4783_, 1);
v_buildTime_4788_ = lean_ctor_get(v_a_4783_, 2);
v_isSharedCheck_4796_ = !lean_is_exclusive(v_a_4783_);
if (v_isSharedCheck_4796_ == 0)
{
v___x_4790_ = v_a_4783_;
v_isShared_4791_ = v_isSharedCheck_4796_;
goto v_resetjp_4789_;
}
else
{
lean_inc(v_buildTime_4788_);
lean_inc(v_trace_4787_);
lean_inc(v_log_4784_);
lean_dec(v_a_4783_);
v___x_4790_ = lean_box(0);
v_isShared_4791_ = v_isSharedCheck_4796_;
goto v_resetjp_4789_;
}
v_resetjp_4789_:
{
lean_object* v___x_4792_; lean_object* v___x_4794_; 
v___x_4792_ = l_Array_shrink___redArg(v_log_4784_, v_a_4782_);
lean_dec(v_a_4782_);
if (v_isShared_4791_ == 0)
{
lean_ctor_set(v___x_4790_, 0, v___x_4792_);
v___x_4794_ = v___x_4790_;
goto v_reusejp_4793_;
}
else
{
lean_object* v_reuseFailAlloc_4795_; 
v_reuseFailAlloc_4795_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4795_, 0, v___x_4792_);
lean_ctor_set(v_reuseFailAlloc_4795_, 1, v_trace_4787_);
lean_ctor_set(v_reuseFailAlloc_4795_, 2, v_buildTime_4788_);
lean_ctor_set_uint8(v_reuseFailAlloc_4795_, sizeof(void*)*3, v_action_4785_);
lean_ctor_set_uint8(v_reuseFailAlloc_4795_, sizeof(void*)*3 + 1, v_wantsRebuild_4786_);
v___x_4794_ = v_reuseFailAlloc_4795_;
goto v_reusejp_4793_;
}
v_reusejp_4793_:
{
v___y_4778_ = v___x_4794_;
goto v___jp_4777_;
}
}
}
v___jp_4797_:
{
if (lean_obj_tag(v___y_4798_) == 0)
{
lean_object* v_a_4799_; 
v_a_4799_ = lean_ctor_get(v___y_4798_, 0);
if (lean_obj_tag(v_a_4799_) == 0)
{
lean_object* v_a_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4808_; 
lean_inc_ref(v_a_4799_);
v_a_4800_ = lean_ctor_get(v___y_4798_, 1);
v_isSharedCheck_4808_ = !lean_is_exclusive(v___y_4798_);
if (v_isSharedCheck_4808_ == 0)
{
lean_object* v_unused_4809_; 
v_unused_4809_ = lean_ctor_get(v___y_4798_, 0);
lean_dec(v_unused_4809_);
v___x_4802_ = v___y_4798_;
v_isShared_4803_ = v_isSharedCheck_4808_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_a_4800_);
lean_dec(v___y_4798_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4808_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v_a_4804_; lean_object* v___x_4806_; 
v_a_4804_ = lean_ctor_get(v_a_4799_, 0);
lean_inc(v_a_4804_);
lean_dec_ref_known(v_a_4799_, 1);
if (v_isShared_4803_ == 0)
{
lean_ctor_set(v___x_4802_, 0, v_a_4804_);
v___x_4806_ = v___x_4802_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_a_4804_);
lean_ctor_set(v_reuseFailAlloc_4807_, 1, v_a_4800_);
v___x_4806_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
return v___x_4806_;
}
}
}
else
{
lean_object* v_a_4810_; 
v_a_4810_ = lean_ctor_get(v___y_4798_, 1);
lean_inc(v_a_4810_);
lean_dec_ref_known(v___y_4798_, 2);
v___y_4778_ = v_a_4810_;
goto v___jp_4777_;
}
}
else
{
lean_object* v_a_4811_; lean_object* v_a_4812_; 
v_a_4811_ = lean_ctor_get(v___y_4798_, 0);
lean_inc(v_a_4811_);
v_a_4812_ = lean_ctor_get(v___y_4798_, 1);
lean_inc(v_a_4812_);
lean_dec_ref_known(v___y_4798_, 2);
v_a_4782_ = v_a_4811_;
v_a_4783_ = v_a_4812_;
goto v___jp_4781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object* v_exe_4879_, lean_object* v___y_4880_, lean_object* v_inputHash_4881_, lean_object* v_savedTrace_4882_, lean_object* v_pkg_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_){
_start:
{
uint8_t v_exe_boxed_4890_; uint64_t v_inputHash_boxed_4891_; lean_object* v_res_4892_; 
v_exe_boxed_4890_ = lean_unbox(v_exe_4879_);
v_inputHash_boxed_4891_ = lean_unbox_uint64(v_inputHash_4881_);
lean_dec_ref(v_inputHash_4881_);
v_res_4892_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(v_exe_boxed_4890_, v___y_4880_, v_inputHash_boxed_4891_, v_savedTrace_4882_, v_pkg_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_);
lean_dec_ref(v_a_4887_);
lean_dec(v_a_4886_);
lean_dec(v_a_4885_);
lean_dec(v_a_4884_);
return v_res_4892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1(lean_object* v_as_4893_, size_t v_i_4894_, size_t v_stop_4895_, lean_object* v_b_4896_){
_start:
{
uint8_t v___x_4897_; 
v___x_4897_ = lean_usize_dec_eq(v_i_4894_, v_stop_4895_);
if (v___x_4897_ == 0)
{
lean_object* v___x_4898_; lean_object* v_message_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; size_t v___x_4903_; size_t v___x_4904_; 
v___x_4898_ = lean_array_uget_borrowed(v_as_4893_, v_i_4894_);
v_message_4899_ = lean_ctor_get(v___x_4898_, 0);
v___x_4900_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___lam__0___closed__0));
v___x_4901_ = lean_string_append(v_b_4896_, v___x_4900_);
v___x_4902_ = lean_string_append(v___x_4901_, v_message_4899_);
v___x_4903_ = ((size_t)1ULL);
v___x_4904_ = lean_usize_add(v_i_4894_, v___x_4903_);
v_i_4894_ = v___x_4904_;
v_b_4896_ = v___x_4902_;
goto _start;
}
else
{
return v_b_4896_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1___boxed(lean_object* v_as_4906_, lean_object* v_i_4907_, lean_object* v_stop_4908_, lean_object* v_b_4909_){
_start:
{
size_t v_i_boxed_4910_; size_t v_stop_boxed_4911_; lean_object* v_res_4912_; 
v_i_boxed_4910_ = lean_unbox_usize(v_i_4907_);
lean_dec(v_i_4907_);
v_stop_boxed_4911_ = lean_unbox_usize(v_stop_4908_);
lean_dec(v_stop_4908_);
v_res_4912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1(v_as_4906_, v_i_boxed_4910_, v_stop_boxed_4911_, v_b_4909_);
lean_dec_ref(v_as_4906_);
return v_res_4912_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(uint8_t v_exe_4913_, lean_object* v___y_4914_, uint64_t v_inputHash_4915_, lean_object* v_pkg_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_){
_start:
{
lean_object* v_r_4924_; lean_object* v___y_4925_; lean_object* v___y_4928_; lean_object* v___y_4929_; lean_object* v___y_4930_; uint8_t v___y_4931_; uint8_t v___y_4932_; lean_object* v___y_4933_; lean_object* v_a_4940_; lean_object* v_log_4941_; uint8_t v_action_4942_; uint8_t v_wantsRebuild_4943_; lean_object* v_trace_4944_; lean_object* v_buildTime_4945_; lean_object* v_toContext_4966_; lean_object* v_log_4967_; uint8_t v_action_4968_; uint8_t v_wantsRebuild_4969_; lean_object* v_trace_4970_; lean_object* v_buildTime_4971_; lean_object* v___x_4973_; uint8_t v_isShared_4974_; uint8_t v_isSharedCheck_5004_; 
v_toContext_4966_ = lean_ctor_get(v_a_4920_, 1);
v_log_4967_ = lean_ctor_get(v_a_4921_, 0);
v_action_4968_ = lean_ctor_get_uint8(v_a_4921_, sizeof(void*)*3);
v_wantsRebuild_4969_ = lean_ctor_get_uint8(v_a_4921_, sizeof(void*)*3 + 1);
v_trace_4970_ = lean_ctor_get(v_a_4921_, 1);
v_buildTime_4971_ = lean_ctor_get(v_a_4921_, 2);
v_isSharedCheck_5004_ = !lean_is_exclusive(v_a_4921_);
if (v_isSharedCheck_5004_ == 0)
{
v___x_4973_ = v_a_4921_;
v_isShared_4974_ = v_isSharedCheck_5004_;
goto v_resetjp_4972_;
}
else
{
lean_inc(v_buildTime_4971_);
lean_inc(v_trace_4970_);
lean_inc(v_log_4967_);
lean_dec(v_a_4921_);
v___x_4973_ = lean_box(0);
v_isShared_4974_ = v_isSharedCheck_5004_;
goto v_resetjp_4972_;
}
v___jp_4923_:
{
lean_object* v___x_4926_; 
v___x_4926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4926_, 0, v_r_4924_);
lean_ctor_set(v___x_4926_, 1, v___y_4925_);
return v___x_4926_;
}
v___jp_4927_:
{
uint8_t v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; 
v___x_4934_ = 0;
v___x_4935_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4935_, 0, v___y_4933_);
lean_ctor_set_uint8(v___x_4935_, sizeof(void*)*1, v___x_4934_);
v___x_4936_ = lean_array_push(v___y_4929_, v___x_4935_);
v___x_4937_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4937_, 0, v___x_4936_);
lean_ctor_set(v___x_4937_, 1, v___y_4928_);
lean_ctor_set(v___x_4937_, 2, v___y_4930_);
lean_ctor_set_uint8(v___x_4937_, sizeof(void*)*3, v___y_4932_);
lean_ctor_set_uint8(v___x_4937_, sizeof(void*)*3 + 1, v___y_4931_);
v___x_4938_ = lean_box(0);
v_r_4924_ = v___x_4938_;
v___y_4925_ = v___x_4937_;
goto v___jp_4923_;
}
v___jp_4939_:
{
lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; uint8_t v___x_4962_; 
v___x_4946_ = lean_array_get_size(v_log_4941_);
lean_inc(v_a_4940_);
v___x_4947_ = l_Array_extract___redArg(v_log_4941_, v_a_4940_, v___x_4946_);
v___x_4948_ = l_Array_shrink___redArg(v_log_4941_, v_a_4940_);
lean_dec(v_a_4940_);
v___x_4949_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__1));
v___x_4950_ = l_Lake_lowerHexUInt64(v_inputHash_4915_);
v___x_4951_ = lean_unsigned_to_nat(7u);
v___x_4952_ = lean_unsigned_to_nat(0u);
v___x_4953_ = lean_string_utf8_byte_size(v___x_4950_);
lean_inc_ref(v___x_4950_);
v___x_4954_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4954_, 0, v___x_4950_);
lean_ctor_set(v___x_4954_, 1, v___x_4952_);
lean_ctor_set(v___x_4954_, 2, v___x_4953_);
v___x_4955_ = l_String_Slice_Pos_nextn(v___x_4954_, v___x_4952_, v___x_4951_);
lean_dec_ref_known(v___x_4954_, 3);
v___x_4956_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4956_, 0, v___x_4950_);
lean_ctor_set(v___x_4956_, 1, v___x_4952_);
lean_ctor_set(v___x_4956_, 2, v___x_4955_);
v___x_4957_ = l_String_Slice_toString(v___x_4956_);
lean_dec_ref_known(v___x_4956_, 3);
v___x_4958_ = lean_string_append(v___x_4949_, v___x_4957_);
lean_dec_ref(v___x_4957_);
v___x_4959_ = ((lean_object*)(l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___redArg___closed__2));
v___x_4960_ = lean_string_append(v___x_4958_, v___x_4959_);
v___x_4961_ = lean_array_get_size(v___x_4947_);
v___x_4962_ = lean_nat_dec_lt(v___x_4952_, v___x_4961_);
if (v___x_4962_ == 0)
{
lean_dec_ref(v___x_4947_);
v___y_4928_ = v_trace_4944_;
v___y_4929_ = v___x_4948_;
v___y_4930_ = v_buildTime_4945_;
v___y_4931_ = v_wantsRebuild_4943_;
v___y_4932_ = v_action_4942_;
v___y_4933_ = v___x_4960_;
goto v___jp_4927_;
}
else
{
size_t v___x_4963_; size_t v___x_4964_; lean_object* v___x_4965_; 
v___x_4963_ = ((size_t)0ULL);
v___x_4964_ = lean_usize_of_nat(v___x_4961_);
v___x_4965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1_spec__1(v___x_4947_, v___x_4963_, v___x_4964_, v___x_4960_);
lean_dec_ref(v___x_4947_);
v___y_4928_ = v_trace_4944_;
v___y_4929_ = v___x_4948_;
v___y_4930_ = v_buildTime_4945_;
v___y_4931_ = v_wantsRebuild_4943_;
v___y_4932_ = v_action_4942_;
v___y_4933_ = v___x_4965_;
goto v___jp_4927_;
}
}
v_resetjp_4972_:
{
lean_object* v_lakeCache_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; 
v_lakeCache_4975_ = lean_ctor_get(v_toContext_4966_, 2);
v___x_4976_ = l_Lake_Package_cacheScope(v_pkg_4916_);
lean_inc_ref(v_lakeCache_4975_);
v___x_4977_ = l_Lake_Cache_readOutputs_x3f(v_lakeCache_4975_, v___x_4976_, v_inputHash_4915_, v_log_4967_);
if (lean_obj_tag(v___x_4977_) == 0)
{
lean_object* v_a_4978_; lean_object* v_a_4979_; lean_object* v___x_4981_; 
v_a_4978_ = lean_ctor_get(v___x_4977_, 0);
lean_inc(v_a_4978_);
v_a_4979_ = lean_ctor_get(v___x_4977_, 1);
lean_inc(v_a_4979_);
lean_dec_ref_known(v___x_4977_, 2);
if (v_isShared_4974_ == 0)
{
lean_ctor_set(v___x_4973_, 0, v_a_4979_);
v___x_4981_ = v___x_4973_;
goto v_reusejp_4980_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v_a_4979_);
lean_ctor_set(v_reuseFailAlloc_5001_, 1, v_trace_4970_);
lean_ctor_set(v_reuseFailAlloc_5001_, 2, v_buildTime_4971_);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, sizeof(void*)*3, v_action_4968_);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, sizeof(void*)*3 + 1, v_wantsRebuild_4969_);
v___x_4981_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4980_;
}
v_reusejp_4980_:
{
if (lean_obj_tag(v_a_4978_) == 0)
{
lean_object* v___x_4982_; 
lean_dec_ref(v___y_4914_);
v___x_4982_ = lean_box(0);
v_r_4924_ = v___x_4982_;
v___y_4925_ = v___x_4981_;
goto v___jp_4923_;
}
else
{
lean_object* v_val_4983_; lean_object* v___x_4985_; uint8_t v_isShared_4986_; uint8_t v_isSharedCheck_5000_; 
v_val_4983_ = lean_ctor_get(v_a_4978_, 0);
v_isSharedCheck_5000_ = !lean_is_exclusive(v_a_4978_);
if (v_isSharedCheck_5000_ == 0)
{
v___x_4985_ = v_a_4978_;
v_isShared_4986_ = v_isSharedCheck_5000_;
goto v_resetjp_4984_;
}
else
{
lean_inc(v_val_4983_);
lean_dec(v_a_4978_);
v___x_4985_ = lean_box(0);
v_isShared_4986_ = v_isSharedCheck_5000_;
goto v_resetjp_4984_;
}
v_resetjp_4984_:
{
lean_object* v___x_4987_; 
v___x_4987_ = l_Lake_resolveArtifactOutput(v_val_4983_, v_exe_4913_, v___y_4914_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v___x_4981_);
if (lean_obj_tag(v___x_4987_) == 0)
{
lean_object* v_a_4988_; lean_object* v_a_4989_; lean_object* v___x_4991_; 
v_a_4988_ = lean_ctor_get(v___x_4987_, 0);
lean_inc(v_a_4988_);
v_a_4989_ = lean_ctor_get(v___x_4987_, 1);
lean_inc(v_a_4989_);
lean_dec_ref_known(v___x_4987_, 2);
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 0, v_a_4988_);
v___x_4991_ = v___x_4985_;
goto v_reusejp_4990_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v_a_4988_);
v___x_4991_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4990_;
}
v_reusejp_4990_:
{
v_r_4924_ = v___x_4991_;
v___y_4925_ = v_a_4989_;
goto v___jp_4923_;
}
}
else
{
lean_object* v_a_4993_; lean_object* v_a_4994_; lean_object* v_log_4995_; uint8_t v_action_4996_; uint8_t v_wantsRebuild_4997_; lean_object* v_trace_4998_; lean_object* v_buildTime_4999_; 
lean_del_object(v___x_4985_);
v_a_4993_ = lean_ctor_get(v___x_4987_, 1);
lean_inc(v_a_4993_);
v_a_4994_ = lean_ctor_get(v___x_4987_, 0);
lean_inc(v_a_4994_);
lean_dec_ref_known(v___x_4987_, 2);
v_log_4995_ = lean_ctor_get(v_a_4993_, 0);
lean_inc_ref(v_log_4995_);
v_action_4996_ = lean_ctor_get_uint8(v_a_4993_, sizeof(void*)*3);
v_wantsRebuild_4997_ = lean_ctor_get_uint8(v_a_4993_, sizeof(void*)*3 + 1);
v_trace_4998_ = lean_ctor_get(v_a_4993_, 1);
lean_inc_ref(v_trace_4998_);
v_buildTime_4999_ = lean_ctor_get(v_a_4993_, 2);
lean_inc(v_buildTime_4999_);
lean_dec(v_a_4993_);
v_a_4940_ = v_a_4994_;
v_log_4941_ = v_log_4995_;
v_action_4942_ = v_action_4996_;
v_wantsRebuild_4943_ = v_wantsRebuild_4997_;
v_trace_4944_ = v_trace_4998_;
v_buildTime_4945_ = v_buildTime_4999_;
goto v___jp_4939_;
}
}
}
}
}
else
{
lean_object* v_a_5002_; lean_object* v_a_5003_; 
lean_del_object(v___x_4973_);
lean_dec_ref(v___y_4914_);
v_a_5002_ = lean_ctor_get(v___x_4977_, 0);
lean_inc(v_a_5002_);
v_a_5003_ = lean_ctor_get(v___x_4977_, 1);
lean_inc(v_a_5003_);
lean_dec_ref_known(v___x_4977_, 2);
v_a_4940_ = v_a_5002_;
v_log_4941_ = v_a_5003_;
v_action_4942_ = v_action_4968_;
v_wantsRebuild_4943_ = v_wantsRebuild_4969_;
v_trace_4944_ = v_trace_4970_;
v_buildTime_4945_ = v_buildTime_4971_;
goto v___jp_4939_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___boxed(lean_object* v_exe_5005_, lean_object* v___y_5006_, lean_object* v_inputHash_5007_, lean_object* v_pkg_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_){
_start:
{
uint8_t v_exe_boxed_5015_; uint64_t v_inputHash_boxed_5016_; lean_object* v_res_5017_; 
v_exe_boxed_5015_ = lean_unbox(v_exe_5005_);
v_inputHash_boxed_5016_ = lean_unbox_uint64(v_inputHash_5007_);
lean_dec_ref(v_inputHash_5007_);
v_res_5017_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(v_exe_boxed_5015_, v___y_5006_, v_inputHash_boxed_5016_, v_pkg_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_);
lean_dec_ref(v_a_5012_);
lean_dec(v_a_5011_);
lean_dec(v_a_5010_);
lean_dec(v_a_5009_);
return v_res_5017_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(uint8_t v_exe_5018_, uint64_t v_hash_5019_, lean_object* v_a_5020_, lean_object* v_val_5021_, lean_object* v_file_5022_, lean_object* v___x_5023_, uint8_t v_restore_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_){
_start:
{
lean_object* v_a_5033_; lean_object* v___y_5037_; lean_object* v___y_5038_; lean_object* v___y_5039_; uint8_t v___y_5077_; uint8_t v___y_5078_; lean_object* v___y_5079_; lean_object* v___y_5080_; lean_object* v___y_5081_; lean_object* v___y_5082_; lean_object* v___y_5083_; lean_object* v___y_5084_; lean_object* v_a_5098_; lean_object* v_val_5099_; lean_object* v_a_5100_; lean_object* v_a_5154_; lean_object* v___y_5155_; lean_object* v___x_5157_; lean_object* v_a_5158_; 
lean_inc_ref(v_val_5021_);
lean_inc(v_a_5020_);
lean_inc_ref(v___y_5025_);
v___x_5157_ = l_Lake_getArtifactsUsingTrace_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__0(v_exe_5018_, v___y_5025_, v_hash_5019_, v_a_5020_, v_val_5021_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_);
v_a_5158_ = lean_ctor_get(v___x_5157_, 0);
lean_inc(v_a_5158_);
if (lean_obj_tag(v_a_5158_) == 1)
{
lean_object* v_a_5159_; lean_object* v_val_5160_; 
lean_dec_ref(v___y_5025_);
lean_dec_ref(v_val_5021_);
v_a_5159_ = lean_ctor_get(v___x_5157_, 1);
lean_inc(v_a_5159_);
lean_dec_ref(v___x_5157_);
v_val_5160_ = lean_ctor_get(v_a_5158_, 0);
lean_inc(v_val_5160_);
lean_dec_ref_known(v_a_5158_, 1);
v_a_5154_ = v_val_5160_;
v___y_5155_ = v_a_5159_;
goto v___jp_5153_;
}
else
{
lean_object* v_a_5161_; lean_object* v___x_5162_; lean_object* v_a_5163_; 
lean_dec(v_a_5158_);
v_a_5161_ = lean_ctor_get(v___x_5157_, 1);
lean_inc(v_a_5161_);
lean_dec_ref(v___x_5157_);
v___x_5162_ = l___private_Lake_Build_Common_0__Lake_getArtifactsUsingCache_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(v_exe_5018_, v___y_5025_, v_hash_5019_, v_val_5021_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v_a_5161_);
v_a_5163_ = lean_ctor_get(v___x_5162_, 0);
lean_inc(v_a_5163_);
if (lean_obj_tag(v_a_5163_) == 1)
{
lean_object* v_a_5164_; lean_object* v_val_5165_; 
v_a_5164_ = lean_ctor_get(v___x_5162_, 1);
lean_inc(v_a_5164_);
lean_dec_ref(v___x_5162_);
v_val_5165_ = lean_ctor_get(v_a_5163_, 0);
lean_inc(v_val_5165_);
lean_dec_ref_known(v_a_5163_, 1);
v_a_5154_ = v_val_5165_;
v___y_5155_ = v_a_5164_;
goto v___jp_5153_;
}
else
{
lean_object* v_a_5166_; 
lean_dec(v_a_5163_);
lean_dec_ref(v___x_5023_);
lean_dec_ref(v_file_5022_);
lean_dec(v_a_5020_);
v_a_5166_ = lean_ctor_get(v___x_5162_, 1);
lean_inc(v_a_5166_);
lean_dec_ref(v___x_5162_);
v_a_5033_ = v_a_5166_;
goto v___jp_5032_;
}
}
v___jp_5032_:
{
lean_object* v___x_5034_; lean_object* v___x_5035_; 
v___x_5034_ = lean_box(0);
v___x_5035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5035_, 0, v___x_5034_);
lean_ctor_set(v___x_5035_, 1, v_a_5033_);
return v___x_5035_;
}
v___jp_5036_:
{
if (v_restore_5024_ == 0)
{
lean_object* v___x_5040_; 
lean_dec_ref(v___y_5037_);
lean_dec_ref(v_file_5022_);
v___x_5040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5040_, 0, v___y_5038_);
lean_ctor_set(v___x_5040_, 1, v___y_5039_);
return v___x_5040_;
}
else
{
lean_object* v_log_5041_; uint8_t v_action_5042_; uint8_t v_wantsRebuild_5043_; lean_object* v_trace_5044_; lean_object* v_buildTime_5045_; lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5075_; 
lean_dec(v___y_5038_);
v_log_5041_ = lean_ctor_get(v___y_5039_, 0);
v_action_5042_ = lean_ctor_get_uint8(v___y_5039_, sizeof(void*)*3);
v_wantsRebuild_5043_ = lean_ctor_get_uint8(v___y_5039_, sizeof(void*)*3 + 1);
v_trace_5044_ = lean_ctor_get(v___y_5039_, 1);
v_buildTime_5045_ = lean_ctor_get(v___y_5039_, 2);
v_isSharedCheck_5075_ = !lean_is_exclusive(v___y_5039_);
if (v_isSharedCheck_5075_ == 0)
{
v___x_5047_ = v___y_5039_;
v_isShared_5048_ = v_isSharedCheck_5075_;
goto v_resetjp_5046_;
}
else
{
lean_inc(v_buildTime_5045_);
lean_inc(v_trace_5044_);
lean_inc(v_log_5041_);
lean_dec(v___y_5039_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5075_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v___x_5049_; 
v___x_5049_ = l_Lake_restoreArtifact(v_file_5022_, v___y_5037_, v_exe_5018_, v_log_5041_);
if (lean_obj_tag(v___x_5049_) == 0)
{
lean_object* v_a_5050_; lean_object* v_a_5051_; lean_object* v___x_5053_; uint8_t v_isShared_5054_; uint8_t v_isSharedCheck_5062_; 
v_a_5050_ = lean_ctor_get(v___x_5049_, 0);
v_a_5051_ = lean_ctor_get(v___x_5049_, 1);
v_isSharedCheck_5062_ = !lean_is_exclusive(v___x_5049_);
if (v_isSharedCheck_5062_ == 0)
{
v___x_5053_ = v___x_5049_;
v_isShared_5054_ = v_isSharedCheck_5062_;
goto v_resetjp_5052_;
}
else
{
lean_inc(v_a_5051_);
lean_inc(v_a_5050_);
lean_dec(v___x_5049_);
v___x_5053_ = lean_box(0);
v_isShared_5054_ = v_isSharedCheck_5062_;
goto v_resetjp_5052_;
}
v_resetjp_5052_:
{
lean_object* v___x_5056_; 
if (v_isShared_5048_ == 0)
{
lean_ctor_set(v___x_5047_, 0, v_a_5051_);
v___x_5056_ = v___x_5047_;
goto v_reusejp_5055_;
}
else
{
lean_object* v_reuseFailAlloc_5061_; 
v_reuseFailAlloc_5061_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5061_, 0, v_a_5051_);
lean_ctor_set(v_reuseFailAlloc_5061_, 1, v_trace_5044_);
lean_ctor_set(v_reuseFailAlloc_5061_, 2, v_buildTime_5045_);
lean_ctor_set_uint8(v_reuseFailAlloc_5061_, sizeof(void*)*3, v_action_5042_);
lean_ctor_set_uint8(v_reuseFailAlloc_5061_, sizeof(void*)*3 + 1, v_wantsRebuild_5043_);
v___x_5056_ = v_reuseFailAlloc_5061_;
goto v_reusejp_5055_;
}
v_reusejp_5055_:
{
lean_object* v___x_5057_; lean_object* v___x_5059_; 
v___x_5057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5057_, 0, v_a_5050_);
if (v_isShared_5054_ == 0)
{
lean_ctor_set(v___x_5053_, 1, v___x_5056_);
lean_ctor_set(v___x_5053_, 0, v___x_5057_);
v___x_5059_ = v___x_5053_;
goto v_reusejp_5058_;
}
else
{
lean_object* v_reuseFailAlloc_5060_; 
v_reuseFailAlloc_5060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5060_, 0, v___x_5057_);
lean_ctor_set(v_reuseFailAlloc_5060_, 1, v___x_5056_);
v___x_5059_ = v_reuseFailAlloc_5060_;
goto v_reusejp_5058_;
}
v_reusejp_5058_:
{
return v___x_5059_;
}
}
}
}
else
{
lean_object* v_a_5063_; lean_object* v_a_5064_; lean_object* v___x_5066_; uint8_t v_isShared_5067_; uint8_t v_isSharedCheck_5074_; 
v_a_5063_ = lean_ctor_get(v___x_5049_, 0);
v_a_5064_ = lean_ctor_get(v___x_5049_, 1);
v_isSharedCheck_5074_ = !lean_is_exclusive(v___x_5049_);
if (v_isSharedCheck_5074_ == 0)
{
v___x_5066_ = v___x_5049_;
v_isShared_5067_ = v_isSharedCheck_5074_;
goto v_resetjp_5065_;
}
else
{
lean_inc(v_a_5064_);
lean_inc(v_a_5063_);
lean_dec(v___x_5049_);
v___x_5066_ = lean_box(0);
v_isShared_5067_ = v_isSharedCheck_5074_;
goto v_resetjp_5065_;
}
v_resetjp_5065_:
{
lean_object* v___x_5069_; 
if (v_isShared_5048_ == 0)
{
lean_ctor_set(v___x_5047_, 0, v_a_5064_);
v___x_5069_ = v___x_5047_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5073_; 
v_reuseFailAlloc_5073_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5073_, 0, v_a_5064_);
lean_ctor_set(v_reuseFailAlloc_5073_, 1, v_trace_5044_);
lean_ctor_set(v_reuseFailAlloc_5073_, 2, v_buildTime_5045_);
lean_ctor_set_uint8(v_reuseFailAlloc_5073_, sizeof(void*)*3, v_action_5042_);
lean_ctor_set_uint8(v_reuseFailAlloc_5073_, sizeof(void*)*3 + 1, v_wantsRebuild_5043_);
v___x_5069_ = v_reuseFailAlloc_5073_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
lean_object* v___x_5071_; 
if (v_isShared_5067_ == 0)
{
lean_ctor_set(v___x_5066_, 1, v___x_5069_);
v___x_5071_ = v___x_5066_;
goto v_reusejp_5070_;
}
else
{
lean_object* v_reuseFailAlloc_5072_; 
v_reuseFailAlloc_5072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5072_, 0, v_a_5063_);
lean_ctor_set(v_reuseFailAlloc_5072_, 1, v___x_5069_);
v___x_5071_ = v_reuseFailAlloc_5072_;
goto v_reusejp_5070_;
}
v_reusejp_5070_:
{
return v___x_5071_;
}
}
}
}
}
}
}
v___jp_5076_:
{
lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; 
v___x_5085_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5085_, 0, v___y_5084_);
v___x_5086_ = l_Lake_BuildMetadata_ofFetch(v_hash_5019_, v___x_5085_);
v___x_5087_ = l_Lake_BuildMetadata_writeFile(v___x_5023_, v___x_5086_);
if (lean_obj_tag(v___x_5087_) == 0)
{
lean_object* v___x_5088_; 
lean_dec_ref_known(v___x_5087_, 1);
v___x_5088_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5088_, 0, v___y_5079_);
lean_ctor_set(v___x_5088_, 1, v___y_5081_);
lean_ctor_set(v___x_5088_, 2, v___y_5083_);
lean_ctor_set_uint8(v___x_5088_, sizeof(void*)*3, v___y_5078_);
lean_ctor_set_uint8(v___x_5088_, sizeof(void*)*3 + 1, v___y_5077_);
v___y_5037_ = v___y_5080_;
v___y_5038_ = v___y_5082_;
v___y_5039_ = v___x_5088_;
goto v___jp_5036_;
}
else
{
lean_object* v_a_5089_; lean_object* v___x_5090_; uint8_t v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; 
lean_dec(v___y_5082_);
lean_dec_ref(v___y_5080_);
lean_dec_ref(v_file_5022_);
v_a_5089_ = lean_ctor_get(v___x_5087_, 0);
lean_inc(v_a_5089_);
lean_dec_ref_known(v___x_5087_, 1);
v___x_5090_ = lean_io_error_to_string(v_a_5089_);
v___x_5091_ = 3;
v___x_5092_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5092_, 0, v___x_5090_);
lean_ctor_set_uint8(v___x_5092_, sizeof(void*)*1, v___x_5091_);
v___x_5093_ = lean_array_get_size(v___y_5079_);
v___x_5094_ = lean_array_push(v___y_5079_, v___x_5092_);
v___x_5095_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5095_, 0, v___x_5094_);
lean_ctor_set(v___x_5095_, 1, v___y_5081_);
lean_ctor_set(v___x_5095_, 2, v___y_5083_);
lean_ctor_set_uint8(v___x_5095_, sizeof(void*)*3, v___y_5078_);
lean_ctor_set_uint8(v___x_5095_, sizeof(void*)*3 + 1, v___y_5077_);
v___x_5096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5096_, 0, v___x_5093_);
lean_ctor_set(v___x_5096_, 1, v___x_5095_);
return v___x_5096_;
}
}
v___jp_5097_:
{
lean_object* v___x_5101_; 
v___x_5101_ = l_Lake_SavedTrace_replayCachedIfUpToDate___redArg(v_hash_5019_, v_a_5020_, v_a_5100_);
lean_dec(v_a_5020_);
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
v___x_5116_ = l_Lake_removeFileIfExists(v_file_5022_);
if (lean_obj_tag(v___x_5116_) == 0)
{
lean_object* v_descr_5117_; uint64_t v_hash_5118_; lean_object* v_ext_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; uint8_t v___x_5122_; 
lean_dec_ref_known(v___x_5116_, 1);
lean_del_object(v___x_5114_);
lean_del_object(v___x_5106_);
v_descr_5117_ = lean_ctor_get(v_val_5099_, 0);
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
v___y_5077_ = v_wantsRebuild_5110_;
v___y_5078_ = v_action_5109_;
v___y_5079_ = v_log_5108_;
v___y_5080_ = v_val_5099_;
v___y_5081_ = v_trace_5111_;
v___y_5082_ = v_a_5098_;
v___y_5083_ = v_buildTime_5112_;
v___y_5084_ = v___x_5126_;
goto v___jp_5076_;
}
else
{
lean_object* v___x_5127_; 
v___x_5127_ = l_Lake_lowerHexUInt64(v_hash_5118_);
v___y_5077_ = v_wantsRebuild_5110_;
v___y_5078_ = v_action_5109_;
v___y_5079_ = v_log_5108_;
v___y_5080_ = v_val_5099_;
v___y_5081_ = v_trace_5111_;
v___y_5082_ = v_a_5098_;
v___y_5083_ = v_buildTime_5112_;
v___y_5084_ = v___x_5127_;
goto v___jp_5076_;
}
}
else
{
lean_object* v_a_5128_; lean_object* v___x_5129_; uint8_t v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5135_; 
lean_dec_ref(v_val_5099_);
lean_dec(v_a_5098_);
lean_dec_ref(v___x_5023_);
lean_dec_ref(v_file_5022_);
v_a_5128_ = lean_ctor_get(v___x_5116_, 0);
lean_inc(v_a_5128_);
lean_dec_ref_known(v___x_5116_, 1);
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
lean_dec_ref(v___x_5023_);
v_a_5143_ = lean_ctor_get(v___x_5101_, 1);
lean_inc(v_a_5143_);
lean_dec_ref_known(v___x_5101_, 2);
v___y_5037_ = v_val_5099_;
v___y_5038_ = v_a_5098_;
v___y_5039_ = v_a_5143_;
goto v___jp_5036_;
}
}
else
{
lean_object* v_a_5144_; lean_object* v_a_5145_; lean_object* v___x_5147_; uint8_t v_isShared_5148_; uint8_t v_isSharedCheck_5152_; 
lean_dec_ref(v_val_5099_);
lean_dec(v_a_5098_);
lean_dec_ref(v___x_5023_);
lean_dec_ref(v_file_5022_);
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
v___jp_5153_:
{
lean_object* v___x_5156_; 
lean_inc_ref(v_a_5154_);
v___x_5156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5156_, 0, v_a_5154_);
v_a_5098_ = v___x_5156_;
v_val_5099_ = v_a_5154_;
v_a_5100_ = v___y_5155_;
goto v___jp_5097_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object* v_exe_5167_, lean_object* v_hash_5168_, lean_object* v_a_5169_, lean_object* v_val_5170_, lean_object* v_file_5171_, lean_object* v___x_5172_, lean_object* v_restore_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_){
_start:
{
uint8_t v_exe_boxed_5181_; uint64_t v_hash_boxed_5182_; uint8_t v_restore_boxed_5183_; lean_object* v_res_5184_; 
v_exe_boxed_5181_ = lean_unbox(v_exe_5167_);
v_hash_boxed_5182_ = lean_unbox_uint64(v_hash_5168_);
lean_dec_ref(v_hash_5168_);
v_restore_boxed_5183_ = lean_unbox(v_restore_5173_);
v_res_5184_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_boxed_5181_, v_hash_boxed_5182_, v_a_5169_, v_val_5170_, v_file_5171_, v___x_5172_, v_restore_boxed_5183_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_5179_);
lean_dec_ref(v___y_5178_);
lean_dec(v___y_5177_);
lean_dec(v___y_5176_);
lean_dec(v___y_5175_);
return v_res_5184_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1(uint8_t v_a_5185_, lean_object* v_file_5186_, lean_object* v_ext_5187_, uint8_t v_text_5188_, uint8_t v_exe_5189_, uint8_t v___y_5190_, lean_object* v_val_5191_, uint64_t v_hash_5192_, uint8_t v_a_5193_, lean_object* v_____r_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_){
_start:
{
lean_object* v___x_5202_; lean_object* v___x_5203_; uint8_t v___x_5204_; 
v___x_5202_ = l_Lake_OutputStatus_ctorIdx(v_a_5185_);
v___x_5203_ = lean_obj_once(&l_Lake_OutputStatus_isCacheable___closed__0, &l_Lake_OutputStatus_isCacheable___closed__0_once, _init_l_Lake_OutputStatus_isCacheable___closed__0);
v___x_5204_ = lean_nat_dec_eq(v___x_5202_, v___x_5203_);
lean_dec(v___x_5202_);
if (v___x_5204_ == 0)
{
lean_object* v_toContext_5205_; lean_object* v_log_5206_; uint8_t v_action_5207_; uint8_t v_wantsRebuild_5208_; lean_object* v_trace_5209_; lean_object* v_buildTime_5210_; lean_object* v_lakeCache_5211_; lean_object* v___x_5212_; 
v_toContext_5205_ = lean_ctor_get(v___y_5199_, 1);
v_log_5206_ = lean_ctor_get(v___y_5200_, 0);
v_action_5207_ = lean_ctor_get_uint8(v___y_5200_, sizeof(void*)*3);
v_wantsRebuild_5208_ = lean_ctor_get_uint8(v___y_5200_, sizeof(void*)*3 + 1);
v_trace_5209_ = lean_ctor_get(v___y_5200_, 1);
v_buildTime_5210_ = lean_ctor_get(v___y_5200_, 2);
v_lakeCache_5211_ = lean_ctor_get(v_toContext_5205_, 2);
lean_inc_ref(v_lakeCache_5211_);
v___x_5212_ = l_Lake_Cache_saveArtifact(v_lakeCache_5211_, v_file_5186_, v_ext_5187_, v_text_5188_, v_exe_5189_, v___y_5190_);
if (lean_obj_tag(v___x_5212_) == 0)
{
lean_object* v_a_5213_; lean_object* v___x_5215_; uint8_t v_isShared_5216_; uint8_t v_isSharedCheck_5254_; 
v_a_5213_ = lean_ctor_get(v___x_5212_, 0);
v_isSharedCheck_5254_ = !lean_is_exclusive(v___x_5212_);
if (v_isSharedCheck_5254_ == 0)
{
v___x_5215_ = v___x_5212_;
v_isShared_5216_ = v_isSharedCheck_5254_;
goto v_resetjp_5214_;
}
else
{
lean_inc(v_a_5213_);
lean_dec(v___x_5212_);
v___x_5215_ = lean_box(0);
v_isShared_5216_ = v_isSharedCheck_5254_;
goto v_resetjp_5214_;
}
v_resetjp_5214_:
{
lean_object* v_descr_5217_; uint64_t v_hash_5218_; lean_object* v_ext_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___y_5223_; lean_object* v___x_5246_; lean_object* v___x_5247_; uint8_t v___x_5248_; 
v_descr_5217_ = lean_ctor_get(v_a_5213_, 0);
v_hash_5218_ = lean_ctor_get_uint64(v_descr_5217_, sizeof(void*)*1);
v_ext_5219_ = lean_ctor_get(v_descr_5217_, 0);
v___x_5220_ = l_Lake_Package_cacheScope(v_val_5191_);
v___x_5221_ = lean_box(0);
v___x_5246_ = lean_string_utf8_byte_size(v_ext_5219_);
v___x_5247_ = lean_unsigned_to_nat(0u);
v___x_5248_ = lean_nat_dec_eq(v___x_5246_, v___x_5247_);
if (v___x_5248_ == 0)
{
lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; 
v___x_5249_ = l_Lake_lowerHexUInt64(v_hash_5218_);
v___x_5250_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5251_ = lean_string_append(v___x_5249_, v___x_5250_);
v___x_5252_ = lean_string_append(v___x_5251_, v_ext_5219_);
v___y_5223_ = v___x_5252_;
goto v___jp_5222_;
}
else
{
lean_object* v___x_5253_; 
v___x_5253_ = l_Lake_lowerHexUInt64(v_hash_5218_);
v___y_5223_ = v___x_5253_;
goto v___jp_5222_;
}
v___jp_5222_:
{
lean_object* v___x_5225_; 
if (v_isShared_5216_ == 0)
{
lean_ctor_set_tag(v___x_5215_, 3);
lean_ctor_set(v___x_5215_, 0, v___y_5223_);
v___x_5225_ = v___x_5215_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5245_; 
v_reuseFailAlloc_5245_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5245_, 0, v___y_5223_);
v___x_5225_ = v_reuseFailAlloc_5245_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
lean_object* v___x_5226_; 
lean_inc_ref(v_lakeCache_5211_);
v___x_5226_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_lakeCache_5211_, v___x_5220_, v_hash_5192_, v___x_5225_, v___x_5221_, v___x_5221_, v_a_5193_);
if (lean_obj_tag(v___x_5226_) == 0)
{
lean_object* v___x_5227_; 
lean_dec_ref_known(v___x_5226_, 1);
v___x_5227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5227_, 0, v_a_5213_);
lean_ctor_set(v___x_5227_, 1, v___y_5200_);
return v___x_5227_;
}
else
{
lean_object* v___x_5229_; uint8_t v_isShared_5230_; uint8_t v_isSharedCheck_5241_; 
lean_inc(v_buildTime_5210_);
lean_inc_ref(v_trace_5209_);
lean_inc_ref(v_log_5206_);
lean_dec(v_a_5213_);
v_isSharedCheck_5241_ = !lean_is_exclusive(v___y_5200_);
if (v_isSharedCheck_5241_ == 0)
{
lean_object* v_unused_5242_; lean_object* v_unused_5243_; lean_object* v_unused_5244_; 
v_unused_5242_ = lean_ctor_get(v___y_5200_, 2);
lean_dec(v_unused_5242_);
v_unused_5243_ = lean_ctor_get(v___y_5200_, 1);
lean_dec(v_unused_5243_);
v_unused_5244_ = lean_ctor_get(v___y_5200_, 0);
lean_dec(v_unused_5244_);
v___x_5229_ = v___y_5200_;
v_isShared_5230_ = v_isSharedCheck_5241_;
goto v_resetjp_5228_;
}
else
{
lean_dec(v___y_5200_);
v___x_5229_ = lean_box(0);
v_isShared_5230_ = v_isSharedCheck_5241_;
goto v_resetjp_5228_;
}
v_resetjp_5228_:
{
lean_object* v_a_5231_; lean_object* v___x_5232_; uint8_t v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5238_; 
v_a_5231_ = lean_ctor_get(v___x_5226_, 0);
lean_inc(v_a_5231_);
lean_dec_ref_known(v___x_5226_, 1);
v___x_5232_ = lean_io_error_to_string(v_a_5231_);
v___x_5233_ = 3;
v___x_5234_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5234_, 0, v___x_5232_);
lean_ctor_set_uint8(v___x_5234_, sizeof(void*)*1, v___x_5233_);
v___x_5235_ = lean_array_get_size(v_log_5206_);
v___x_5236_ = lean_array_push(v_log_5206_, v___x_5234_);
if (v_isShared_5230_ == 0)
{
lean_ctor_set(v___x_5229_, 0, v___x_5236_);
v___x_5238_ = v___x_5229_;
goto v_reusejp_5237_;
}
else
{
lean_object* v_reuseFailAlloc_5240_; 
v_reuseFailAlloc_5240_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5240_, 0, v___x_5236_);
lean_ctor_set(v_reuseFailAlloc_5240_, 1, v_trace_5209_);
lean_ctor_set(v_reuseFailAlloc_5240_, 2, v_buildTime_5210_);
lean_ctor_set_uint8(v_reuseFailAlloc_5240_, sizeof(void*)*3, v_action_5207_);
lean_ctor_set_uint8(v_reuseFailAlloc_5240_, sizeof(void*)*3 + 1, v_wantsRebuild_5208_);
v___x_5238_ = v_reuseFailAlloc_5240_;
goto v_reusejp_5237_;
}
v_reusejp_5237_:
{
lean_object* v___x_5239_; 
v___x_5239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5239_, 0, v___x_5235_);
lean_ctor_set(v___x_5239_, 1, v___x_5238_);
return v___x_5239_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5256_; uint8_t v_isShared_5257_; uint8_t v_isSharedCheck_5268_; 
lean_inc(v_buildTime_5210_);
lean_inc_ref(v_trace_5209_);
lean_inc_ref(v_log_5206_);
lean_dec_ref(v_val_5191_);
v_isSharedCheck_5268_ = !lean_is_exclusive(v___y_5200_);
if (v_isSharedCheck_5268_ == 0)
{
lean_object* v_unused_5269_; lean_object* v_unused_5270_; lean_object* v_unused_5271_; 
v_unused_5269_ = lean_ctor_get(v___y_5200_, 2);
lean_dec(v_unused_5269_);
v_unused_5270_ = lean_ctor_get(v___y_5200_, 1);
lean_dec(v_unused_5270_);
v_unused_5271_ = lean_ctor_get(v___y_5200_, 0);
lean_dec(v_unused_5271_);
v___x_5256_ = v___y_5200_;
v_isShared_5257_ = v_isSharedCheck_5268_;
goto v_resetjp_5255_;
}
else
{
lean_dec(v___y_5200_);
v___x_5256_ = lean_box(0);
v_isShared_5257_ = v_isSharedCheck_5268_;
goto v_resetjp_5255_;
}
v_resetjp_5255_:
{
lean_object* v_a_5258_; lean_object* v___x_5259_; uint8_t v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5265_; 
v_a_5258_ = lean_ctor_get(v___x_5212_, 0);
lean_inc(v_a_5258_);
lean_dec_ref_known(v___x_5212_, 1);
v___x_5259_ = lean_io_error_to_string(v_a_5258_);
v___x_5260_ = 3;
v___x_5261_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5261_, 0, v___x_5259_);
lean_ctor_set_uint8(v___x_5261_, sizeof(void*)*1, v___x_5260_);
v___x_5262_ = lean_array_get_size(v_log_5206_);
v___x_5263_ = lean_array_push(v_log_5206_, v___x_5261_);
if (v_isShared_5257_ == 0)
{
lean_ctor_set(v___x_5256_, 0, v___x_5263_);
v___x_5265_ = v___x_5256_;
goto v_reusejp_5264_;
}
else
{
lean_object* v_reuseFailAlloc_5267_; 
v_reuseFailAlloc_5267_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5267_, 0, v___x_5263_);
lean_ctor_set(v_reuseFailAlloc_5267_, 1, v_trace_5209_);
lean_ctor_set(v_reuseFailAlloc_5267_, 2, v_buildTime_5210_);
lean_ctor_set_uint8(v_reuseFailAlloc_5267_, sizeof(void*)*3, v_action_5207_);
lean_ctor_set_uint8(v_reuseFailAlloc_5267_, sizeof(void*)*3 + 1, v_wantsRebuild_5208_);
v___x_5265_ = v_reuseFailAlloc_5267_;
goto v_reusejp_5264_;
}
v_reusejp_5264_:
{
lean_object* v___x_5266_; 
v___x_5266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5266_, 0, v___x_5262_);
lean_ctor_set(v___x_5266_, 1, v___x_5265_);
return v___x_5266_;
}
}
}
}
else
{
lean_object* v___x_5272_; 
lean_dec_ref(v_val_5191_);
v___x_5272_ = l_Lake_computeArtifact___redArg(v_file_5186_, v_ext_5187_, v_text_5188_, v___y_5199_, v___y_5200_);
return v___x_5272_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___boxed(lean_object** _args){
lean_object* v_a_5273_ = _args[0];
lean_object* v_file_5274_ = _args[1];
lean_object* v_ext_5275_ = _args[2];
lean_object* v_text_5276_ = _args[3];
lean_object* v_exe_5277_ = _args[4];
lean_object* v___y_5278_ = _args[5];
lean_object* v_val_5279_ = _args[6];
lean_object* v_hash_5280_ = _args[7];
lean_object* v_a_5281_ = _args[8];
lean_object* v_____r_5282_ = _args[9];
lean_object* v___y_5283_ = _args[10];
lean_object* v___y_5284_ = _args[11];
lean_object* v___y_5285_ = _args[12];
lean_object* v___y_5286_ = _args[13];
lean_object* v___y_5287_ = _args[14];
lean_object* v___y_5288_ = _args[15];
lean_object* v___y_5289_ = _args[16];
_start:
{
uint8_t v_a_287934__boxed_5290_; uint8_t v_text_boxed_5291_; uint8_t v_exe_boxed_5292_; uint8_t v___y_287935__boxed_5293_; uint64_t v_hash_boxed_5294_; uint8_t v_a_287937__boxed_5295_; lean_object* v_res_5296_; 
v_a_287934__boxed_5290_ = lean_unbox(v_a_5273_);
v_text_boxed_5291_ = lean_unbox(v_text_5276_);
v_exe_boxed_5292_ = lean_unbox(v_exe_5277_);
v___y_287935__boxed_5293_ = lean_unbox(v___y_5278_);
v_hash_boxed_5294_ = lean_unbox_uint64(v_hash_5280_);
lean_dec_ref(v_hash_5280_);
v_a_287937__boxed_5295_ = lean_unbox(v_a_5281_);
v_res_5296_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v_a_287934__boxed_5290_, v_file_5274_, v_ext_5275_, v_text_boxed_5291_, v_exe_boxed_5292_, v___y_287935__boxed_5293_, v_val_5279_, v_hash_boxed_5294_, v_a_287937__boxed_5295_, v_____r_5282_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_);
lean_dec_ref(v___y_5287_);
lean_dec(v___y_5286_);
lean_dec(v___y_5285_);
lean_dec(v___y_5284_);
lean_dec_ref(v___y_5283_);
return v_res_5296_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object* v_file_5297_, lean_object* v_build_5298_, uint8_t v_text_5299_, lean_object* v_ext_5300_, uint8_t v_restore_5301_, uint8_t v_exe_5302_, uint8_t v_platformIndependent_5303_, lean_object* v_a_5304_, lean_object* v_a_5305_, lean_object* v_a_5306_, lean_object* v_a_5307_, lean_object* v_a_5308_, lean_object* v_a_5309_){
_start:
{
lean_object* v_log_5311_; uint8_t v_action_5312_; uint8_t v_wantsRebuild_5313_; lean_object* v_trace_5314_; lean_object* v_buildTime_5315_; lean_object* v___x_5317_; uint8_t v_isShared_5318_; uint8_t v_isSharedCheck_5579_; 
v_log_5311_ = lean_ctor_get(v_a_5309_, 0);
v_action_5312_ = lean_ctor_get_uint8(v_a_5309_, sizeof(void*)*3);
v_wantsRebuild_5313_ = lean_ctor_get_uint8(v_a_5309_, sizeof(void*)*3 + 1);
v_trace_5314_ = lean_ctor_get(v_a_5309_, 1);
v_buildTime_5315_ = lean_ctor_get(v_a_5309_, 2);
v_isSharedCheck_5579_ = !lean_is_exclusive(v_a_5309_);
if (v_isSharedCheck_5579_ == 0)
{
v___x_5317_ = v_a_5309_;
v_isShared_5318_ = v_isSharedCheck_5579_;
goto v_resetjp_5316_;
}
else
{
lean_inc(v_buildTime_5315_);
lean_inc(v_trace_5314_);
lean_inc(v_log_5311_);
lean_dec(v_a_5309_);
v___x_5317_ = lean_box(0);
v_isShared_5318_ = v_isSharedCheck_5579_;
goto v_resetjp_5316_;
}
v_resetjp_5316_:
{
lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v_art_5322_; lean_object* v___y_5323_; lean_object* v___y_5339_; lean_object* v_log_5340_; uint8_t v_action_5341_; uint8_t v_wantsRebuild_5342_; lean_object* v_buildTime_5343_; lean_object* v___x_5349_; 
v___x_5319_ = ((lean_object*)(l_Lake_buildFileUnlessUpToDate_x27___closed__0));
lean_inc_ref(v_file_5297_);
v___x_5320_ = lean_string_append(v_file_5297_, v___x_5319_);
lean_inc_ref(v___x_5320_);
v___x_5349_ = l_Lake_readTraceFile(v___x_5320_, v_log_5311_);
if (lean_obj_tag(v___x_5349_) == 0)
{
if (lean_obj_tag(v_a_5305_) == 1)
{
lean_object* v_a_5350_; lean_object* v_a_5351_; lean_object* v_val_5352_; uint64_t v_hash_5353_; lean_object* v_mtime_5354_; lean_object* v___y_5356_; lean_object* v___y_5357_; lean_object* v___y_5358_; lean_object* v___y_5359_; lean_object* v___y_5360_; uint8_t v___y_5361_; uint8_t v___y_5362_; lean_object* v___y_5363_; lean_object* v___y_5364_; lean_object* v_wsIdx_5368_; lean_object* v_config_5369_; lean_object* v_a_5371_; lean_object* v_a_5372_; lean_object* v___y_5402_; lean_object* v_enableArtifactCache_x3f_5405_; lean_object* v_restoreAllArtifacts_x3f_5406_; uint8_t v___y_5408_; lean_object* v___y_5409_; uint8_t v___y_5410_; uint8_t v___y_5450_; uint8_t v___y_5451_; uint8_t v_a_5452_; lean_object* v_a_5453_; uint8_t v___y_5455_; lean_object* v_a_5456_; uint8_t v___y_5473_; uint8_t v_a_5474_; lean_object* v_a_5475_; lean_object* v_a_5478_; uint8_t v_a_5511_; lean_object* v_a_5512_; lean_object* v___x_5528_; 
v_a_5350_ = lean_ctor_get(v___x_5349_, 0);
lean_inc(v_a_5350_);
v_a_5351_ = lean_ctor_get(v___x_5349_, 1);
lean_inc(v_a_5351_);
lean_dec_ref_known(v___x_5349_, 2);
v_val_5352_ = lean_ctor_get(v_a_5305_, 0);
v_hash_5353_ = lean_ctor_get_uint64(v_trace_5314_, sizeof(void*)*3);
v_mtime_5354_ = lean_ctor_get(v_trace_5314_, 2);
v_wsIdx_5368_ = lean_ctor_get(v_val_5352_, 0);
v_config_5369_ = lean_ctor_get(v_val_5352_, 6);
v_enableArtifactCache_x3f_5405_ = lean_ctor_get(v_config_5369_, 24);
v_restoreAllArtifacts_x3f_5406_ = lean_ctor_get(v_config_5369_, 25);
lean_inc_ref(v_trace_5314_);
v___x_5528_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5528_, 0, v_a_5351_);
lean_ctor_set(v___x_5528_, 1, v_trace_5314_);
lean_ctor_set(v___x_5528_, 2, v_buildTime_5315_);
lean_ctor_set_uint8(v___x_5528_, sizeof(void*)*3, v_action_5312_);
lean_ctor_set_uint8(v___x_5528_, sizeof(void*)*3 + 1, v_wantsRebuild_5313_);
if (lean_obj_tag(v_enableArtifactCache_x3f_5405_) == 0)
{
lean_object* v_toContext_5529_; lean_object* v_lakeEnv_5530_; lean_object* v_enableArtifactCache_x3f_5531_; 
v_toContext_5529_ = lean_ctor_get(v_a_5308_, 1);
v_lakeEnv_5530_ = lean_ctor_get(v_toContext_5529_, 0);
v_enableArtifactCache_x3f_5531_ = lean_ctor_get(v_lakeEnv_5530_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_5531_) == 0)
{
lean_object* v_packages_5532_; lean_object* v___x_5533_; lean_object* v___x_5534_; lean_object* v_config_5535_; lean_object* v_enableArtifactCache_x3f_5536_; 
v_packages_5532_ = lean_ctor_get(v_toContext_5529_, 4);
v___x_5533_ = lean_unsigned_to_nat(0u);
v___x_5534_ = lean_array_fget_borrowed(v_packages_5532_, v___x_5533_);
v_config_5535_ = lean_ctor_get(v___x_5534_, 6);
v_enableArtifactCache_x3f_5536_ = lean_ctor_get(v_config_5535_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_5536_) == 0)
{
v_a_5478_ = v___x_5528_;
goto v___jp_5477_;
}
else
{
lean_object* v_val_5537_; uint8_t v___x_5538_; 
v_val_5537_ = lean_ctor_get(v_enableArtifactCache_x3f_5536_, 0);
v___x_5538_ = lean_unbox(v_val_5537_);
v_a_5511_ = v___x_5538_;
v_a_5512_ = v___x_5528_;
goto v___jp_5510_;
}
}
else
{
lean_object* v_val_5539_; uint8_t v___x_5540_; 
v_val_5539_ = lean_ctor_get(v_enableArtifactCache_x3f_5531_, 0);
v___x_5540_ = lean_unbox(v_val_5539_);
v_a_5511_ = v___x_5540_;
v_a_5512_ = v___x_5528_;
goto v___jp_5510_;
}
}
else
{
lean_object* v_val_5541_; uint8_t v___x_5542_; 
v_val_5541_ = lean_ctor_get(v_enableArtifactCache_x3f_5405_, 0);
v___x_5542_ = lean_unbox(v_val_5541_);
v_a_5511_ = v___x_5542_;
v_a_5512_ = v___x_5528_;
goto v___jp_5510_;
}
v___jp_5355_:
{
lean_object* v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; 
lean_dec_ref(v___y_5360_);
v___x_5365_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5365_, 0, v___y_5364_);
v___x_5366_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_hash_5353_, v___x_5365_, v___y_5363_, v_platformIndependent_5303_);
v___x_5367_ = lean_st_ref_put(v___y_5359_, v___x_5366_);
v___y_5339_ = v___y_5357_;
v_log_5340_ = v___y_5358_;
v_action_5341_ = v___y_5362_;
v_wantsRebuild_5342_ = v___y_5361_;
v_buildTime_5343_ = v___y_5356_;
goto v___jp_5338_;
}
v___jp_5370_:
{
lean_object* v___x_5373_; uint8_t v___x_5374_; 
v___x_5373_ = lean_unsigned_to_nat(0u);
v___x_5374_ = lean_nat_dec_eq(v_wsIdx_5368_, v___x_5373_);
if (v___x_5374_ == 0)
{
lean_object* v_log_5375_; uint8_t v_action_5376_; uint8_t v_wantsRebuild_5377_; lean_object* v_buildTime_5378_; 
v_log_5375_ = lean_ctor_get(v_a_5372_, 0);
lean_inc_ref(v_log_5375_);
v_action_5376_ = lean_ctor_get_uint8(v_a_5372_, sizeof(void*)*3);
v_wantsRebuild_5377_ = lean_ctor_get_uint8(v_a_5372_, sizeof(void*)*3 + 1);
v_buildTime_5378_ = lean_ctor_get(v_a_5372_, 2);
lean_inc(v_buildTime_5378_);
lean_dec_ref(v_a_5372_);
v___y_5339_ = v_a_5371_;
v_log_5340_ = v_log_5375_;
v_action_5341_ = v_action_5376_;
v_wantsRebuild_5342_ = v_wantsRebuild_5377_;
v_buildTime_5343_ = v_buildTime_5378_;
goto v___jp_5338_;
}
else
{
lean_object* v_outputsRef_x3f_5379_; 
v_outputsRef_x3f_5379_ = lean_ctor_get(v_a_5308_, 5);
if (lean_obj_tag(v_outputsRef_x3f_5379_) == 1)
{
lean_object* v_log_5380_; uint8_t v_action_5381_; uint8_t v_wantsRebuild_5382_; lean_object* v_trace_5383_; lean_object* v_buildTime_5384_; lean_object* v_val_5385_; lean_object* v___x_5386_; lean_object* v_descr_5387_; uint64_t v_hash_5388_; lean_object* v_ext_5389_; lean_object* v___x_5390_; uint8_t v___x_5391_; 
v_log_5380_ = lean_ctor_get(v_a_5372_, 0);
lean_inc_ref(v_log_5380_);
v_action_5381_ = lean_ctor_get_uint8(v_a_5372_, sizeof(void*)*3);
v_wantsRebuild_5382_ = lean_ctor_get_uint8(v_a_5372_, sizeof(void*)*3 + 1);
v_trace_5383_ = lean_ctor_get(v_a_5372_, 1);
lean_inc_ref(v_trace_5383_);
v_buildTime_5384_ = lean_ctor_get(v_a_5372_, 2);
lean_inc(v_buildTime_5384_);
lean_dec_ref(v_a_5372_);
v_val_5385_ = lean_ctor_get(v_outputsRef_x3f_5379_, 0);
v___x_5386_ = lean_st_ref_take(v_val_5385_);
v_descr_5387_ = lean_ctor_get(v_a_5371_, 0);
v_hash_5388_ = lean_ctor_get_uint64(v_descr_5387_, sizeof(void*)*1);
v_ext_5389_ = lean_ctor_get(v_descr_5387_, 0);
v___x_5390_ = lean_string_utf8_byte_size(v_ext_5389_);
v___x_5391_ = lean_nat_dec_eq(v___x_5390_, v___x_5373_);
if (v___x_5391_ == 0)
{
lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; 
v___x_5392_ = l_Lake_lowerHexUInt64(v_hash_5388_);
v___x_5393_ = ((lean_object*)(l_Lake_instToOutputJsonArtifact___lam__0___closed__0));
v___x_5394_ = lean_string_append(v___x_5392_, v___x_5393_);
v___x_5395_ = lean_string_append(v___x_5394_, v_ext_5389_);
v___y_5356_ = v_buildTime_5384_;
v___y_5357_ = v_a_5371_;
v___y_5358_ = v_log_5380_;
v___y_5359_ = v_val_5385_;
v___y_5360_ = v_trace_5383_;
v___y_5361_ = v_wantsRebuild_5382_;
v___y_5362_ = v_action_5381_;
v___y_5363_ = v___x_5386_;
v___y_5364_ = v___x_5395_;
goto v___jp_5355_;
}
else
{
lean_object* v___x_5396_; 
v___x_5396_ = l_Lake_lowerHexUInt64(v_hash_5388_);
v___y_5356_ = v_buildTime_5384_;
v___y_5357_ = v_a_5371_;
v___y_5358_ = v_log_5380_;
v___y_5359_ = v_val_5385_;
v___y_5360_ = v_trace_5383_;
v___y_5361_ = v_wantsRebuild_5382_;
v___y_5362_ = v_action_5381_;
v___y_5363_ = v___x_5386_;
v___y_5364_ = v___x_5396_;
goto v___jp_5355_;
}
}
else
{
lean_object* v_log_5397_; uint8_t v_action_5398_; uint8_t v_wantsRebuild_5399_; lean_object* v_buildTime_5400_; 
v_log_5397_ = lean_ctor_get(v_a_5372_, 0);
lean_inc_ref(v_log_5397_);
v_action_5398_ = lean_ctor_get_uint8(v_a_5372_, sizeof(void*)*3);
v_wantsRebuild_5399_ = lean_ctor_get_uint8(v_a_5372_, sizeof(void*)*3 + 1);
v_buildTime_5400_ = lean_ctor_get(v_a_5372_, 2);
lean_inc(v_buildTime_5400_);
lean_dec_ref(v_a_5372_);
v___y_5339_ = v_a_5371_;
v_log_5340_ = v_log_5397_;
v_action_5341_ = v_action_5398_;
v_wantsRebuild_5342_ = v_wantsRebuild_5399_;
v_buildTime_5343_ = v_buildTime_5400_;
goto v___jp_5338_;
}
}
}
v___jp_5401_:
{
if (lean_obj_tag(v___y_5402_) == 0)
{
lean_object* v_a_5403_; lean_object* v_a_5404_; 
v_a_5403_ = lean_ctor_get(v___y_5402_, 0);
lean_inc(v_a_5403_);
v_a_5404_ = lean_ctor_get(v___y_5402_, 1);
lean_inc(v_a_5404_);
lean_dec_ref_known(v___y_5402_, 2);
v_a_5371_ = v_a_5403_;
v_a_5372_ = v_a_5404_;
goto v___jp_5370_;
}
else
{
lean_dec_ref(v___x_5320_);
lean_del_object(v___x_5317_);
return v___y_5402_;
}
}
v___jp_5407_:
{
lean_object* v___x_5411_; 
lean_inc_ref(v_a_5304_);
lean_inc_ref(v___x_5320_);
lean_inc_ref(v_file_5297_);
lean_inc(v_val_5352_);
lean_inc(v_a_5350_);
v___x_5411_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_5302_, v_hash_5353_, v_a_5350_, v_val_5352_, v_file_5297_, v___x_5320_, v___y_5410_, v_a_5304_, v_a_5305_, v_a_5306_, v_a_5307_, v_a_5308_, v___y_5409_);
if (lean_obj_tag(v___x_5411_) == 0)
{
lean_object* v_a_5412_; 
v_a_5412_ = lean_ctor_get(v___x_5411_, 0);
lean_inc(v_a_5412_);
if (lean_obj_tag(v_a_5412_) == 1)
{
lean_object* v_a_5413_; lean_object* v_val_5414_; 
lean_dec(v_a_5350_);
lean_dec_ref(v_trace_5314_);
lean_dec_ref(v_a_5304_);
lean_dec_ref(v_ext_5300_);
lean_dec_ref(v_build_5298_);
lean_dec_ref(v_file_5297_);
v_a_5413_ = lean_ctor_get(v___x_5411_, 1);
lean_inc(v_a_5413_);
lean_dec_ref_known(v___x_5411_, 2);
v_val_5414_ = lean_ctor_get(v_a_5412_, 0);
lean_inc(v_val_5414_);
lean_dec_ref_known(v_a_5412_, 1);
v_a_5371_ = v_val_5414_;
v_a_5372_ = v_a_5413_;
goto v___jp_5370_;
}
else
{
lean_object* v_a_5415_; lean_object* v___x_5416_; 
lean_dec(v_a_5412_);
v_a_5415_ = lean_ctor_get(v___x_5411_, 1);
lean_inc(v_a_5415_);
lean_dec_ref_known(v___x_5411_, 2);
v___x_5416_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5304_, v_file_5297_, v_trace_5314_, v_a_5350_, v_mtime_5354_, v_a_5305_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5415_);
if (lean_obj_tag(v___x_5416_) == 0)
{
lean_object* v_a_5417_; lean_object* v_a_5418_; uint8_t v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; uint8_t v___x_5422_; 
v_a_5417_ = lean_ctor_get(v___x_5416_, 0);
lean_inc(v_a_5417_);
v_a_5418_ = lean_ctor_get(v___x_5416_, 1);
lean_inc(v_a_5418_);
lean_dec_ref_known(v___x_5416_, 2);
v___x_5419_ = lean_unbox(v_a_5417_);
v___x_5420_ = l_Lake_OutputStatus_ctorIdx(v___x_5419_);
v___x_5421_ = lean_obj_once(&l_Lake_OutputStatus_isUpToDate___closed__0, &l_Lake_OutputStatus_isUpToDate___closed__0_once, _init_l_Lake_OutputStatus_isUpToDate___closed__0);
v___x_5422_ = lean_nat_dec_eq(v___x_5420_, v___x_5421_);
lean_dec(v___x_5420_);
if (v___x_5422_ == 0)
{
lean_object* v___x_5423_; uint8_t v___x_5424_; lean_object* v___x_5425_; 
lean_dec_ref(v_trace_5314_);
lean_dec_ref(v_build_5298_);
v___x_5423_ = lean_box(0);
v___x_5424_ = lean_unbox(v_a_5417_);
lean_dec(v_a_5417_);
lean_inc(v_val_5352_);
v___x_5425_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v___x_5424_, v_file_5297_, v_ext_5300_, v_text_5299_, v_exe_5302_, v___y_5410_, v_val_5352_, v_hash_5353_, v___y_5408_, v___x_5423_, v_a_5304_, v_a_5305_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5418_);
lean_dec_ref(v_a_5304_);
v___y_5402_ = v___x_5425_;
goto v___jp_5401_;
}
else
{
lean_object* v___x_5426_; 
lean_inc_ref(v_a_5304_);
lean_inc_ref(v___x_5320_);
lean_inc_ref(v_ext_5300_);
lean_inc_ref(v_file_5297_);
v___x_5426_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5297_, v_build_5298_, v_text_5299_, v_ext_5300_, v_trace_5314_, v___x_5320_, v_a_5304_, v_a_5305_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5418_);
lean_dec_ref(v_trace_5314_);
if (lean_obj_tag(v___x_5426_) == 0)
{
lean_object* v_a_5427_; lean_object* v___x_5428_; uint8_t v___x_5429_; lean_object* v___x_5430_; 
v_a_5427_ = lean_ctor_get(v___x_5426_, 1);
lean_inc(v_a_5427_);
lean_dec_ref_known(v___x_5426_, 2);
v___x_5428_ = lean_box(0);
v___x_5429_ = lean_unbox(v_a_5417_);
lean_dec(v_a_5417_);
lean_inc(v_val_5352_);
v___x_5430_ = l_Lake_buildArtifactUnlessUpToDate___lam__1(v___x_5429_, v_file_5297_, v_ext_5300_, v_text_5299_, v_exe_5302_, v___y_5410_, v_val_5352_, v_hash_5353_, v___y_5408_, v___x_5428_, v_a_5304_, v_a_5305_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5427_);
lean_dec_ref(v_a_5304_);
v___y_5402_ = v___x_5430_;
goto v___jp_5401_;
}
else
{
lean_dec(v_a_5417_);
lean_dec_ref(v___x_5320_);
lean_del_object(v___x_5317_);
lean_dec_ref(v_a_5304_);
lean_dec_ref(v_ext_5300_);
lean_dec_ref(v_file_5297_);
return v___x_5426_;
}
}
}
else
{
lean_object* v_a_5431_; lean_object* v_a_5432_; lean_object* v___x_5434_; uint8_t v_isShared_5435_; uint8_t v_isSharedCheck_5439_; 
lean_dec_ref(v___x_5320_);
lean_del_object(v___x_5317_);
lean_dec_ref(v_trace_5314_);
lean_dec_ref(v_a_5304_);
lean_dec_ref(v_ext_5300_);
lean_dec_ref(v_build_5298_);
lean_dec_ref(v_file_5297_);
v_a_5431_ = lean_ctor_get(v___x_5416_, 0);
v_a_5432_ = lean_ctor_get(v___x_5416_, 1);
v_isSharedCheck_5439_ = !lean_is_exclusive(v___x_5416_);
if (v_isSharedCheck_5439_ == 0)
{
v___x_5434_ = v___x_5416_;
v_isShared_5435_ = v_isSharedCheck_5439_;
goto v_resetjp_5433_;
}
else
{
lean_inc(v_a_5432_);
lean_inc(v_a_5431_);
lean_dec(v___x_5416_);
v___x_5434_ = lean_box(0);
v_isShared_5435_ = v_isSharedCheck_5439_;
goto v_resetjp_5433_;
}
v_resetjp_5433_:
{
lean_object* v___x_5437_; 
if (v_isShared_5435_ == 0)
{
v___x_5437_ = v___x_5434_;
goto v_reusejp_5436_;
}
else
{
lean_object* v_reuseFailAlloc_5438_; 
v_reuseFailAlloc_5438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5438_, 0, v_a_5431_);
lean_ctor_set(v_reuseFailAlloc_5438_, 1, v_a_5432_);
v___x_5437_ = v_reuseFailAlloc_5438_;
goto v_reusejp_5436_;
}
v_reusejp_5436_:
{
return v___x_5437_;
}
}
}
}
}
else
{
lean_object* v_a_5440_; lean_object* v_a_5441_; lean_object* v___x_5443_; uint8_t v_isShared_5444_; uint8_t v_isSharedCheck_5448_; 
lean_dec(v_a_5350_);
lean_dec_ref(v___x_5320_);
lean_del_object(v___x_5317_);
lean_dec_ref(v_trace_5314_);
lean_dec_ref(v_a_5304_);
lean_dec_ref(v_ext_5300_);
lean_dec_ref(v_build_5298_);
lean_dec_ref(v_file_5297_);
v_a_5440_ = lean_ctor_get(v___x_5411_, 0);
v_a_5441_ = lean_ctor_get(v___x_5411_, 1);
v_isSharedCheck_5448_ = !lean_is_exclusive(v___x_5411_);
if (v_isSharedCheck_5448_ == 0)
{
v___x_5443_ = v___x_5411_;
v_isShared_5444_ = v_isSharedCheck_5448_;
goto v_resetjp_5442_;
}
else
{
lean_inc(v_a_5441_);
lean_inc(v_a_5440_);
lean_dec(v___x_5411_);
v___x_5443_ = lean_box(0);
v_isShared_5444_ = v_isSharedCheck_5448_;
goto v_resetjp_5442_;
}
v_resetjp_5442_:
{
lean_object* v___x_5446_; 
if (v_isShared_5444_ == 0)
{
v___x_5446_ = v___x_5443_;
goto v_reusejp_5445_;
}
else
{
lean_object* v_reuseFailAlloc_5447_; 
v_reuseFailAlloc_5447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5447_, 0, v_a_5440_);
lean_ctor_set(v_reuseFailAlloc_5447_, 1, v_a_5441_);
v___x_5446_ = v_reuseFailAlloc_5447_;
goto v_reusejp_5445_;
}
v_reusejp_5445_:
{
return v___x_5446_;
}
}
}
}
v___jp_5449_:
{
if (v_restore_5301_ == 0)
{
v___y_5408_ = v___y_5450_;
v___y_5409_ = v_a_5453_;
v___y_5410_ = v_a_5452_;
goto v___jp_5407_;
}
else
{
v___y_5408_ = v___y_5450_;
v___y_5409_ = v_a_5453_;
v___y_5410_ = v___y_5451_;
goto v___jp_5407_;
}
}
v___jp_5454_:
{
lean_object* v___x_5457_; 
lean_inc_ref(v_a_5304_);
lean_inc_ref(v___x_5320_);
lean_inc_ref(v_file_5297_);
lean_inc(v_val_5352_);
v___x_5457_ = l_Lake_buildArtifactUnlessUpToDate___lam__0(v_exe_5302_, v_hash_5353_, v_a_5350_, v_val_5352_, v_file_5297_, v___x_5320_, v___y_5455_, v_a_5304_, v_a_5305_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5456_);
if (lean_obj_tag(v___x_5457_) == 0)
{
lean_object* v_a_5458_; 
v_a_5458_ = lean_ctor_get(v___x_5457_, 0);
lean_inc(v_a_5458_);
if (lean_obj_tag(v_a_5458_) == 1)
{
lean_object* v_a_5459_; lean_object* v_val_5460_; 
lean_dec_ref(v_trace_5314_);
lean_dec_ref(v_a_5304_);
lean_dec_ref(v_ext_5300_);
lean_dec_ref(v_build_5298_);
lean_dec_ref(v_file_5297_);
v_a_5459_ = lean_ctor_get(v___x_5457_, 1);
lean_inc(v_a_5459_);
lean_dec_ref_known(v___x_5457_, 2);
v_val_5460_ = lean_ctor_get(v_a_5458_, 0);
lean_inc(v_val_5460_);
lean_dec_ref_known(v_a_5458_, 1);
v_a_5371_ = v_val_5460_;
v_a_5372_ = v_a_5459_;
goto v___jp_5370_;
}
else
{
lean_object* v_a_5461_; lean_object* v___x_5462_; 
lean_dec(v_a_5458_);
v_a_5461_ = lean_ctor_get(v___x_5457_, 1);
lean_inc(v_a_5461_);
lean_dec_ref_known(v___x_5457_, 2);
lean_inc_ref(v___x_5320_);
v___x_5462_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5297_, v_build_5298_, v_text_5299_, v_ext_5300_, v_trace_5314_, v___x_5320_, v_a_5304_, v_a_5305_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5461_);
lean_dec_ref(v_trace_5314_);
v___y_5402_ = v___x_5462_;
goto v___jp_5401_;
}
}
else
{
lean_object* v_a_5463_; lean_object* v_a_5464_; lean_object* v___x_5466_; uint8_t v_isShared_5467_; uint8_t v_isSharedCheck_5471_; 
lean_dec_ref(v___x_5320_);
lean_del_object(v___x_5317_);
lean_dec_ref(v_trace_5314_);
lean_dec_ref(v_a_5304_);
lean_dec_ref(v_ext_5300_);
lean_dec_ref(v_build_5298_);
lean_dec_ref(v_file_5297_);
v_a_5463_ = lean_ctor_get(v___x_5457_, 0);
v_a_5464_ = lean_ctor_get(v___x_5457_, 1);
v_isSharedCheck_5471_ = !lean_is_exclusive(v___x_5457_);
if (v_isSharedCheck_5471_ == 0)
{
v___x_5466_ = v___x_5457_;
v_isShared_5467_ = v_isSharedCheck_5471_;
goto v_resetjp_5465_;
}
else
{
lean_inc(v_a_5464_);
lean_inc(v_a_5463_);
lean_dec(v___x_5457_);
v___x_5466_ = lean_box(0);
v_isShared_5467_ = v_isSharedCheck_5471_;
goto v_resetjp_5465_;
}
v_resetjp_5465_:
{
lean_object* v___x_5469_; 
if (v_isShared_5467_ == 0)
{
v___x_5469_ = v___x_5466_;
goto v_reusejp_5468_;
}
else
{
lean_object* v_reuseFailAlloc_5470_; 
v_reuseFailAlloc_5470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5470_, 0, v_a_5463_);
lean_ctor_set(v_reuseFailAlloc_5470_, 1, v_a_5464_);
v___x_5469_ = v_reuseFailAlloc_5470_;
goto v_reusejp_5468_;
}
v_reusejp_5468_:
{
return v___x_5469_;
}
}
}
}
v___jp_5472_:
{
if (v_a_5474_ == 0)
{
lean_object* v___x_5476_; 
lean_dec(v_a_5350_);
lean_inc_ref(v___x_5320_);
v___x_5476_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5297_, v_build_5298_, v_text_5299_, v_ext_5300_, v_trace_5314_, v___x_5320_, v_a_5304_, v_a_5305_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5475_);
lean_dec_ref(v_trace_5314_);
v___y_5402_ = v___x_5476_;
goto v___jp_5401_;
}
else
{
v___y_5455_ = v___y_5473_;
v_a_5456_ = v_a_5475_;
goto v___jp_5454_;
}
}
v___jp_5477_:
{
lean_object* v___x_5479_; 
lean_inc(v_a_5350_);
v___x_5479_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5304_, v_file_5297_, v_trace_5314_, v_a_5350_, v_mtime_5354_, v_a_5305_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5478_);
if (lean_obj_tag(v___x_5479_) == 0)
{
lean_object* v_a_5480_; lean_object* v_a_5481_; uint8_t v___x_5482_; lean_object* v___x_5483_; lean_object* v___x_5484_; uint8_t v___x_5485_; 
v_a_5480_ = lean_ctor_get(v___x_5479_, 0);
lean_inc(v_a_5480_);
v_a_5481_ = lean_ctor_get(v___x_5479_, 1);
lean_inc(v_a_5481_);
lean_dec_ref_known(v___x_5479_, 2);
v___x_5482_ = lean_unbox(v_a_5480_);
lean_dec(v_a_5480_);
v___x_5483_ = l_Lake_OutputStatus_ctorIdx(v___x_5482_);
v___x_5484_ = lean_obj_once(&l_Lake_OutputStatus_isUpToDate___closed__0, &l_Lake_OutputStatus_isUpToDate___closed__0_once, _init_l_Lake_OutputStatus_isUpToDate___closed__0);
v___x_5485_ = lean_nat_dec_eq(v___x_5483_, v___x_5484_);
lean_dec(v___x_5483_);
if (v___x_5485_ == 0)
{
lean_object* v___x_5486_; 
lean_dec(v_a_5350_);
lean_dec_ref(v_trace_5314_);
lean_dec_ref(v_a_5304_);
lean_dec_ref(v_build_5298_);
v___x_5486_ = l_Lake_computeArtifact___redArg(v_file_5297_, v_ext_5300_, v_text_5299_, v_a_5308_, v_a_5481_);
v___y_5402_ = v___x_5486_;
goto v___jp_5401_;
}
else
{
if (lean_obj_tag(v_enableArtifactCache_x3f_5405_) == 0)
{
lean_object* v_toContext_5487_; lean_object* v_lakeEnv_5488_; lean_object* v_enableArtifactCache_x3f_5489_; 
v_toContext_5487_ = lean_ctor_get(v_a_5308_, 1);
v_lakeEnv_5488_ = lean_ctor_get(v_toContext_5487_, 0);
v_enableArtifactCache_x3f_5489_ = lean_ctor_get(v_lakeEnv_5488_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_5489_) == 0)
{
lean_object* v_packages_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; lean_object* v_config_5493_; lean_object* v_enableArtifactCache_x3f_5494_; 
v_packages_5490_ = lean_ctor_get(v_toContext_5487_, 4);
v___x_5491_ = lean_unsigned_to_nat(0u);
v___x_5492_ = lean_array_fget_borrowed(v_packages_5490_, v___x_5491_);
v_config_5493_ = lean_ctor_get(v___x_5492_, 6);
v_enableArtifactCache_x3f_5494_ = lean_ctor_get(v_config_5493_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_5494_) == 0)
{
v___y_5455_ = v___x_5485_;
v_a_5456_ = v_a_5481_;
goto v___jp_5454_;
}
else
{
lean_object* v_val_5495_; uint8_t v___x_5496_; 
v_val_5495_ = lean_ctor_get(v_enableArtifactCache_x3f_5494_, 0);
v___x_5496_ = lean_unbox(v_val_5495_);
v___y_5473_ = v___x_5485_;
v_a_5474_ = v___x_5496_;
v_a_5475_ = v_a_5481_;
goto v___jp_5472_;
}
}
else
{
lean_object* v_val_5497_; uint8_t v___x_5498_; 
v_val_5497_ = lean_ctor_get(v_enableArtifactCache_x3f_5489_, 0);
v___x_5498_ = lean_unbox(v_val_5497_);
v___y_5473_ = v___x_5485_;
v_a_5474_ = v___x_5498_;
v_a_5475_ = v_a_5481_;
goto v___jp_5472_;
}
}
else
{
lean_object* v_val_5499_; uint8_t v___x_5500_; 
v_val_5499_ = lean_ctor_get(v_enableArtifactCache_x3f_5405_, 0);
v___x_5500_ = lean_unbox(v_val_5499_);
v___y_5473_ = v___x_5485_;
v_a_5474_ = v___x_5500_;
v_a_5475_ = v_a_5481_;
goto v___jp_5472_;
}
}
}
else
{
lean_object* v_a_5501_; lean_object* v_a_5502_; lean_object* v___x_5504_; uint8_t v_isShared_5505_; uint8_t v_isSharedCheck_5509_; 
lean_dec(v_a_5350_);
lean_dec_ref(v___x_5320_);
lean_del_object(v___x_5317_);
lean_dec_ref(v_trace_5314_);
lean_dec_ref(v_a_5304_);
lean_dec_ref(v_ext_5300_);
lean_dec_ref(v_build_5298_);
lean_dec_ref(v_file_5297_);
v_a_5501_ = lean_ctor_get(v___x_5479_, 0);
v_a_5502_ = lean_ctor_get(v___x_5479_, 1);
v_isSharedCheck_5509_ = !lean_is_exclusive(v___x_5479_);
if (v_isSharedCheck_5509_ == 0)
{
v___x_5504_ = v___x_5479_;
v_isShared_5505_ = v_isSharedCheck_5509_;
goto v_resetjp_5503_;
}
else
{
lean_inc(v_a_5502_);
lean_inc(v_a_5501_);
lean_dec(v___x_5479_);
v___x_5504_ = lean_box(0);
v_isShared_5505_ = v_isSharedCheck_5509_;
goto v_resetjp_5503_;
}
v_resetjp_5503_:
{
lean_object* v___x_5507_; 
if (v_isShared_5505_ == 0)
{
v___x_5507_ = v___x_5504_;
goto v_reusejp_5506_;
}
else
{
lean_object* v_reuseFailAlloc_5508_; 
v_reuseFailAlloc_5508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5508_, 0, v_a_5501_);
lean_ctor_set(v_reuseFailAlloc_5508_, 1, v_a_5502_);
v___x_5507_ = v_reuseFailAlloc_5508_;
goto v_reusejp_5506_;
}
v_reusejp_5506_:
{
return v___x_5507_;
}
}
}
}
v___jp_5510_:
{
if (v_a_5511_ == 0)
{
v_a_5478_ = v_a_5512_;
goto v___jp_5477_;
}
else
{
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5406_) == 0)
{
lean_object* v_toContext_5513_; lean_object* v_lakeEnv_5514_; lean_object* v_restoreAllArtifacts_x3f_5515_; 
v_toContext_5513_ = lean_ctor_get(v_a_5308_, 1);
v_lakeEnv_5514_ = lean_ctor_get(v_toContext_5513_, 0);
v_restoreAllArtifacts_x3f_5515_ = lean_ctor_get(v_lakeEnv_5514_, 7);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5515_) == 0)
{
lean_object* v_packages_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v_config_5519_; lean_object* v_restoreAllArtifacts_x3f_5520_; 
v_packages_5516_ = lean_ctor_get(v_toContext_5513_, 4);
v___x_5517_ = lean_unsigned_to_nat(0u);
v___x_5518_ = lean_array_fget_borrowed(v_packages_5516_, v___x_5517_);
v_config_5519_ = lean_ctor_get(v___x_5518_, 6);
v_restoreAllArtifacts_x3f_5520_ = lean_ctor_get(v_config_5519_, 25);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_5520_) == 0)
{
uint8_t v___x_5521_; 
v___x_5521_ = 0;
v___y_5450_ = v_a_5511_;
v___y_5451_ = v_a_5511_;
v_a_5452_ = v___x_5521_;
v_a_5453_ = v_a_5512_;
goto v___jp_5449_;
}
else
{
lean_object* v_val_5522_; uint8_t v___x_5523_; 
v_val_5522_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5520_, 0);
v___x_5523_ = lean_unbox(v_val_5522_);
v___y_5450_ = v_a_5511_;
v___y_5451_ = v_a_5511_;
v_a_5452_ = v___x_5523_;
v_a_5453_ = v_a_5512_;
goto v___jp_5449_;
}
}
else
{
lean_object* v_val_5524_; uint8_t v___x_5525_; 
v_val_5524_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5515_, 0);
v___x_5525_ = lean_unbox(v_val_5524_);
v___y_5450_ = v_a_5511_;
v___y_5451_ = v_a_5511_;
v_a_5452_ = v___x_5525_;
v_a_5453_ = v_a_5512_;
goto v___jp_5449_;
}
}
else
{
lean_object* v_val_5526_; uint8_t v___x_5527_; 
v_val_5526_ = lean_ctor_get(v_restoreAllArtifacts_x3f_5406_, 0);
v___x_5527_ = lean_unbox(v_val_5526_);
v___y_5450_ = v_a_5511_;
v___y_5451_ = v_a_5511_;
v_a_5452_ = v___x_5527_;
v_a_5453_ = v_a_5512_;
goto v___jp_5449_;
}
}
}
}
else
{
lean_object* v_a_5543_; lean_object* v_a_5544_; lean_object* v_mtime_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; 
lean_del_object(v___x_5317_);
v_a_5543_ = lean_ctor_get(v___x_5349_, 0);
lean_inc(v_a_5543_);
v_a_5544_ = lean_ctor_get(v___x_5349_, 1);
lean_inc(v_a_5544_);
lean_dec_ref_known(v___x_5349_, 2);
v_mtime_5545_ = lean_ctor_get(v_trace_5314_, 2);
lean_inc_ref(v_trace_5314_);
v___x_5546_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5546_, 0, v_a_5544_);
lean_ctor_set(v___x_5546_, 1, v_trace_5314_);
lean_ctor_set(v___x_5546_, 2, v_buildTime_5315_);
lean_ctor_set_uint8(v___x_5546_, sizeof(void*)*3, v_action_5312_);
lean_ctor_set_uint8(v___x_5546_, sizeof(void*)*3 + 1, v_wantsRebuild_5313_);
v___x_5547_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(v_a_5304_, v_file_5297_, v_trace_5314_, v_a_5543_, v_mtime_5545_, v_a_5305_, v_a_5306_, v_a_5307_, v_a_5308_, v___x_5546_);
if (lean_obj_tag(v___x_5547_) == 0)
{
lean_object* v_a_5548_; lean_object* v_a_5549_; uint8_t v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; uint8_t v___x_5553_; 
v_a_5548_ = lean_ctor_get(v___x_5547_, 0);
lean_inc(v_a_5548_);
v_a_5549_ = lean_ctor_get(v___x_5547_, 1);
lean_inc(v_a_5549_);
lean_dec_ref_known(v___x_5547_, 2);
v___x_5550_ = lean_unbox(v_a_5548_);
lean_dec(v_a_5548_);
v___x_5551_ = l_Lake_OutputStatus_ctorIdx(v___x_5550_);
v___x_5552_ = lean_obj_once(&l_Lake_OutputStatus_isUpToDate___closed__0, &l_Lake_OutputStatus_isUpToDate___closed__0_once, _init_l_Lake_OutputStatus_isUpToDate___closed__0);
v___x_5553_ = lean_nat_dec_eq(v___x_5551_, v___x_5552_);
lean_dec(v___x_5551_);
if (v___x_5553_ == 0)
{
lean_object* v___x_5554_; 
lean_dec_ref(v_trace_5314_);
lean_dec_ref(v_a_5304_);
lean_dec_ref(v_build_5298_);
v___x_5554_ = l_Lake_computeArtifact___redArg(v_file_5297_, v_ext_5300_, v_text_5299_, v_a_5308_, v_a_5549_);
if (lean_obj_tag(v___x_5554_) == 0)
{
lean_object* v_a_5555_; lean_object* v_a_5556_; 
v_a_5555_ = lean_ctor_get(v___x_5554_, 0);
lean_inc(v_a_5555_);
v_a_5556_ = lean_ctor_get(v___x_5554_, 1);
lean_inc(v_a_5556_);
lean_dec_ref_known(v___x_5554_, 2);
v_art_5322_ = v_a_5555_;
v___y_5323_ = v_a_5556_;
goto v___jp_5321_;
}
else
{
lean_dec_ref(v___x_5320_);
return v___x_5554_;
}
}
else
{
lean_object* v___x_5557_; 
lean_inc_ref(v___x_5320_);
v___x_5557_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(v_file_5297_, v_build_5298_, v_text_5299_, v_ext_5300_, v_trace_5314_, v___x_5320_, v_a_5304_, v_a_5305_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5549_);
lean_dec_ref(v_trace_5314_);
if (lean_obj_tag(v___x_5557_) == 0)
{
lean_object* v_a_5558_; lean_object* v_a_5559_; 
v_a_5558_ = lean_ctor_get(v___x_5557_, 0);
lean_inc(v_a_5558_);
v_a_5559_ = lean_ctor_get(v___x_5557_, 1);
lean_inc(v_a_5559_);
lean_dec_ref_known(v___x_5557_, 2);
v_art_5322_ = v_a_5558_;
v___y_5323_ = v_a_5559_;
goto v___jp_5321_;
}
else
{
lean_dec_ref(v___x_5320_);
return v___x_5557_;
}
}
}
else
{
lean_object* v_a_5560_; lean_object* v_a_5561_; lean_object* v___x_5563_; uint8_t v_isShared_5564_; uint8_t v_isSharedCheck_5568_; 
lean_dec_ref(v___x_5320_);
lean_dec_ref(v_trace_5314_);
lean_dec_ref(v_a_5304_);
lean_dec_ref(v_ext_5300_);
lean_dec_ref(v_build_5298_);
lean_dec_ref(v_file_5297_);
v_a_5560_ = lean_ctor_get(v___x_5547_, 0);
v_a_5561_ = lean_ctor_get(v___x_5547_, 1);
v_isSharedCheck_5568_ = !lean_is_exclusive(v___x_5547_);
if (v_isSharedCheck_5568_ == 0)
{
v___x_5563_ = v___x_5547_;
v_isShared_5564_ = v_isSharedCheck_5568_;
goto v_resetjp_5562_;
}
else
{
lean_inc(v_a_5561_);
lean_inc(v_a_5560_);
lean_dec(v___x_5547_);
v___x_5563_ = lean_box(0);
v_isShared_5564_ = v_isSharedCheck_5568_;
goto v_resetjp_5562_;
}
v_resetjp_5562_:
{
lean_object* v___x_5566_; 
if (v_isShared_5564_ == 0)
{
v___x_5566_ = v___x_5563_;
goto v_reusejp_5565_;
}
else
{
lean_object* v_reuseFailAlloc_5567_; 
v_reuseFailAlloc_5567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5567_, 0, v_a_5560_);
lean_ctor_set(v_reuseFailAlloc_5567_, 1, v_a_5561_);
v___x_5566_ = v_reuseFailAlloc_5567_;
goto v_reusejp_5565_;
}
v_reusejp_5565_:
{
return v___x_5566_;
}
}
}
}
}
else
{
lean_object* v_a_5569_; lean_object* v_a_5570_; lean_object* v___x_5572_; uint8_t v_isShared_5573_; uint8_t v_isSharedCheck_5578_; 
lean_dec_ref(v___x_5320_);
lean_del_object(v___x_5317_);
lean_dec_ref(v_a_5304_);
lean_dec_ref(v_ext_5300_);
lean_dec_ref(v_build_5298_);
lean_dec_ref(v_file_5297_);
v_a_5569_ = lean_ctor_get(v___x_5349_, 0);
v_a_5570_ = lean_ctor_get(v___x_5349_, 1);
v_isSharedCheck_5578_ = !lean_is_exclusive(v___x_5349_);
if (v_isSharedCheck_5578_ == 0)
{
v___x_5572_ = v___x_5349_;
v_isShared_5573_ = v_isSharedCheck_5578_;
goto v_resetjp_5571_;
}
else
{
lean_inc(v_a_5570_);
lean_inc(v_a_5569_);
lean_dec(v___x_5349_);
v___x_5572_ = lean_box(0);
v_isShared_5573_ = v_isSharedCheck_5578_;
goto v_resetjp_5571_;
}
v_resetjp_5571_:
{
lean_object* v___x_5574_; lean_object* v___x_5576_; 
v___x_5574_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5574_, 0, v_a_5570_);
lean_ctor_set(v___x_5574_, 1, v_trace_5314_);
lean_ctor_set(v___x_5574_, 2, v_buildTime_5315_);
lean_ctor_set_uint8(v___x_5574_, sizeof(void*)*3, v_action_5312_);
lean_ctor_set_uint8(v___x_5574_, sizeof(void*)*3 + 1, v_wantsRebuild_5313_);
if (v_isShared_5573_ == 0)
{
lean_ctor_set(v___x_5572_, 1, v___x_5574_);
v___x_5576_ = v___x_5572_;
goto v_reusejp_5575_;
}
else
{
lean_object* v_reuseFailAlloc_5577_; 
v_reuseFailAlloc_5577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5577_, 0, v_a_5569_);
lean_ctor_set(v_reuseFailAlloc_5577_, 1, v___x_5574_);
v___x_5576_ = v_reuseFailAlloc_5577_;
goto v_reusejp_5575_;
}
v_reusejp_5575_:
{
return v___x_5576_;
}
}
}
v___jp_5321_:
{
lean_object* v_log_5324_; uint8_t v_action_5325_; uint8_t v_wantsRebuild_5326_; lean_object* v_buildTime_5327_; lean_object* v___x_5329_; uint8_t v_isShared_5330_; uint8_t v_isSharedCheck_5336_; 
v_log_5324_ = lean_ctor_get(v___y_5323_, 0);
v_action_5325_ = lean_ctor_get_uint8(v___y_5323_, sizeof(void*)*3);
v_wantsRebuild_5326_ = lean_ctor_get_uint8(v___y_5323_, sizeof(void*)*3 + 1);
v_buildTime_5327_ = lean_ctor_get(v___y_5323_, 2);
v_isSharedCheck_5336_ = !lean_is_exclusive(v___y_5323_);
if (v_isSharedCheck_5336_ == 0)
{
lean_object* v_unused_5337_; 
v_unused_5337_ = lean_ctor_get(v___y_5323_, 1);
lean_dec(v_unused_5337_);
v___x_5329_ = v___y_5323_;
v_isShared_5330_ = v_isSharedCheck_5336_;
goto v_resetjp_5328_;
}
else
{
lean_inc(v_buildTime_5327_);
lean_inc(v_log_5324_);
lean_dec(v___y_5323_);
v___x_5329_ = lean_box(0);
v_isShared_5330_ = v_isSharedCheck_5336_;
goto v_resetjp_5328_;
}
v_resetjp_5328_:
{
lean_object* v___x_5331_; lean_object* v___x_5333_; 
v___x_5331_ = l_Lake_Artifact_trace(v_art_5322_);
if (v_isShared_5330_ == 0)
{
lean_ctor_set(v___x_5329_, 1, v___x_5331_);
v___x_5333_ = v___x_5329_;
goto v_reusejp_5332_;
}
else
{
lean_object* v_reuseFailAlloc_5335_; 
v_reuseFailAlloc_5335_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5335_, 0, v_log_5324_);
lean_ctor_set(v_reuseFailAlloc_5335_, 1, v___x_5331_);
lean_ctor_set(v_reuseFailAlloc_5335_, 2, v_buildTime_5327_);
lean_ctor_set_uint8(v_reuseFailAlloc_5335_, sizeof(void*)*3, v_action_5325_);
lean_ctor_set_uint8(v_reuseFailAlloc_5335_, sizeof(void*)*3 + 1, v_wantsRebuild_5326_);
v___x_5333_ = v_reuseFailAlloc_5335_;
goto v_reusejp_5332_;
}
v_reusejp_5332_:
{
lean_object* v___x_5334_; 
v___x_5334_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v_art_5322_, v___x_5320_, v___x_5333_);
lean_dec_ref(v___x_5320_);
return v___x_5334_;
}
}
}
v___jp_5338_:
{
lean_object* v___x_5344_; lean_object* v___x_5346_; 
v___x_5344_ = l_Lake_Artifact_trace(v___y_5339_);
if (v_isShared_5318_ == 0)
{
lean_ctor_set(v___x_5317_, 2, v_buildTime_5343_);
lean_ctor_set(v___x_5317_, 1, v___x_5344_);
lean_ctor_set(v___x_5317_, 0, v_log_5340_);
v___x_5346_ = v___x_5317_;
goto v_reusejp_5345_;
}
else
{
lean_object* v_reuseFailAlloc_5348_; 
v_reuseFailAlloc_5348_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5348_, 0, v_log_5340_);
lean_ctor_set(v_reuseFailAlloc_5348_, 1, v___x_5344_);
lean_ctor_set(v_reuseFailAlloc_5348_, 2, v_buildTime_5343_);
v___x_5346_ = v_reuseFailAlloc_5348_;
goto v_reusejp_5345_;
}
v_reusejp_5345_:
{
lean_object* v___x_5347_; 
lean_ctor_set_uint8(v___x_5346_, sizeof(void*)*3, v_action_5341_);
lean_ctor_set_uint8(v___x_5346_, sizeof(void*)*3 + 1, v_wantsRebuild_5342_);
v___x_5347_ = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_setMTime___redArg(v___y_5339_, v___x_5320_, v___x_5346_);
lean_dec_ref(v___x_5320_);
return v___x_5347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___boxed(lean_object* v_file_5580_, lean_object* v_build_5581_, lean_object* v_text_5582_, lean_object* v_ext_5583_, lean_object* v_restore_5584_, lean_object* v_exe_5585_, lean_object* v_platformIndependent_5586_, lean_object* v_a_5587_, lean_object* v_a_5588_, lean_object* v_a_5589_, lean_object* v_a_5590_, lean_object* v_a_5591_, lean_object* v_a_5592_, lean_object* v_a_5593_){
_start:
{
uint8_t v_text_boxed_5594_; uint8_t v_restore_boxed_5595_; uint8_t v_exe_boxed_5596_; uint8_t v_platformIndependent_boxed_5597_; lean_object* v_res_5598_; 
v_text_boxed_5594_ = lean_unbox(v_text_5582_);
v_restore_boxed_5595_ = lean_unbox(v_restore_5584_);
v_exe_boxed_5596_ = lean_unbox(v_exe_5585_);
v_platformIndependent_boxed_5597_ = lean_unbox(v_platformIndependent_5586_);
v_res_5598_ = l_Lake_buildArtifactUnlessUpToDate(v_file_5580_, v_build_5581_, v_text_boxed_5594_, v_ext_5583_, v_restore_boxed_5595_, v_exe_boxed_5596_, v_platformIndependent_boxed_5597_, v_a_5587_, v_a_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_);
lean_dec_ref(v_a_5591_);
lean_dec(v_a_5590_);
lean_dec(v_a_5589_);
lean_dec(v_a_5588_);
return v_res_5598_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0(lean_object* v_extraDepTrace_5600_, lean_object* v_build_5601_, lean_object* v_file_5602_, uint8_t v_text_5603_, lean_object* v_depInfo_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_, lean_object* v___y_5610_){
_start:
{
lean_object* v___x_5612_; 
lean_inc_ref(v___y_5609_);
lean_inc(v___y_5608_);
lean_inc(v___y_5607_);
lean_inc(v___y_5606_);
lean_inc_ref(v___y_5605_);
v___x_5612_ = lean_apply_7(v_extraDepTrace_5600_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_, lean_box(0));
if (lean_obj_tag(v___x_5612_) == 0)
{
lean_object* v_a_5613_; lean_object* v_a_5614_; lean_object* v_log_5615_; uint8_t v_action_5616_; uint8_t v_wantsRebuild_5617_; lean_object* v_trace_5618_; lean_object* v_buildTime_5619_; lean_object* v___x_5621_; uint8_t v_isShared_5622_; uint8_t v_isSharedCheck_5650_; 
v_a_5613_ = lean_ctor_get(v___x_5612_, 1);
lean_inc(v_a_5613_);
v_a_5614_ = lean_ctor_get(v___x_5612_, 0);
lean_inc(v_a_5614_);
lean_dec_ref_known(v___x_5612_, 2);
v_log_5615_ = lean_ctor_get(v_a_5613_, 0);
v_action_5616_ = lean_ctor_get_uint8(v_a_5613_, sizeof(void*)*3);
v_wantsRebuild_5617_ = lean_ctor_get_uint8(v_a_5613_, sizeof(void*)*3 + 1);
v_trace_5618_ = lean_ctor_get(v_a_5613_, 1);
v_buildTime_5619_ = lean_ctor_get(v_a_5613_, 2);
v_isSharedCheck_5650_ = !lean_is_exclusive(v_a_5613_);
if (v_isSharedCheck_5650_ == 0)
{
v___x_5621_ = v_a_5613_;
v_isShared_5622_ = v_isSharedCheck_5650_;
goto v_resetjp_5620_;
}
else
{
lean_inc(v_buildTime_5619_);
lean_inc(v_trace_5618_);
lean_inc(v_log_5615_);
lean_dec(v_a_5613_);
v___x_5621_ = lean_box(0);
v_isShared_5622_ = v_isSharedCheck_5650_;
goto v_resetjp_5620_;
}
v_resetjp_5620_:
{
lean_object* v___x_5623_; lean_object* v___x_5625_; 
v___x_5623_ = l_Lake_BuildTrace_mix(v_trace_5618_, v_a_5614_);
if (v_isShared_5622_ == 0)
{
lean_ctor_set(v___x_5621_, 1, v___x_5623_);
v___x_5625_ = v___x_5621_;
goto v_reusejp_5624_;
}
else
{
lean_object* v_reuseFailAlloc_5649_; 
v_reuseFailAlloc_5649_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5649_, 0, v_log_5615_);
lean_ctor_set(v_reuseFailAlloc_5649_, 1, v___x_5623_);
lean_ctor_set(v_reuseFailAlloc_5649_, 2, v_buildTime_5619_);
lean_ctor_set_uint8(v_reuseFailAlloc_5649_, sizeof(void*)*3, v_action_5616_);
lean_ctor_set_uint8(v_reuseFailAlloc_5649_, sizeof(void*)*3 + 1, v_wantsRebuild_5617_);
v___x_5625_ = v_reuseFailAlloc_5649_;
goto v_reusejp_5624_;
}
v_reusejp_5624_:
{
lean_object* v___x_5626_; lean_object* v___x_5627_; uint8_t v___x_5628_; lean_object* v___x_5629_; 
v___x_5626_ = lean_apply_1(v_build_5601_, v_depInfo_5604_);
v___x_5627_ = ((lean_object*)(l_Lake_buildFileAfterDep___redArg___lam__0___closed__0));
v___x_5628_ = 0;
v___x_5629_ = l_Lake_buildArtifactUnlessUpToDate(v_file_5602_, v___x_5626_, v_text_5603_, v___x_5627_, v___x_5628_, v___x_5628_, v___x_5628_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_, v___y_5609_, v___x_5625_);
if (lean_obj_tag(v___x_5629_) == 0)
{
lean_object* v_a_5630_; lean_object* v_a_5631_; lean_object* v___x_5633_; uint8_t v_isShared_5634_; uint8_t v_isSharedCheck_5639_; 
v_a_5630_ = lean_ctor_get(v___x_5629_, 0);
v_a_5631_ = lean_ctor_get(v___x_5629_, 1);
v_isSharedCheck_5639_ = !lean_is_exclusive(v___x_5629_);
if (v_isSharedCheck_5639_ == 0)
{
v___x_5633_ = v___x_5629_;
v_isShared_5634_ = v_isSharedCheck_5639_;
goto v_resetjp_5632_;
}
else
{
lean_inc(v_a_5631_);
lean_inc(v_a_5630_);
lean_dec(v___x_5629_);
v___x_5633_ = lean_box(0);
v_isShared_5634_ = v_isSharedCheck_5639_;
goto v_resetjp_5632_;
}
v_resetjp_5632_:
{
lean_object* v_path_5635_; lean_object* v___x_5637_; 
v_path_5635_ = lean_ctor_get(v_a_5630_, 1);
lean_inc_ref(v_path_5635_);
lean_dec(v_a_5630_);
if (v_isShared_5634_ == 0)
{
lean_ctor_set(v___x_5633_, 0, v_path_5635_);
v___x_5637_ = v___x_5633_;
goto v_reusejp_5636_;
}
else
{
lean_object* v_reuseFailAlloc_5638_; 
v_reuseFailAlloc_5638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5638_, 0, v_path_5635_);
lean_ctor_set(v_reuseFailAlloc_5638_, 1, v_a_5631_);
v___x_5637_ = v_reuseFailAlloc_5638_;
goto v_reusejp_5636_;
}
v_reusejp_5636_:
{
return v___x_5637_;
}
}
}
else
{
lean_object* v_a_5640_; lean_object* v_a_5641_; lean_object* v___x_5643_; uint8_t v_isShared_5644_; uint8_t v_isSharedCheck_5648_; 
v_a_5640_ = lean_ctor_get(v___x_5629_, 0);
v_a_5641_ = lean_ctor_get(v___x_5629_, 1);
v_isSharedCheck_5648_ = !lean_is_exclusive(v___x_5629_);
if (v_isSharedCheck_5648_ == 0)
{
v___x_5643_ = v___x_5629_;
v_isShared_5644_ = v_isSharedCheck_5648_;
goto v_resetjp_5642_;
}
else
{
lean_inc(v_a_5641_);
lean_inc(v_a_5640_);
lean_dec(v___x_5629_);
v___x_5643_ = lean_box(0);
v_isShared_5644_ = v_isSharedCheck_5648_;
goto v_resetjp_5642_;
}
v_resetjp_5642_:
{
lean_object* v___x_5646_; 
if (v_isShared_5644_ == 0)
{
v___x_5646_ = v___x_5643_;
goto v_reusejp_5645_;
}
else
{
lean_object* v_reuseFailAlloc_5647_; 
v_reuseFailAlloc_5647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5647_, 0, v_a_5640_);
lean_ctor_set(v_reuseFailAlloc_5647_, 1, v_a_5641_);
v___x_5646_ = v_reuseFailAlloc_5647_;
goto v_reusejp_5645_;
}
v_reusejp_5645_:
{
return v___x_5646_;
}
}
}
}
}
}
else
{
lean_object* v_a_5651_; lean_object* v_a_5652_; lean_object* v___x_5654_; uint8_t v_isShared_5655_; uint8_t v_isSharedCheck_5659_; 
lean_dec_ref(v___y_5605_);
lean_dec(v_depInfo_5604_);
lean_dec_ref(v_file_5602_);
lean_dec_ref(v_build_5601_);
v_a_5651_ = lean_ctor_get(v___x_5612_, 0);
v_a_5652_ = lean_ctor_get(v___x_5612_, 1);
v_isSharedCheck_5659_ = !lean_is_exclusive(v___x_5612_);
if (v_isSharedCheck_5659_ == 0)
{
v___x_5654_ = v___x_5612_;
v_isShared_5655_ = v_isSharedCheck_5659_;
goto v_resetjp_5653_;
}
else
{
lean_inc(v_a_5652_);
lean_inc(v_a_5651_);
lean_dec(v___x_5612_);
v___x_5654_ = lean_box(0);
v_isShared_5655_ = v_isSharedCheck_5659_;
goto v_resetjp_5653_;
}
v_resetjp_5653_:
{
lean_object* v___x_5657_; 
if (v_isShared_5655_ == 0)
{
v___x_5657_ = v___x_5654_;
goto v_reusejp_5656_;
}
else
{
lean_object* v_reuseFailAlloc_5658_; 
v_reuseFailAlloc_5658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5658_, 0, v_a_5651_);
lean_ctor_set(v_reuseFailAlloc_5658_, 1, v_a_5652_);
v___x_5657_ = v_reuseFailAlloc_5658_;
goto v_reusejp_5656_;
}
v_reusejp_5656_:
{
return v___x_5657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___boxed(lean_object* v_extraDepTrace_5660_, lean_object* v_build_5661_, lean_object* v_file_5662_, lean_object* v_text_5663_, lean_object* v_depInfo_5664_, lean_object* v___y_5665_, lean_object* v___y_5666_, lean_object* v___y_5667_, lean_object* v___y_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_){
_start:
{
uint8_t v_text_boxed_5672_; lean_object* v_res_5673_; 
v_text_boxed_5672_ = lean_unbox(v_text_5663_);
v_res_5673_ = l_Lake_buildFileAfterDep___redArg___lam__0(v_extraDepTrace_5660_, v_build_5661_, v_file_5662_, v_text_boxed_5672_, v_depInfo_5664_, v___y_5665_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_);
lean_dec_ref(v___y_5669_);
lean_dec(v___y_5668_);
lean_dec(v___y_5667_);
lean_dec(v___y_5666_);
return v_res_5673_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg(lean_object* v_file_5674_, lean_object* v_dep_5675_, lean_object* v_build_5676_, lean_object* v_extraDepTrace_5677_, uint8_t v_text_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_, lean_object* v_a_5681_, lean_object* v_a_5682_, lean_object* v_a_5683_, lean_object* v_a_5684_){
_start:
{
lean_object* v___x_5686_; lean_object* v___f_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; uint8_t v___x_5690_; lean_object* v___x_5691_; 
v___x_5686_ = lean_box(v_text_5678_);
v___f_5687_ = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_5687_, 0, v_extraDepTrace_5677_);
lean_closure_set(v___f_5687_, 1, v_build_5676_);
lean_closure_set(v___f_5687_, 2, v_file_5674_);
lean_closure_set(v___f_5687_, 3, v___x_5686_);
v___x_5688_ = l_Lake_instDataKindFilePath;
v___x_5689_ = lean_unsigned_to_nat(0u);
v___x_5690_ = 0;
v___x_5691_ = l_Lake_Job_mapM___redArg(v___x_5688_, v_dep_5675_, v___f_5687_, v___x_5689_, v___x_5690_, v_a_5679_, v_a_5680_, v_a_5681_, v_a_5682_, v_a_5683_, v_a_5684_);
return v___x_5691_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___boxed(lean_object* v_file_5692_, lean_object* v_dep_5693_, lean_object* v_build_5694_, lean_object* v_extraDepTrace_5695_, lean_object* v_text_5696_, lean_object* v_a_5697_, lean_object* v_a_5698_, lean_object* v_a_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_, lean_object* v_a_5703_){
_start:
{
uint8_t v_text_boxed_5704_; lean_object* v_res_5705_; 
v_text_boxed_5704_ = lean_unbox(v_text_5696_);
v_res_5705_ = l_Lake_buildFileAfterDep___redArg(v_file_5692_, v_dep_5693_, v_build_5694_, v_extraDepTrace_5695_, v_text_boxed_5704_, v_a_5697_, v_a_5698_, v_a_5699_, v_a_5700_, v_a_5701_, v_a_5702_);
lean_dec_ref(v_a_5702_);
lean_dec_ref(v_a_5701_);
lean_dec(v_a_5700_);
lean_dec(v_a_5699_);
lean_dec(v_a_5698_);
return v_res_5705_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object* v_00_u03b1_5706_, lean_object* v_file_5707_, lean_object* v_dep_5708_, lean_object* v_build_5709_, lean_object* v_extraDepTrace_5710_, uint8_t v_text_5711_, lean_object* v_a_5712_, lean_object* v_a_5713_, lean_object* v_a_5714_, lean_object* v_a_5715_, lean_object* v_a_5716_, lean_object* v_a_5717_){
_start:
{
lean_object* v___x_5719_; lean_object* v___f_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; uint8_t v___x_5723_; lean_object* v___x_5724_; 
v___x_5719_ = lean_box(v_text_5711_);
v___f_5720_ = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_5720_, 0, v_extraDepTrace_5710_);
lean_closure_set(v___f_5720_, 1, v_build_5709_);
lean_closure_set(v___f_5720_, 2, v_file_5707_);
lean_closure_set(v___f_5720_, 3, v___x_5719_);
v___x_5721_ = l_Lake_instDataKindFilePath;
v___x_5722_ = lean_unsigned_to_nat(0u);
v___x_5723_ = 0;
v___x_5724_ = l_Lake_Job_mapM___redArg(v___x_5721_, v_dep_5708_, v___f_5720_, v___x_5722_, v___x_5723_, v_a_5712_, v_a_5713_, v_a_5714_, v_a_5715_, v_a_5716_, v_a_5717_);
return v___x_5724_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___boxed(lean_object* v_00_u03b1_5725_, lean_object* v_file_5726_, lean_object* v_dep_5727_, lean_object* v_build_5728_, lean_object* v_extraDepTrace_5729_, lean_object* v_text_5730_, lean_object* v_a_5731_, lean_object* v_a_5732_, lean_object* v_a_5733_, lean_object* v_a_5734_, lean_object* v_a_5735_, lean_object* v_a_5736_, lean_object* v_a_5737_){
_start:
{
uint8_t v_text_boxed_5738_; lean_object* v_res_5739_; 
v_text_boxed_5738_ = lean_unbox(v_text_5730_);
v_res_5739_ = l_Lake_buildFileAfterDep(v_00_u03b1_5725_, v_file_5726_, v_dep_5727_, v_build_5728_, v_extraDepTrace_5729_, v_text_boxed_5738_, v_a_5731_, v_a_5732_, v_a_5733_, v_a_5734_, v_a_5735_, v_a_5736_);
lean_dec_ref(v_a_5736_);
lean_dec_ref(v_a_5735_);
lean_dec(v_a_5734_);
lean_dec(v_a_5733_);
lean_dec(v_a_5732_);
return v_res_5739_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(lean_object* v_info_5740_){
_start:
{
lean_object* v___x_5742_; 
v___x_5742_ = l_Lake_computeBinFileHash(v_info_5740_);
if (lean_obj_tag(v___x_5742_) == 0)
{
lean_object* v_a_5743_; lean_object* v___x_5744_; 
v_a_5743_ = lean_ctor_get(v___x_5742_, 0);
lean_inc(v_a_5743_);
lean_dec_ref_known(v___x_5742_, 1);
v___x_5744_ = lean_io_metadata(v_info_5740_);
if (lean_obj_tag(v___x_5744_) == 0)
{
lean_object* v_a_5745_; lean_object* v___x_5747_; uint8_t v_isShared_5748_; uint8_t v_isSharedCheck_5756_; 
v_a_5745_ = lean_ctor_get(v___x_5744_, 0);
v_isSharedCheck_5756_ = !lean_is_exclusive(v___x_5744_);
if (v_isSharedCheck_5756_ == 0)
{
v___x_5747_ = v___x_5744_;
v_isShared_5748_ = v_isSharedCheck_5756_;
goto v_resetjp_5746_;
}
else
{
lean_inc(v_a_5745_);
lean_dec(v___x_5744_);
v___x_5747_ = lean_box(0);
v_isShared_5748_ = v_isSharedCheck_5756_;
goto v_resetjp_5746_;
}
v_resetjp_5746_:
{
lean_object* v_modified_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; uint64_t v___x_5752_; lean_object* v___x_5754_; 
v_modified_5749_ = lean_ctor_get(v_a_5745_, 1);
lean_inc_ref(v_modified_5749_);
lean_dec(v_a_5745_);
v___x_5750_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_5751_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_5751_, 0, v_info_5740_);
lean_ctor_set(v___x_5751_, 1, v___x_5750_);
lean_ctor_set(v___x_5751_, 2, v_modified_5749_);
v___x_5752_ = lean_unbox_uint64(v_a_5743_);
lean_dec(v_a_5743_);
lean_ctor_set_uint64(v___x_5751_, sizeof(void*)*3, v___x_5752_);
if (v_isShared_5748_ == 0)
{
lean_ctor_set(v___x_5747_, 0, v___x_5751_);
v___x_5754_ = v___x_5747_;
goto v_reusejp_5753_;
}
else
{
lean_object* v_reuseFailAlloc_5755_; 
v_reuseFailAlloc_5755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5755_, 0, v___x_5751_);
v___x_5754_ = v_reuseFailAlloc_5755_;
goto v_reusejp_5753_;
}
v_reusejp_5753_:
{
return v___x_5754_;
}
}
}
else
{
lean_object* v_a_5757_; lean_object* v___x_5759_; uint8_t v_isShared_5760_; uint8_t v_isSharedCheck_5764_; 
lean_dec(v_a_5743_);
lean_dec_ref(v_info_5740_);
v_a_5757_ = lean_ctor_get(v___x_5744_, 0);
v_isSharedCheck_5764_ = !lean_is_exclusive(v___x_5744_);
if (v_isSharedCheck_5764_ == 0)
{
v___x_5759_ = v___x_5744_;
v_isShared_5760_ = v_isSharedCheck_5764_;
goto v_resetjp_5758_;
}
else
{
lean_inc(v_a_5757_);
lean_dec(v___x_5744_);
v___x_5759_ = lean_box(0);
v_isShared_5760_ = v_isSharedCheck_5764_;
goto v_resetjp_5758_;
}
v_resetjp_5758_:
{
lean_object* v___x_5762_; 
if (v_isShared_5760_ == 0)
{
v___x_5762_ = v___x_5759_;
goto v_reusejp_5761_;
}
else
{
lean_object* v_reuseFailAlloc_5763_; 
v_reuseFailAlloc_5763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5763_, 0, v_a_5757_);
v___x_5762_ = v_reuseFailAlloc_5763_;
goto v_reusejp_5761_;
}
v_reusejp_5761_:
{
return v___x_5762_;
}
}
}
}
else
{
lean_object* v_a_5765_; lean_object* v___x_5767_; uint8_t v_isShared_5768_; uint8_t v_isSharedCheck_5772_; 
lean_dec_ref(v_info_5740_);
v_a_5765_ = lean_ctor_get(v___x_5742_, 0);
v_isSharedCheck_5772_ = !lean_is_exclusive(v___x_5742_);
if (v_isSharedCheck_5772_ == 0)
{
v___x_5767_ = v___x_5742_;
v_isShared_5768_ = v_isSharedCheck_5772_;
goto v_resetjp_5766_;
}
else
{
lean_inc(v_a_5765_);
lean_dec(v___x_5742_);
v___x_5767_ = lean_box(0);
v_isShared_5768_ = v_isSharedCheck_5772_;
goto v_resetjp_5766_;
}
v_resetjp_5766_:
{
lean_object* v___x_5770_; 
if (v_isShared_5768_ == 0)
{
v___x_5770_ = v___x_5767_;
goto v_reusejp_5769_;
}
else
{
lean_object* v_reuseFailAlloc_5771_; 
v_reuseFailAlloc_5771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5771_, 0, v_a_5765_);
v___x_5770_ = v_reuseFailAlloc_5771_;
goto v_reusejp_5769_;
}
v_reusejp_5769_:
{
return v___x_5770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0___boxed(lean_object* v_info_5773_, lean_object* v_a_5774_){
_start:
{
lean_object* v_res_5775_; 
v_res_5775_ = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(v_info_5773_);
return v_res_5775_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0(lean_object* v_path_5776_, lean_object* v___y_5777_, lean_object* v___y_5778_, lean_object* v___y_5779_, lean_object* v___y_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_){
_start:
{
lean_object* v_log_5784_; uint8_t v_action_5785_; uint8_t v_wantsRebuild_5786_; lean_object* v_trace_5787_; lean_object* v_buildTime_5788_; lean_object* v___x_5790_; uint8_t v_isShared_5791_; uint8_t v_isSharedCheck_5808_; 
v_log_5784_ = lean_ctor_get(v___y_5782_, 0);
v_action_5785_ = lean_ctor_get_uint8(v___y_5782_, sizeof(void*)*3);
v_wantsRebuild_5786_ = lean_ctor_get_uint8(v___y_5782_, sizeof(void*)*3 + 1);
v_trace_5787_ = lean_ctor_get(v___y_5782_, 1);
v_buildTime_5788_ = lean_ctor_get(v___y_5782_, 2);
v_isSharedCheck_5808_ = !lean_is_exclusive(v___y_5782_);
if (v_isSharedCheck_5808_ == 0)
{
v___x_5790_ = v___y_5782_;
v_isShared_5791_ = v_isSharedCheck_5808_;
goto v_resetjp_5789_;
}
else
{
lean_inc(v_buildTime_5788_);
lean_inc(v_trace_5787_);
lean_inc(v_log_5784_);
lean_dec(v___y_5782_);
v___x_5790_ = lean_box(0);
v_isShared_5791_ = v_isSharedCheck_5808_;
goto v_resetjp_5789_;
}
v_resetjp_5789_:
{
lean_object* v___x_5792_; 
lean_inc_ref(v_path_5776_);
v___x_5792_ = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(v_path_5776_);
if (lean_obj_tag(v___x_5792_) == 0)
{
lean_object* v_a_5793_; lean_object* v___x_5795_; 
lean_dec_ref(v_trace_5787_);
v_a_5793_ = lean_ctor_get(v___x_5792_, 0);
lean_inc(v_a_5793_);
lean_dec_ref_known(v___x_5792_, 1);
if (v_isShared_5791_ == 0)
{
lean_ctor_set(v___x_5790_, 1, v_a_5793_);
v___x_5795_ = v___x_5790_;
goto v_reusejp_5794_;
}
else
{
lean_object* v_reuseFailAlloc_5797_; 
v_reuseFailAlloc_5797_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5797_, 0, v_log_5784_);
lean_ctor_set(v_reuseFailAlloc_5797_, 1, v_a_5793_);
lean_ctor_set(v_reuseFailAlloc_5797_, 2, v_buildTime_5788_);
lean_ctor_set_uint8(v_reuseFailAlloc_5797_, sizeof(void*)*3, v_action_5785_);
lean_ctor_set_uint8(v_reuseFailAlloc_5797_, sizeof(void*)*3 + 1, v_wantsRebuild_5786_);
v___x_5795_ = v_reuseFailAlloc_5797_;
goto v_reusejp_5794_;
}
v_reusejp_5794_:
{
lean_object* v___x_5796_; 
v___x_5796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5796_, 0, v_path_5776_);
lean_ctor_set(v___x_5796_, 1, v___x_5795_);
return v___x_5796_;
}
}
else
{
lean_object* v_a_5798_; lean_object* v___x_5799_; uint8_t v___x_5800_; lean_object* v___x_5801_; lean_object* v___x_5802_; lean_object* v___x_5803_; lean_object* v___x_5805_; 
lean_dec_ref(v_path_5776_);
v_a_5798_ = lean_ctor_get(v___x_5792_, 0);
lean_inc(v_a_5798_);
lean_dec_ref_known(v___x_5792_, 1);
v___x_5799_ = lean_io_error_to_string(v_a_5798_);
v___x_5800_ = 3;
v___x_5801_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5801_, 0, v___x_5799_);
lean_ctor_set_uint8(v___x_5801_, sizeof(void*)*1, v___x_5800_);
v___x_5802_ = lean_array_get_size(v_log_5784_);
v___x_5803_ = lean_array_push(v_log_5784_, v___x_5801_);
if (v_isShared_5791_ == 0)
{
lean_ctor_set(v___x_5790_, 0, v___x_5803_);
v___x_5805_ = v___x_5790_;
goto v_reusejp_5804_;
}
else
{
lean_object* v_reuseFailAlloc_5807_; 
v_reuseFailAlloc_5807_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5807_, 0, v___x_5803_);
lean_ctor_set(v_reuseFailAlloc_5807_, 1, v_trace_5787_);
lean_ctor_set(v_reuseFailAlloc_5807_, 2, v_buildTime_5788_);
lean_ctor_set_uint8(v_reuseFailAlloc_5807_, sizeof(void*)*3, v_action_5785_);
lean_ctor_set_uint8(v_reuseFailAlloc_5807_, sizeof(void*)*3 + 1, v_wantsRebuild_5786_);
v___x_5805_ = v_reuseFailAlloc_5807_;
goto v_reusejp_5804_;
}
v_reusejp_5804_:
{
lean_object* v___x_5806_; 
v___x_5806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5806_, 0, v___x_5802_);
lean_ctor_set(v___x_5806_, 1, v___x_5805_);
return v___x_5806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0___boxed(lean_object* v_path_5809_, lean_object* v___y_5810_, lean_object* v___y_5811_, lean_object* v___y_5812_, lean_object* v___y_5813_, lean_object* v___y_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_){
_start:
{
lean_object* v_res_5817_; 
v_res_5817_ = l_Lake_inputBinFile___redArg___lam__0(v_path_5809_, v___y_5810_, v___y_5811_, v___y_5812_, v___y_5813_, v___y_5814_, v___y_5815_);
lean_dec_ref(v___y_5814_);
lean_dec(v___y_5813_);
lean_dec(v___y_5812_);
lean_dec(v___y_5811_);
lean_dec_ref(v___y_5810_);
return v_res_5817_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg(lean_object* v_path_5819_, lean_object* v_a_5820_, lean_object* v_a_5821_, lean_object* v_a_5822_, lean_object* v_a_5823_, lean_object* v_a_5824_){
_start:
{
lean_object* v___f_5826_; lean_object* v___x_5827_; lean_object* v___x_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; 
v___f_5826_ = lean_alloc_closure((void*)(l_Lake_inputBinFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5826_, 0, v_path_5819_);
v___x_5827_ = l_Lake_instDataKindFilePath;
v___x_5828_ = lean_unsigned_to_nat(0u);
v___x_5829_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
v___x_5830_ = l_Lake_Job_async___redArg(v___x_5827_, v___f_5826_, v___x_5828_, v___x_5829_, v_a_5820_, v_a_5821_, v_a_5822_, v_a_5823_, v_a_5824_);
return v___x_5830_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___boxed(lean_object* v_path_5831_, lean_object* v_a_5832_, lean_object* v_a_5833_, lean_object* v_a_5834_, lean_object* v_a_5835_, lean_object* v_a_5836_, lean_object* v_a_5837_){
_start:
{
lean_object* v_res_5838_; 
v_res_5838_ = l_Lake_inputBinFile___redArg(v_path_5831_, v_a_5832_, v_a_5833_, v_a_5834_, v_a_5835_, v_a_5836_);
lean_dec_ref(v_a_5836_);
lean_dec(v_a_5835_);
lean_dec(v_a_5834_);
lean_dec(v_a_5833_);
return v_res_5838_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object* v_path_5839_, lean_object* v_a_5840_, lean_object* v_a_5841_, lean_object* v_a_5842_, lean_object* v_a_5843_, lean_object* v_a_5844_, lean_object* v_a_5845_){
_start:
{
lean_object* v___x_5847_; 
v___x_5847_ = l_Lake_inputBinFile___redArg(v_path_5839_, v_a_5840_, v_a_5841_, v_a_5842_, v_a_5843_, v_a_5844_);
return v___x_5847_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___boxed(lean_object* v_path_5848_, lean_object* v_a_5849_, lean_object* v_a_5850_, lean_object* v_a_5851_, lean_object* v_a_5852_, lean_object* v_a_5853_, lean_object* v_a_5854_, lean_object* v_a_5855_){
_start:
{
lean_object* v_res_5856_; 
v_res_5856_ = l_Lake_inputBinFile(v_path_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_);
lean_dec_ref(v_a_5854_);
lean_dec_ref(v_a_5853_);
lean_dec(v_a_5852_);
lean_dec(v_a_5851_);
lean_dec(v_a_5850_);
return v_res_5856_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(lean_object* v_info_5857_){
_start:
{
lean_object* v___x_5859_; 
v___x_5859_ = l_Lake_computeTextFileHash(v_info_5857_);
if (lean_obj_tag(v___x_5859_) == 0)
{
lean_object* v_a_5860_; lean_object* v___x_5861_; 
v_a_5860_ = lean_ctor_get(v___x_5859_, 0);
lean_inc(v_a_5860_);
lean_dec_ref_known(v___x_5859_, 1);
v___x_5861_ = lean_io_metadata(v_info_5857_);
if (lean_obj_tag(v___x_5861_) == 0)
{
lean_object* v_a_5862_; lean_object* v___x_5864_; uint8_t v_isShared_5865_; uint8_t v_isSharedCheck_5873_; 
v_a_5862_ = lean_ctor_get(v___x_5861_, 0);
v_isSharedCheck_5873_ = !lean_is_exclusive(v___x_5861_);
if (v_isSharedCheck_5873_ == 0)
{
v___x_5864_ = v___x_5861_;
v_isShared_5865_ = v_isSharedCheck_5873_;
goto v_resetjp_5863_;
}
else
{
lean_inc(v_a_5862_);
lean_dec(v___x_5861_);
v___x_5864_ = lean_box(0);
v_isShared_5865_ = v_isSharedCheck_5873_;
goto v_resetjp_5863_;
}
v_resetjp_5863_:
{
lean_object* v_modified_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; uint64_t v___x_5869_; lean_object* v___x_5871_; 
v_modified_5866_ = lean_ctor_get(v_a_5862_, 1);
lean_inc_ref(v_modified_5866_);
lean_dec(v_a_5862_);
v___x_5867_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_5868_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_5868_, 0, v_info_5857_);
lean_ctor_set(v___x_5868_, 1, v___x_5867_);
lean_ctor_set(v___x_5868_, 2, v_modified_5866_);
v___x_5869_ = lean_unbox_uint64(v_a_5860_);
lean_dec(v_a_5860_);
lean_ctor_set_uint64(v___x_5868_, sizeof(void*)*3, v___x_5869_);
if (v_isShared_5865_ == 0)
{
lean_ctor_set(v___x_5864_, 0, v___x_5868_);
v___x_5871_ = v___x_5864_;
goto v_reusejp_5870_;
}
else
{
lean_object* v_reuseFailAlloc_5872_; 
v_reuseFailAlloc_5872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5872_, 0, v___x_5868_);
v___x_5871_ = v_reuseFailAlloc_5872_;
goto v_reusejp_5870_;
}
v_reusejp_5870_:
{
return v___x_5871_;
}
}
}
else
{
lean_object* v_a_5874_; lean_object* v___x_5876_; uint8_t v_isShared_5877_; uint8_t v_isSharedCheck_5881_; 
lean_dec(v_a_5860_);
lean_dec_ref(v_info_5857_);
v_a_5874_ = lean_ctor_get(v___x_5861_, 0);
v_isSharedCheck_5881_ = !lean_is_exclusive(v___x_5861_);
if (v_isSharedCheck_5881_ == 0)
{
v___x_5876_ = v___x_5861_;
v_isShared_5877_ = v_isSharedCheck_5881_;
goto v_resetjp_5875_;
}
else
{
lean_inc(v_a_5874_);
lean_dec(v___x_5861_);
v___x_5876_ = lean_box(0);
v_isShared_5877_ = v_isSharedCheck_5881_;
goto v_resetjp_5875_;
}
v_resetjp_5875_:
{
lean_object* v___x_5879_; 
if (v_isShared_5877_ == 0)
{
v___x_5879_ = v___x_5876_;
goto v_reusejp_5878_;
}
else
{
lean_object* v_reuseFailAlloc_5880_; 
v_reuseFailAlloc_5880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5880_, 0, v_a_5874_);
v___x_5879_ = v_reuseFailAlloc_5880_;
goto v_reusejp_5878_;
}
v_reusejp_5878_:
{
return v___x_5879_;
}
}
}
}
else
{
lean_object* v_a_5882_; lean_object* v___x_5884_; uint8_t v_isShared_5885_; uint8_t v_isSharedCheck_5889_; 
lean_dec_ref(v_info_5857_);
v_a_5882_ = lean_ctor_get(v___x_5859_, 0);
v_isSharedCheck_5889_ = !lean_is_exclusive(v___x_5859_);
if (v_isSharedCheck_5889_ == 0)
{
v___x_5884_ = v___x_5859_;
v_isShared_5885_ = v_isSharedCheck_5889_;
goto v_resetjp_5883_;
}
else
{
lean_inc(v_a_5882_);
lean_dec(v___x_5859_);
v___x_5884_ = lean_box(0);
v_isShared_5885_ = v_isSharedCheck_5889_;
goto v_resetjp_5883_;
}
v_resetjp_5883_:
{
lean_object* v___x_5887_; 
if (v_isShared_5885_ == 0)
{
v___x_5887_ = v___x_5884_;
goto v_reusejp_5886_;
}
else
{
lean_object* v_reuseFailAlloc_5888_; 
v_reuseFailAlloc_5888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5888_, 0, v_a_5882_);
v___x_5887_ = v_reuseFailAlloc_5888_;
goto v_reusejp_5886_;
}
v_reusejp_5886_:
{
return v___x_5887_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0___boxed(lean_object* v_info_5890_, lean_object* v_a_5891_){
_start:
{
lean_object* v_res_5892_; 
v_res_5892_ = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(v_info_5890_);
return v_res_5892_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0(lean_object* v_path_5893_, lean_object* v___y_5894_, lean_object* v___y_5895_, lean_object* v___y_5896_, lean_object* v___y_5897_, lean_object* v___y_5898_, lean_object* v___y_5899_){
_start:
{
lean_object* v_log_5901_; uint8_t v_action_5902_; uint8_t v_wantsRebuild_5903_; lean_object* v_trace_5904_; lean_object* v_buildTime_5905_; lean_object* v___x_5907_; uint8_t v_isShared_5908_; uint8_t v_isSharedCheck_5925_; 
v_log_5901_ = lean_ctor_get(v___y_5899_, 0);
v_action_5902_ = lean_ctor_get_uint8(v___y_5899_, sizeof(void*)*3);
v_wantsRebuild_5903_ = lean_ctor_get_uint8(v___y_5899_, sizeof(void*)*3 + 1);
v_trace_5904_ = lean_ctor_get(v___y_5899_, 1);
v_buildTime_5905_ = lean_ctor_get(v___y_5899_, 2);
v_isSharedCheck_5925_ = !lean_is_exclusive(v___y_5899_);
if (v_isSharedCheck_5925_ == 0)
{
v___x_5907_ = v___y_5899_;
v_isShared_5908_ = v_isSharedCheck_5925_;
goto v_resetjp_5906_;
}
else
{
lean_inc(v_buildTime_5905_);
lean_inc(v_trace_5904_);
lean_inc(v_log_5901_);
lean_dec(v___y_5899_);
v___x_5907_ = lean_box(0);
v_isShared_5908_ = v_isSharedCheck_5925_;
goto v_resetjp_5906_;
}
v_resetjp_5906_:
{
lean_object* v___x_5909_; 
lean_inc_ref(v_path_5893_);
v___x_5909_ = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(v_path_5893_);
if (lean_obj_tag(v___x_5909_) == 0)
{
lean_object* v_a_5910_; lean_object* v___x_5912_; 
lean_dec_ref(v_trace_5904_);
v_a_5910_ = lean_ctor_get(v___x_5909_, 0);
lean_inc(v_a_5910_);
lean_dec_ref_known(v___x_5909_, 1);
if (v_isShared_5908_ == 0)
{
lean_ctor_set(v___x_5907_, 1, v_a_5910_);
v___x_5912_ = v___x_5907_;
goto v_reusejp_5911_;
}
else
{
lean_object* v_reuseFailAlloc_5914_; 
v_reuseFailAlloc_5914_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5914_, 0, v_log_5901_);
lean_ctor_set(v_reuseFailAlloc_5914_, 1, v_a_5910_);
lean_ctor_set(v_reuseFailAlloc_5914_, 2, v_buildTime_5905_);
lean_ctor_set_uint8(v_reuseFailAlloc_5914_, sizeof(void*)*3, v_action_5902_);
lean_ctor_set_uint8(v_reuseFailAlloc_5914_, sizeof(void*)*3 + 1, v_wantsRebuild_5903_);
v___x_5912_ = v_reuseFailAlloc_5914_;
goto v_reusejp_5911_;
}
v_reusejp_5911_:
{
lean_object* v___x_5913_; 
v___x_5913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5913_, 0, v_path_5893_);
lean_ctor_set(v___x_5913_, 1, v___x_5912_);
return v___x_5913_;
}
}
else
{
lean_object* v_a_5915_; lean_object* v___x_5916_; uint8_t v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5922_; 
lean_dec_ref(v_path_5893_);
v_a_5915_ = lean_ctor_get(v___x_5909_, 0);
lean_inc(v_a_5915_);
lean_dec_ref_known(v___x_5909_, 1);
v___x_5916_ = lean_io_error_to_string(v_a_5915_);
v___x_5917_ = 3;
v___x_5918_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5918_, 0, v___x_5916_);
lean_ctor_set_uint8(v___x_5918_, sizeof(void*)*1, v___x_5917_);
v___x_5919_ = lean_array_get_size(v_log_5901_);
v___x_5920_ = lean_array_push(v_log_5901_, v___x_5918_);
if (v_isShared_5908_ == 0)
{
lean_ctor_set(v___x_5907_, 0, v___x_5920_);
v___x_5922_ = v___x_5907_;
goto v_reusejp_5921_;
}
else
{
lean_object* v_reuseFailAlloc_5924_; 
v_reuseFailAlloc_5924_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5924_, 0, v___x_5920_);
lean_ctor_set(v_reuseFailAlloc_5924_, 1, v_trace_5904_);
lean_ctor_set(v_reuseFailAlloc_5924_, 2, v_buildTime_5905_);
lean_ctor_set_uint8(v_reuseFailAlloc_5924_, sizeof(void*)*3, v_action_5902_);
lean_ctor_set_uint8(v_reuseFailAlloc_5924_, sizeof(void*)*3 + 1, v_wantsRebuild_5903_);
v___x_5922_ = v_reuseFailAlloc_5924_;
goto v_reusejp_5921_;
}
v_reusejp_5921_:
{
lean_object* v___x_5923_; 
v___x_5923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5923_, 0, v___x_5919_);
lean_ctor_set(v___x_5923_, 1, v___x_5922_);
return v___x_5923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0___boxed(lean_object* v_path_5926_, lean_object* v___y_5927_, lean_object* v___y_5928_, lean_object* v___y_5929_, lean_object* v___y_5930_, lean_object* v___y_5931_, lean_object* v___y_5932_, lean_object* v___y_5933_){
_start:
{
lean_object* v_res_5934_; 
v_res_5934_ = l_Lake_inputTextFile___redArg___lam__0(v_path_5926_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_);
lean_dec_ref(v___y_5931_);
lean_dec(v___y_5930_);
lean_dec(v___y_5929_);
lean_dec(v___y_5928_);
lean_dec_ref(v___y_5927_);
return v_res_5934_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg(lean_object* v_path_5935_, lean_object* v_a_5936_, lean_object* v_a_5937_, lean_object* v_a_5938_, lean_object* v_a_5939_, lean_object* v_a_5940_){
_start:
{
lean_object* v___f_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; 
v___f_5942_ = lean_alloc_closure((void*)(l_Lake_inputTextFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5942_, 0, v_path_5935_);
v___x_5943_ = l_Lake_instDataKindFilePath;
v___x_5944_ = lean_unsigned_to_nat(0u);
v___x_5945_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
v___x_5946_ = l_Lake_Job_async___redArg(v___x_5943_, v___f_5942_, v___x_5944_, v___x_5945_, v_a_5936_, v_a_5937_, v_a_5938_, v_a_5939_, v_a_5940_);
return v___x_5946_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___boxed(lean_object* v_path_5947_, lean_object* v_a_5948_, lean_object* v_a_5949_, lean_object* v_a_5950_, lean_object* v_a_5951_, lean_object* v_a_5952_, lean_object* v_a_5953_){
_start:
{
lean_object* v_res_5954_; 
v_res_5954_ = l_Lake_inputTextFile___redArg(v_path_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_);
lean_dec_ref(v_a_5952_);
lean_dec(v_a_5951_);
lean_dec(v_a_5950_);
lean_dec(v_a_5949_);
return v_res_5954_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object* v_path_5955_, lean_object* v_a_5956_, lean_object* v_a_5957_, lean_object* v_a_5958_, lean_object* v_a_5959_, lean_object* v_a_5960_, lean_object* v_a_5961_){
_start:
{
lean_object* v___x_5963_; 
v___x_5963_ = l_Lake_inputTextFile___redArg(v_path_5955_, v_a_5956_, v_a_5957_, v_a_5958_, v_a_5959_, v_a_5960_);
return v___x_5963_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___boxed(lean_object* v_path_5964_, lean_object* v_a_5965_, lean_object* v_a_5966_, lean_object* v_a_5967_, lean_object* v_a_5968_, lean_object* v_a_5969_, lean_object* v_a_5970_, lean_object* v_a_5971_){
_start:
{
lean_object* v_res_5972_; 
v_res_5972_ = l_Lake_inputTextFile(v_path_5964_, v_a_5965_, v_a_5966_, v_a_5967_, v_a_5968_, v_a_5969_, v_a_5970_);
lean_dec_ref(v_a_5970_);
lean_dec_ref(v_a_5969_);
lean_dec(v_a_5968_);
lean_dec(v_a_5967_);
lean_dec(v_a_5966_);
return v_res_5972_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg(lean_object* v_path_5973_, uint8_t v_text_5974_, lean_object* v_a_5975_, lean_object* v_a_5976_, lean_object* v_a_5977_, lean_object* v_a_5978_, lean_object* v_a_5979_){
_start:
{
if (v_text_5974_ == 0)
{
lean_object* v___x_5981_; 
v___x_5981_ = l_Lake_inputBinFile___redArg(v_path_5973_, v_a_5975_, v_a_5976_, v_a_5977_, v_a_5978_, v_a_5979_);
return v___x_5981_;
}
else
{
lean_object* v___x_5982_; 
v___x_5982_ = l_Lake_inputTextFile___redArg(v_path_5973_, v_a_5975_, v_a_5976_, v_a_5977_, v_a_5978_, v_a_5979_);
return v___x_5982_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg___boxed(lean_object* v_path_5983_, lean_object* v_text_5984_, lean_object* v_a_5985_, lean_object* v_a_5986_, lean_object* v_a_5987_, lean_object* v_a_5988_, lean_object* v_a_5989_, lean_object* v_a_5990_){
_start:
{
uint8_t v_text_boxed_5991_; lean_object* v_res_5992_; 
v_text_boxed_5991_ = lean_unbox(v_text_5984_);
v_res_5992_ = l_Lake_inputFile___redArg(v_path_5983_, v_text_boxed_5991_, v_a_5985_, v_a_5986_, v_a_5987_, v_a_5988_, v_a_5989_);
lean_dec_ref(v_a_5989_);
lean_dec(v_a_5988_);
lean_dec(v_a_5987_);
lean_dec(v_a_5986_);
return v_res_5992_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object* v_path_5993_, uint8_t v_text_5994_, lean_object* v_a_5995_, lean_object* v_a_5996_, lean_object* v_a_5997_, lean_object* v_a_5998_, lean_object* v_a_5999_, lean_object* v_a_6000_){
_start:
{
if (v_text_5994_ == 0)
{
lean_object* v___x_6002_; 
v___x_6002_ = l_Lake_inputBinFile___redArg(v_path_5993_, v_a_5995_, v_a_5996_, v_a_5997_, v_a_5998_, v_a_5999_);
return v___x_6002_;
}
else
{
lean_object* v___x_6003_; 
v___x_6003_ = l_Lake_inputTextFile___redArg(v_path_5993_, v_a_5995_, v_a_5996_, v_a_5997_, v_a_5998_, v_a_5999_);
return v___x_6003_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object* v_path_6004_, lean_object* v_text_6005_, lean_object* v_a_6006_, lean_object* v_a_6007_, lean_object* v_a_6008_, lean_object* v_a_6009_, lean_object* v_a_6010_, lean_object* v_a_6011_, lean_object* v_a_6012_){
_start:
{
uint8_t v_text_boxed_6013_; lean_object* v_res_6014_; 
v_text_boxed_6013_ = lean_unbox(v_text_6005_);
v_res_6014_ = l_Lake_inputFile(v_path_6004_, v_text_boxed_6013_, v_a_6006_, v_a_6007_, v_a_6008_, v_a_6009_, v_a_6010_, v_a_6011_);
lean_dec_ref(v_a_6011_);
lean_dec_ref(v_a_6010_);
lean_dec(v_a_6009_);
lean_dec(v_a_6008_);
lean_dec(v_a_6007_);
return v_res_6014_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0(lean_object* v_x_6015_){
_start:
{
uint8_t v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; 
v___x_6017_ = 1;
v___x_6018_ = lean_box(v___x_6017_);
v___x_6019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6019_, 0, v___x_6018_);
return v___x_6019_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0___boxed(lean_object* v_x_6020_, lean_object* v___y_6021_){
_start:
{
lean_object* v_res_6022_; 
v_res_6022_ = l_Lake_inputDir___lam__0(v_x_6020_);
lean_dec_ref(v_x_6020_);
return v_res_6022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(lean_object* v_filter_6023_, lean_object* v_as_6024_, size_t v_i_6025_, size_t v_stop_6026_, lean_object* v_b_6027_, lean_object* v___y_6028_){
_start:
{
lean_object* v_a_6031_; lean_object* v_a_6032_; uint8_t v___x_6036_; 
v___x_6036_ = lean_usize_dec_eq(v_i_6025_, v_stop_6026_);
if (v___x_6036_ == 0)
{
lean_object* v___x_6037_; uint8_t v___x_6038_; 
v___x_6037_ = lean_array_uget_borrowed(v_as_6024_, v_i_6025_);
v___x_6038_ = l_System_FilePath_isDir(v___x_6037_);
if (v___x_6038_ == 0)
{
lean_object* v___x_6039_; uint8_t v___x_6040_; 
lean_inc_ref(v_filter_6023_);
lean_inc(v___x_6037_);
v___x_6039_ = lean_apply_1(v_filter_6023_, v___x_6037_);
v___x_6040_ = lean_unbox(v___x_6039_);
if (v___x_6040_ == 0)
{
v_a_6031_ = v_b_6027_;
v_a_6032_ = v___y_6028_;
goto v___jp_6030_;
}
else
{
lean_object* v___x_6041_; 
lean_inc(v___x_6037_);
v___x_6041_ = lean_array_push(v_b_6027_, v___x_6037_);
v_a_6031_ = v___x_6041_;
v_a_6032_ = v___y_6028_;
goto v___jp_6030_;
}
}
else
{
v_a_6031_ = v_b_6027_;
v_a_6032_ = v___y_6028_;
goto v___jp_6030_;
}
}
else
{
lean_object* v___x_6042_; 
lean_dec_ref(v_filter_6023_);
v___x_6042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6042_, 0, v_b_6027_);
lean_ctor_set(v___x_6042_, 1, v___y_6028_);
return v___x_6042_;
}
v___jp_6030_:
{
size_t v___x_6033_; size_t v___x_6034_; 
v___x_6033_ = ((size_t)1ULL);
v___x_6034_ = lean_usize_add(v_i_6025_, v___x_6033_);
v_i_6025_ = v___x_6034_;
v_b_6027_ = v_a_6031_;
v___y_6028_ = v_a_6032_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg___boxed(lean_object* v_filter_6043_, lean_object* v_as_6044_, lean_object* v_i_6045_, lean_object* v_stop_6046_, lean_object* v_b_6047_, lean_object* v___y_6048_, lean_object* v___y_6049_){
_start:
{
size_t v_i_boxed_6050_; size_t v_stop_boxed_6051_; lean_object* v_res_6052_; 
v_i_boxed_6050_ = lean_unbox_usize(v_i_6045_);
lean_dec(v_i_6045_);
v_stop_boxed_6051_ = lean_unbox_usize(v_stop_6046_);
lean_dec(v_stop_6046_);
v_res_6052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6043_, v_as_6044_, v_i_boxed_6050_, v_stop_boxed_6051_, v_b_6047_, v___y_6048_);
lean_dec_ref(v_as_6044_);
return v_res_6052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(lean_object* v_hi_6053_, lean_object* v_pivot_6054_, lean_object* v_as_6055_, lean_object* v_i_6056_, lean_object* v_k_6057_){
_start:
{
uint8_t v___x_6058_; 
v___x_6058_ = lean_nat_dec_lt(v_k_6057_, v_hi_6053_);
if (v___x_6058_ == 0)
{
lean_object* v___x_6059_; lean_object* v___x_6060_; 
lean_dec(v_k_6057_);
v___x_6059_ = lean_array_fswap(v_as_6055_, v_i_6056_, v_hi_6053_);
v___x_6060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6060_, 0, v_i_6056_);
lean_ctor_set(v___x_6060_, 1, v___x_6059_);
return v___x_6060_;
}
else
{
lean_object* v___x_6061_; uint8_t v___x_6062_; 
v___x_6061_ = lean_array_fget_borrowed(v_as_6055_, v_k_6057_);
v___x_6062_ = lean_string_dec_lt(v___x_6061_, v_pivot_6054_);
if (v___x_6062_ == 0)
{
lean_object* v___x_6063_; lean_object* v___x_6064_; 
v___x_6063_ = lean_unsigned_to_nat(1u);
v___x_6064_ = lean_nat_add(v_k_6057_, v___x_6063_);
lean_dec(v_k_6057_);
v_k_6057_ = v___x_6064_;
goto _start;
}
else
{
lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; 
v___x_6066_ = lean_array_fswap(v_as_6055_, v_i_6056_, v_k_6057_);
v___x_6067_ = lean_unsigned_to_nat(1u);
v___x_6068_ = lean_nat_add(v_i_6056_, v___x_6067_);
lean_dec(v_i_6056_);
v___x_6069_ = lean_nat_add(v_k_6057_, v___x_6067_);
lean_dec(v_k_6057_);
v_as_6055_ = v___x_6066_;
v_i_6056_ = v___x_6068_;
v_k_6057_ = v___x_6069_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg___boxed(lean_object* v_hi_6071_, lean_object* v_pivot_6072_, lean_object* v_as_6073_, lean_object* v_i_6074_, lean_object* v_k_6075_){
_start:
{
lean_object* v_res_6076_; 
v_res_6076_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(v_hi_6071_, v_pivot_6072_, v_as_6073_, v_i_6074_, v_k_6075_);
lean_dec_ref(v_pivot_6072_);
lean_dec(v_hi_6071_);
return v_res_6076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(lean_object* v_n_6077_, lean_object* v_as_6078_, lean_object* v_lo_6079_, lean_object* v_hi_6080_){
_start:
{
lean_object* v___y_6082_; uint8_t v___x_6092_; 
v___x_6092_ = lean_nat_dec_lt(v_lo_6079_, v_hi_6080_);
if (v___x_6092_ == 0)
{
lean_dec(v_lo_6079_);
return v_as_6078_;
}
else
{
lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v_mid_6095_; lean_object* v___y_6097_; lean_object* v___y_6103_; lean_object* v___x_6108_; lean_object* v___x_6109_; uint8_t v___x_6110_; 
v___x_6093_ = lean_nat_add(v_lo_6079_, v_hi_6080_);
v___x_6094_ = lean_unsigned_to_nat(1u);
v_mid_6095_ = lean_nat_shiftr(v___x_6093_, v___x_6094_);
lean_dec(v___x_6093_);
v___x_6108_ = lean_array_fget_borrowed(v_as_6078_, v_mid_6095_);
v___x_6109_ = lean_array_fget_borrowed(v_as_6078_, v_lo_6079_);
v___x_6110_ = lean_string_dec_lt(v___x_6108_, v___x_6109_);
if (v___x_6110_ == 0)
{
v___y_6103_ = v_as_6078_;
goto v___jp_6102_;
}
else
{
lean_object* v___x_6111_; 
v___x_6111_ = lean_array_fswap(v_as_6078_, v_lo_6079_, v_mid_6095_);
v___y_6103_ = v___x_6111_;
goto v___jp_6102_;
}
v___jp_6096_:
{
lean_object* v___x_6098_; lean_object* v___x_6099_; uint8_t v___x_6100_; 
v___x_6098_ = lean_array_fget_borrowed(v___y_6097_, v_mid_6095_);
v___x_6099_ = lean_array_fget_borrowed(v___y_6097_, v_hi_6080_);
v___x_6100_ = lean_string_dec_lt(v___x_6098_, v___x_6099_);
if (v___x_6100_ == 0)
{
lean_dec(v_mid_6095_);
v___y_6082_ = v___y_6097_;
goto v___jp_6081_;
}
else
{
lean_object* v___x_6101_; 
v___x_6101_ = lean_array_fswap(v___y_6097_, v_mid_6095_, v_hi_6080_);
lean_dec(v_mid_6095_);
v___y_6082_ = v___x_6101_;
goto v___jp_6081_;
}
}
v___jp_6102_:
{
lean_object* v___x_6104_; lean_object* v___x_6105_; uint8_t v___x_6106_; 
v___x_6104_ = lean_array_fget_borrowed(v___y_6103_, v_hi_6080_);
v___x_6105_ = lean_array_fget_borrowed(v___y_6103_, v_lo_6079_);
v___x_6106_ = lean_string_dec_lt(v___x_6104_, v___x_6105_);
if (v___x_6106_ == 0)
{
v___y_6097_ = v___y_6103_;
goto v___jp_6096_;
}
else
{
lean_object* v___x_6107_; 
v___x_6107_ = lean_array_fswap(v___y_6103_, v_lo_6079_, v_hi_6080_);
v___y_6097_ = v___x_6107_;
goto v___jp_6096_;
}
}
}
v___jp_6081_:
{
lean_object* v_pivot_6083_; lean_object* v___x_6084_; lean_object* v_fst_6085_; lean_object* v_snd_6086_; uint8_t v___x_6087_; 
v_pivot_6083_ = lean_array_fget(v___y_6082_, v_hi_6080_);
lean_inc_n(v_lo_6079_, 2);
v___x_6084_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(v_hi_6080_, v_pivot_6083_, v___y_6082_, v_lo_6079_, v_lo_6079_);
lean_dec(v_pivot_6083_);
v_fst_6085_ = lean_ctor_get(v___x_6084_, 0);
lean_inc(v_fst_6085_);
v_snd_6086_ = lean_ctor_get(v___x_6084_, 1);
lean_inc(v_snd_6086_);
lean_dec_ref(v___x_6084_);
v___x_6087_ = lean_nat_dec_le(v_hi_6080_, v_fst_6085_);
if (v___x_6087_ == 0)
{
lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; 
v___x_6088_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_n_6077_, v_snd_6086_, v_lo_6079_, v_fst_6085_);
v___x_6089_ = lean_unsigned_to_nat(1u);
v___x_6090_ = lean_nat_add(v_fst_6085_, v___x_6089_);
lean_dec(v_fst_6085_);
v_as_6078_ = v___x_6088_;
v_lo_6079_ = v___x_6090_;
goto _start;
}
else
{
lean_dec(v_fst_6085_);
lean_dec(v_lo_6079_);
return v_snd_6086_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___boxed(lean_object* v_n_6112_, lean_object* v_as_6113_, lean_object* v_lo_6114_, lean_object* v_hi_6115_){
_start:
{
lean_object* v_res_6116_; 
v_res_6116_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_n_6112_, v_as_6113_, v_lo_6114_, v_hi_6115_);
lean_dec(v_hi_6115_);
lean_dec(v_n_6112_);
return v_res_6116_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1(lean_object* v_path_6119_, lean_object* v___f_6120_, lean_object* v_filter_6121_, lean_object* v___y_6122_, lean_object* v___y_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_){
_start:
{
lean_object* v___y_6130_; lean_object* v___y_6131_; lean_object* v___y_6134_; lean_object* v___y_6135_; lean_object* v___y_6136_; lean_object* v___y_6137_; lean_object* v___y_6138_; lean_object* v___y_6141_; lean_object* v___y_6142_; lean_object* v___y_6143_; lean_object* v___y_6144_; lean_object* v___y_6145_; lean_object* v_log_6147_; uint8_t v_action_6148_; uint8_t v_wantsRebuild_6149_; lean_object* v_trace_6150_; lean_object* v_buildTime_6151_; lean_object* v___x_6152_; 
v_log_6147_ = lean_ctor_get(v___y_6127_, 0);
v_action_6148_ = lean_ctor_get_uint8(v___y_6127_, sizeof(void*)*3);
v_wantsRebuild_6149_ = lean_ctor_get_uint8(v___y_6127_, sizeof(void*)*3 + 1);
v_trace_6150_ = lean_ctor_get(v___y_6127_, 1);
v_buildTime_6151_ = lean_ctor_get(v___y_6127_, 2);
v___x_6152_ = l_System_FilePath_walkDir(v_path_6119_, v___f_6120_);
if (lean_obj_tag(v___x_6152_) == 0)
{
lean_object* v_a_6153_; lean_object* v___x_6154_; lean_object* v_a_6156_; lean_object* v_a_6157_; lean_object* v___y_6164_; lean_object* v___x_6167_; lean_object* v___x_6168_; uint8_t v___x_6169_; 
v_a_6153_ = lean_ctor_get(v___x_6152_, 0);
lean_inc(v_a_6153_);
lean_dec_ref_known(v___x_6152_, 1);
v___x_6154_ = lean_unsigned_to_nat(0u);
v___x_6167_ = lean_array_get_size(v_a_6153_);
v___x_6168_ = ((lean_object*)(l_Lake_inputDir___lam__1___closed__0));
v___x_6169_ = lean_nat_dec_lt(v___x_6154_, v___x_6167_);
if (v___x_6169_ == 0)
{
lean_dec(v_a_6153_);
lean_dec_ref(v_filter_6121_);
v_a_6156_ = v___x_6168_;
v_a_6157_ = v___y_6127_;
goto v___jp_6155_;
}
else
{
uint8_t v___x_6170_; 
v___x_6170_ = lean_nat_dec_le(v___x_6167_, v___x_6167_);
if (v___x_6170_ == 0)
{
if (v___x_6169_ == 0)
{
lean_dec(v_a_6153_);
lean_dec_ref(v_filter_6121_);
v_a_6156_ = v___x_6168_;
v_a_6157_ = v___y_6127_;
goto v___jp_6155_;
}
else
{
size_t v___x_6171_; size_t v___x_6172_; lean_object* v___x_6173_; 
v___x_6171_ = ((size_t)0ULL);
v___x_6172_ = lean_usize_of_nat(v___x_6167_);
v___x_6173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6121_, v_a_6153_, v___x_6171_, v___x_6172_, v___x_6168_, v___y_6127_);
lean_dec(v_a_6153_);
v___y_6164_ = v___x_6173_;
goto v___jp_6163_;
}
}
else
{
size_t v___x_6174_; size_t v___x_6175_; lean_object* v___x_6176_; 
v___x_6174_ = ((size_t)0ULL);
v___x_6175_ = lean_usize_of_nat(v___x_6167_);
v___x_6176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6121_, v_a_6153_, v___x_6174_, v___x_6175_, v___x_6168_, v___y_6127_);
lean_dec(v_a_6153_);
v___y_6164_ = v___x_6176_;
goto v___jp_6163_;
}
}
v___jp_6155_:
{
lean_object* v___x_6158_; uint8_t v___x_6159_; 
v___x_6158_ = lean_array_get_size(v_a_6156_);
v___x_6159_ = lean_nat_dec_eq(v___x_6158_, v___x_6154_);
if (v___x_6159_ == 0)
{
lean_object* v___x_6160_; lean_object* v___x_6161_; uint8_t v___x_6162_; 
v___x_6160_ = lean_unsigned_to_nat(1u);
v___x_6161_ = lean_nat_sub(v___x_6158_, v___x_6160_);
v___x_6162_ = lean_nat_dec_le(v___x_6154_, v___x_6161_);
if (v___x_6162_ == 0)
{
lean_inc(v___x_6161_);
v___y_6141_ = v_a_6156_;
v___y_6142_ = v___x_6158_;
v___y_6143_ = v___x_6161_;
v___y_6144_ = v_a_6157_;
v___y_6145_ = v___x_6161_;
goto v___jp_6140_;
}
else
{
v___y_6141_ = v_a_6156_;
v___y_6142_ = v___x_6158_;
v___y_6143_ = v___x_6161_;
v___y_6144_ = v_a_6157_;
v___y_6145_ = v___x_6154_;
goto v___jp_6140_;
}
}
else
{
v___y_6130_ = v_a_6157_;
v___y_6131_ = v_a_6156_;
goto v___jp_6129_;
}
}
v___jp_6163_:
{
if (lean_obj_tag(v___y_6164_) == 0)
{
lean_object* v_a_6165_; lean_object* v_a_6166_; 
v_a_6165_ = lean_ctor_get(v___y_6164_, 0);
lean_inc(v_a_6165_);
v_a_6166_ = lean_ctor_get(v___y_6164_, 1);
lean_inc(v_a_6166_);
lean_dec_ref_known(v___y_6164_, 2);
v_a_6156_ = v_a_6165_;
v_a_6157_ = v_a_6166_;
goto v___jp_6155_;
}
else
{
return v___y_6164_;
}
}
}
else
{
lean_object* v___x_6178_; uint8_t v_isShared_6179_; uint8_t v_isSharedCheck_6190_; 
lean_inc(v_buildTime_6151_);
lean_inc_ref(v_trace_6150_);
lean_inc_ref(v_log_6147_);
lean_dec_ref(v_filter_6121_);
v_isSharedCheck_6190_ = !lean_is_exclusive(v___y_6127_);
if (v_isSharedCheck_6190_ == 0)
{
lean_object* v_unused_6191_; lean_object* v_unused_6192_; lean_object* v_unused_6193_; 
v_unused_6191_ = lean_ctor_get(v___y_6127_, 2);
lean_dec(v_unused_6191_);
v_unused_6192_ = lean_ctor_get(v___y_6127_, 1);
lean_dec(v_unused_6192_);
v_unused_6193_ = lean_ctor_get(v___y_6127_, 0);
lean_dec(v_unused_6193_);
v___x_6178_ = v___y_6127_;
v_isShared_6179_ = v_isSharedCheck_6190_;
goto v_resetjp_6177_;
}
else
{
lean_dec(v___y_6127_);
v___x_6178_ = lean_box(0);
v_isShared_6179_ = v_isSharedCheck_6190_;
goto v_resetjp_6177_;
}
v_resetjp_6177_:
{
lean_object* v_a_6180_; lean_object* v___x_6181_; uint8_t v___x_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6187_; 
v_a_6180_ = lean_ctor_get(v___x_6152_, 0);
lean_inc(v_a_6180_);
lean_dec_ref_known(v___x_6152_, 1);
v___x_6181_ = lean_io_error_to_string(v_a_6180_);
v___x_6182_ = 3;
v___x_6183_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6183_, 0, v___x_6181_);
lean_ctor_set_uint8(v___x_6183_, sizeof(void*)*1, v___x_6182_);
v___x_6184_ = lean_array_get_size(v_log_6147_);
v___x_6185_ = lean_array_push(v_log_6147_, v___x_6183_);
if (v_isShared_6179_ == 0)
{
lean_ctor_set(v___x_6178_, 0, v___x_6185_);
v___x_6187_ = v___x_6178_;
goto v_reusejp_6186_;
}
else
{
lean_object* v_reuseFailAlloc_6189_; 
v_reuseFailAlloc_6189_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6189_, 0, v___x_6185_);
lean_ctor_set(v_reuseFailAlloc_6189_, 1, v_trace_6150_);
lean_ctor_set(v_reuseFailAlloc_6189_, 2, v_buildTime_6151_);
lean_ctor_set_uint8(v_reuseFailAlloc_6189_, sizeof(void*)*3, v_action_6148_);
lean_ctor_set_uint8(v_reuseFailAlloc_6189_, sizeof(void*)*3 + 1, v_wantsRebuild_6149_);
v___x_6187_ = v_reuseFailAlloc_6189_;
goto v_reusejp_6186_;
}
v_reusejp_6186_:
{
lean_object* v___x_6188_; 
v___x_6188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6188_, 0, v___x_6184_);
lean_ctor_set(v___x_6188_, 1, v___x_6187_);
return v___x_6188_;
}
}
}
v___jp_6129_:
{
lean_object* v___x_6132_; 
v___x_6132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6132_, 0, v___y_6131_);
lean_ctor_set(v___x_6132_, 1, v___y_6130_);
return v___x_6132_;
}
v___jp_6133_:
{
lean_object* v___x_6139_; 
v___x_6139_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v___y_6135_, v___y_6134_, v___y_6137_, v___y_6138_);
lean_dec(v___y_6138_);
lean_dec(v___y_6135_);
v___y_6130_ = v___y_6136_;
v___y_6131_ = v___x_6139_;
goto v___jp_6129_;
}
v___jp_6140_:
{
uint8_t v___x_6146_; 
v___x_6146_ = lean_nat_dec_le(v___y_6145_, v___y_6143_);
if (v___x_6146_ == 0)
{
lean_dec(v___y_6143_);
lean_inc(v___y_6145_);
v___y_6134_ = v___y_6141_;
v___y_6135_ = v___y_6142_;
v___y_6136_ = v___y_6144_;
v___y_6137_ = v___y_6145_;
v___y_6138_ = v___y_6145_;
goto v___jp_6133_;
}
else
{
v___y_6134_ = v___y_6141_;
v___y_6135_ = v___y_6142_;
v___y_6136_ = v___y_6144_;
v___y_6137_ = v___y_6145_;
v___y_6138_ = v___y_6143_;
goto v___jp_6133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1___boxed(lean_object* v_path_6194_, lean_object* v___f_6195_, lean_object* v_filter_6196_, lean_object* v___y_6197_, lean_object* v___y_6198_, lean_object* v___y_6199_, lean_object* v___y_6200_, lean_object* v___y_6201_, lean_object* v___y_6202_, lean_object* v___y_6203_){
_start:
{
lean_object* v_res_6204_; 
v_res_6204_ = l_Lake_inputDir___lam__1(v_path_6194_, v___f_6195_, v_filter_6196_, v___y_6197_, v___y_6198_, v___y_6199_, v___y_6200_, v___y_6201_, v___y_6202_);
lean_dec_ref(v___y_6201_);
lean_dec(v___y_6200_);
lean_dec(v___y_6199_);
lean_dec(v___y_6198_);
lean_dec_ref(v___y_6197_);
return v_res_6204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(uint8_t v_text_6205_, size_t v_sz_6206_, size_t v_i_6207_, lean_object* v_bs_6208_, lean_object* v___y_6209_, lean_object* v___y_6210_, lean_object* v___y_6211_, lean_object* v___y_6212_, lean_object* v___y_6213_, lean_object* v___y_6214_){
_start:
{
uint8_t v___x_6216_; 
v___x_6216_ = lean_usize_dec_lt(v_i_6207_, v_sz_6206_);
if (v___x_6216_ == 0)
{
lean_object* v___x_6217_; 
lean_dec_ref(v___y_6209_);
v___x_6217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6217_, 0, v_bs_6208_);
lean_ctor_set(v___x_6217_, 1, v___y_6214_);
return v___x_6217_;
}
else
{
lean_object* v_v_6218_; lean_object* v___x_6219_; lean_object* v_bs_x27_6220_; lean_object* v___y_6222_; 
v_v_6218_ = lean_array_uget(v_bs_6208_, v_i_6207_);
v___x_6219_ = lean_unsigned_to_nat(0u);
v_bs_x27_6220_ = lean_array_uset(v_bs_6208_, v_i_6207_, v___x_6219_);
if (v_text_6205_ == 0)
{
lean_object* v___x_6227_; 
lean_inc_ref(v___y_6209_);
v___x_6227_ = l_Lake_inputBinFile___redArg(v_v_6218_, v___y_6209_, v___y_6210_, v___y_6211_, v___y_6212_, v___y_6213_);
v___y_6222_ = v___x_6227_;
goto v___jp_6221_;
}
else
{
lean_object* v___x_6228_; 
lean_inc_ref(v___y_6209_);
v___x_6228_ = l_Lake_inputTextFile___redArg(v_v_6218_, v___y_6209_, v___y_6210_, v___y_6211_, v___y_6212_, v___y_6213_);
v___y_6222_ = v___x_6228_;
goto v___jp_6221_;
}
v___jp_6221_:
{
size_t v___x_6223_; size_t v___x_6224_; lean_object* v___x_6225_; 
v___x_6223_ = ((size_t)1ULL);
v___x_6224_ = lean_usize_add(v_i_6207_, v___x_6223_);
v___x_6225_ = lean_array_uset(v_bs_x27_6220_, v_i_6207_, v___y_6222_);
v_i_6207_ = v___x_6224_;
v_bs_6208_ = v___x_6225_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0___boxed(lean_object* v_text_6229_, lean_object* v_sz_6230_, lean_object* v_i_6231_, lean_object* v_bs_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_, lean_object* v___y_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_, lean_object* v___y_6238_, lean_object* v___y_6239_){
_start:
{
uint8_t v_text_boxed_6240_; size_t v_sz_boxed_6241_; size_t v_i_boxed_6242_; lean_object* v_res_6243_; 
v_text_boxed_6240_ = lean_unbox(v_text_6229_);
v_sz_boxed_6241_ = lean_unbox_usize(v_sz_6230_);
lean_dec(v_sz_6230_);
v_i_boxed_6242_ = lean_unbox_usize(v_i_6231_);
lean_dec(v_i_6231_);
v_res_6243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(v_text_boxed_6240_, v_sz_boxed_6241_, v_i_boxed_6242_, v_bs_6232_, v___y_6233_, v___y_6234_, v___y_6235_, v___y_6236_, v___y_6237_, v___y_6238_);
lean_dec_ref(v___y_6237_);
lean_dec(v___y_6236_);
lean_dec(v___y_6235_);
lean_dec(v___y_6234_);
return v_res_6243_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2(uint8_t v_text_6244_, lean_object* v_path_6245_, lean_object* v_ps_6246_, lean_object* v___y_6247_, lean_object* v___y_6248_, lean_object* v___y_6249_, lean_object* v___y_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_){
_start:
{
size_t v_sz_6254_; size_t v___x_6255_; lean_object* v___x_6256_; 
v_sz_6254_ = lean_array_size(v_ps_6246_);
v___x_6255_ = ((size_t)0ULL);
v___x_6256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(v_text_6244_, v_sz_6254_, v___x_6255_, v_ps_6246_, v___y_6247_, v___y_6248_, v___y_6249_, v___y_6250_, v___y_6251_, v___y_6252_);
if (lean_obj_tag(v___x_6256_) == 0)
{
lean_object* v_a_6257_; lean_object* v_a_6258_; lean_object* v___x_6260_; uint8_t v_isShared_6261_; uint8_t v_isSharedCheck_6266_; 
v_a_6257_ = lean_ctor_get(v___x_6256_, 0);
v_a_6258_ = lean_ctor_get(v___x_6256_, 1);
v_isSharedCheck_6266_ = !lean_is_exclusive(v___x_6256_);
if (v_isSharedCheck_6266_ == 0)
{
v___x_6260_ = v___x_6256_;
v_isShared_6261_ = v_isSharedCheck_6266_;
goto v_resetjp_6259_;
}
else
{
lean_inc(v_a_6258_);
lean_inc(v_a_6257_);
lean_dec(v___x_6256_);
v___x_6260_ = lean_box(0);
v_isShared_6261_ = v_isSharedCheck_6266_;
goto v_resetjp_6259_;
}
v_resetjp_6259_:
{
lean_object* v___x_6262_; lean_object* v___x_6264_; 
v___x_6262_ = l_Lake_Job_collectArray___redArg(v_a_6257_, v_path_6245_);
lean_dec(v_a_6257_);
if (v_isShared_6261_ == 0)
{
lean_ctor_set(v___x_6260_, 0, v___x_6262_);
v___x_6264_ = v___x_6260_;
goto v_reusejp_6263_;
}
else
{
lean_object* v_reuseFailAlloc_6265_; 
v_reuseFailAlloc_6265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6265_, 0, v___x_6262_);
lean_ctor_set(v_reuseFailAlloc_6265_, 1, v_a_6258_);
v___x_6264_ = v_reuseFailAlloc_6265_;
goto v_reusejp_6263_;
}
v_reusejp_6263_:
{
return v___x_6264_;
}
}
}
else
{
lean_object* v_a_6267_; lean_object* v_a_6268_; lean_object* v___x_6270_; uint8_t v_isShared_6271_; uint8_t v_isSharedCheck_6275_; 
lean_dec_ref(v_path_6245_);
v_a_6267_ = lean_ctor_get(v___x_6256_, 0);
v_a_6268_ = lean_ctor_get(v___x_6256_, 1);
v_isSharedCheck_6275_ = !lean_is_exclusive(v___x_6256_);
if (v_isSharedCheck_6275_ == 0)
{
v___x_6270_ = v___x_6256_;
v_isShared_6271_ = v_isSharedCheck_6275_;
goto v_resetjp_6269_;
}
else
{
lean_inc(v_a_6268_);
lean_inc(v_a_6267_);
lean_dec(v___x_6256_);
v___x_6270_ = lean_box(0);
v_isShared_6271_ = v_isSharedCheck_6275_;
goto v_resetjp_6269_;
}
v_resetjp_6269_:
{
lean_object* v___x_6273_; 
if (v_isShared_6271_ == 0)
{
v___x_6273_ = v___x_6270_;
goto v_reusejp_6272_;
}
else
{
lean_object* v_reuseFailAlloc_6274_; 
v_reuseFailAlloc_6274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6274_, 0, v_a_6267_);
lean_ctor_set(v_reuseFailAlloc_6274_, 1, v_a_6268_);
v___x_6273_ = v_reuseFailAlloc_6274_;
goto v_reusejp_6272_;
}
v_reusejp_6272_:
{
return v___x_6273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2___boxed(lean_object* v_text_6276_, lean_object* v_path_6277_, lean_object* v_ps_6278_, lean_object* v___y_6279_, lean_object* v___y_6280_, lean_object* v___y_6281_, lean_object* v___y_6282_, lean_object* v___y_6283_, lean_object* v___y_6284_, lean_object* v___y_6285_){
_start:
{
uint8_t v_text_boxed_6286_; lean_object* v_res_6287_; 
v_text_boxed_6286_ = lean_unbox(v_text_6276_);
v_res_6287_ = l_Lake_inputDir___lam__2(v_text_boxed_6286_, v_path_6277_, v_ps_6278_, v___y_6279_, v___y_6280_, v___y_6281_, v___y_6282_, v___y_6283_, v___y_6284_);
lean_dec_ref(v___y_6283_);
lean_dec(v___y_6282_);
lean_dec(v___y_6281_);
lean_dec(v___y_6280_);
return v_res_6287_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir(lean_object* v_path_6289_, uint8_t v_text_6290_, lean_object* v_filter_6291_, lean_object* v_a_6292_, lean_object* v_a_6293_, lean_object* v_a_6294_, lean_object* v_a_6295_, lean_object* v_a_6296_, lean_object* v_a_6297_){
_start:
{
lean_object* v___f_6299_; lean_object* v___f_6300_; lean_object* v___x_6301_; lean_object* v___x_6302_; lean_object* v___x_6303_; lean_object* v___x_6304_; lean_object* v___x_6305_; lean_object* v___f_6306_; uint8_t v___x_6307_; lean_object* v___x_6308_; 
v___f_6299_ = ((lean_object*)(l_Lake_inputDir___closed__0));
lean_inc_ref(v_path_6289_);
v___f_6300_ = lean_alloc_closure((void*)(l_Lake_inputDir___lam__1___boxed), 10, 3);
lean_closure_set(v___f_6300_, 0, v_path_6289_);
lean_closure_set(v___f_6300_, 1, v___f_6299_);
lean_closure_set(v___f_6300_, 2, v_filter_6291_);
v___x_6301_ = lean_box(0);
v___x_6302_ = lean_unsigned_to_nat(0u);
v___x_6303_ = ((lean_object*)(l_Lake_inputBinFile___redArg___closed__0));
lean_inc_ref(v_a_6292_);
v___x_6304_ = l_Lake_Job_async___redArg(v___x_6301_, v___f_6300_, v___x_6302_, v___x_6303_, v_a_6292_, v_a_6293_, v_a_6294_, v_a_6295_, v_a_6296_);
v___x_6305_ = lean_box(v_text_6290_);
v___f_6306_ = lean_alloc_closure((void*)(l_Lake_inputDir___lam__2___boxed), 10, 2);
lean_closure_set(v___f_6306_, 0, v___x_6305_);
lean_closure_set(v___f_6306_, 1, v_path_6289_);
v___x_6307_ = 0;
v___x_6308_ = l_Lake_Job_bindM___redArg(v___x_6301_, v___x_6304_, v___f_6306_, v___x_6302_, v___x_6307_, v_a_6292_, v_a_6293_, v_a_6294_, v_a_6295_, v_a_6296_, v_a_6297_);
return v___x_6308_;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___boxed(lean_object* v_path_6309_, lean_object* v_text_6310_, lean_object* v_filter_6311_, lean_object* v_a_6312_, lean_object* v_a_6313_, lean_object* v_a_6314_, lean_object* v_a_6315_, lean_object* v_a_6316_, lean_object* v_a_6317_, lean_object* v_a_6318_){
_start:
{
uint8_t v_text_boxed_6319_; lean_object* v_res_6320_; 
v_text_boxed_6319_ = lean_unbox(v_text_6310_);
v_res_6320_ = l_Lake_inputDir(v_path_6309_, v_text_boxed_6319_, v_filter_6311_, v_a_6312_, v_a_6313_, v_a_6314_, v_a_6315_, v_a_6316_, v_a_6317_);
lean_dec_ref(v_a_6317_);
lean_dec_ref(v_a_6316_);
lean_dec(v_a_6315_);
lean_dec(v_a_6314_);
lean_dec(v_a_6313_);
return v_res_6320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(lean_object* v_n_6321_, lean_object* v_as_6322_, lean_object* v_lo_6323_, lean_object* v_hi_6324_, lean_object* v_w_6325_, lean_object* v_hlo_6326_, lean_object* v_hhi_6327_){
_start:
{
lean_object* v___x_6328_; 
v___x_6328_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(v_n_6321_, v_as_6322_, v_lo_6323_, v_hi_6324_);
return v___x_6328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___boxed(lean_object* v_n_6329_, lean_object* v_as_6330_, lean_object* v_lo_6331_, lean_object* v_hi_6332_, lean_object* v_w_6333_, lean_object* v_hlo_6334_, lean_object* v_hhi_6335_){
_start:
{
lean_object* v_res_6336_; 
v_res_6336_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(v_n_6329_, v_as_6330_, v_lo_6331_, v_hi_6332_, v_w_6333_, v_hlo_6334_, v_hhi_6335_);
lean_dec(v_hi_6332_);
lean_dec(v_n_6329_);
return v_res_6336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(lean_object* v_filter_6337_, lean_object* v_as_6338_, size_t v_i_6339_, size_t v_stop_6340_, lean_object* v_b_6341_, lean_object* v___y_6342_, lean_object* v___y_6343_, lean_object* v___y_6344_, lean_object* v___y_6345_, lean_object* v___y_6346_, lean_object* v___y_6347_){
_start:
{
lean_object* v___x_6349_; 
v___x_6349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(v_filter_6337_, v_as_6338_, v_i_6339_, v_stop_6340_, v_b_6341_, v___y_6347_);
return v___x_6349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___boxed(lean_object* v_filter_6350_, lean_object* v_as_6351_, lean_object* v_i_6352_, lean_object* v_stop_6353_, lean_object* v_b_6354_, lean_object* v___y_6355_, lean_object* v___y_6356_, lean_object* v___y_6357_, lean_object* v___y_6358_, lean_object* v___y_6359_, lean_object* v___y_6360_, lean_object* v___y_6361_){
_start:
{
size_t v_i_boxed_6362_; size_t v_stop_boxed_6363_; lean_object* v_res_6364_; 
v_i_boxed_6362_ = lean_unbox_usize(v_i_6352_);
lean_dec(v_i_6352_);
v_stop_boxed_6363_ = lean_unbox_usize(v_stop_6353_);
lean_dec(v_stop_6353_);
v_res_6364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(v_filter_6350_, v_as_6351_, v_i_boxed_6362_, v_stop_boxed_6363_, v_b_6354_, v___y_6355_, v___y_6356_, v___y_6357_, v___y_6358_, v___y_6359_, v___y_6360_);
lean_dec_ref(v___y_6359_);
lean_dec(v___y_6358_);
lean_dec(v___y_6357_);
lean_dec(v___y_6356_);
lean_dec_ref(v___y_6355_);
lean_dec_ref(v_as_6351_);
return v_res_6364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1(lean_object* v_n_6365_, lean_object* v_lo_6366_, lean_object* v_hi_6367_, lean_object* v_hhi_6368_, lean_object* v_pivot_6369_, lean_object* v_as_6370_, lean_object* v_i_6371_, lean_object* v_k_6372_, lean_object* v_ilo_6373_, lean_object* v_ik_6374_, lean_object* v_w_6375_){
_start:
{
lean_object* v___x_6376_; 
v___x_6376_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___redArg(v_hi_6367_, v_pivot_6369_, v_as_6370_, v_i_6371_, v_k_6372_);
return v___x_6376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1___boxed(lean_object* v_n_6377_, lean_object* v_lo_6378_, lean_object* v_hi_6379_, lean_object* v_hhi_6380_, lean_object* v_pivot_6381_, lean_object* v_as_6382_, lean_object* v_i_6383_, lean_object* v_k_6384_, lean_object* v_ilo_6385_, lean_object* v_ik_6386_, lean_object* v_w_6387_){
_start:
{
lean_object* v_res_6388_; 
v_res_6388_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1_spec__1(v_n_6377_, v_lo_6378_, v_hi_6379_, v_hhi_6380_, v_pivot_6381_, v_as_6382_, v_i_6383_, v_k_6384_, v_ilo_6385_, v_ik_6386_, v_w_6387_);
lean_dec_ref(v_pivot_6381_);
lean_dec(v_hi_6379_);
lean_dec(v_lo_6378_);
lean_dec(v_n_6377_);
return v_res_6388_;
}
}
LEAN_EXPORT uint64_t l_Lake_buildO___lam__0(uint64_t v_ts_6389_, lean_object* v_t_6390_){
_start:
{
uint64_t v___x_6391_; uint64_t v___x_6392_; uint64_t v___x_6393_; uint64_t v___x_6394_; 
v___x_6391_ = l_Lake_Hash_nil;
v___x_6392_ = lean_string_hash(v_t_6390_);
v___x_6393_ = lean_uint64_mix_hash(v___x_6391_, v___x_6392_);
v___x_6394_ = lean_uint64_mix_hash(v_ts_6389_, v___x_6393_);
return v___x_6394_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__0___boxed(lean_object* v_ts_6395_, lean_object* v_t_6396_){
_start:
{
uint64_t v_ts_boxed_6397_; uint64_t v_res_6398_; lean_object* v_r_6399_; 
v_ts_boxed_6397_ = lean_unbox_uint64(v_ts_6395_);
lean_dec_ref(v_ts_6395_);
v_res_6398_ = l_Lake_buildO___lam__0(v_ts_boxed_6397_, v_t_6396_);
lean_dec_ref(v_t_6396_);
v_r_6399_ = lean_box_uint64(v_res_6398_);
return v_r_6399_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1(lean_object* v_oFile_6400_, lean_object* v_srcFile_6401_, lean_object* v___x_6402_, lean_object* v_compiler_6403_, lean_object* v___y_6404_, lean_object* v___y_6405_, lean_object* v___y_6406_, lean_object* v___y_6407_, lean_object* v___y_6408_, lean_object* v___y_6409_){
_start:
{
lean_object* v_log_6411_; uint8_t v_action_6412_; uint8_t v_wantsRebuild_6413_; lean_object* v_trace_6414_; lean_object* v_buildTime_6415_; lean_object* v___x_6417_; uint8_t v_isShared_6418_; uint8_t v_isSharedCheck_6444_; 
v_log_6411_ = lean_ctor_get(v___y_6409_, 0);
v_action_6412_ = lean_ctor_get_uint8(v___y_6409_, sizeof(void*)*3);
v_wantsRebuild_6413_ = lean_ctor_get_uint8(v___y_6409_, sizeof(void*)*3 + 1);
v_trace_6414_ = lean_ctor_get(v___y_6409_, 1);
v_buildTime_6415_ = lean_ctor_get(v___y_6409_, 2);
v_isSharedCheck_6444_ = !lean_is_exclusive(v___y_6409_);
if (v_isSharedCheck_6444_ == 0)
{
v___x_6417_ = v___y_6409_;
v_isShared_6418_ = v_isSharedCheck_6444_;
goto v_resetjp_6416_;
}
else
{
lean_inc(v_buildTime_6415_);
lean_inc(v_trace_6414_);
lean_inc(v_log_6411_);
lean_dec(v___y_6409_);
v___x_6417_ = lean_box(0);
v_isShared_6418_ = v_isSharedCheck_6444_;
goto v_resetjp_6416_;
}
v_resetjp_6416_:
{
lean_object* v___x_6419_; 
v___x_6419_ = l_Lake_compileO(v_oFile_6400_, v_srcFile_6401_, v___x_6402_, v_compiler_6403_, v_log_6411_);
if (lean_obj_tag(v___x_6419_) == 0)
{
lean_object* v_a_6420_; lean_object* v_a_6421_; lean_object* v___x_6423_; uint8_t v_isShared_6424_; uint8_t v_isSharedCheck_6431_; 
v_a_6420_ = lean_ctor_get(v___x_6419_, 0);
v_a_6421_ = lean_ctor_get(v___x_6419_, 1);
v_isSharedCheck_6431_ = !lean_is_exclusive(v___x_6419_);
if (v_isSharedCheck_6431_ == 0)
{
v___x_6423_ = v___x_6419_;
v_isShared_6424_ = v_isSharedCheck_6431_;
goto v_resetjp_6422_;
}
else
{
lean_inc(v_a_6421_);
lean_inc(v_a_6420_);
lean_dec(v___x_6419_);
v___x_6423_ = lean_box(0);
v_isShared_6424_ = v_isSharedCheck_6431_;
goto v_resetjp_6422_;
}
v_resetjp_6422_:
{
lean_object* v___x_6426_; 
if (v_isShared_6418_ == 0)
{
lean_ctor_set(v___x_6417_, 0, v_a_6421_);
v___x_6426_ = v___x_6417_;
goto v_reusejp_6425_;
}
else
{
lean_object* v_reuseFailAlloc_6430_; 
v_reuseFailAlloc_6430_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6430_, 0, v_a_6421_);
lean_ctor_set(v_reuseFailAlloc_6430_, 1, v_trace_6414_);
lean_ctor_set(v_reuseFailAlloc_6430_, 2, v_buildTime_6415_);
lean_ctor_set_uint8(v_reuseFailAlloc_6430_, sizeof(void*)*3, v_action_6412_);
lean_ctor_set_uint8(v_reuseFailAlloc_6430_, sizeof(void*)*3 + 1, v_wantsRebuild_6413_);
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
v_reuseFailAlloc_6429_ = lean_alloc_ctor(0, 2, 0);
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
else
{
lean_object* v_a_6432_; lean_object* v_a_6433_; lean_object* v___x_6435_; uint8_t v_isShared_6436_; uint8_t v_isSharedCheck_6443_; 
v_a_6432_ = lean_ctor_get(v___x_6419_, 0);
v_a_6433_ = lean_ctor_get(v___x_6419_, 1);
v_isSharedCheck_6443_ = !lean_is_exclusive(v___x_6419_);
if (v_isSharedCheck_6443_ == 0)
{
v___x_6435_ = v___x_6419_;
v_isShared_6436_ = v_isSharedCheck_6443_;
goto v_resetjp_6434_;
}
else
{
lean_inc(v_a_6433_);
lean_inc(v_a_6432_);
lean_dec(v___x_6419_);
v___x_6435_ = lean_box(0);
v_isShared_6436_ = v_isSharedCheck_6443_;
goto v_resetjp_6434_;
}
v_resetjp_6434_:
{
lean_object* v___x_6438_; 
if (v_isShared_6418_ == 0)
{
lean_ctor_set(v___x_6417_, 0, v_a_6433_);
v___x_6438_ = v___x_6417_;
goto v_reusejp_6437_;
}
else
{
lean_object* v_reuseFailAlloc_6442_; 
v_reuseFailAlloc_6442_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6442_, 0, v_a_6433_);
lean_ctor_set(v_reuseFailAlloc_6442_, 1, v_trace_6414_);
lean_ctor_set(v_reuseFailAlloc_6442_, 2, v_buildTime_6415_);
lean_ctor_set_uint8(v_reuseFailAlloc_6442_, sizeof(void*)*3, v_action_6412_);
lean_ctor_set_uint8(v_reuseFailAlloc_6442_, sizeof(void*)*3 + 1, v_wantsRebuild_6413_);
v___x_6438_ = v_reuseFailAlloc_6442_;
goto v_reusejp_6437_;
}
v_reusejp_6437_:
{
lean_object* v___x_6440_; 
if (v_isShared_6436_ == 0)
{
lean_ctor_set(v___x_6435_, 1, v___x_6438_);
v___x_6440_ = v___x_6435_;
goto v_reusejp_6439_;
}
else
{
lean_object* v_reuseFailAlloc_6441_; 
v_reuseFailAlloc_6441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6441_, 0, v_a_6432_);
lean_ctor_set(v_reuseFailAlloc_6441_, 1, v___x_6438_);
v___x_6440_ = v_reuseFailAlloc_6441_;
goto v_reusejp_6439_;
}
v_reusejp_6439_:
{
return v___x_6440_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1___boxed(lean_object* v_oFile_6445_, lean_object* v_srcFile_6446_, lean_object* v___x_6447_, lean_object* v_compiler_6448_, lean_object* v___y_6449_, lean_object* v___y_6450_, lean_object* v___y_6451_, lean_object* v___y_6452_, lean_object* v___y_6453_, lean_object* v___y_6454_, lean_object* v___y_6455_){
_start:
{
lean_object* v_res_6456_; 
v_res_6456_ = l_Lake_buildO___lam__1(v_oFile_6445_, v_srcFile_6446_, v___x_6447_, v_compiler_6448_, v___y_6449_, v___y_6450_, v___y_6451_, v___y_6452_, v___y_6453_, v___y_6454_);
lean_dec_ref(v___y_6453_);
lean_dec(v___y_6452_);
lean_dec(v___y_6451_);
lean_dec(v___y_6450_);
lean_dec_ref(v___y_6449_);
lean_dec_ref(v___x_6447_);
return v_res_6456_;
}
}
static lean_object* _init_l_Lake_buildO___lam__2___boxed__const__1(void){
_start:
{
uint64_t v___x_6460_; lean_object* v___x_6461_; 
v___x_6460_ = l_Lake_Hash_nil;
v___x_6461_ = lean_box_uint64(v___x_6460_);
return v___x_6461_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2(lean_object* v_traceArgs_6462_, lean_object* v___f_6463_, lean_object* v_extraDepTrace_6464_, lean_object* v_weakArgs_6465_, lean_object* v_oFile_6466_, lean_object* v_compiler_6467_, lean_object* v___x_6468_, lean_object* v___f_6469_, lean_object* v_srcFile_6470_, lean_object* v___y_6471_, lean_object* v___y_6472_, lean_object* v___y_6473_, lean_object* v___y_6474_, lean_object* v___y_6475_, lean_object* v___y_6476_){
_start:
{
lean_object* v_log_6478_; uint8_t v_action_6479_; uint8_t v_wantsRebuild_6480_; lean_object* v_trace_6481_; lean_object* v_buildTime_6482_; lean_object* v___x_6484_; uint8_t v_isShared_6485_; uint8_t v_isSharedCheck_6561_; 
v_log_6478_ = lean_ctor_get(v___y_6476_, 0);
v_action_6479_ = lean_ctor_get_uint8(v___y_6476_, sizeof(void*)*3);
v_wantsRebuild_6480_ = lean_ctor_get_uint8(v___y_6476_, sizeof(void*)*3 + 1);
v_trace_6481_ = lean_ctor_get(v___y_6476_, 1);
v_buildTime_6482_ = lean_ctor_get(v___y_6476_, 2);
v_isSharedCheck_6561_ = !lean_is_exclusive(v___y_6476_);
if (v_isSharedCheck_6561_ == 0)
{
v___x_6484_ = v___y_6476_;
v_isShared_6485_ = v_isSharedCheck_6561_;
goto v_resetjp_6483_;
}
else
{
lean_inc(v_buildTime_6482_);
lean_inc(v_trace_6481_);
lean_inc(v_log_6478_);
lean_dec(v___y_6476_);
v___x_6484_ = lean_box(0);
v_isShared_6485_ = v_isSharedCheck_6561_;
goto v_resetjp_6483_;
}
v_resetjp_6483_:
{
lean_object* v___x_6486_; lean_object* v___x_6487_; uint64_t v___y_6489_; uint64_t v___x_6552_; lean_object* v___x_6553_; lean_object* v___x_6554_; uint8_t v___x_6555_; 
v___x_6486_ = l_Lake_platformTrace;
v___x_6487_ = l_Lake_BuildTrace_mix(v_trace_6481_, v___x_6486_);
v___x_6552_ = l_Lake_Hash_nil;
v___x_6553_ = lean_unsigned_to_nat(0u);
v___x_6554_ = lean_array_get_size(v_traceArgs_6462_);
v___x_6555_ = lean_nat_dec_lt(v___x_6553_, v___x_6554_);
if (v___x_6555_ == 0)
{
lean_dec_ref(v___f_6469_);
lean_dec_ref(v___x_6468_);
v___y_6489_ = v___x_6552_;
goto v___jp_6488_;
}
else
{
size_t v___x_6556_; size_t v___x_6557_; lean_object* v___x_6558_; lean_object* v___x_6559_; uint64_t v___x_6560_; 
v___x_6556_ = ((size_t)0ULL);
v___x_6557_ = lean_usize_of_nat(v___x_6554_);
v___x_6558_ = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(v_traceArgs_6462_);
v___x_6559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_6468_, v___f_6469_, v_traceArgs_6462_, v___x_6556_, v___x_6557_, v___x_6558_);
v___x_6560_ = lean_unbox_uint64(v___x_6559_);
lean_dec(v___x_6559_);
v___y_6489_ = v___x_6560_;
goto v___jp_6488_;
}
v___jp_6488_:
{
lean_object* v___x_6490_; lean_object* v___x_6491_; lean_object* v___x_6492_; lean_object* v___x_6493_; lean_object* v___x_6494_; lean_object* v___x_6495_; lean_object* v___x_6496_; lean_object* v___x_6497_; lean_object* v___x_6498_; lean_object* v___x_6499_; lean_object* v___x_6501_; 
v___x_6490_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_6491_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_6462_);
v___x_6492_ = lean_array_to_list(v_traceArgs_6462_);
v___x_6493_ = l_List_toString___redArg(v___f_6463_, v___x_6492_);
v___x_6494_ = lean_string_append(v___x_6491_, v___x_6493_);
lean_dec_ref(v___x_6493_);
v___x_6495_ = lean_string_append(v___x_6490_, v___x_6494_);
lean_dec_ref(v___x_6494_);
v___x_6496_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_6497_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_6498_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6498_, 0, v___x_6495_);
lean_ctor_set(v___x_6498_, 1, v___x_6496_);
lean_ctor_set(v___x_6498_, 2, v___x_6497_);
lean_ctor_set_uint64(v___x_6498_, sizeof(void*)*3, v___y_6489_);
v___x_6499_ = l_Lake_BuildTrace_mix(v___x_6487_, v___x_6498_);
if (v_isShared_6485_ == 0)
{
lean_ctor_set(v___x_6484_, 1, v___x_6499_);
v___x_6501_ = v___x_6484_;
goto v_reusejp_6500_;
}
else
{
lean_object* v_reuseFailAlloc_6551_; 
v_reuseFailAlloc_6551_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6551_, 0, v_log_6478_);
lean_ctor_set(v_reuseFailAlloc_6551_, 1, v___x_6499_);
lean_ctor_set(v_reuseFailAlloc_6551_, 2, v_buildTime_6482_);
lean_ctor_set_uint8(v_reuseFailAlloc_6551_, sizeof(void*)*3, v_action_6479_);
lean_ctor_set_uint8(v_reuseFailAlloc_6551_, sizeof(void*)*3 + 1, v_wantsRebuild_6480_);
v___x_6501_ = v_reuseFailAlloc_6551_;
goto v_reusejp_6500_;
}
v_reusejp_6500_:
{
lean_object* v___x_6502_; 
lean_inc_ref(v___y_6475_);
lean_inc(v___y_6474_);
lean_inc(v___y_6473_);
lean_inc(v___y_6472_);
lean_inc_ref(v___y_6471_);
v___x_6502_ = lean_apply_7(v_extraDepTrace_6464_, v___y_6471_, v___y_6472_, v___y_6473_, v___y_6474_, v___y_6475_, v___x_6501_, lean_box(0));
if (lean_obj_tag(v___x_6502_) == 0)
{
lean_object* v_a_6503_; lean_object* v_a_6504_; lean_object* v_log_6505_; uint8_t v_action_6506_; uint8_t v_wantsRebuild_6507_; lean_object* v_trace_6508_; lean_object* v_buildTime_6509_; lean_object* v___x_6511_; uint8_t v_isShared_6512_; uint8_t v_isSharedCheck_6541_; 
v_a_6503_ = lean_ctor_get(v___x_6502_, 1);
lean_inc(v_a_6503_);
v_a_6504_ = lean_ctor_get(v___x_6502_, 0);
lean_inc(v_a_6504_);
lean_dec_ref_known(v___x_6502_, 2);
v_log_6505_ = lean_ctor_get(v_a_6503_, 0);
v_action_6506_ = lean_ctor_get_uint8(v_a_6503_, sizeof(void*)*3);
v_wantsRebuild_6507_ = lean_ctor_get_uint8(v_a_6503_, sizeof(void*)*3 + 1);
v_trace_6508_ = lean_ctor_get(v_a_6503_, 1);
v_buildTime_6509_ = lean_ctor_get(v_a_6503_, 2);
v_isSharedCheck_6541_ = !lean_is_exclusive(v_a_6503_);
if (v_isSharedCheck_6541_ == 0)
{
v___x_6511_ = v_a_6503_;
v_isShared_6512_ = v_isSharedCheck_6541_;
goto v_resetjp_6510_;
}
else
{
lean_inc(v_buildTime_6509_);
lean_inc(v_trace_6508_);
lean_inc(v_log_6505_);
lean_dec(v_a_6503_);
v___x_6511_ = lean_box(0);
v_isShared_6512_ = v_isSharedCheck_6541_;
goto v_resetjp_6510_;
}
v_resetjp_6510_:
{
lean_object* v___x_6513_; lean_object* v___x_6515_; 
v___x_6513_ = l_Lake_BuildTrace_mix(v_trace_6508_, v_a_6504_);
if (v_isShared_6512_ == 0)
{
lean_ctor_set(v___x_6511_, 1, v___x_6513_);
v___x_6515_ = v___x_6511_;
goto v_reusejp_6514_;
}
else
{
lean_object* v_reuseFailAlloc_6540_; 
v_reuseFailAlloc_6540_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6540_, 0, v_log_6505_);
lean_ctor_set(v_reuseFailAlloc_6540_, 1, v___x_6513_);
lean_ctor_set(v_reuseFailAlloc_6540_, 2, v_buildTime_6509_);
lean_ctor_set_uint8(v_reuseFailAlloc_6540_, sizeof(void*)*3, v_action_6506_);
lean_ctor_set_uint8(v_reuseFailAlloc_6540_, sizeof(void*)*3 + 1, v_wantsRebuild_6507_);
v___x_6515_ = v_reuseFailAlloc_6540_;
goto v_reusejp_6514_;
}
v_reusejp_6514_:
{
lean_object* v___x_6516_; lean_object* v___f_6517_; uint8_t v___x_6518_; lean_object* v___x_6519_; lean_object* v___x_6520_; 
v___x_6516_ = l_Array_append___redArg(v_weakArgs_6465_, v_traceArgs_6462_);
lean_dec_ref(v_traceArgs_6462_);
lean_inc_ref(v_oFile_6466_);
v___f_6517_ = lean_alloc_closure((void*)(l_Lake_buildO___lam__1___boxed), 11, 4);
lean_closure_set(v___f_6517_, 0, v_oFile_6466_);
lean_closure_set(v___f_6517_, 1, v_srcFile_6470_);
lean_closure_set(v___f_6517_, 2, v___x_6516_);
lean_closure_set(v___f_6517_, 3, v_compiler_6467_);
v___x_6518_ = 0;
v___x_6519_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
v___x_6520_ = l_Lake_buildArtifactUnlessUpToDate(v_oFile_6466_, v___f_6517_, v___x_6518_, v___x_6519_, v___x_6518_, v___x_6518_, v___x_6518_, v___y_6471_, v___y_6472_, v___y_6473_, v___y_6474_, v___y_6475_, v___x_6515_);
if (lean_obj_tag(v___x_6520_) == 0)
{
lean_object* v_a_6521_; lean_object* v_a_6522_; lean_object* v___x_6524_; uint8_t v_isShared_6525_; uint8_t v_isSharedCheck_6530_; 
v_a_6521_ = lean_ctor_get(v___x_6520_, 0);
v_a_6522_ = lean_ctor_get(v___x_6520_, 1);
v_isSharedCheck_6530_ = !lean_is_exclusive(v___x_6520_);
if (v_isSharedCheck_6530_ == 0)
{
v___x_6524_ = v___x_6520_;
v_isShared_6525_ = v_isSharedCheck_6530_;
goto v_resetjp_6523_;
}
else
{
lean_inc(v_a_6522_);
lean_inc(v_a_6521_);
lean_dec(v___x_6520_);
v___x_6524_ = lean_box(0);
v_isShared_6525_ = v_isSharedCheck_6530_;
goto v_resetjp_6523_;
}
v_resetjp_6523_:
{
lean_object* v_path_6526_; lean_object* v___x_6528_; 
v_path_6526_ = lean_ctor_get(v_a_6521_, 1);
lean_inc_ref(v_path_6526_);
lean_dec(v_a_6521_);
if (v_isShared_6525_ == 0)
{
lean_ctor_set(v___x_6524_, 0, v_path_6526_);
v___x_6528_ = v___x_6524_;
goto v_reusejp_6527_;
}
else
{
lean_object* v_reuseFailAlloc_6529_; 
v_reuseFailAlloc_6529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6529_, 0, v_path_6526_);
lean_ctor_set(v_reuseFailAlloc_6529_, 1, v_a_6522_);
v___x_6528_ = v_reuseFailAlloc_6529_;
goto v_reusejp_6527_;
}
v_reusejp_6527_:
{
return v___x_6528_;
}
}
}
else
{
lean_object* v_a_6531_; lean_object* v_a_6532_; lean_object* v___x_6534_; uint8_t v_isShared_6535_; uint8_t v_isSharedCheck_6539_; 
v_a_6531_ = lean_ctor_get(v___x_6520_, 0);
v_a_6532_ = lean_ctor_get(v___x_6520_, 1);
v_isSharedCheck_6539_ = !lean_is_exclusive(v___x_6520_);
if (v_isSharedCheck_6539_ == 0)
{
v___x_6534_ = v___x_6520_;
v_isShared_6535_ = v_isSharedCheck_6539_;
goto v_resetjp_6533_;
}
else
{
lean_inc(v_a_6532_);
lean_inc(v_a_6531_);
lean_dec(v___x_6520_);
v___x_6534_ = lean_box(0);
v_isShared_6535_ = v_isSharedCheck_6539_;
goto v_resetjp_6533_;
}
v_resetjp_6533_:
{
lean_object* v___x_6537_; 
if (v_isShared_6535_ == 0)
{
v___x_6537_ = v___x_6534_;
goto v_reusejp_6536_;
}
else
{
lean_object* v_reuseFailAlloc_6538_; 
v_reuseFailAlloc_6538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6538_, 0, v_a_6531_);
lean_ctor_set(v_reuseFailAlloc_6538_, 1, v_a_6532_);
v___x_6537_ = v_reuseFailAlloc_6538_;
goto v_reusejp_6536_;
}
v_reusejp_6536_:
{
return v___x_6537_;
}
}
}
}
}
}
else
{
lean_object* v_a_6542_; lean_object* v_a_6543_; lean_object* v___x_6545_; uint8_t v_isShared_6546_; uint8_t v_isSharedCheck_6550_; 
lean_dec_ref(v___y_6471_);
lean_dec_ref(v_srcFile_6470_);
lean_dec_ref(v_compiler_6467_);
lean_dec_ref(v_oFile_6466_);
lean_dec_ref(v_weakArgs_6465_);
lean_dec_ref(v_traceArgs_6462_);
v_a_6542_ = lean_ctor_get(v___x_6502_, 0);
v_a_6543_ = lean_ctor_get(v___x_6502_, 1);
v_isSharedCheck_6550_ = !lean_is_exclusive(v___x_6502_);
if (v_isSharedCheck_6550_ == 0)
{
v___x_6545_ = v___x_6502_;
v_isShared_6546_ = v_isSharedCheck_6550_;
goto v_resetjp_6544_;
}
else
{
lean_inc(v_a_6543_);
lean_inc(v_a_6542_);
lean_dec(v___x_6502_);
v___x_6545_ = lean_box(0);
v_isShared_6546_ = v_isSharedCheck_6550_;
goto v_resetjp_6544_;
}
v_resetjp_6544_:
{
lean_object* v___x_6548_; 
if (v_isShared_6546_ == 0)
{
v___x_6548_ = v___x_6545_;
goto v_reusejp_6547_;
}
else
{
lean_object* v_reuseFailAlloc_6549_; 
v_reuseFailAlloc_6549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6549_, 0, v_a_6542_);
lean_ctor_set(v_reuseFailAlloc_6549_, 1, v_a_6543_);
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
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed(lean_object* v_traceArgs_6562_, lean_object* v___f_6563_, lean_object* v_extraDepTrace_6564_, lean_object* v_weakArgs_6565_, lean_object* v_oFile_6566_, lean_object* v_compiler_6567_, lean_object* v___x_6568_, lean_object* v___f_6569_, lean_object* v_srcFile_6570_, lean_object* v___y_6571_, lean_object* v___y_6572_, lean_object* v___y_6573_, lean_object* v___y_6574_, lean_object* v___y_6575_, lean_object* v___y_6576_, lean_object* v___y_6577_){
_start:
{
lean_object* v_res_6578_; 
v_res_6578_ = l_Lake_buildO___lam__2(v_traceArgs_6562_, v___f_6563_, v_extraDepTrace_6564_, v_weakArgs_6565_, v_oFile_6566_, v_compiler_6567_, v___x_6568_, v___f_6569_, v_srcFile_6570_, v___y_6571_, v___y_6572_, v___y_6573_, v___y_6574_, v___y_6575_, v___y_6576_);
lean_dec_ref(v___y_6575_);
lean_dec(v___y_6574_);
lean_dec(v___y_6573_);
lean_dec(v___y_6572_);
return v_res_6578_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object* v_oFile_6581_, lean_object* v_srcJob_6582_, lean_object* v_weakArgs_6583_, lean_object* v_traceArgs_6584_, lean_object* v_compiler_6585_, lean_object* v_extraDepTrace_6586_, lean_object* v_a_6587_, lean_object* v_a_6588_, lean_object* v_a_6589_, lean_object* v_a_6590_, lean_object* v_a_6591_, lean_object* v_a_6592_){
_start:
{
lean_object* v___f_6594_; lean_object* v___x_6595_; lean_object* v___f_6596_; lean_object* v___x_6597_; lean_object* v___f_6598_; lean_object* v___x_6599_; uint8_t v___x_6600_; lean_object* v___x_6601_; 
v___f_6594_ = ((lean_object*)(l_Lake_buildO___closed__0));
v___x_6595_ = l_Lake_instDataKindFilePath;
v___f_6596_ = ((lean_object*)(l_Lake_buildO___closed__1));
v___x_6597_ = ((lean_object*)(l_Lake_instMonadWorkspaceJobM___closed__9));
v___f_6598_ = lean_alloc_closure((void*)(l_Lake_buildO___lam__2___boxed), 16, 8);
lean_closure_set(v___f_6598_, 0, v_traceArgs_6584_);
lean_closure_set(v___f_6598_, 1, v___f_6596_);
lean_closure_set(v___f_6598_, 2, v_extraDepTrace_6586_);
lean_closure_set(v___f_6598_, 3, v_weakArgs_6583_);
lean_closure_set(v___f_6598_, 4, v_oFile_6581_);
lean_closure_set(v___f_6598_, 5, v_compiler_6585_);
lean_closure_set(v___f_6598_, 6, v___x_6597_);
lean_closure_set(v___f_6598_, 7, v___f_6594_);
v___x_6599_ = lean_unsigned_to_nat(0u);
v___x_6600_ = 0;
v___x_6601_ = l_Lake_Job_mapM___redArg(v___x_6595_, v_srcJob_6582_, v___f_6598_, v___x_6599_, v___x_6600_, v_a_6587_, v_a_6588_, v_a_6589_, v_a_6590_, v_a_6591_, v_a_6592_);
return v___x_6601_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___boxed(lean_object* v_oFile_6602_, lean_object* v_srcJob_6603_, lean_object* v_weakArgs_6604_, lean_object* v_traceArgs_6605_, lean_object* v_compiler_6606_, lean_object* v_extraDepTrace_6607_, lean_object* v_a_6608_, lean_object* v_a_6609_, lean_object* v_a_6610_, lean_object* v_a_6611_, lean_object* v_a_6612_, lean_object* v_a_6613_, lean_object* v_a_6614_){
_start:
{
lean_object* v_res_6615_; 
v_res_6615_ = l_Lake_buildO(v_oFile_6602_, v_srcJob_6603_, v_weakArgs_6604_, v_traceArgs_6605_, v_compiler_6606_, v_extraDepTrace_6607_, v_a_6608_, v_a_6609_, v_a_6610_, v_a_6611_, v_a_6612_, v_a_6613_);
lean_dec_ref(v_a_6613_);
lean_dec_ref(v_a_6612_);
lean_dec(v_a_6611_);
lean_dec(v_a_6610_);
lean_dec(v_a_6609_);
return v_res_6615_;
}
}
static lean_object* _init_l_Lake_Internal_buildLeanO___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6617_; lean_object* v___x_6618_; lean_object* v___x_6619_; lean_object* v___x_6620_; 
v___x_6617_ = ((lean_object*)(l_Lake_Internal_buildLeanO___lam__0___closed__0));
v___x_6618_ = lean_unsigned_to_nat(2u);
v___x_6619_ = lean_mk_empty_array_with_capacity(v___x_6618_);
v___x_6620_ = lean_array_push(v___x_6619_, v___x_6617_);
return v___x_6620_;
}
}
LEAN_EXPORT lean_object* l_Lake_Internal_buildLeanO___lam__0(lean_object* v_weakArgs_6621_, lean_object* v_traceArgs_6622_, lean_object* v_oFile_6623_, lean_object* v_srcFile_6624_, lean_object* v_leanIncludeDir_x3f_6625_, lean_object* v___y_6626_, lean_object* v___y_6627_, lean_object* v___y_6628_, lean_object* v___y_6629_, lean_object* v___y_6630_, lean_object* v___y_6631_){
_start:
{
lean_object* v_toContext_6633_; lean_object* v_lakeEnv_6634_; lean_object* v_log_6635_; uint8_t v_action_6636_; uint8_t v_wantsRebuild_6637_; lean_object* v_trace_6638_; lean_object* v_buildTime_6639_; lean_object* v___x_6641_; uint8_t v_isShared_6642_; uint8_t v_isSharedCheck_6681_; 
v_toContext_6633_ = lean_ctor_get(v___y_6630_, 1);
v_lakeEnv_6634_ = lean_ctor_get(v_toContext_6633_, 0);
v_log_6635_ = lean_ctor_get(v___y_6631_, 0);
v_action_6636_ = lean_ctor_get_uint8(v___y_6631_, sizeof(void*)*3);
v_wantsRebuild_6637_ = lean_ctor_get_uint8(v___y_6631_, sizeof(void*)*3 + 1);
v_trace_6638_ = lean_ctor_get(v___y_6631_, 1);
v_buildTime_6639_ = lean_ctor_get(v___y_6631_, 2);
v_isSharedCheck_6681_ = !lean_is_exclusive(v___y_6631_);
if (v_isSharedCheck_6681_ == 0)
{
v___x_6641_ = v___y_6631_;
v_isShared_6642_ = v_isSharedCheck_6681_;
goto v_resetjp_6640_;
}
else
{
lean_inc(v_buildTime_6639_);
lean_inc(v_trace_6638_);
lean_inc(v_log_6635_);
lean_dec(v___y_6631_);
v___x_6641_ = lean_box(0);
v_isShared_6642_ = v_isSharedCheck_6681_;
goto v_resetjp_6640_;
}
v_resetjp_6640_:
{
lean_object* v_lean_6643_; lean_object* v___y_6645_; 
v_lean_6643_ = lean_ctor_get(v_lakeEnv_6634_, 1);
if (lean_obj_tag(v_leanIncludeDir_x3f_6625_) == 0)
{
lean_object* v_includeDir_6678_; 
v_includeDir_6678_ = lean_ctor_get(v_lean_6643_, 4);
lean_inc_ref(v_includeDir_6678_);
v___y_6645_ = v_includeDir_6678_;
goto v___jp_6644_;
}
else
{
lean_object* v_val_6679_; lean_object* v_fst_6680_; 
v_val_6679_ = lean_ctor_get(v_leanIncludeDir_x3f_6625_, 0);
lean_inc(v_val_6679_);
lean_dec_ref_known(v_leanIncludeDir_x3f_6625_, 1);
v_fst_6680_ = lean_ctor_get(v_val_6679_, 0);
lean_inc(v_fst_6680_);
lean_dec(v_val_6679_);
v___y_6645_ = v_fst_6680_;
goto v___jp_6644_;
}
v___jp_6644_:
{
lean_object* v_cc_6646_; lean_object* v_ccFlags_6647_; lean_object* v___x_6648_; lean_object* v___x_6649_; lean_object* v___x_6650_; lean_object* v___x_6651_; lean_object* v___x_6652_; lean_object* v___x_6653_; 
v_cc_6646_ = lean_ctor_get(v_lean_6643_, 14);
v_ccFlags_6647_ = lean_ctor_get(v_lean_6643_, 18);
v___x_6648_ = lean_obj_once(&l_Lake_Internal_buildLeanO___lam__0___closed__1, &l_Lake_Internal_buildLeanO___lam__0___closed__1_once, _init_l_Lake_Internal_buildLeanO___lam__0___closed__1);
v___x_6649_ = lean_array_push(v___x_6648_, v___y_6645_);
v___x_6650_ = l_Array_append___redArg(v___x_6649_, v_ccFlags_6647_);
v___x_6651_ = l_Array_append___redArg(v___x_6650_, v_weakArgs_6621_);
v___x_6652_ = l_Array_append___redArg(v___x_6651_, v_traceArgs_6622_);
lean_inc_ref(v_cc_6646_);
v___x_6653_ = l_Lake_compileO(v_oFile_6623_, v_srcFile_6624_, v___x_6652_, v_cc_6646_, v_log_6635_);
lean_dec_ref(v___x_6652_);
if (lean_obj_tag(v___x_6653_) == 0)
{
lean_object* v_a_6654_; lean_object* v_a_6655_; lean_object* v___x_6657_; uint8_t v_isShared_6658_; uint8_t v_isSharedCheck_6665_; 
v_a_6654_ = lean_ctor_get(v___x_6653_, 0);
v_a_6655_ = lean_ctor_get(v___x_6653_, 1);
v_isSharedCheck_6665_ = !lean_is_exclusive(v___x_6653_);
if (v_isSharedCheck_6665_ == 0)
{
v___x_6657_ = v___x_6653_;
v_isShared_6658_ = v_isSharedCheck_6665_;
goto v_resetjp_6656_;
}
else
{
lean_inc(v_a_6655_);
lean_inc(v_a_6654_);
lean_dec(v___x_6653_);
v___x_6657_ = lean_box(0);
v_isShared_6658_ = v_isSharedCheck_6665_;
goto v_resetjp_6656_;
}
v_resetjp_6656_:
{
lean_object* v___x_6660_; 
if (v_isShared_6642_ == 0)
{
lean_ctor_set(v___x_6641_, 0, v_a_6655_);
v___x_6660_ = v___x_6641_;
goto v_reusejp_6659_;
}
else
{
lean_object* v_reuseFailAlloc_6664_; 
v_reuseFailAlloc_6664_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6664_, 0, v_a_6655_);
lean_ctor_set(v_reuseFailAlloc_6664_, 1, v_trace_6638_);
lean_ctor_set(v_reuseFailAlloc_6664_, 2, v_buildTime_6639_);
lean_ctor_set_uint8(v_reuseFailAlloc_6664_, sizeof(void*)*3, v_action_6636_);
lean_ctor_set_uint8(v_reuseFailAlloc_6664_, sizeof(void*)*3 + 1, v_wantsRebuild_6637_);
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
v_reuseFailAlloc_6663_ = lean_alloc_ctor(0, 2, 0);
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
else
{
lean_object* v_a_6666_; lean_object* v_a_6667_; lean_object* v___x_6669_; uint8_t v_isShared_6670_; uint8_t v_isSharedCheck_6677_; 
v_a_6666_ = lean_ctor_get(v___x_6653_, 0);
v_a_6667_ = lean_ctor_get(v___x_6653_, 1);
v_isSharedCheck_6677_ = !lean_is_exclusive(v___x_6653_);
if (v_isSharedCheck_6677_ == 0)
{
v___x_6669_ = v___x_6653_;
v_isShared_6670_ = v_isSharedCheck_6677_;
goto v_resetjp_6668_;
}
else
{
lean_inc(v_a_6667_);
lean_inc(v_a_6666_);
lean_dec(v___x_6653_);
v___x_6669_ = lean_box(0);
v_isShared_6670_ = v_isSharedCheck_6677_;
goto v_resetjp_6668_;
}
v_resetjp_6668_:
{
lean_object* v___x_6672_; 
if (v_isShared_6642_ == 0)
{
lean_ctor_set(v___x_6641_, 0, v_a_6667_);
v___x_6672_ = v___x_6641_;
goto v_reusejp_6671_;
}
else
{
lean_object* v_reuseFailAlloc_6676_; 
v_reuseFailAlloc_6676_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6676_, 0, v_a_6667_);
lean_ctor_set(v_reuseFailAlloc_6676_, 1, v_trace_6638_);
lean_ctor_set(v_reuseFailAlloc_6676_, 2, v_buildTime_6639_);
lean_ctor_set_uint8(v_reuseFailAlloc_6676_, sizeof(void*)*3, v_action_6636_);
lean_ctor_set_uint8(v_reuseFailAlloc_6676_, sizeof(void*)*3 + 1, v_wantsRebuild_6637_);
v___x_6672_ = v_reuseFailAlloc_6676_;
goto v_reusejp_6671_;
}
v_reusejp_6671_:
{
lean_object* v___x_6674_; 
if (v_isShared_6670_ == 0)
{
lean_ctor_set(v___x_6669_, 1, v___x_6672_);
v___x_6674_ = v___x_6669_;
goto v_reusejp_6673_;
}
else
{
lean_object* v_reuseFailAlloc_6675_; 
v_reuseFailAlloc_6675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6675_, 0, v_a_6666_);
lean_ctor_set(v_reuseFailAlloc_6675_, 1, v___x_6672_);
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
LEAN_EXPORT lean_object* l_Lake_Internal_buildLeanO___lam__0___boxed(lean_object* v_weakArgs_6682_, lean_object* v_traceArgs_6683_, lean_object* v_oFile_6684_, lean_object* v_srcFile_6685_, lean_object* v_leanIncludeDir_x3f_6686_, lean_object* v___y_6687_, lean_object* v___y_6688_, lean_object* v___y_6689_, lean_object* v___y_6690_, lean_object* v___y_6691_, lean_object* v___y_6692_, lean_object* v___y_6693_){
_start:
{
lean_object* v_res_6694_; 
v_res_6694_ = l_Lake_Internal_buildLeanO___lam__0(v_weakArgs_6682_, v_traceArgs_6683_, v_oFile_6684_, v_srcFile_6685_, v_leanIncludeDir_x3f_6686_, v___y_6687_, v___y_6688_, v___y_6689_, v___y_6690_, v___y_6691_, v___y_6692_);
lean_dec_ref(v___y_6691_);
lean_dec(v___y_6690_);
lean_dec(v___y_6689_);
lean_dec(v___y_6688_);
lean_dec_ref(v___y_6687_);
lean_dec_ref(v_traceArgs_6683_);
lean_dec_ref(v_weakArgs_6682_);
return v_res_6694_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_Internal_buildLeanO_spec__0_spec__0(lean_object* v_x_6696_, lean_object* v_x_6697_){
_start:
{
if (lean_obj_tag(v_x_6697_) == 0)
{
return v_x_6696_;
}
else
{
lean_object* v_head_6698_; lean_object* v_tail_6699_; lean_object* v___x_6700_; lean_object* v___x_6701_; lean_object* v___x_6702_; 
v_head_6698_ = lean_ctor_get(v_x_6697_, 0);
v_tail_6699_ = lean_ctor_get(v_x_6697_, 1);
v___x_6700_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lake_Internal_buildLeanO_spec__0_spec__0___closed__0));
v___x_6701_ = lean_string_append(v_x_6696_, v___x_6700_);
v___x_6702_ = lean_string_append(v___x_6701_, v_head_6698_);
v_x_6696_ = v___x_6702_;
v_x_6697_ = v_tail_6699_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_Internal_buildLeanO_spec__0_spec__0___boxed(lean_object* v_x_6704_, lean_object* v_x_6705_){
_start:
{
lean_object* v_res_6706_; 
v_res_6706_ = l_List_foldl___at___00List_toString___at___00Lake_Internal_buildLeanO_spec__0_spec__0(v_x_6704_, v_x_6705_);
lean_dec(v_x_6705_);
return v_res_6706_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_Internal_buildLeanO_spec__0(lean_object* v_x_6710_){
_start:
{
if (lean_obj_tag(v_x_6710_) == 0)
{
lean_object* v___x_6711_; 
v___x_6711_ = ((lean_object*)(l_List_toString___at___00Lake_Internal_buildLeanO_spec__0___closed__0));
return v___x_6711_;
}
else
{
lean_object* v_tail_6712_; 
v_tail_6712_ = lean_ctor_get(v_x_6710_, 1);
if (lean_obj_tag(v_tail_6712_) == 0)
{
lean_object* v_head_6713_; lean_object* v___x_6714_; lean_object* v___x_6715_; lean_object* v___x_6716_; lean_object* v___x_6717_; 
v_head_6713_ = lean_ctor_get(v_x_6710_, 0);
v___x_6714_ = ((lean_object*)(l_List_toString___at___00Lake_Internal_buildLeanO_spec__0___closed__1));
v___x_6715_ = lean_string_append(v___x_6714_, v_head_6713_);
v___x_6716_ = ((lean_object*)(l_List_toString___at___00Lake_Internal_buildLeanO_spec__0___closed__2));
v___x_6717_ = lean_string_append(v___x_6715_, v___x_6716_);
return v___x_6717_;
}
else
{
lean_object* v_head_6718_; lean_object* v___x_6719_; lean_object* v___x_6720_; lean_object* v___x_6721_; uint32_t v___x_6722_; lean_object* v___x_6723_; 
v_head_6718_ = lean_ctor_get(v_x_6710_, 0);
v___x_6719_ = ((lean_object*)(l_List_toString___at___00Lake_Internal_buildLeanO_spec__0___closed__1));
v___x_6720_ = lean_string_append(v___x_6719_, v_head_6718_);
v___x_6721_ = l_List_foldl___at___00List_toString___at___00Lake_Internal_buildLeanO_spec__0_spec__0(v___x_6720_, v_tail_6712_);
v___x_6722_ = 93;
v___x_6723_ = lean_string_push(v___x_6721_, v___x_6722_);
return v___x_6723_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_Internal_buildLeanO_spec__0___boxed(lean_object* v_x_6724_){
_start:
{
lean_object* v_res_6725_; 
v_res_6725_ = l_List_toString___at___00Lake_Internal_buildLeanO_spec__0(v_x_6724_);
lean_dec(v_x_6724_);
return v_res_6725_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Internal_buildLeanO_spec__1(lean_object* v_as_6726_, size_t v_i_6727_, size_t v_stop_6728_, uint64_t v_b_6729_){
_start:
{
uint8_t v___x_6730_; 
v___x_6730_ = lean_usize_dec_eq(v_i_6727_, v_stop_6728_);
if (v___x_6730_ == 0)
{
lean_object* v___x_6731_; uint64_t v___x_6732_; uint64_t v___x_6733_; uint64_t v___x_6734_; uint64_t v___x_6735_; size_t v___x_6736_; size_t v___x_6737_; 
v___x_6731_ = lean_array_uget_borrowed(v_as_6726_, v_i_6727_);
v___x_6732_ = l_Lake_Hash_nil;
v___x_6733_ = lean_string_hash(v___x_6731_);
v___x_6734_ = lean_uint64_mix_hash(v___x_6732_, v___x_6733_);
v___x_6735_ = lean_uint64_mix_hash(v_b_6729_, v___x_6734_);
v___x_6736_ = ((size_t)1ULL);
v___x_6737_ = lean_usize_add(v_i_6727_, v___x_6736_);
v_i_6727_ = v___x_6737_;
v_b_6729_ = v___x_6735_;
goto _start;
}
else
{
return v_b_6729_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Internal_buildLeanO_spec__1___boxed(lean_object* v_as_6739_, lean_object* v_i_6740_, lean_object* v_stop_6741_, lean_object* v_b_6742_){
_start:
{
size_t v_i_boxed_6743_; size_t v_stop_boxed_6744_; uint64_t v_b_boxed_6745_; uint64_t v_res_6746_; lean_object* v_r_6747_; 
v_i_boxed_6743_ = lean_unbox_usize(v_i_6740_);
lean_dec(v_i_6740_);
v_stop_boxed_6744_ = lean_unbox_usize(v_stop_6741_);
lean_dec(v_stop_6741_);
v_b_boxed_6745_ = lean_unbox_uint64(v_b_6742_);
lean_dec_ref(v_b_6742_);
v_res_6746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Internal_buildLeanO_spec__1(v_as_6739_, v_i_boxed_6743_, v_stop_boxed_6744_, v_b_boxed_6745_);
lean_dec_ref(v_as_6739_);
v_r_6747_ = lean_box_uint64(v_res_6746_);
return v_r_6747_;
}
}
LEAN_EXPORT lean_object* l_Lake_Internal_buildLeanO___lam__1(lean_object* v_weakArgs_6748_, lean_object* v_traceArgs_6749_, lean_object* v_oFile_6750_, lean_object* v_leanIncludeDir_x3f_6751_, lean_object* v_srcFile_6752_, lean_object* v___y_6753_, lean_object* v___y_6754_, lean_object* v___y_6755_, lean_object* v___y_6756_, lean_object* v___y_6757_, lean_object* v___y_6758_){
_start:
{
lean_object* v_log_6760_; uint8_t v_action_6761_; uint8_t v_wantsRebuild_6762_; lean_object* v_trace_6763_; lean_object* v_buildTime_6764_; lean_object* v___x_6766_; uint8_t v_isShared_6767_; uint8_t v_isSharedCheck_6848_; 
v_log_6760_ = lean_ctor_get(v___y_6758_, 0);
v_action_6761_ = lean_ctor_get_uint8(v___y_6758_, sizeof(void*)*3);
v_wantsRebuild_6762_ = lean_ctor_get_uint8(v___y_6758_, sizeof(void*)*3 + 1);
v_trace_6763_ = lean_ctor_get(v___y_6758_, 1);
v_buildTime_6764_ = lean_ctor_get(v___y_6758_, 2);
v_isSharedCheck_6848_ = !lean_is_exclusive(v___y_6758_);
if (v_isSharedCheck_6848_ == 0)
{
v___x_6766_ = v___y_6758_;
v_isShared_6767_ = v_isSharedCheck_6848_;
goto v_resetjp_6765_;
}
else
{
lean_inc(v_buildTime_6764_);
lean_inc(v_trace_6763_);
lean_inc(v_log_6760_);
lean_dec(v___y_6758_);
v___x_6766_ = lean_box(0);
v_isShared_6767_ = v_isSharedCheck_6848_;
goto v_resetjp_6765_;
}
v_resetjp_6765_:
{
lean_object* v_leanTrace_6768_; lean_object* v___f_6769_; lean_object* v___y_6771_; lean_object* v___y_6772_; lean_object* v___y_6773_; lean_object* v___y_6774_; lean_object* v___y_6775_; lean_object* v___y_6776_; uint64_t v___y_6777_; lean_object* v___y_6825_; lean_object* v___y_6826_; lean_object* v___y_6827_; lean_object* v___y_6828_; lean_object* v___y_6829_; lean_object* v___y_6830_; lean_object* v___x_6838_; 
v_leanTrace_6768_ = lean_ctor_get(v___y_6757_, 2);
lean_inc(v_leanIncludeDir_x3f_6751_);
lean_inc_ref(v_oFile_6750_);
lean_inc_ref(v_traceArgs_6749_);
v___f_6769_ = lean_alloc_closure((void*)(l_Lake_Internal_buildLeanO___lam__0___boxed), 12, 5);
lean_closure_set(v___f_6769_, 0, v_weakArgs_6748_);
lean_closure_set(v___f_6769_, 1, v_traceArgs_6749_);
lean_closure_set(v___f_6769_, 2, v_oFile_6750_);
lean_closure_set(v___f_6769_, 3, v_srcFile_6752_);
lean_closure_set(v___f_6769_, 4, v_leanIncludeDir_x3f_6751_);
lean_inc_ref(v_leanTrace_6768_);
v___x_6838_ = l_Lake_BuildTrace_mix(v_trace_6763_, v_leanTrace_6768_);
if (lean_obj_tag(v_leanIncludeDir_x3f_6751_) == 1)
{
lean_object* v_val_6839_; lean_object* v_snd_6840_; lean_object* v___x_6841_; lean_object* v___x_6843_; 
v_val_6839_ = lean_ctor_get(v_leanIncludeDir_x3f_6751_, 0);
lean_inc(v_val_6839_);
lean_dec_ref_known(v_leanIncludeDir_x3f_6751_, 1);
v_snd_6840_ = lean_ctor_get(v_val_6839_, 1);
lean_inc(v_snd_6840_);
lean_dec(v_val_6839_);
v___x_6841_ = l_Lake_BuildTrace_mix(v___x_6838_, v_snd_6840_);
if (v_isShared_6767_ == 0)
{
lean_ctor_set(v___x_6766_, 1, v___x_6841_);
v___x_6843_ = v___x_6766_;
goto v_reusejp_6842_;
}
else
{
lean_object* v_reuseFailAlloc_6844_; 
v_reuseFailAlloc_6844_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6844_, 0, v_log_6760_);
lean_ctor_set(v_reuseFailAlloc_6844_, 1, v___x_6841_);
lean_ctor_set(v_reuseFailAlloc_6844_, 2, v_buildTime_6764_);
lean_ctor_set_uint8(v_reuseFailAlloc_6844_, sizeof(void*)*3, v_action_6761_);
lean_ctor_set_uint8(v_reuseFailAlloc_6844_, sizeof(void*)*3 + 1, v_wantsRebuild_6762_);
v___x_6843_ = v_reuseFailAlloc_6844_;
goto v_reusejp_6842_;
}
v_reusejp_6842_:
{
v___y_6825_ = v___y_6753_;
v___y_6826_ = v___y_6754_;
v___y_6827_ = v___y_6755_;
v___y_6828_ = v___y_6756_;
v___y_6829_ = v___y_6757_;
v___y_6830_ = v___x_6843_;
goto v___jp_6824_;
}
}
else
{
lean_object* v___x_6846_; 
lean_dec(v_leanIncludeDir_x3f_6751_);
if (v_isShared_6767_ == 0)
{
lean_ctor_set(v___x_6766_, 1, v___x_6838_);
v___x_6846_ = v___x_6766_;
goto v_reusejp_6845_;
}
else
{
lean_object* v_reuseFailAlloc_6847_; 
v_reuseFailAlloc_6847_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6847_, 0, v_log_6760_);
lean_ctor_set(v_reuseFailAlloc_6847_, 1, v___x_6838_);
lean_ctor_set(v_reuseFailAlloc_6847_, 2, v_buildTime_6764_);
lean_ctor_set_uint8(v_reuseFailAlloc_6847_, sizeof(void*)*3, v_action_6761_);
lean_ctor_set_uint8(v_reuseFailAlloc_6847_, sizeof(void*)*3 + 1, v_wantsRebuild_6762_);
v___x_6846_ = v_reuseFailAlloc_6847_;
goto v_reusejp_6845_;
}
v_reusejp_6845_:
{
v___y_6825_ = v___y_6753_;
v___y_6826_ = v___y_6754_;
v___y_6827_ = v___y_6755_;
v___y_6828_ = v___y_6756_;
v___y_6829_ = v___y_6757_;
v___y_6830_ = v___x_6846_;
goto v___jp_6824_;
}
}
v___jp_6770_:
{
lean_object* v_log_6778_; uint8_t v_action_6779_; uint8_t v_wantsRebuild_6780_; lean_object* v_trace_6781_; lean_object* v_buildTime_6782_; lean_object* v___x_6784_; uint8_t v_isShared_6785_; uint8_t v_isSharedCheck_6823_; 
v_log_6778_ = lean_ctor_get(v___y_6771_, 0);
v_action_6779_ = lean_ctor_get_uint8(v___y_6771_, sizeof(void*)*3);
v_wantsRebuild_6780_ = lean_ctor_get_uint8(v___y_6771_, sizeof(void*)*3 + 1);
v_trace_6781_ = lean_ctor_get(v___y_6771_, 1);
v_buildTime_6782_ = lean_ctor_get(v___y_6771_, 2);
v_isSharedCheck_6823_ = !lean_is_exclusive(v___y_6771_);
if (v_isSharedCheck_6823_ == 0)
{
v___x_6784_ = v___y_6771_;
v_isShared_6785_ = v_isSharedCheck_6823_;
goto v_resetjp_6783_;
}
else
{
lean_inc(v_buildTime_6782_);
lean_inc(v_trace_6781_);
lean_inc(v_log_6778_);
lean_dec(v___y_6771_);
v___x_6784_ = lean_box(0);
v_isShared_6785_ = v_isSharedCheck_6823_;
goto v_resetjp_6783_;
}
v_resetjp_6783_:
{
lean_object* v___x_6786_; lean_object* v___x_6787_; lean_object* v___x_6788_; lean_object* v___x_6789_; lean_object* v___x_6790_; lean_object* v___x_6791_; lean_object* v___x_6792_; lean_object* v___x_6793_; lean_object* v___x_6794_; lean_object* v___x_6795_; lean_object* v___x_6796_; lean_object* v___x_6797_; lean_object* v___x_6799_; 
v___x_6786_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_6787_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_6788_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
v___x_6789_ = lean_array_to_list(v_traceArgs_6749_);
v___x_6790_ = l_List_toString___at___00Lake_Internal_buildLeanO_spec__0(v___x_6789_);
lean_dec(v___x_6789_);
v___x_6791_ = lean_string_append(v___x_6788_, v___x_6790_);
lean_dec_ref(v___x_6790_);
v___x_6792_ = lean_string_append(v___x_6787_, v___x_6791_);
lean_dec_ref(v___x_6791_);
v___x_6793_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_6794_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_6794_, 0, v___x_6792_);
lean_ctor_set(v___x_6794_, 1, v___x_6786_);
lean_ctor_set(v___x_6794_, 2, v___x_6793_);
lean_ctor_set_uint64(v___x_6794_, sizeof(void*)*3, v___y_6777_);
v___x_6795_ = l_Lake_BuildTrace_mix(v_trace_6781_, v___x_6794_);
v___x_6796_ = l_Lake_platformTrace;
v___x_6797_ = l_Lake_BuildTrace_mix(v___x_6795_, v___x_6796_);
if (v_isShared_6785_ == 0)
{
lean_ctor_set(v___x_6784_, 1, v___x_6797_);
v___x_6799_ = v___x_6784_;
goto v_reusejp_6798_;
}
else
{
lean_object* v_reuseFailAlloc_6822_; 
v_reuseFailAlloc_6822_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6822_, 0, v_log_6778_);
lean_ctor_set(v_reuseFailAlloc_6822_, 1, v___x_6797_);
lean_ctor_set(v_reuseFailAlloc_6822_, 2, v_buildTime_6782_);
lean_ctor_set_uint8(v_reuseFailAlloc_6822_, sizeof(void*)*3, v_action_6779_);
lean_ctor_set_uint8(v_reuseFailAlloc_6822_, sizeof(void*)*3 + 1, v_wantsRebuild_6780_);
v___x_6799_ = v_reuseFailAlloc_6822_;
goto v_reusejp_6798_;
}
v_reusejp_6798_:
{
uint8_t v___x_6800_; lean_object* v___x_6801_; lean_object* v___x_6802_; 
v___x_6800_ = 0;
v___x_6801_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__2));
v___x_6802_ = l_Lake_buildArtifactUnlessUpToDate(v_oFile_6750_, v___f_6769_, v___x_6800_, v___x_6801_, v___x_6800_, v___x_6800_, v___x_6800_, v___y_6774_, v___y_6776_, v___y_6775_, v___y_6773_, v___y_6772_, v___x_6799_);
if (lean_obj_tag(v___x_6802_) == 0)
{
lean_object* v_a_6803_; lean_object* v_a_6804_; lean_object* v___x_6806_; uint8_t v_isShared_6807_; uint8_t v_isSharedCheck_6812_; 
v_a_6803_ = lean_ctor_get(v___x_6802_, 0);
v_a_6804_ = lean_ctor_get(v___x_6802_, 1);
v_isSharedCheck_6812_ = !lean_is_exclusive(v___x_6802_);
if (v_isSharedCheck_6812_ == 0)
{
v___x_6806_ = v___x_6802_;
v_isShared_6807_ = v_isSharedCheck_6812_;
goto v_resetjp_6805_;
}
else
{
lean_inc(v_a_6804_);
lean_inc(v_a_6803_);
lean_dec(v___x_6802_);
v___x_6806_ = lean_box(0);
v_isShared_6807_ = v_isSharedCheck_6812_;
goto v_resetjp_6805_;
}
v_resetjp_6805_:
{
lean_object* v_path_6808_; lean_object* v___x_6810_; 
v_path_6808_ = lean_ctor_get(v_a_6803_, 1);
lean_inc_ref(v_path_6808_);
lean_dec(v_a_6803_);
if (v_isShared_6807_ == 0)
{
lean_ctor_set(v___x_6806_, 0, v_path_6808_);
v___x_6810_ = v___x_6806_;
goto v_reusejp_6809_;
}
else
{
lean_object* v_reuseFailAlloc_6811_; 
v_reuseFailAlloc_6811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6811_, 0, v_path_6808_);
lean_ctor_set(v_reuseFailAlloc_6811_, 1, v_a_6804_);
v___x_6810_ = v_reuseFailAlloc_6811_;
goto v_reusejp_6809_;
}
v_reusejp_6809_:
{
return v___x_6810_;
}
}
}
else
{
lean_object* v_a_6813_; lean_object* v_a_6814_; lean_object* v___x_6816_; uint8_t v_isShared_6817_; uint8_t v_isSharedCheck_6821_; 
v_a_6813_ = lean_ctor_get(v___x_6802_, 0);
v_a_6814_ = lean_ctor_get(v___x_6802_, 1);
v_isSharedCheck_6821_ = !lean_is_exclusive(v___x_6802_);
if (v_isSharedCheck_6821_ == 0)
{
v___x_6816_ = v___x_6802_;
v_isShared_6817_ = v_isSharedCheck_6821_;
goto v_resetjp_6815_;
}
else
{
lean_inc(v_a_6814_);
lean_inc(v_a_6813_);
lean_dec(v___x_6802_);
v___x_6816_ = lean_box(0);
v_isShared_6817_ = v_isSharedCheck_6821_;
goto v_resetjp_6815_;
}
v_resetjp_6815_:
{
lean_object* v___x_6819_; 
if (v_isShared_6817_ == 0)
{
v___x_6819_ = v___x_6816_;
goto v_reusejp_6818_;
}
else
{
lean_object* v_reuseFailAlloc_6820_; 
v_reuseFailAlloc_6820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6820_, 0, v_a_6813_);
lean_ctor_set(v_reuseFailAlloc_6820_, 1, v_a_6814_);
v___x_6819_ = v_reuseFailAlloc_6820_;
goto v_reusejp_6818_;
}
v_reusejp_6818_:
{
return v___x_6819_;
}
}
}
}
}
}
v___jp_6824_:
{
uint64_t v___x_6831_; lean_object* v___x_6832_; lean_object* v___x_6833_; uint8_t v___x_6834_; 
v___x_6831_ = l_Lake_Hash_nil;
v___x_6832_ = lean_unsigned_to_nat(0u);
v___x_6833_ = lean_array_get_size(v_traceArgs_6749_);
v___x_6834_ = lean_nat_dec_lt(v___x_6832_, v___x_6833_);
if (v___x_6834_ == 0)
{
v___y_6771_ = v___y_6830_;
v___y_6772_ = v___y_6829_;
v___y_6773_ = v___y_6828_;
v___y_6774_ = v___y_6825_;
v___y_6775_ = v___y_6827_;
v___y_6776_ = v___y_6826_;
v___y_6777_ = v___x_6831_;
goto v___jp_6770_;
}
else
{
size_t v___x_6835_; size_t v___x_6836_; uint64_t v___x_6837_; 
v___x_6835_ = ((size_t)0ULL);
v___x_6836_ = lean_usize_of_nat(v___x_6833_);
v___x_6837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Internal_buildLeanO_spec__1(v_traceArgs_6749_, v___x_6835_, v___x_6836_, v___x_6831_);
v___y_6771_ = v___y_6830_;
v___y_6772_ = v___y_6829_;
v___y_6773_ = v___y_6828_;
v___y_6774_ = v___y_6825_;
v___y_6775_ = v___y_6827_;
v___y_6776_ = v___y_6826_;
v___y_6777_ = v___x_6837_;
goto v___jp_6770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Internal_buildLeanO___lam__1___boxed(lean_object* v_weakArgs_6849_, lean_object* v_traceArgs_6850_, lean_object* v_oFile_6851_, lean_object* v_leanIncludeDir_x3f_6852_, lean_object* v_srcFile_6853_, lean_object* v___y_6854_, lean_object* v___y_6855_, lean_object* v___y_6856_, lean_object* v___y_6857_, lean_object* v___y_6858_, lean_object* v___y_6859_, lean_object* v___y_6860_){
_start:
{
lean_object* v_res_6861_; 
v_res_6861_ = l_Lake_Internal_buildLeanO___lam__1(v_weakArgs_6849_, v_traceArgs_6850_, v_oFile_6851_, v_leanIncludeDir_x3f_6852_, v_srcFile_6853_, v___y_6854_, v___y_6855_, v___y_6856_, v___y_6857_, v___y_6858_, v___y_6859_);
lean_dec_ref(v___y_6858_);
lean_dec(v___y_6857_);
lean_dec(v___y_6856_);
lean_dec(v___y_6855_);
return v_res_6861_;
}
}
LEAN_EXPORT lean_object* l_Lake_Internal_buildLeanO(lean_object* v_oFile_6862_, lean_object* v_srcJob_6863_, lean_object* v_weakArgs_6864_, lean_object* v_traceArgs_6865_, lean_object* v_leanIncludeDir_x3f_6866_, lean_object* v_a_6867_, lean_object* v_a_6868_, lean_object* v_a_6869_, lean_object* v_a_6870_, lean_object* v_a_6871_, lean_object* v_a_6872_){
_start:
{
lean_object* v___f_6874_; lean_object* v___x_6875_; lean_object* v___x_6876_; uint8_t v___x_6877_; lean_object* v___x_6878_; 
v___f_6874_ = lean_alloc_closure((void*)(l_Lake_Internal_buildLeanO___lam__1___boxed), 12, 4);
lean_closure_set(v___f_6874_, 0, v_weakArgs_6864_);
lean_closure_set(v___f_6874_, 1, v_traceArgs_6865_);
lean_closure_set(v___f_6874_, 2, v_oFile_6862_);
lean_closure_set(v___f_6874_, 3, v_leanIncludeDir_x3f_6866_);
v___x_6875_ = l_Lake_instDataKindFilePath;
v___x_6876_ = lean_unsigned_to_nat(0u);
v___x_6877_ = 0;
v___x_6878_ = l_Lake_Job_mapM___redArg(v___x_6875_, v_srcJob_6863_, v___f_6874_, v___x_6876_, v___x_6877_, v_a_6867_, v_a_6868_, v_a_6869_, v_a_6870_, v_a_6871_, v_a_6872_);
return v___x_6878_;
}
}
LEAN_EXPORT lean_object* l_Lake_Internal_buildLeanO___boxed(lean_object* v_oFile_6879_, lean_object* v_srcJob_6880_, lean_object* v_weakArgs_6881_, lean_object* v_traceArgs_6882_, lean_object* v_leanIncludeDir_x3f_6883_, lean_object* v_a_6884_, lean_object* v_a_6885_, lean_object* v_a_6886_, lean_object* v_a_6887_, lean_object* v_a_6888_, lean_object* v_a_6889_, lean_object* v_a_6890_){
_start:
{
lean_object* v_res_6891_; 
v_res_6891_ = l_Lake_Internal_buildLeanO(v_oFile_6879_, v_srcJob_6880_, v_weakArgs_6881_, v_traceArgs_6882_, v_leanIncludeDir_x3f_6883_, v_a_6884_, v_a_6885_, v_a_6886_, v_a_6887_, v_a_6888_, v_a_6889_);
lean_dec_ref(v_a_6889_);
lean_dec_ref(v_a_6888_);
lean_dec(v_a_6887_);
lean_dec(v_a_6886_);
lean_dec(v_a_6885_);
return v_res_6891_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object* v_oFile_6892_, lean_object* v_srcJob_6893_, lean_object* v_weakArgs_6894_, lean_object* v_traceArgs_6895_, lean_object* v_a_6896_, lean_object* v_a_6897_, lean_object* v_a_6898_, lean_object* v_a_6899_, lean_object* v_a_6900_, lean_object* v_a_6901_){
_start:
{
lean_object* v___x_6903_; lean_object* v___x_6904_; 
v___x_6903_ = lean_box(0);
v___x_6904_ = l_Lake_Internal_buildLeanO(v_oFile_6892_, v_srcJob_6893_, v_weakArgs_6894_, v_traceArgs_6895_, v___x_6903_, v_a_6896_, v_a_6897_, v_a_6898_, v_a_6899_, v_a_6900_, v_a_6901_);
return v___x_6904_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___boxed(lean_object* v_oFile_6905_, lean_object* v_srcJob_6906_, lean_object* v_weakArgs_6907_, lean_object* v_traceArgs_6908_, lean_object* v_a_6909_, lean_object* v_a_6910_, lean_object* v_a_6911_, lean_object* v_a_6912_, lean_object* v_a_6913_, lean_object* v_a_6914_, lean_object* v_a_6915_){
_start:
{
lean_object* v_res_6916_; 
v_res_6916_ = l_Lake_buildLeanO(v_oFile_6905_, v_srcJob_6906_, v_weakArgs_6907_, v_traceArgs_6908_, v_a_6909_, v_a_6910_, v_a_6911_, v_a_6912_, v_a_6913_, v_a_6914_);
lean_dec_ref(v_a_6914_);
lean_dec_ref(v_a_6913_);
lean_dec(v_a_6912_);
lean_dec(v_a_6911_);
lean_dec(v_a_6910_);
return v_res_6916_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0(lean_object* v_libFile_6917_, lean_object* v_oFiles_6918_, uint8_t v_thin_6919_, lean_object* v___y_6920_, lean_object* v___y_6921_, lean_object* v___y_6922_, lean_object* v___y_6923_, lean_object* v___y_6924_, lean_object* v___y_6925_){
_start:
{
lean_object* v_toContext_6927_; lean_object* v_lakeEnv_6928_; lean_object* v_lean_6929_; lean_object* v_log_6930_; uint8_t v_action_6931_; uint8_t v_wantsRebuild_6932_; lean_object* v_trace_6933_; lean_object* v_buildTime_6934_; lean_object* v___x_6936_; uint8_t v_isShared_6937_; uint8_t v_isSharedCheck_6964_; 
v_toContext_6927_ = lean_ctor_get(v___y_6924_, 1);
v_lakeEnv_6928_ = lean_ctor_get(v_toContext_6927_, 0);
v_lean_6929_ = lean_ctor_get(v_lakeEnv_6928_, 1);
v_log_6930_ = lean_ctor_get(v___y_6925_, 0);
v_action_6931_ = lean_ctor_get_uint8(v___y_6925_, sizeof(void*)*3);
v_wantsRebuild_6932_ = lean_ctor_get_uint8(v___y_6925_, sizeof(void*)*3 + 1);
v_trace_6933_ = lean_ctor_get(v___y_6925_, 1);
v_buildTime_6934_ = lean_ctor_get(v___y_6925_, 2);
v_isSharedCheck_6964_ = !lean_is_exclusive(v___y_6925_);
if (v_isSharedCheck_6964_ == 0)
{
v___x_6936_ = v___y_6925_;
v_isShared_6937_ = v_isSharedCheck_6964_;
goto v_resetjp_6935_;
}
else
{
lean_inc(v_buildTime_6934_);
lean_inc(v_trace_6933_);
lean_inc(v_log_6930_);
lean_dec(v___y_6925_);
v___x_6936_ = lean_box(0);
v_isShared_6937_ = v_isSharedCheck_6964_;
goto v_resetjp_6935_;
}
v_resetjp_6935_:
{
lean_object* v_ar_6938_; lean_object* v___x_6939_; 
v_ar_6938_ = lean_ctor_get(v_lean_6929_, 13);
lean_inc_ref(v_ar_6938_);
v___x_6939_ = l_Lake_compileStaticLib(v_libFile_6917_, v_oFiles_6918_, v_ar_6938_, v_thin_6919_, v_log_6930_);
if (lean_obj_tag(v___x_6939_) == 0)
{
lean_object* v_a_6940_; lean_object* v_a_6941_; lean_object* v___x_6943_; uint8_t v_isShared_6944_; uint8_t v_isSharedCheck_6951_; 
v_a_6940_ = lean_ctor_get(v___x_6939_, 0);
v_a_6941_ = lean_ctor_get(v___x_6939_, 1);
v_isSharedCheck_6951_ = !lean_is_exclusive(v___x_6939_);
if (v_isSharedCheck_6951_ == 0)
{
v___x_6943_ = v___x_6939_;
v_isShared_6944_ = v_isSharedCheck_6951_;
goto v_resetjp_6942_;
}
else
{
lean_inc(v_a_6941_);
lean_inc(v_a_6940_);
lean_dec(v___x_6939_);
v___x_6943_ = lean_box(0);
v_isShared_6944_ = v_isSharedCheck_6951_;
goto v_resetjp_6942_;
}
v_resetjp_6942_:
{
lean_object* v___x_6946_; 
if (v_isShared_6937_ == 0)
{
lean_ctor_set(v___x_6936_, 0, v_a_6941_);
v___x_6946_ = v___x_6936_;
goto v_reusejp_6945_;
}
else
{
lean_object* v_reuseFailAlloc_6950_; 
v_reuseFailAlloc_6950_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6950_, 0, v_a_6941_);
lean_ctor_set(v_reuseFailAlloc_6950_, 1, v_trace_6933_);
lean_ctor_set(v_reuseFailAlloc_6950_, 2, v_buildTime_6934_);
lean_ctor_set_uint8(v_reuseFailAlloc_6950_, sizeof(void*)*3, v_action_6931_);
lean_ctor_set_uint8(v_reuseFailAlloc_6950_, sizeof(void*)*3 + 1, v_wantsRebuild_6932_);
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
v_reuseFailAlloc_6949_ = lean_alloc_ctor(0, 2, 0);
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
else
{
lean_object* v_a_6952_; lean_object* v_a_6953_; lean_object* v___x_6955_; uint8_t v_isShared_6956_; uint8_t v_isSharedCheck_6963_; 
v_a_6952_ = lean_ctor_get(v___x_6939_, 0);
v_a_6953_ = lean_ctor_get(v___x_6939_, 1);
v_isSharedCheck_6963_ = !lean_is_exclusive(v___x_6939_);
if (v_isSharedCheck_6963_ == 0)
{
v___x_6955_ = v___x_6939_;
v_isShared_6956_ = v_isSharedCheck_6963_;
goto v_resetjp_6954_;
}
else
{
lean_inc(v_a_6953_);
lean_inc(v_a_6952_);
lean_dec(v___x_6939_);
v___x_6955_ = lean_box(0);
v_isShared_6956_ = v_isSharedCheck_6963_;
goto v_resetjp_6954_;
}
v_resetjp_6954_:
{
lean_object* v___x_6958_; 
if (v_isShared_6937_ == 0)
{
lean_ctor_set(v___x_6936_, 0, v_a_6953_);
v___x_6958_ = v___x_6936_;
goto v_reusejp_6957_;
}
else
{
lean_object* v_reuseFailAlloc_6962_; 
v_reuseFailAlloc_6962_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_6962_, 0, v_a_6953_);
lean_ctor_set(v_reuseFailAlloc_6962_, 1, v_trace_6933_);
lean_ctor_set(v_reuseFailAlloc_6962_, 2, v_buildTime_6934_);
lean_ctor_set_uint8(v_reuseFailAlloc_6962_, sizeof(void*)*3, v_action_6931_);
lean_ctor_set_uint8(v_reuseFailAlloc_6962_, sizeof(void*)*3 + 1, v_wantsRebuild_6932_);
v___x_6958_ = v_reuseFailAlloc_6962_;
goto v_reusejp_6957_;
}
v_reusejp_6957_:
{
lean_object* v___x_6960_; 
if (v_isShared_6956_ == 0)
{
lean_ctor_set(v___x_6955_, 1, v___x_6958_);
v___x_6960_ = v___x_6955_;
goto v_reusejp_6959_;
}
else
{
lean_object* v_reuseFailAlloc_6961_; 
v_reuseFailAlloc_6961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6961_, 0, v_a_6952_);
lean_ctor_set(v_reuseFailAlloc_6961_, 1, v___x_6958_);
v___x_6960_ = v_reuseFailAlloc_6961_;
goto v_reusejp_6959_;
}
v_reusejp_6959_:
{
return v___x_6960_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0___boxed(lean_object* v_libFile_6965_, lean_object* v_oFiles_6966_, lean_object* v_thin_6967_, lean_object* v___y_6968_, lean_object* v___y_6969_, lean_object* v___y_6970_, lean_object* v___y_6971_, lean_object* v___y_6972_, lean_object* v___y_6973_, lean_object* v___y_6974_){
_start:
{
uint8_t v_thin_boxed_6975_; lean_object* v_res_6976_; 
v_thin_boxed_6975_ = lean_unbox(v_thin_6967_);
v_res_6976_ = l_Lake_buildStaticLib___lam__0(v_libFile_6965_, v_oFiles_6966_, v_thin_boxed_6975_, v___y_6968_, v___y_6969_, v___y_6970_, v___y_6971_, v___y_6972_, v___y_6973_);
lean_dec_ref(v___y_6972_);
lean_dec(v___y_6971_);
lean_dec(v___y_6970_);
lean_dec(v___y_6969_);
lean_dec_ref(v___y_6968_);
return v_res_6976_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1(lean_object* v_libFile_6978_, uint8_t v_thin_6979_, lean_object* v_oFiles_6980_, lean_object* v___y_6981_, lean_object* v___y_6982_, lean_object* v___y_6983_, lean_object* v___y_6984_, lean_object* v___y_6985_, lean_object* v___y_6986_){
_start:
{
lean_object* v___x_6988_; lean_object* v___f_6989_; uint8_t v___x_6990_; lean_object* v___x_6991_; uint8_t v___x_6992_; lean_object* v___x_6993_; 
v___x_6988_ = lean_box(v_thin_6979_);
lean_inc_ref(v_libFile_6978_);
v___f_6989_ = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6989_, 0, v_libFile_6978_);
lean_closure_set(v___f_6989_, 1, v_oFiles_6980_);
lean_closure_set(v___f_6989_, 2, v___x_6988_);
v___x_6990_ = 0;
v___x_6991_ = ((lean_object*)(l_Lake_buildStaticLib___lam__1___closed__0));
v___x_6992_ = 1;
v___x_6993_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_6978_, v___f_6989_, v___x_6990_, v___x_6991_, v___x_6992_, v___x_6990_, v___x_6990_, v___y_6981_, v___y_6982_, v___y_6983_, v___y_6984_, v___y_6985_, v___y_6986_);
if (lean_obj_tag(v___x_6993_) == 0)
{
lean_object* v_a_6994_; lean_object* v_a_6995_; lean_object* v___x_6997_; uint8_t v_isShared_6998_; uint8_t v_isSharedCheck_7003_; 
v_a_6994_ = lean_ctor_get(v___x_6993_, 0);
v_a_6995_ = lean_ctor_get(v___x_6993_, 1);
v_isSharedCheck_7003_ = !lean_is_exclusive(v___x_6993_);
if (v_isSharedCheck_7003_ == 0)
{
v___x_6997_ = v___x_6993_;
v_isShared_6998_ = v_isSharedCheck_7003_;
goto v_resetjp_6996_;
}
else
{
lean_inc(v_a_6995_);
lean_inc(v_a_6994_);
lean_dec(v___x_6993_);
v___x_6997_ = lean_box(0);
v_isShared_6998_ = v_isSharedCheck_7003_;
goto v_resetjp_6996_;
}
v_resetjp_6996_:
{
lean_object* v_path_6999_; lean_object* v___x_7001_; 
v_path_6999_ = lean_ctor_get(v_a_6994_, 1);
lean_inc_ref(v_path_6999_);
lean_dec(v_a_6994_);
if (v_isShared_6998_ == 0)
{
lean_ctor_set(v___x_6997_, 0, v_path_6999_);
v___x_7001_ = v___x_6997_;
goto v_reusejp_7000_;
}
else
{
lean_object* v_reuseFailAlloc_7002_; 
v_reuseFailAlloc_7002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7002_, 0, v_path_6999_);
lean_ctor_set(v_reuseFailAlloc_7002_, 1, v_a_6995_);
v___x_7001_ = v_reuseFailAlloc_7002_;
goto v_reusejp_7000_;
}
v_reusejp_7000_:
{
return v___x_7001_;
}
}
}
else
{
lean_object* v_a_7004_; lean_object* v_a_7005_; lean_object* v___x_7007_; uint8_t v_isShared_7008_; uint8_t v_isSharedCheck_7012_; 
v_a_7004_ = lean_ctor_get(v___x_6993_, 0);
v_a_7005_ = lean_ctor_get(v___x_6993_, 1);
v_isSharedCheck_7012_ = !lean_is_exclusive(v___x_6993_);
if (v_isSharedCheck_7012_ == 0)
{
v___x_7007_ = v___x_6993_;
v_isShared_7008_ = v_isSharedCheck_7012_;
goto v_resetjp_7006_;
}
else
{
lean_inc(v_a_7005_);
lean_inc(v_a_7004_);
lean_dec(v___x_6993_);
v___x_7007_ = lean_box(0);
v_isShared_7008_ = v_isSharedCheck_7012_;
goto v_resetjp_7006_;
}
v_resetjp_7006_:
{
lean_object* v___x_7010_; 
if (v_isShared_7008_ == 0)
{
v___x_7010_ = v___x_7007_;
goto v_reusejp_7009_;
}
else
{
lean_object* v_reuseFailAlloc_7011_; 
v_reuseFailAlloc_7011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7011_, 0, v_a_7004_);
lean_ctor_set(v_reuseFailAlloc_7011_, 1, v_a_7005_);
v___x_7010_ = v_reuseFailAlloc_7011_;
goto v_reusejp_7009_;
}
v_reusejp_7009_:
{
return v___x_7010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1___boxed(lean_object* v_libFile_7013_, lean_object* v_thin_7014_, lean_object* v_oFiles_7015_, lean_object* v___y_7016_, lean_object* v___y_7017_, lean_object* v___y_7018_, lean_object* v___y_7019_, lean_object* v___y_7020_, lean_object* v___y_7021_, lean_object* v___y_7022_){
_start:
{
uint8_t v_thin_boxed_7023_; lean_object* v_res_7024_; 
v_thin_boxed_7023_ = lean_unbox(v_thin_7014_);
v_res_7024_ = l_Lake_buildStaticLib___lam__1(v_libFile_7013_, v_thin_boxed_7023_, v_oFiles_7015_, v___y_7016_, v___y_7017_, v___y_7018_, v___y_7019_, v___y_7020_, v___y_7021_);
lean_dec_ref(v___y_7020_);
lean_dec(v___y_7019_);
lean_dec(v___y_7018_);
lean_dec(v___y_7017_);
return v_res_7024_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object* v_libFile_7026_, lean_object* v_oFileJobs_7027_, uint8_t v_thin_7028_, lean_object* v_a_7029_, lean_object* v_a_7030_, lean_object* v_a_7031_, lean_object* v_a_7032_, lean_object* v_a_7033_, lean_object* v_a_7034_){
_start:
{
lean_object* v___x_7036_; lean_object* v___f_7037_; lean_object* v___x_7038_; lean_object* v___x_7039_; lean_object* v___x_7040_; lean_object* v___x_7041_; uint8_t v___x_7042_; lean_object* v___x_7043_; 
v___x_7036_ = lean_box(v_thin_7028_);
v___f_7037_ = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__1___boxed), 10, 2);
lean_closure_set(v___f_7037_, 0, v_libFile_7026_);
lean_closure_set(v___f_7037_, 1, v___x_7036_);
v___x_7038_ = l_Lake_instDataKindFilePath;
v___x_7039_ = ((lean_object*)(l_Lake_buildStaticLib___closed__0));
v___x_7040_ = l_Lake_Job_collectArray___redArg(v_oFileJobs_7027_, v___x_7039_);
v___x_7041_ = lean_unsigned_to_nat(0u);
v___x_7042_ = 0;
v___x_7043_ = l_Lake_Job_mapM___redArg(v___x_7038_, v___x_7040_, v___f_7037_, v___x_7041_, v___x_7042_, v_a_7029_, v_a_7030_, v_a_7031_, v_a_7032_, v_a_7033_, v_a_7034_);
return v___x_7043_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object* v_libFile_7044_, lean_object* v_oFileJobs_7045_, lean_object* v_thin_7046_, lean_object* v_a_7047_, lean_object* v_a_7048_, lean_object* v_a_7049_, lean_object* v_a_7050_, lean_object* v_a_7051_, lean_object* v_a_7052_, lean_object* v_a_7053_){
_start:
{
uint8_t v_thin_boxed_7054_; lean_object* v_res_7055_; 
v_thin_boxed_7054_ = lean_unbox(v_thin_7046_);
v_res_7055_ = l_Lake_buildStaticLib(v_libFile_7044_, v_oFileJobs_7045_, v_thin_boxed_7054_, v_a_7047_, v_a_7048_, v_a_7049_, v_a_7050_, v_a_7051_, v_a_7052_);
lean_dec_ref(v_a_7052_);
lean_dec_ref(v_a_7051_);
lean_dec(v_a_7050_);
lean_dec(v_a_7049_);
lean_dec(v_a_7048_);
lean_dec_ref(v_oFileJobs_7045_);
return v_res_7055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(lean_object* v_as_7056_, size_t v_sz_7057_, size_t v_i_7058_, lean_object* v_b_7059_){
_start:
{
uint8_t v___x_7060_; 
v___x_7060_ = lean_usize_dec_lt(v_i_7058_, v_sz_7057_);
if (v___x_7060_ == 0)
{
return v_b_7059_;
}
else
{
lean_object* v_a_7061_; lean_object* v___x_7062_; size_t v___x_7063_; size_t v___x_7064_; 
v_a_7061_ = lean_array_uget_borrowed(v_as_7056_, v_i_7058_);
lean_inc(v_a_7061_);
v___x_7062_ = lean_array_push(v_b_7059_, v_a_7061_);
v___x_7063_ = ((size_t)1ULL);
v___x_7064_ = lean_usize_add(v_i_7058_, v___x_7063_);
v_i_7058_ = v___x_7064_;
v_b_7059_ = v___x_7062_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0___boxed(lean_object* v_as_7066_, lean_object* v_sz_7067_, lean_object* v_i_7068_, lean_object* v_b_7069_){
_start:
{
size_t v_sz_boxed_7070_; size_t v_i_boxed_7071_; lean_object* v_res_7072_; 
v_sz_boxed_7070_ = lean_unbox_usize(v_sz_7067_);
lean_dec(v_sz_7067_);
v_i_boxed_7071_ = lean_unbox_usize(v_i_7068_);
lean_dec(v_i_7068_);
v_res_7072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(v_as_7066_, v_sz_boxed_7070_, v_i_boxed_7071_, v_b_7069_);
lean_dec_ref(v_as_7066_);
return v_res_7072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(lean_object* v_as_7075_, size_t v_sz_7076_, size_t v_i_7077_, lean_object* v_b_7078_){
_start:
{
uint8_t v___x_7079_; 
v___x_7079_ = lean_usize_dec_lt(v_i_7077_, v_sz_7076_);
if (v___x_7079_ == 0)
{
return v_b_7078_;
}
else
{
lean_object* v_a_7080_; lean_object* v_args_7082_; lean_object* v___x_7090_; 
v_a_7080_ = lean_array_uget_borrowed(v_as_7075_, v_i_7077_);
lean_inc(v_a_7080_);
v___x_7090_ = l_Lake_Dynlib_dir_x3f(v_a_7080_);
if (lean_obj_tag(v___x_7090_) == 1)
{
lean_object* v_val_7091_; lean_object* v___x_7092_; lean_object* v___x_7093_; lean_object* v___x_7094_; 
v_val_7091_ = lean_ctor_get(v___x_7090_, 0);
lean_inc(v_val_7091_);
lean_dec_ref_known(v___x_7090_, 1);
v___x_7092_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
v___x_7093_ = lean_string_append(v___x_7092_, v_val_7091_);
lean_dec(v_val_7091_);
v___x_7094_ = lean_array_push(v_b_7078_, v___x_7093_);
v_args_7082_ = v___x_7094_;
goto v___jp_7081_;
}
else
{
lean_dec(v___x_7090_);
v_args_7082_ = v_b_7078_;
goto v___jp_7081_;
}
v___jp_7081_:
{
lean_object* v_name_7083_; lean_object* v___x_7084_; lean_object* v___x_7085_; lean_object* v___x_7086_; size_t v___x_7087_; size_t v___x_7088_; 
v_name_7083_ = lean_ctor_get(v_a_7080_, 1);
v___x_7084_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0));
v___x_7085_ = lean_string_append(v___x_7084_, v_name_7083_);
v___x_7086_ = lean_array_push(v_args_7082_, v___x_7085_);
v___x_7087_ = ((size_t)1ULL);
v___x_7088_ = lean_usize_add(v_i_7077_, v___x_7087_);
v_i_7077_ = v___x_7088_;
v_b_7078_ = v___x_7086_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___boxed(lean_object* v_as_7095_, lean_object* v_sz_7096_, lean_object* v_i_7097_, lean_object* v_b_7098_){
_start:
{
size_t v_sz_boxed_7099_; size_t v_i_boxed_7100_; lean_object* v_res_7101_; 
v_sz_boxed_7099_ = lean_unbox_usize(v_sz_7096_);
lean_dec(v_sz_7096_);
v_i_boxed_7100_ = lean_unbox_usize(v_i_7097_);
lean_dec(v_i_7097_);
v_res_7101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(v_as_7095_, v_sz_boxed_7099_, v_i_boxed_7100_, v_b_7098_);
lean_dec_ref(v_as_7095_);
return v_res_7101_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(lean_object* v_objs_7102_, lean_object* v_libs_7103_){
_start:
{
lean_object* v_args_7104_; size_t v_sz_7105_; size_t v___x_7106_; lean_object* v___x_7107_; size_t v_sz_7108_; lean_object* v___x_7109_; 
v_args_7104_ = ((lean_object*)(l_Lake_inputDir___lam__1___closed__0));
v_sz_7105_ = lean_array_size(v_objs_7102_);
v___x_7106_ = ((size_t)0ULL);
v___x_7107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(v_objs_7102_, v_sz_7105_, v___x_7106_, v_args_7104_);
v_sz_7108_ = lean_array_size(v_libs_7103_);
v___x_7109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(v_libs_7103_, v_sz_7108_, v___x_7106_, v___x_7107_);
return v___x_7109_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs___boxed(lean_object* v_objs_7110_, lean_object* v_libs_7111_){
_start:
{
lean_object* v_res_7112_; 
v_res_7112_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7110_, v_libs_7111_);
lean_dec_ref(v_libs_7111_);
lean_dec_ref(v_objs_7110_);
return v_res_7112_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(lean_object* v_k_7113_, lean_object* v_t_7114_){
_start:
{
if (lean_obj_tag(v_t_7114_) == 0)
{
lean_object* v_k_7115_; lean_object* v_l_7116_; lean_object* v_r_7117_; uint8_t v___x_7118_; 
v_k_7115_ = lean_ctor_get(v_t_7114_, 1);
v_l_7116_ = lean_ctor_get(v_t_7114_, 3);
v_r_7117_ = lean_ctor_get(v_t_7114_, 4);
v___x_7118_ = lean_string_compare(v_k_7113_, v_k_7115_);
switch(v___x_7118_)
{
case 0:
{
v_t_7114_ = v_l_7116_;
goto _start;
}
case 1:
{
uint8_t v___x_7120_; 
v___x_7120_ = 1;
return v___x_7120_;
}
default: 
{
v_t_7114_ = v_r_7117_;
goto _start;
}
}
}
else
{
uint8_t v___x_7122_; 
v___x_7122_ = 0;
return v___x_7122_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg___boxed(lean_object* v_k_7123_, lean_object* v_t_7124_){
_start:
{
uint8_t v_res_7125_; lean_object* v_r_7126_; 
v_res_7125_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_k_7123_, v_t_7124_);
lean_dec(v_t_7124_);
lean_dec_ref(v_k_7123_);
v_r_7126_ = lean_box(v_res_7125_);
return v_r_7126_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(lean_object* v_a_7127_, lean_object* v_x_7128_){
_start:
{
if (lean_obj_tag(v_x_7128_) == 0)
{
uint8_t v___x_7129_; 
v___x_7129_ = 0;
return v___x_7129_;
}
else
{
lean_object* v_head_7130_; lean_object* v_tail_7131_; uint8_t v___x_7132_; 
v_head_7130_ = lean_ctor_get(v_x_7128_, 0);
v_tail_7131_ = lean_ctor_get(v_x_7128_, 1);
v___x_7132_ = lean_string_dec_eq(v_a_7127_, v_head_7130_);
if (v___x_7132_ == 0)
{
v_x_7128_ = v_tail_7131_;
goto _start;
}
else
{
return v___x_7132_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1___boxed(lean_object* v_a_7134_, lean_object* v_x_7135_){
_start:
{
uint8_t v_res_7136_; lean_object* v_r_7137_; 
v_res_7136_ = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(v_a_7134_, v_x_7135_);
lean_dec(v_x_7135_);
lean_dec_ref(v_a_7134_);
v_r_7137_ = lean_box(v_res_7136_);
return v_r_7137_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(lean_object* v_k_7138_, lean_object* v_v_7139_, lean_object* v_t_7140_){
_start:
{
if (lean_obj_tag(v_t_7140_) == 0)
{
lean_object* v_size_7141_; lean_object* v_k_7142_; lean_object* v_v_7143_; lean_object* v_l_7144_; lean_object* v_r_7145_; lean_object* v___x_7147_; uint8_t v_isShared_7148_; uint8_t v_isSharedCheck_7425_; 
v_size_7141_ = lean_ctor_get(v_t_7140_, 0);
v_k_7142_ = lean_ctor_get(v_t_7140_, 1);
v_v_7143_ = lean_ctor_get(v_t_7140_, 2);
v_l_7144_ = lean_ctor_get(v_t_7140_, 3);
v_r_7145_ = lean_ctor_get(v_t_7140_, 4);
v_isSharedCheck_7425_ = !lean_is_exclusive(v_t_7140_);
if (v_isSharedCheck_7425_ == 0)
{
v___x_7147_ = v_t_7140_;
v_isShared_7148_ = v_isSharedCheck_7425_;
goto v_resetjp_7146_;
}
else
{
lean_inc(v_r_7145_);
lean_inc(v_l_7144_);
lean_inc(v_v_7143_);
lean_inc(v_k_7142_);
lean_inc(v_size_7141_);
lean_dec(v_t_7140_);
v___x_7147_ = lean_box(0);
v_isShared_7148_ = v_isSharedCheck_7425_;
goto v_resetjp_7146_;
}
v_resetjp_7146_:
{
uint8_t v___x_7149_; 
v___x_7149_ = lean_string_compare(v_k_7138_, v_k_7142_);
switch(v___x_7149_)
{
case 0:
{
lean_object* v_impl_7150_; lean_object* v___x_7151_; 
lean_dec(v_size_7141_);
v_impl_7150_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7138_, v_v_7139_, v_l_7144_);
v___x_7151_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_7145_) == 0)
{
lean_object* v_size_7152_; lean_object* v_size_7153_; lean_object* v_k_7154_; lean_object* v_v_7155_; lean_object* v_l_7156_; lean_object* v_r_7157_; lean_object* v___x_7158_; lean_object* v___x_7159_; uint8_t v___x_7160_; 
v_size_7152_ = lean_ctor_get(v_r_7145_, 0);
v_size_7153_ = lean_ctor_get(v_impl_7150_, 0);
lean_inc(v_size_7153_);
v_k_7154_ = lean_ctor_get(v_impl_7150_, 1);
lean_inc(v_k_7154_);
v_v_7155_ = lean_ctor_get(v_impl_7150_, 2);
lean_inc(v_v_7155_);
v_l_7156_ = lean_ctor_get(v_impl_7150_, 3);
lean_inc(v_l_7156_);
v_r_7157_ = lean_ctor_get(v_impl_7150_, 4);
lean_inc(v_r_7157_);
v___x_7158_ = lean_unsigned_to_nat(3u);
v___x_7159_ = lean_nat_mul(v___x_7158_, v_size_7152_);
v___x_7160_ = lean_nat_dec_lt(v___x_7159_, v_size_7153_);
lean_dec(v___x_7159_);
if (v___x_7160_ == 0)
{
lean_object* v___x_7161_; lean_object* v___x_7162_; lean_object* v___x_7164_; 
lean_dec(v_r_7157_);
lean_dec(v_l_7156_);
lean_dec(v_v_7155_);
lean_dec(v_k_7154_);
v___x_7161_ = lean_nat_add(v___x_7151_, v_size_7153_);
lean_dec(v_size_7153_);
v___x_7162_ = lean_nat_add(v___x_7161_, v_size_7152_);
lean_dec(v___x_7161_);
if (v_isShared_7148_ == 0)
{
lean_ctor_set(v___x_7147_, 3, v_impl_7150_);
lean_ctor_set(v___x_7147_, 0, v___x_7162_);
v___x_7164_ = v___x_7147_;
goto v_reusejp_7163_;
}
else
{
lean_object* v_reuseFailAlloc_7165_; 
v_reuseFailAlloc_7165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7165_, 0, v___x_7162_);
lean_ctor_set(v_reuseFailAlloc_7165_, 1, v_k_7142_);
lean_ctor_set(v_reuseFailAlloc_7165_, 2, v_v_7143_);
lean_ctor_set(v_reuseFailAlloc_7165_, 3, v_impl_7150_);
lean_ctor_set(v_reuseFailAlloc_7165_, 4, v_r_7145_);
v___x_7164_ = v_reuseFailAlloc_7165_;
goto v_reusejp_7163_;
}
v_reusejp_7163_:
{
return v___x_7164_;
}
}
else
{
lean_object* v___x_7167_; uint8_t v_isShared_7168_; uint8_t v_isSharedCheck_7231_; 
v_isSharedCheck_7231_ = !lean_is_exclusive(v_impl_7150_);
if (v_isSharedCheck_7231_ == 0)
{
lean_object* v_unused_7232_; lean_object* v_unused_7233_; lean_object* v_unused_7234_; lean_object* v_unused_7235_; lean_object* v_unused_7236_; 
v_unused_7232_ = lean_ctor_get(v_impl_7150_, 4);
lean_dec(v_unused_7232_);
v_unused_7233_ = lean_ctor_get(v_impl_7150_, 3);
lean_dec(v_unused_7233_);
v_unused_7234_ = lean_ctor_get(v_impl_7150_, 2);
lean_dec(v_unused_7234_);
v_unused_7235_ = lean_ctor_get(v_impl_7150_, 1);
lean_dec(v_unused_7235_);
v_unused_7236_ = lean_ctor_get(v_impl_7150_, 0);
lean_dec(v_unused_7236_);
v___x_7167_ = v_impl_7150_;
v_isShared_7168_ = v_isSharedCheck_7231_;
goto v_resetjp_7166_;
}
else
{
lean_dec(v_impl_7150_);
v___x_7167_ = lean_box(0);
v_isShared_7168_ = v_isSharedCheck_7231_;
goto v_resetjp_7166_;
}
v_resetjp_7166_:
{
lean_object* v_size_7169_; lean_object* v_size_7170_; lean_object* v_k_7171_; lean_object* v_v_7172_; lean_object* v_l_7173_; lean_object* v_r_7174_; lean_object* v___x_7175_; lean_object* v___x_7176_; uint8_t v___x_7177_; 
v_size_7169_ = lean_ctor_get(v_l_7156_, 0);
v_size_7170_ = lean_ctor_get(v_r_7157_, 0);
v_k_7171_ = lean_ctor_get(v_r_7157_, 1);
v_v_7172_ = lean_ctor_get(v_r_7157_, 2);
v_l_7173_ = lean_ctor_get(v_r_7157_, 3);
v_r_7174_ = lean_ctor_get(v_r_7157_, 4);
v___x_7175_ = lean_unsigned_to_nat(2u);
v___x_7176_ = lean_nat_mul(v___x_7175_, v_size_7169_);
v___x_7177_ = lean_nat_dec_lt(v_size_7170_, v___x_7176_);
lean_dec(v___x_7176_);
if (v___x_7177_ == 0)
{
lean_object* v___x_7179_; uint8_t v_isShared_7180_; uint8_t v_isSharedCheck_7206_; 
lean_inc(v_r_7174_);
lean_inc(v_l_7173_);
lean_inc(v_v_7172_);
lean_inc(v_k_7171_);
v_isSharedCheck_7206_ = !lean_is_exclusive(v_r_7157_);
if (v_isSharedCheck_7206_ == 0)
{
lean_object* v_unused_7207_; lean_object* v_unused_7208_; lean_object* v_unused_7209_; lean_object* v_unused_7210_; lean_object* v_unused_7211_; 
v_unused_7207_ = lean_ctor_get(v_r_7157_, 4);
lean_dec(v_unused_7207_);
v_unused_7208_ = lean_ctor_get(v_r_7157_, 3);
lean_dec(v_unused_7208_);
v_unused_7209_ = lean_ctor_get(v_r_7157_, 2);
lean_dec(v_unused_7209_);
v_unused_7210_ = lean_ctor_get(v_r_7157_, 1);
lean_dec(v_unused_7210_);
v_unused_7211_ = lean_ctor_get(v_r_7157_, 0);
lean_dec(v_unused_7211_);
v___x_7179_ = v_r_7157_;
v_isShared_7180_ = v_isSharedCheck_7206_;
goto v_resetjp_7178_;
}
else
{
lean_dec(v_r_7157_);
v___x_7179_ = lean_box(0);
v_isShared_7180_ = v_isSharedCheck_7206_;
goto v_resetjp_7178_;
}
v_resetjp_7178_:
{
lean_object* v___x_7181_; lean_object* v___x_7182_; lean_object* v___y_7184_; lean_object* v___y_7185_; lean_object* v___y_7186_; lean_object* v___x_7194_; lean_object* v___y_7196_; 
v___x_7181_ = lean_nat_add(v___x_7151_, v_size_7153_);
lean_dec(v_size_7153_);
v___x_7182_ = lean_nat_add(v___x_7181_, v_size_7152_);
lean_dec(v___x_7181_);
v___x_7194_ = lean_nat_add(v___x_7151_, v_size_7169_);
if (lean_obj_tag(v_l_7173_) == 0)
{
lean_object* v_size_7204_; 
v_size_7204_ = lean_ctor_get(v_l_7173_, 0);
lean_inc(v_size_7204_);
v___y_7196_ = v_size_7204_;
goto v___jp_7195_;
}
else
{
lean_object* v___x_7205_; 
v___x_7205_ = lean_unsigned_to_nat(0u);
v___y_7196_ = v___x_7205_;
goto v___jp_7195_;
}
v___jp_7183_:
{
lean_object* v___x_7187_; lean_object* v___x_7189_; 
v___x_7187_ = lean_nat_add(v___y_7184_, v___y_7186_);
lean_dec(v___y_7186_);
lean_dec(v___y_7184_);
if (v_isShared_7180_ == 0)
{
lean_ctor_set(v___x_7179_, 4, v_r_7145_);
lean_ctor_set(v___x_7179_, 3, v_r_7174_);
lean_ctor_set(v___x_7179_, 2, v_v_7143_);
lean_ctor_set(v___x_7179_, 1, v_k_7142_);
lean_ctor_set(v___x_7179_, 0, v___x_7187_);
v___x_7189_ = v___x_7179_;
goto v_reusejp_7188_;
}
else
{
lean_object* v_reuseFailAlloc_7193_; 
v_reuseFailAlloc_7193_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7193_, 0, v___x_7187_);
lean_ctor_set(v_reuseFailAlloc_7193_, 1, v_k_7142_);
lean_ctor_set(v_reuseFailAlloc_7193_, 2, v_v_7143_);
lean_ctor_set(v_reuseFailAlloc_7193_, 3, v_r_7174_);
lean_ctor_set(v_reuseFailAlloc_7193_, 4, v_r_7145_);
v___x_7189_ = v_reuseFailAlloc_7193_;
goto v_reusejp_7188_;
}
v_reusejp_7188_:
{
lean_object* v___x_7191_; 
if (v_isShared_7168_ == 0)
{
lean_ctor_set(v___x_7167_, 4, v___x_7189_);
lean_ctor_set(v___x_7167_, 3, v___y_7185_);
lean_ctor_set(v___x_7167_, 2, v_v_7172_);
lean_ctor_set(v___x_7167_, 1, v_k_7171_);
lean_ctor_set(v___x_7167_, 0, v___x_7182_);
v___x_7191_ = v___x_7167_;
goto v_reusejp_7190_;
}
else
{
lean_object* v_reuseFailAlloc_7192_; 
v_reuseFailAlloc_7192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7192_, 0, v___x_7182_);
lean_ctor_set(v_reuseFailAlloc_7192_, 1, v_k_7171_);
lean_ctor_set(v_reuseFailAlloc_7192_, 2, v_v_7172_);
lean_ctor_set(v_reuseFailAlloc_7192_, 3, v___y_7185_);
lean_ctor_set(v_reuseFailAlloc_7192_, 4, v___x_7189_);
v___x_7191_ = v_reuseFailAlloc_7192_;
goto v_reusejp_7190_;
}
v_reusejp_7190_:
{
return v___x_7191_;
}
}
}
v___jp_7195_:
{
lean_object* v___x_7197_; lean_object* v___x_7199_; 
v___x_7197_ = lean_nat_add(v___x_7194_, v___y_7196_);
lean_dec(v___y_7196_);
lean_dec(v___x_7194_);
if (v_isShared_7148_ == 0)
{
lean_ctor_set(v___x_7147_, 4, v_l_7173_);
lean_ctor_set(v___x_7147_, 3, v_l_7156_);
lean_ctor_set(v___x_7147_, 2, v_v_7155_);
lean_ctor_set(v___x_7147_, 1, v_k_7154_);
lean_ctor_set(v___x_7147_, 0, v___x_7197_);
v___x_7199_ = v___x_7147_;
goto v_reusejp_7198_;
}
else
{
lean_object* v_reuseFailAlloc_7203_; 
v_reuseFailAlloc_7203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7203_, 0, v___x_7197_);
lean_ctor_set(v_reuseFailAlloc_7203_, 1, v_k_7154_);
lean_ctor_set(v_reuseFailAlloc_7203_, 2, v_v_7155_);
lean_ctor_set(v_reuseFailAlloc_7203_, 3, v_l_7156_);
lean_ctor_set(v_reuseFailAlloc_7203_, 4, v_l_7173_);
v___x_7199_ = v_reuseFailAlloc_7203_;
goto v_reusejp_7198_;
}
v_reusejp_7198_:
{
lean_object* v___x_7200_; 
v___x_7200_ = lean_nat_add(v___x_7151_, v_size_7152_);
if (lean_obj_tag(v_r_7174_) == 0)
{
lean_object* v_size_7201_; 
v_size_7201_ = lean_ctor_get(v_r_7174_, 0);
lean_inc(v_size_7201_);
v___y_7184_ = v___x_7200_;
v___y_7185_ = v___x_7199_;
v___y_7186_ = v_size_7201_;
goto v___jp_7183_;
}
else
{
lean_object* v___x_7202_; 
v___x_7202_ = lean_unsigned_to_nat(0u);
v___y_7184_ = v___x_7200_;
v___y_7185_ = v___x_7199_;
v___y_7186_ = v___x_7202_;
goto v___jp_7183_;
}
}
}
}
}
else
{
lean_object* v___x_7212_; lean_object* v___x_7213_; lean_object* v___x_7214_; lean_object* v___x_7215_; lean_object* v___x_7217_; 
lean_del_object(v___x_7147_);
v___x_7212_ = lean_nat_add(v___x_7151_, v_size_7153_);
lean_dec(v_size_7153_);
v___x_7213_ = lean_nat_add(v___x_7212_, v_size_7152_);
lean_dec(v___x_7212_);
v___x_7214_ = lean_nat_add(v___x_7151_, v_size_7152_);
v___x_7215_ = lean_nat_add(v___x_7214_, v_size_7170_);
lean_dec(v___x_7214_);
lean_inc_ref(v_r_7145_);
if (v_isShared_7168_ == 0)
{
lean_ctor_set(v___x_7167_, 4, v_r_7145_);
lean_ctor_set(v___x_7167_, 3, v_r_7157_);
lean_ctor_set(v___x_7167_, 2, v_v_7143_);
lean_ctor_set(v___x_7167_, 1, v_k_7142_);
lean_ctor_set(v___x_7167_, 0, v___x_7215_);
v___x_7217_ = v___x_7167_;
goto v_reusejp_7216_;
}
else
{
lean_object* v_reuseFailAlloc_7230_; 
v_reuseFailAlloc_7230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7230_, 0, v___x_7215_);
lean_ctor_set(v_reuseFailAlloc_7230_, 1, v_k_7142_);
lean_ctor_set(v_reuseFailAlloc_7230_, 2, v_v_7143_);
lean_ctor_set(v_reuseFailAlloc_7230_, 3, v_r_7157_);
lean_ctor_set(v_reuseFailAlloc_7230_, 4, v_r_7145_);
v___x_7217_ = v_reuseFailAlloc_7230_;
goto v_reusejp_7216_;
}
v_reusejp_7216_:
{
lean_object* v___x_7219_; uint8_t v_isShared_7220_; uint8_t v_isSharedCheck_7224_; 
v_isSharedCheck_7224_ = !lean_is_exclusive(v_r_7145_);
if (v_isSharedCheck_7224_ == 0)
{
lean_object* v_unused_7225_; lean_object* v_unused_7226_; lean_object* v_unused_7227_; lean_object* v_unused_7228_; lean_object* v_unused_7229_; 
v_unused_7225_ = lean_ctor_get(v_r_7145_, 4);
lean_dec(v_unused_7225_);
v_unused_7226_ = lean_ctor_get(v_r_7145_, 3);
lean_dec(v_unused_7226_);
v_unused_7227_ = lean_ctor_get(v_r_7145_, 2);
lean_dec(v_unused_7227_);
v_unused_7228_ = lean_ctor_get(v_r_7145_, 1);
lean_dec(v_unused_7228_);
v_unused_7229_ = lean_ctor_get(v_r_7145_, 0);
lean_dec(v_unused_7229_);
v___x_7219_ = v_r_7145_;
v_isShared_7220_ = v_isSharedCheck_7224_;
goto v_resetjp_7218_;
}
else
{
lean_dec(v_r_7145_);
v___x_7219_ = lean_box(0);
v_isShared_7220_ = v_isSharedCheck_7224_;
goto v_resetjp_7218_;
}
v_resetjp_7218_:
{
lean_object* v___x_7222_; 
if (v_isShared_7220_ == 0)
{
lean_ctor_set(v___x_7219_, 4, v___x_7217_);
lean_ctor_set(v___x_7219_, 3, v_l_7156_);
lean_ctor_set(v___x_7219_, 2, v_v_7155_);
lean_ctor_set(v___x_7219_, 1, v_k_7154_);
lean_ctor_set(v___x_7219_, 0, v___x_7213_);
v___x_7222_ = v___x_7219_;
goto v_reusejp_7221_;
}
else
{
lean_object* v_reuseFailAlloc_7223_; 
v_reuseFailAlloc_7223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7223_, 0, v___x_7213_);
lean_ctor_set(v_reuseFailAlloc_7223_, 1, v_k_7154_);
lean_ctor_set(v_reuseFailAlloc_7223_, 2, v_v_7155_);
lean_ctor_set(v_reuseFailAlloc_7223_, 3, v_l_7156_);
lean_ctor_set(v_reuseFailAlloc_7223_, 4, v___x_7217_);
v___x_7222_ = v_reuseFailAlloc_7223_;
goto v_reusejp_7221_;
}
v_reusejp_7221_:
{
return v___x_7222_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_7237_; 
v_l_7237_ = lean_ctor_get(v_impl_7150_, 3);
lean_inc(v_l_7237_);
if (lean_obj_tag(v_l_7237_) == 0)
{
lean_object* v_r_7238_; lean_object* v_k_7239_; lean_object* v_v_7240_; lean_object* v___x_7242_; uint8_t v_isShared_7243_; uint8_t v_isSharedCheck_7251_; 
v_r_7238_ = lean_ctor_get(v_impl_7150_, 4);
v_k_7239_ = lean_ctor_get(v_impl_7150_, 1);
v_v_7240_ = lean_ctor_get(v_impl_7150_, 2);
v_isSharedCheck_7251_ = !lean_is_exclusive(v_impl_7150_);
if (v_isSharedCheck_7251_ == 0)
{
lean_object* v_unused_7252_; lean_object* v_unused_7253_; 
v_unused_7252_ = lean_ctor_get(v_impl_7150_, 3);
lean_dec(v_unused_7252_);
v_unused_7253_ = lean_ctor_get(v_impl_7150_, 0);
lean_dec(v_unused_7253_);
v___x_7242_ = v_impl_7150_;
v_isShared_7243_ = v_isSharedCheck_7251_;
goto v_resetjp_7241_;
}
else
{
lean_inc(v_r_7238_);
lean_inc(v_v_7240_);
lean_inc(v_k_7239_);
lean_dec(v_impl_7150_);
v___x_7242_ = lean_box(0);
v_isShared_7243_ = v_isSharedCheck_7251_;
goto v_resetjp_7241_;
}
v_resetjp_7241_:
{
lean_object* v___x_7244_; lean_object* v___x_7246_; 
v___x_7244_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_7238_);
if (v_isShared_7243_ == 0)
{
lean_ctor_set(v___x_7242_, 3, v_r_7238_);
lean_ctor_set(v___x_7242_, 2, v_v_7143_);
lean_ctor_set(v___x_7242_, 1, v_k_7142_);
lean_ctor_set(v___x_7242_, 0, v___x_7151_);
v___x_7246_ = v___x_7242_;
goto v_reusejp_7245_;
}
else
{
lean_object* v_reuseFailAlloc_7250_; 
v_reuseFailAlloc_7250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7250_, 0, v___x_7151_);
lean_ctor_set(v_reuseFailAlloc_7250_, 1, v_k_7142_);
lean_ctor_set(v_reuseFailAlloc_7250_, 2, v_v_7143_);
lean_ctor_set(v_reuseFailAlloc_7250_, 3, v_r_7238_);
lean_ctor_set(v_reuseFailAlloc_7250_, 4, v_r_7238_);
v___x_7246_ = v_reuseFailAlloc_7250_;
goto v_reusejp_7245_;
}
v_reusejp_7245_:
{
lean_object* v___x_7248_; 
if (v_isShared_7148_ == 0)
{
lean_ctor_set(v___x_7147_, 4, v___x_7246_);
lean_ctor_set(v___x_7147_, 3, v_l_7237_);
lean_ctor_set(v___x_7147_, 2, v_v_7240_);
lean_ctor_set(v___x_7147_, 1, v_k_7239_);
lean_ctor_set(v___x_7147_, 0, v___x_7244_);
v___x_7248_ = v___x_7147_;
goto v_reusejp_7247_;
}
else
{
lean_object* v_reuseFailAlloc_7249_; 
v_reuseFailAlloc_7249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7249_, 0, v___x_7244_);
lean_ctor_set(v_reuseFailAlloc_7249_, 1, v_k_7239_);
lean_ctor_set(v_reuseFailAlloc_7249_, 2, v_v_7240_);
lean_ctor_set(v_reuseFailAlloc_7249_, 3, v_l_7237_);
lean_ctor_set(v_reuseFailAlloc_7249_, 4, v___x_7246_);
v___x_7248_ = v_reuseFailAlloc_7249_;
goto v_reusejp_7247_;
}
v_reusejp_7247_:
{
return v___x_7248_;
}
}
}
}
else
{
lean_object* v_r_7254_; 
v_r_7254_ = lean_ctor_get(v_impl_7150_, 4);
lean_inc(v_r_7254_);
if (lean_obj_tag(v_r_7254_) == 0)
{
lean_object* v_k_7255_; lean_object* v_v_7256_; lean_object* v___x_7258_; uint8_t v_isShared_7259_; uint8_t v_isSharedCheck_7279_; 
v_k_7255_ = lean_ctor_get(v_impl_7150_, 1);
v_v_7256_ = lean_ctor_get(v_impl_7150_, 2);
v_isSharedCheck_7279_ = !lean_is_exclusive(v_impl_7150_);
if (v_isSharedCheck_7279_ == 0)
{
lean_object* v_unused_7280_; lean_object* v_unused_7281_; lean_object* v_unused_7282_; 
v_unused_7280_ = lean_ctor_get(v_impl_7150_, 4);
lean_dec(v_unused_7280_);
v_unused_7281_ = lean_ctor_get(v_impl_7150_, 3);
lean_dec(v_unused_7281_);
v_unused_7282_ = lean_ctor_get(v_impl_7150_, 0);
lean_dec(v_unused_7282_);
v___x_7258_ = v_impl_7150_;
v_isShared_7259_ = v_isSharedCheck_7279_;
goto v_resetjp_7257_;
}
else
{
lean_inc(v_v_7256_);
lean_inc(v_k_7255_);
lean_dec(v_impl_7150_);
v___x_7258_ = lean_box(0);
v_isShared_7259_ = v_isSharedCheck_7279_;
goto v_resetjp_7257_;
}
v_resetjp_7257_:
{
lean_object* v_k_7260_; lean_object* v_v_7261_; lean_object* v___x_7263_; uint8_t v_isShared_7264_; uint8_t v_isSharedCheck_7275_; 
v_k_7260_ = lean_ctor_get(v_r_7254_, 1);
v_v_7261_ = lean_ctor_get(v_r_7254_, 2);
v_isSharedCheck_7275_ = !lean_is_exclusive(v_r_7254_);
if (v_isSharedCheck_7275_ == 0)
{
lean_object* v_unused_7276_; lean_object* v_unused_7277_; lean_object* v_unused_7278_; 
v_unused_7276_ = lean_ctor_get(v_r_7254_, 4);
lean_dec(v_unused_7276_);
v_unused_7277_ = lean_ctor_get(v_r_7254_, 3);
lean_dec(v_unused_7277_);
v_unused_7278_ = lean_ctor_get(v_r_7254_, 0);
lean_dec(v_unused_7278_);
v___x_7263_ = v_r_7254_;
v_isShared_7264_ = v_isSharedCheck_7275_;
goto v_resetjp_7262_;
}
else
{
lean_inc(v_v_7261_);
lean_inc(v_k_7260_);
lean_dec(v_r_7254_);
v___x_7263_ = lean_box(0);
v_isShared_7264_ = v_isSharedCheck_7275_;
goto v_resetjp_7262_;
}
v_resetjp_7262_:
{
lean_object* v___x_7265_; lean_object* v___x_7267_; 
v___x_7265_ = lean_unsigned_to_nat(3u);
if (v_isShared_7264_ == 0)
{
lean_ctor_set(v___x_7263_, 4, v_l_7237_);
lean_ctor_set(v___x_7263_, 3, v_l_7237_);
lean_ctor_set(v___x_7263_, 2, v_v_7256_);
lean_ctor_set(v___x_7263_, 1, v_k_7255_);
lean_ctor_set(v___x_7263_, 0, v___x_7151_);
v___x_7267_ = v___x_7263_;
goto v_reusejp_7266_;
}
else
{
lean_object* v_reuseFailAlloc_7274_; 
v_reuseFailAlloc_7274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7274_, 0, v___x_7151_);
lean_ctor_set(v_reuseFailAlloc_7274_, 1, v_k_7255_);
lean_ctor_set(v_reuseFailAlloc_7274_, 2, v_v_7256_);
lean_ctor_set(v_reuseFailAlloc_7274_, 3, v_l_7237_);
lean_ctor_set(v_reuseFailAlloc_7274_, 4, v_l_7237_);
v___x_7267_ = v_reuseFailAlloc_7274_;
goto v_reusejp_7266_;
}
v_reusejp_7266_:
{
lean_object* v___x_7269_; 
if (v_isShared_7259_ == 0)
{
lean_ctor_set(v___x_7258_, 4, v_l_7237_);
lean_ctor_set(v___x_7258_, 2, v_v_7143_);
lean_ctor_set(v___x_7258_, 1, v_k_7142_);
lean_ctor_set(v___x_7258_, 0, v___x_7151_);
v___x_7269_ = v___x_7258_;
goto v_reusejp_7268_;
}
else
{
lean_object* v_reuseFailAlloc_7273_; 
v_reuseFailAlloc_7273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7273_, 0, v___x_7151_);
lean_ctor_set(v_reuseFailAlloc_7273_, 1, v_k_7142_);
lean_ctor_set(v_reuseFailAlloc_7273_, 2, v_v_7143_);
lean_ctor_set(v_reuseFailAlloc_7273_, 3, v_l_7237_);
lean_ctor_set(v_reuseFailAlloc_7273_, 4, v_l_7237_);
v___x_7269_ = v_reuseFailAlloc_7273_;
goto v_reusejp_7268_;
}
v_reusejp_7268_:
{
lean_object* v___x_7271_; 
if (v_isShared_7148_ == 0)
{
lean_ctor_set(v___x_7147_, 4, v___x_7269_);
lean_ctor_set(v___x_7147_, 3, v___x_7267_);
lean_ctor_set(v___x_7147_, 2, v_v_7261_);
lean_ctor_set(v___x_7147_, 1, v_k_7260_);
lean_ctor_set(v___x_7147_, 0, v___x_7265_);
v___x_7271_ = v___x_7147_;
goto v_reusejp_7270_;
}
else
{
lean_object* v_reuseFailAlloc_7272_; 
v_reuseFailAlloc_7272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7272_, 0, v___x_7265_);
lean_ctor_set(v_reuseFailAlloc_7272_, 1, v_k_7260_);
lean_ctor_set(v_reuseFailAlloc_7272_, 2, v_v_7261_);
lean_ctor_set(v_reuseFailAlloc_7272_, 3, v___x_7267_);
lean_ctor_set(v_reuseFailAlloc_7272_, 4, v___x_7269_);
v___x_7271_ = v_reuseFailAlloc_7272_;
goto v_reusejp_7270_;
}
v_reusejp_7270_:
{
return v___x_7271_;
}
}
}
}
}
}
else
{
lean_object* v___x_7283_; lean_object* v___x_7285_; 
v___x_7283_ = lean_unsigned_to_nat(2u);
if (v_isShared_7148_ == 0)
{
lean_ctor_set(v___x_7147_, 4, v_r_7254_);
lean_ctor_set(v___x_7147_, 3, v_impl_7150_);
lean_ctor_set(v___x_7147_, 0, v___x_7283_);
v___x_7285_ = v___x_7147_;
goto v_reusejp_7284_;
}
else
{
lean_object* v_reuseFailAlloc_7286_; 
v_reuseFailAlloc_7286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7286_, 0, v___x_7283_);
lean_ctor_set(v_reuseFailAlloc_7286_, 1, v_k_7142_);
lean_ctor_set(v_reuseFailAlloc_7286_, 2, v_v_7143_);
lean_ctor_set(v_reuseFailAlloc_7286_, 3, v_impl_7150_);
lean_ctor_set(v_reuseFailAlloc_7286_, 4, v_r_7254_);
v___x_7285_ = v_reuseFailAlloc_7286_;
goto v_reusejp_7284_;
}
v_reusejp_7284_:
{
return v___x_7285_;
}
}
}
}
}
case 1:
{
lean_object* v___x_7288_; 
lean_dec(v_v_7143_);
lean_dec(v_k_7142_);
if (v_isShared_7148_ == 0)
{
lean_ctor_set(v___x_7147_, 2, v_v_7139_);
lean_ctor_set(v___x_7147_, 1, v_k_7138_);
v___x_7288_ = v___x_7147_;
goto v_reusejp_7287_;
}
else
{
lean_object* v_reuseFailAlloc_7289_; 
v_reuseFailAlloc_7289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7289_, 0, v_size_7141_);
lean_ctor_set(v_reuseFailAlloc_7289_, 1, v_k_7138_);
lean_ctor_set(v_reuseFailAlloc_7289_, 2, v_v_7139_);
lean_ctor_set(v_reuseFailAlloc_7289_, 3, v_l_7144_);
lean_ctor_set(v_reuseFailAlloc_7289_, 4, v_r_7145_);
v___x_7288_ = v_reuseFailAlloc_7289_;
goto v_reusejp_7287_;
}
v_reusejp_7287_:
{
return v___x_7288_;
}
}
default: 
{
lean_object* v_impl_7290_; lean_object* v___x_7291_; 
lean_dec(v_size_7141_);
v_impl_7290_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7138_, v_v_7139_, v_r_7145_);
v___x_7291_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_7144_) == 0)
{
lean_object* v_size_7292_; lean_object* v_size_7293_; lean_object* v_k_7294_; lean_object* v_v_7295_; lean_object* v_l_7296_; lean_object* v_r_7297_; lean_object* v___x_7298_; lean_object* v___x_7299_; uint8_t v___x_7300_; 
v_size_7292_ = lean_ctor_get(v_l_7144_, 0);
v_size_7293_ = lean_ctor_get(v_impl_7290_, 0);
lean_inc(v_size_7293_);
v_k_7294_ = lean_ctor_get(v_impl_7290_, 1);
lean_inc(v_k_7294_);
v_v_7295_ = lean_ctor_get(v_impl_7290_, 2);
lean_inc(v_v_7295_);
v_l_7296_ = lean_ctor_get(v_impl_7290_, 3);
lean_inc(v_l_7296_);
v_r_7297_ = lean_ctor_get(v_impl_7290_, 4);
lean_inc(v_r_7297_);
v___x_7298_ = lean_unsigned_to_nat(3u);
v___x_7299_ = lean_nat_mul(v___x_7298_, v_size_7292_);
v___x_7300_ = lean_nat_dec_lt(v___x_7299_, v_size_7293_);
lean_dec(v___x_7299_);
if (v___x_7300_ == 0)
{
lean_object* v___x_7301_; lean_object* v___x_7302_; lean_object* v___x_7304_; 
lean_dec(v_r_7297_);
lean_dec(v_l_7296_);
lean_dec(v_v_7295_);
lean_dec(v_k_7294_);
v___x_7301_ = lean_nat_add(v___x_7291_, v_size_7292_);
v___x_7302_ = lean_nat_add(v___x_7301_, v_size_7293_);
lean_dec(v_size_7293_);
lean_dec(v___x_7301_);
if (v_isShared_7148_ == 0)
{
lean_ctor_set(v___x_7147_, 4, v_impl_7290_);
lean_ctor_set(v___x_7147_, 0, v___x_7302_);
v___x_7304_ = v___x_7147_;
goto v_reusejp_7303_;
}
else
{
lean_object* v_reuseFailAlloc_7305_; 
v_reuseFailAlloc_7305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7305_, 0, v___x_7302_);
lean_ctor_set(v_reuseFailAlloc_7305_, 1, v_k_7142_);
lean_ctor_set(v_reuseFailAlloc_7305_, 2, v_v_7143_);
lean_ctor_set(v_reuseFailAlloc_7305_, 3, v_l_7144_);
lean_ctor_set(v_reuseFailAlloc_7305_, 4, v_impl_7290_);
v___x_7304_ = v_reuseFailAlloc_7305_;
goto v_reusejp_7303_;
}
v_reusejp_7303_:
{
return v___x_7304_;
}
}
else
{
lean_object* v___x_7307_; uint8_t v_isShared_7308_; uint8_t v_isSharedCheck_7369_; 
v_isSharedCheck_7369_ = !lean_is_exclusive(v_impl_7290_);
if (v_isSharedCheck_7369_ == 0)
{
lean_object* v_unused_7370_; lean_object* v_unused_7371_; lean_object* v_unused_7372_; lean_object* v_unused_7373_; lean_object* v_unused_7374_; 
v_unused_7370_ = lean_ctor_get(v_impl_7290_, 4);
lean_dec(v_unused_7370_);
v_unused_7371_ = lean_ctor_get(v_impl_7290_, 3);
lean_dec(v_unused_7371_);
v_unused_7372_ = lean_ctor_get(v_impl_7290_, 2);
lean_dec(v_unused_7372_);
v_unused_7373_ = lean_ctor_get(v_impl_7290_, 1);
lean_dec(v_unused_7373_);
v_unused_7374_ = lean_ctor_get(v_impl_7290_, 0);
lean_dec(v_unused_7374_);
v___x_7307_ = v_impl_7290_;
v_isShared_7308_ = v_isSharedCheck_7369_;
goto v_resetjp_7306_;
}
else
{
lean_dec(v_impl_7290_);
v___x_7307_ = lean_box(0);
v_isShared_7308_ = v_isSharedCheck_7369_;
goto v_resetjp_7306_;
}
v_resetjp_7306_:
{
lean_object* v_size_7309_; lean_object* v_k_7310_; lean_object* v_v_7311_; lean_object* v_l_7312_; lean_object* v_r_7313_; lean_object* v_size_7314_; lean_object* v___x_7315_; lean_object* v___x_7316_; uint8_t v___x_7317_; 
v_size_7309_ = lean_ctor_get(v_l_7296_, 0);
v_k_7310_ = lean_ctor_get(v_l_7296_, 1);
v_v_7311_ = lean_ctor_get(v_l_7296_, 2);
v_l_7312_ = lean_ctor_get(v_l_7296_, 3);
v_r_7313_ = lean_ctor_get(v_l_7296_, 4);
v_size_7314_ = lean_ctor_get(v_r_7297_, 0);
v___x_7315_ = lean_unsigned_to_nat(2u);
v___x_7316_ = lean_nat_mul(v___x_7315_, v_size_7314_);
v___x_7317_ = lean_nat_dec_lt(v_size_7309_, v___x_7316_);
lean_dec(v___x_7316_);
if (v___x_7317_ == 0)
{
lean_object* v___x_7319_; uint8_t v_isShared_7320_; uint8_t v_isSharedCheck_7345_; 
lean_inc(v_r_7313_);
lean_inc(v_l_7312_);
lean_inc(v_v_7311_);
lean_inc(v_k_7310_);
v_isSharedCheck_7345_ = !lean_is_exclusive(v_l_7296_);
if (v_isSharedCheck_7345_ == 0)
{
lean_object* v_unused_7346_; lean_object* v_unused_7347_; lean_object* v_unused_7348_; lean_object* v_unused_7349_; lean_object* v_unused_7350_; 
v_unused_7346_ = lean_ctor_get(v_l_7296_, 4);
lean_dec(v_unused_7346_);
v_unused_7347_ = lean_ctor_get(v_l_7296_, 3);
lean_dec(v_unused_7347_);
v_unused_7348_ = lean_ctor_get(v_l_7296_, 2);
lean_dec(v_unused_7348_);
v_unused_7349_ = lean_ctor_get(v_l_7296_, 1);
lean_dec(v_unused_7349_);
v_unused_7350_ = lean_ctor_get(v_l_7296_, 0);
lean_dec(v_unused_7350_);
v___x_7319_ = v_l_7296_;
v_isShared_7320_ = v_isSharedCheck_7345_;
goto v_resetjp_7318_;
}
else
{
lean_dec(v_l_7296_);
v___x_7319_ = lean_box(0);
v_isShared_7320_ = v_isSharedCheck_7345_;
goto v_resetjp_7318_;
}
v_resetjp_7318_:
{
lean_object* v___x_7321_; lean_object* v___x_7322_; lean_object* v___y_7324_; lean_object* v___y_7325_; lean_object* v___y_7326_; lean_object* v___y_7335_; 
v___x_7321_ = lean_nat_add(v___x_7291_, v_size_7292_);
v___x_7322_ = lean_nat_add(v___x_7321_, v_size_7293_);
lean_dec(v_size_7293_);
if (lean_obj_tag(v_l_7312_) == 0)
{
lean_object* v_size_7343_; 
v_size_7343_ = lean_ctor_get(v_l_7312_, 0);
lean_inc(v_size_7343_);
v___y_7335_ = v_size_7343_;
goto v___jp_7334_;
}
else
{
lean_object* v___x_7344_; 
v___x_7344_ = lean_unsigned_to_nat(0u);
v___y_7335_ = v___x_7344_;
goto v___jp_7334_;
}
v___jp_7323_:
{
lean_object* v___x_7327_; lean_object* v___x_7329_; 
v___x_7327_ = lean_nat_add(v___y_7324_, v___y_7326_);
lean_dec(v___y_7326_);
lean_dec(v___y_7324_);
if (v_isShared_7320_ == 0)
{
lean_ctor_set(v___x_7319_, 4, v_r_7297_);
lean_ctor_set(v___x_7319_, 3, v_r_7313_);
lean_ctor_set(v___x_7319_, 2, v_v_7295_);
lean_ctor_set(v___x_7319_, 1, v_k_7294_);
lean_ctor_set(v___x_7319_, 0, v___x_7327_);
v___x_7329_ = v___x_7319_;
goto v_reusejp_7328_;
}
else
{
lean_object* v_reuseFailAlloc_7333_; 
v_reuseFailAlloc_7333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7333_, 0, v___x_7327_);
lean_ctor_set(v_reuseFailAlloc_7333_, 1, v_k_7294_);
lean_ctor_set(v_reuseFailAlloc_7333_, 2, v_v_7295_);
lean_ctor_set(v_reuseFailAlloc_7333_, 3, v_r_7313_);
lean_ctor_set(v_reuseFailAlloc_7333_, 4, v_r_7297_);
v___x_7329_ = v_reuseFailAlloc_7333_;
goto v_reusejp_7328_;
}
v_reusejp_7328_:
{
lean_object* v___x_7331_; 
if (v_isShared_7308_ == 0)
{
lean_ctor_set(v___x_7307_, 4, v___x_7329_);
lean_ctor_set(v___x_7307_, 3, v___y_7325_);
lean_ctor_set(v___x_7307_, 2, v_v_7311_);
lean_ctor_set(v___x_7307_, 1, v_k_7310_);
lean_ctor_set(v___x_7307_, 0, v___x_7322_);
v___x_7331_ = v___x_7307_;
goto v_reusejp_7330_;
}
else
{
lean_object* v_reuseFailAlloc_7332_; 
v_reuseFailAlloc_7332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7332_, 0, v___x_7322_);
lean_ctor_set(v_reuseFailAlloc_7332_, 1, v_k_7310_);
lean_ctor_set(v_reuseFailAlloc_7332_, 2, v_v_7311_);
lean_ctor_set(v_reuseFailAlloc_7332_, 3, v___y_7325_);
lean_ctor_set(v_reuseFailAlloc_7332_, 4, v___x_7329_);
v___x_7331_ = v_reuseFailAlloc_7332_;
goto v_reusejp_7330_;
}
v_reusejp_7330_:
{
return v___x_7331_;
}
}
}
v___jp_7334_:
{
lean_object* v___x_7336_; lean_object* v___x_7338_; 
v___x_7336_ = lean_nat_add(v___x_7321_, v___y_7335_);
lean_dec(v___y_7335_);
lean_dec(v___x_7321_);
if (v_isShared_7148_ == 0)
{
lean_ctor_set(v___x_7147_, 4, v_l_7312_);
lean_ctor_set(v___x_7147_, 0, v___x_7336_);
v___x_7338_ = v___x_7147_;
goto v_reusejp_7337_;
}
else
{
lean_object* v_reuseFailAlloc_7342_; 
v_reuseFailAlloc_7342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7342_, 0, v___x_7336_);
lean_ctor_set(v_reuseFailAlloc_7342_, 1, v_k_7142_);
lean_ctor_set(v_reuseFailAlloc_7342_, 2, v_v_7143_);
lean_ctor_set(v_reuseFailAlloc_7342_, 3, v_l_7144_);
lean_ctor_set(v_reuseFailAlloc_7342_, 4, v_l_7312_);
v___x_7338_ = v_reuseFailAlloc_7342_;
goto v_reusejp_7337_;
}
v_reusejp_7337_:
{
lean_object* v___x_7339_; 
v___x_7339_ = lean_nat_add(v___x_7291_, v_size_7314_);
if (lean_obj_tag(v_r_7313_) == 0)
{
lean_object* v_size_7340_; 
v_size_7340_ = lean_ctor_get(v_r_7313_, 0);
lean_inc(v_size_7340_);
v___y_7324_ = v___x_7339_;
v___y_7325_ = v___x_7338_;
v___y_7326_ = v_size_7340_;
goto v___jp_7323_;
}
else
{
lean_object* v___x_7341_; 
v___x_7341_ = lean_unsigned_to_nat(0u);
v___y_7324_ = v___x_7339_;
v___y_7325_ = v___x_7338_;
v___y_7326_ = v___x_7341_;
goto v___jp_7323_;
}
}
}
}
}
else
{
lean_object* v___x_7351_; lean_object* v___x_7352_; lean_object* v___x_7353_; lean_object* v___x_7355_; 
lean_del_object(v___x_7147_);
v___x_7351_ = lean_nat_add(v___x_7291_, v_size_7292_);
v___x_7352_ = lean_nat_add(v___x_7351_, v_size_7293_);
lean_dec(v_size_7293_);
v___x_7353_ = lean_nat_add(v___x_7351_, v_size_7309_);
lean_dec(v___x_7351_);
lean_inc_ref(v_l_7144_);
if (v_isShared_7308_ == 0)
{
lean_ctor_set(v___x_7307_, 4, v_l_7296_);
lean_ctor_set(v___x_7307_, 3, v_l_7144_);
lean_ctor_set(v___x_7307_, 2, v_v_7143_);
lean_ctor_set(v___x_7307_, 1, v_k_7142_);
lean_ctor_set(v___x_7307_, 0, v___x_7353_);
v___x_7355_ = v___x_7307_;
goto v_reusejp_7354_;
}
else
{
lean_object* v_reuseFailAlloc_7368_; 
v_reuseFailAlloc_7368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7368_, 0, v___x_7353_);
lean_ctor_set(v_reuseFailAlloc_7368_, 1, v_k_7142_);
lean_ctor_set(v_reuseFailAlloc_7368_, 2, v_v_7143_);
lean_ctor_set(v_reuseFailAlloc_7368_, 3, v_l_7144_);
lean_ctor_set(v_reuseFailAlloc_7368_, 4, v_l_7296_);
v___x_7355_ = v_reuseFailAlloc_7368_;
goto v_reusejp_7354_;
}
v_reusejp_7354_:
{
lean_object* v___x_7357_; uint8_t v_isShared_7358_; uint8_t v_isSharedCheck_7362_; 
v_isSharedCheck_7362_ = !lean_is_exclusive(v_l_7144_);
if (v_isSharedCheck_7362_ == 0)
{
lean_object* v_unused_7363_; lean_object* v_unused_7364_; lean_object* v_unused_7365_; lean_object* v_unused_7366_; lean_object* v_unused_7367_; 
v_unused_7363_ = lean_ctor_get(v_l_7144_, 4);
lean_dec(v_unused_7363_);
v_unused_7364_ = lean_ctor_get(v_l_7144_, 3);
lean_dec(v_unused_7364_);
v_unused_7365_ = lean_ctor_get(v_l_7144_, 2);
lean_dec(v_unused_7365_);
v_unused_7366_ = lean_ctor_get(v_l_7144_, 1);
lean_dec(v_unused_7366_);
v_unused_7367_ = lean_ctor_get(v_l_7144_, 0);
lean_dec(v_unused_7367_);
v___x_7357_ = v_l_7144_;
v_isShared_7358_ = v_isSharedCheck_7362_;
goto v_resetjp_7356_;
}
else
{
lean_dec(v_l_7144_);
v___x_7357_ = lean_box(0);
v_isShared_7358_ = v_isSharedCheck_7362_;
goto v_resetjp_7356_;
}
v_resetjp_7356_:
{
lean_object* v___x_7360_; 
if (v_isShared_7358_ == 0)
{
lean_ctor_set(v___x_7357_, 4, v_r_7297_);
lean_ctor_set(v___x_7357_, 3, v___x_7355_);
lean_ctor_set(v___x_7357_, 2, v_v_7295_);
lean_ctor_set(v___x_7357_, 1, v_k_7294_);
lean_ctor_set(v___x_7357_, 0, v___x_7352_);
v___x_7360_ = v___x_7357_;
goto v_reusejp_7359_;
}
else
{
lean_object* v_reuseFailAlloc_7361_; 
v_reuseFailAlloc_7361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7361_, 0, v___x_7352_);
lean_ctor_set(v_reuseFailAlloc_7361_, 1, v_k_7294_);
lean_ctor_set(v_reuseFailAlloc_7361_, 2, v_v_7295_);
lean_ctor_set(v_reuseFailAlloc_7361_, 3, v___x_7355_);
lean_ctor_set(v_reuseFailAlloc_7361_, 4, v_r_7297_);
v___x_7360_ = v_reuseFailAlloc_7361_;
goto v_reusejp_7359_;
}
v_reusejp_7359_:
{
return v___x_7360_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_7375_; 
v_l_7375_ = lean_ctor_get(v_impl_7290_, 3);
lean_inc(v_l_7375_);
if (lean_obj_tag(v_l_7375_) == 0)
{
lean_object* v_r_7376_; lean_object* v_k_7377_; lean_object* v_v_7378_; lean_object* v___x_7380_; uint8_t v_isShared_7381_; uint8_t v_isSharedCheck_7401_; 
v_r_7376_ = lean_ctor_get(v_impl_7290_, 4);
v_k_7377_ = lean_ctor_get(v_impl_7290_, 1);
v_v_7378_ = lean_ctor_get(v_impl_7290_, 2);
v_isSharedCheck_7401_ = !lean_is_exclusive(v_impl_7290_);
if (v_isSharedCheck_7401_ == 0)
{
lean_object* v_unused_7402_; lean_object* v_unused_7403_; 
v_unused_7402_ = lean_ctor_get(v_impl_7290_, 3);
lean_dec(v_unused_7402_);
v_unused_7403_ = lean_ctor_get(v_impl_7290_, 0);
lean_dec(v_unused_7403_);
v___x_7380_ = v_impl_7290_;
v_isShared_7381_ = v_isSharedCheck_7401_;
goto v_resetjp_7379_;
}
else
{
lean_inc(v_r_7376_);
lean_inc(v_v_7378_);
lean_inc(v_k_7377_);
lean_dec(v_impl_7290_);
v___x_7380_ = lean_box(0);
v_isShared_7381_ = v_isSharedCheck_7401_;
goto v_resetjp_7379_;
}
v_resetjp_7379_:
{
lean_object* v_k_7382_; lean_object* v_v_7383_; lean_object* v___x_7385_; uint8_t v_isShared_7386_; uint8_t v_isSharedCheck_7397_; 
v_k_7382_ = lean_ctor_get(v_l_7375_, 1);
v_v_7383_ = lean_ctor_get(v_l_7375_, 2);
v_isSharedCheck_7397_ = !lean_is_exclusive(v_l_7375_);
if (v_isSharedCheck_7397_ == 0)
{
lean_object* v_unused_7398_; lean_object* v_unused_7399_; lean_object* v_unused_7400_; 
v_unused_7398_ = lean_ctor_get(v_l_7375_, 4);
lean_dec(v_unused_7398_);
v_unused_7399_ = lean_ctor_get(v_l_7375_, 3);
lean_dec(v_unused_7399_);
v_unused_7400_ = lean_ctor_get(v_l_7375_, 0);
lean_dec(v_unused_7400_);
v___x_7385_ = v_l_7375_;
v_isShared_7386_ = v_isSharedCheck_7397_;
goto v_resetjp_7384_;
}
else
{
lean_inc(v_v_7383_);
lean_inc(v_k_7382_);
lean_dec(v_l_7375_);
v___x_7385_ = lean_box(0);
v_isShared_7386_ = v_isSharedCheck_7397_;
goto v_resetjp_7384_;
}
v_resetjp_7384_:
{
lean_object* v___x_7387_; lean_object* v___x_7389_; 
v___x_7387_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_7376_, 2);
if (v_isShared_7386_ == 0)
{
lean_ctor_set(v___x_7385_, 4, v_r_7376_);
lean_ctor_set(v___x_7385_, 3, v_r_7376_);
lean_ctor_set(v___x_7385_, 2, v_v_7143_);
lean_ctor_set(v___x_7385_, 1, v_k_7142_);
lean_ctor_set(v___x_7385_, 0, v___x_7291_);
v___x_7389_ = v___x_7385_;
goto v_reusejp_7388_;
}
else
{
lean_object* v_reuseFailAlloc_7396_; 
v_reuseFailAlloc_7396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7396_, 0, v___x_7291_);
lean_ctor_set(v_reuseFailAlloc_7396_, 1, v_k_7142_);
lean_ctor_set(v_reuseFailAlloc_7396_, 2, v_v_7143_);
lean_ctor_set(v_reuseFailAlloc_7396_, 3, v_r_7376_);
lean_ctor_set(v_reuseFailAlloc_7396_, 4, v_r_7376_);
v___x_7389_ = v_reuseFailAlloc_7396_;
goto v_reusejp_7388_;
}
v_reusejp_7388_:
{
lean_object* v___x_7391_; 
lean_inc(v_r_7376_);
if (v_isShared_7381_ == 0)
{
lean_ctor_set(v___x_7380_, 3, v_r_7376_);
lean_ctor_set(v___x_7380_, 0, v___x_7291_);
v___x_7391_ = v___x_7380_;
goto v_reusejp_7390_;
}
else
{
lean_object* v_reuseFailAlloc_7395_; 
v_reuseFailAlloc_7395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7395_, 0, v___x_7291_);
lean_ctor_set(v_reuseFailAlloc_7395_, 1, v_k_7377_);
lean_ctor_set(v_reuseFailAlloc_7395_, 2, v_v_7378_);
lean_ctor_set(v_reuseFailAlloc_7395_, 3, v_r_7376_);
lean_ctor_set(v_reuseFailAlloc_7395_, 4, v_r_7376_);
v___x_7391_ = v_reuseFailAlloc_7395_;
goto v_reusejp_7390_;
}
v_reusejp_7390_:
{
lean_object* v___x_7393_; 
if (v_isShared_7148_ == 0)
{
lean_ctor_set(v___x_7147_, 4, v___x_7391_);
lean_ctor_set(v___x_7147_, 3, v___x_7389_);
lean_ctor_set(v___x_7147_, 2, v_v_7383_);
lean_ctor_set(v___x_7147_, 1, v_k_7382_);
lean_ctor_set(v___x_7147_, 0, v___x_7387_);
v___x_7393_ = v___x_7147_;
goto v_reusejp_7392_;
}
else
{
lean_object* v_reuseFailAlloc_7394_; 
v_reuseFailAlloc_7394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7394_, 0, v___x_7387_);
lean_ctor_set(v_reuseFailAlloc_7394_, 1, v_k_7382_);
lean_ctor_set(v_reuseFailAlloc_7394_, 2, v_v_7383_);
lean_ctor_set(v_reuseFailAlloc_7394_, 3, v___x_7389_);
lean_ctor_set(v_reuseFailAlloc_7394_, 4, v___x_7391_);
v___x_7393_ = v_reuseFailAlloc_7394_;
goto v_reusejp_7392_;
}
v_reusejp_7392_:
{
return v___x_7393_;
}
}
}
}
}
}
else
{
lean_object* v_r_7404_; 
v_r_7404_ = lean_ctor_get(v_impl_7290_, 4);
lean_inc(v_r_7404_);
if (lean_obj_tag(v_r_7404_) == 0)
{
lean_object* v_k_7405_; lean_object* v_v_7406_; lean_object* v___x_7408_; uint8_t v_isShared_7409_; uint8_t v_isSharedCheck_7417_; 
v_k_7405_ = lean_ctor_get(v_impl_7290_, 1);
v_v_7406_ = lean_ctor_get(v_impl_7290_, 2);
v_isSharedCheck_7417_ = !lean_is_exclusive(v_impl_7290_);
if (v_isSharedCheck_7417_ == 0)
{
lean_object* v_unused_7418_; lean_object* v_unused_7419_; lean_object* v_unused_7420_; 
v_unused_7418_ = lean_ctor_get(v_impl_7290_, 4);
lean_dec(v_unused_7418_);
v_unused_7419_ = lean_ctor_get(v_impl_7290_, 3);
lean_dec(v_unused_7419_);
v_unused_7420_ = lean_ctor_get(v_impl_7290_, 0);
lean_dec(v_unused_7420_);
v___x_7408_ = v_impl_7290_;
v_isShared_7409_ = v_isSharedCheck_7417_;
goto v_resetjp_7407_;
}
else
{
lean_inc(v_v_7406_);
lean_inc(v_k_7405_);
lean_dec(v_impl_7290_);
v___x_7408_ = lean_box(0);
v_isShared_7409_ = v_isSharedCheck_7417_;
goto v_resetjp_7407_;
}
v_resetjp_7407_:
{
lean_object* v___x_7410_; lean_object* v___x_7412_; 
v___x_7410_ = lean_unsigned_to_nat(3u);
if (v_isShared_7409_ == 0)
{
lean_ctor_set(v___x_7408_, 4, v_l_7375_);
lean_ctor_set(v___x_7408_, 2, v_v_7143_);
lean_ctor_set(v___x_7408_, 1, v_k_7142_);
lean_ctor_set(v___x_7408_, 0, v___x_7291_);
v___x_7412_ = v___x_7408_;
goto v_reusejp_7411_;
}
else
{
lean_object* v_reuseFailAlloc_7416_; 
v_reuseFailAlloc_7416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7416_, 0, v___x_7291_);
lean_ctor_set(v_reuseFailAlloc_7416_, 1, v_k_7142_);
lean_ctor_set(v_reuseFailAlloc_7416_, 2, v_v_7143_);
lean_ctor_set(v_reuseFailAlloc_7416_, 3, v_l_7375_);
lean_ctor_set(v_reuseFailAlloc_7416_, 4, v_l_7375_);
v___x_7412_ = v_reuseFailAlloc_7416_;
goto v_reusejp_7411_;
}
v_reusejp_7411_:
{
lean_object* v___x_7414_; 
if (v_isShared_7148_ == 0)
{
lean_ctor_set(v___x_7147_, 4, v_r_7404_);
lean_ctor_set(v___x_7147_, 3, v___x_7412_);
lean_ctor_set(v___x_7147_, 2, v_v_7406_);
lean_ctor_set(v___x_7147_, 1, v_k_7405_);
lean_ctor_set(v___x_7147_, 0, v___x_7410_);
v___x_7414_ = v___x_7147_;
goto v_reusejp_7413_;
}
else
{
lean_object* v_reuseFailAlloc_7415_; 
v_reuseFailAlloc_7415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7415_, 0, v___x_7410_);
lean_ctor_set(v_reuseFailAlloc_7415_, 1, v_k_7405_);
lean_ctor_set(v_reuseFailAlloc_7415_, 2, v_v_7406_);
lean_ctor_set(v_reuseFailAlloc_7415_, 3, v___x_7412_);
lean_ctor_set(v_reuseFailAlloc_7415_, 4, v_r_7404_);
v___x_7414_ = v_reuseFailAlloc_7415_;
goto v_reusejp_7413_;
}
v_reusejp_7413_:
{
return v___x_7414_;
}
}
}
}
else
{
lean_object* v___x_7421_; lean_object* v___x_7423_; 
v___x_7421_ = lean_unsigned_to_nat(2u);
if (v_isShared_7148_ == 0)
{
lean_ctor_set(v___x_7147_, 4, v_impl_7290_);
lean_ctor_set(v___x_7147_, 3, v_r_7404_);
lean_ctor_set(v___x_7147_, 0, v___x_7421_);
v___x_7423_ = v___x_7147_;
goto v_reusejp_7422_;
}
else
{
lean_object* v_reuseFailAlloc_7424_; 
v_reuseFailAlloc_7424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_7424_, 0, v___x_7421_);
lean_ctor_set(v_reuseFailAlloc_7424_, 1, v_k_7142_);
lean_ctor_set(v_reuseFailAlloc_7424_, 2, v_v_7143_);
lean_ctor_set(v_reuseFailAlloc_7424_, 3, v_r_7404_);
lean_ctor_set(v_reuseFailAlloc_7424_, 4, v_impl_7290_);
v___x_7423_ = v_reuseFailAlloc_7424_;
goto v_reusejp_7422_;
}
v_reusejp_7422_:
{
return v___x_7423_;
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
lean_object* v___x_7426_; lean_object* v___x_7427_; 
v___x_7426_ = lean_unsigned_to_nat(1u);
v___x_7427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_7427_, 0, v___x_7426_);
lean_ctor_set(v___x_7427_, 1, v_k_7138_);
lean_ctor_set(v___x_7427_, 2, v_v_7139_);
lean_ctor_set(v___x_7427_, 3, v_t_7140_);
lean_ctor_set(v___x_7427_, 4, v_t_7140_);
return v___x_7427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(lean_object* v_lib_7428_, lean_object* v_ps_7429_, lean_object* v_v_7430_, lean_object* v_o_7431_){
_start:
{
lean_object* v_name_7432_; lean_object* v_deps_7433_; lean_object* v_o_7434_; uint8_t v___x_7435_; 
v_name_7432_ = lean_ctor_get(v_lib_7428_, 1);
lean_inc_ref(v_name_7432_);
v_deps_7433_ = lean_ctor_get(v_lib_7428_, 2);
lean_inc_ref(v_deps_7433_);
v_o_7434_ = lean_array_push(v_o_7431_, v_lib_7428_);
v___x_7435_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_name_7432_, v_v_7430_);
if (v___x_7435_ == 0)
{
uint8_t v___x_7436_; 
v___x_7436_ = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(v_name_7432_, v_ps_7429_);
if (v___x_7436_ == 0)
{
lean_object* v_ps_7437_; lean_object* v___y_7439_; 
lean_inc_ref(v_name_7432_);
v_ps_7437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_ps_7437_, 0, v_name_7432_);
lean_ctor_set(v_ps_7437_, 1, v_ps_7429_);
if (v___x_7435_ == 0)
{
lean_object* v___x_7453_; lean_object* v___x_7454_; 
v___x_7453_ = lean_box(0);
v___x_7454_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_name_7432_, v___x_7453_, v_v_7430_);
v___y_7439_ = v___x_7454_;
goto v___jp_7438_;
}
else
{
lean_dec_ref(v_name_7432_);
v___y_7439_ = v_v_7430_;
goto v___jp_7438_;
}
v___jp_7438_:
{
lean_object* v___x_7440_; lean_object* v___x_7441_; lean_object* v___x_7442_; uint8_t v___x_7443_; 
v___x_7440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7440_, 0, v___y_7439_);
lean_ctor_set(v___x_7440_, 1, v_o_7434_);
v___x_7441_ = lean_unsigned_to_nat(0u);
v___x_7442_ = lean_array_get_size(v_deps_7433_);
v___x_7443_ = lean_nat_dec_lt(v___x_7441_, v___x_7442_);
if (v___x_7443_ == 0)
{
lean_object* v___x_7444_; 
lean_dec_ref_known(v_ps_7437_, 2);
lean_dec_ref(v_deps_7433_);
v___x_7444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7444_, 0, v___x_7440_);
return v___x_7444_;
}
else
{
uint8_t v___x_7445_; 
v___x_7445_ = lean_nat_dec_le(v___x_7442_, v___x_7442_);
if (v___x_7445_ == 0)
{
if (v___x_7443_ == 0)
{
lean_object* v___x_7446_; 
lean_dec_ref_known(v_ps_7437_, 2);
lean_dec_ref(v_deps_7433_);
v___x_7446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7446_, 0, v___x_7440_);
return v___x_7446_;
}
else
{
size_t v___x_7447_; size_t v___x_7448_; lean_object* v___x_7449_; 
v___x_7447_ = ((size_t)0ULL);
v___x_7448_ = lean_usize_of_nat(v___x_7442_);
v___x_7449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7437_, v_deps_7433_, v___x_7447_, v___x_7448_, v___x_7440_);
lean_dec_ref(v_deps_7433_);
return v___x_7449_;
}
}
else
{
size_t v___x_7450_; size_t v___x_7451_; lean_object* v___x_7452_; 
v___x_7450_ = ((size_t)0ULL);
v___x_7451_ = lean_usize_of_nat(v___x_7442_);
v___x_7452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7437_, v_deps_7433_, v___x_7450_, v___x_7451_, v___x_7440_);
lean_dec_ref(v_deps_7433_);
return v___x_7452_;
}
}
}
}
else
{
lean_object* v___x_7455_; lean_object* v___x_7456_; 
lean_dec_ref(v_o_7434_);
lean_dec_ref(v_deps_7433_);
lean_dec(v_v_7430_);
v___x_7455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7455_, 0, v_name_7432_);
lean_ctor_set(v___x_7455_, 1, v_ps_7429_);
v___x_7456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7456_, 0, v___x_7455_);
return v___x_7456_;
}
}
else
{
lean_object* v___x_7457_; lean_object* v___x_7458_; 
lean_dec_ref(v_deps_7433_);
lean_dec_ref(v_name_7432_);
lean_dec(v_ps_7429_);
v___x_7457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7457_, 0, v_v_7430_);
lean_ctor_set(v___x_7457_, 1, v_o_7434_);
v___x_7458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7458_, 0, v___x_7457_);
return v___x_7458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(lean_object* v_ps_7459_, lean_object* v_as_7460_, size_t v_i_7461_, size_t v_stop_7462_, lean_object* v_b_7463_){
_start:
{
uint8_t v___x_7464_; 
v___x_7464_ = lean_usize_dec_eq(v_i_7461_, v_stop_7462_);
if (v___x_7464_ == 0)
{
lean_object* v_fst_7465_; lean_object* v_snd_7466_; lean_object* v___x_7467_; lean_object* v___x_7468_; 
v_fst_7465_ = lean_ctor_get(v_b_7463_, 0);
lean_inc(v_fst_7465_);
v_snd_7466_ = lean_ctor_get(v_b_7463_, 1);
lean_inc(v_snd_7466_);
lean_dec_ref(v_b_7463_);
v___x_7467_ = lean_array_uget_borrowed(v_as_7460_, v_i_7461_);
lean_inc(v_ps_7459_);
lean_inc(v___x_7467_);
v___x_7468_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(v___x_7467_, v_ps_7459_, v_fst_7465_, v_snd_7466_);
if (lean_obj_tag(v___x_7468_) == 0)
{
lean_dec(v_ps_7459_);
return v___x_7468_;
}
else
{
lean_object* v_a_7469_; size_t v___x_7470_; size_t v___x_7471_; 
v_a_7469_ = lean_ctor_get(v___x_7468_, 0);
lean_inc(v_a_7469_);
lean_dec_ref_known(v___x_7468_, 1);
v___x_7470_ = ((size_t)1ULL);
v___x_7471_ = lean_usize_add(v_i_7461_, v___x_7470_);
v_i_7461_ = v___x_7471_;
v_b_7463_ = v_a_7469_;
goto _start;
}
}
else
{
lean_object* v___x_7473_; 
lean_dec(v_ps_7459_);
v___x_7473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7473_, 0, v_b_7463_);
return v___x_7473_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2___boxed(lean_object* v_ps_7474_, lean_object* v_as_7475_, lean_object* v_i_7476_, lean_object* v_stop_7477_, lean_object* v_b_7478_){
_start:
{
size_t v_i_boxed_7479_; size_t v_stop_boxed_7480_; lean_object* v_res_7481_; 
v_i_boxed_7479_ = lean_unbox_usize(v_i_7476_);
lean_dec(v_i_7476_);
v_stop_boxed_7480_ = lean_unbox_usize(v_stop_7477_);
lean_dec(v_stop_7477_);
v_res_7481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(v_ps_7474_, v_as_7475_, v_i_boxed_7479_, v_stop_boxed_7480_, v_b_7478_);
lean_dec_ref(v_as_7475_);
return v_res_7481_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(lean_object* v_00_u03b2_7482_, lean_object* v_k_7483_, lean_object* v_t_7484_){
_start:
{
uint8_t v___x_7485_; 
v___x_7485_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(v_k_7483_, v_t_7484_);
return v___x_7485_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___boxed(lean_object* v_00_u03b2_7486_, lean_object* v_k_7487_, lean_object* v_t_7488_){
_start:
{
uint8_t v_res_7489_; lean_object* v_r_7490_; 
v_res_7489_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(v_00_u03b2_7486_, v_k_7487_, v_t_7488_);
lean_dec(v_t_7488_);
lean_dec_ref(v_k_7487_);
v_r_7490_ = lean_box(v_res_7489_);
return v_r_7490_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3(lean_object* v_00_u03b2_7491_, lean_object* v_k_7492_, lean_object* v_v_7493_, lean_object* v_t_7494_, lean_object* v_hl_7495_){
_start:
{
lean_object* v___x_7496_; 
v___x_7496_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(v_k_7492_, v_v_7493_, v_t_7494_);
return v___x_7496_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0_spec__0(lean_object* v_a_7498_, lean_object* v_a_7499_){
_start:
{
if (lean_obj_tag(v_a_7498_) == 0)
{
lean_object* v___x_7500_; 
v___x_7500_ = l_List_reverse___redArg(v_a_7499_);
return v___x_7500_;
}
else
{
lean_object* v_head_7501_; lean_object* v_tail_7502_; lean_object* v___x_7504_; uint8_t v_isShared_7505_; uint8_t v_isSharedCheck_7512_; 
v_head_7501_ = lean_ctor_get(v_a_7498_, 0);
v_tail_7502_ = lean_ctor_get(v_a_7498_, 1);
v_isSharedCheck_7512_ = !lean_is_exclusive(v_a_7498_);
if (v_isSharedCheck_7512_ == 0)
{
v___x_7504_ = v_a_7498_;
v_isShared_7505_ = v_isSharedCheck_7512_;
goto v_resetjp_7503_;
}
else
{
lean_inc(v_tail_7502_);
lean_inc(v_head_7501_);
lean_dec(v_a_7498_);
v___x_7504_ = lean_box(0);
v_isShared_7505_ = v_isSharedCheck_7512_;
goto v_resetjp_7503_;
}
v_resetjp_7503_:
{
lean_object* v___x_7506_; lean_object* v___x_7507_; lean_object* v___x_7509_; 
v___x_7506_ = ((lean_object*)(l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0_spec__0___closed__0));
v___x_7507_ = lean_string_append(v___x_7506_, v_head_7501_);
lean_dec(v_head_7501_);
if (v_isShared_7505_ == 0)
{
lean_ctor_set(v___x_7504_, 1, v_a_7499_);
lean_ctor_set(v___x_7504_, 0, v___x_7507_);
v___x_7509_ = v___x_7504_;
goto v_reusejp_7508_;
}
else
{
lean_object* v_reuseFailAlloc_7511_; 
v_reuseFailAlloc_7511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7511_, 0, v___x_7507_);
lean_ctor_set(v_reuseFailAlloc_7511_, 1, v_a_7499_);
v___x_7509_ = v_reuseFailAlloc_7511_;
goto v_reusejp_7508_;
}
v_reusejp_7508_:
{
v_a_7498_ = v_tail_7502_;
v_a_7499_ = v___x_7509_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0(lean_object* v_cycle_7513_){
_start:
{
lean_object* v___x_7514_; lean_object* v___x_7515_; lean_object* v___x_7516_; lean_object* v___x_7517_; 
v___x_7514_ = ((lean_object*)(l_Lake_resolveArtifactOutput___closed__1));
v___x_7515_ = lean_box(0);
v___x_7516_ = l_List_mapTR_loop___at___00Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0_spec__0(v_cycle_7513_, v___x_7515_);
v___x_7517_ = l_String_intercalate(v___x_7514_, v___x_7516_);
return v___x_7517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1(lean_object* v_as_7518_, size_t v_i_7519_, size_t v_stop_7520_, lean_object* v_b_7521_){
_start:
{
uint8_t v___x_7522_; 
v___x_7522_ = lean_usize_dec_eq(v_i_7519_, v_stop_7520_);
if (v___x_7522_ == 0)
{
lean_object* v_fst_7523_; lean_object* v_snd_7524_; lean_object* v___x_7525_; lean_object* v___x_7526_; lean_object* v___x_7527_; 
v_fst_7523_ = lean_ctor_get(v_b_7521_, 0);
lean_inc(v_fst_7523_);
v_snd_7524_ = lean_ctor_get(v_b_7521_, 1);
lean_inc(v_snd_7524_);
lean_dec_ref(v_b_7521_);
v___x_7525_ = lean_array_uget_borrowed(v_as_7518_, v_i_7519_);
v___x_7526_ = lean_box(0);
lean_inc(v___x_7525_);
v___x_7527_ = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(v___x_7525_, v___x_7526_, v_fst_7523_, v_snd_7524_);
if (lean_obj_tag(v___x_7527_) == 0)
{
return v___x_7527_;
}
else
{
lean_object* v_a_7528_; size_t v___x_7529_; size_t v___x_7530_; 
v_a_7528_ = lean_ctor_get(v___x_7527_, 0);
lean_inc(v_a_7528_);
lean_dec_ref_known(v___x_7527_, 1);
v___x_7529_ = ((size_t)1ULL);
v___x_7530_ = lean_usize_add(v_i_7519_, v___x_7529_);
v_i_7519_ = v___x_7530_;
v_b_7521_ = v_a_7528_;
goto _start;
}
}
else
{
lean_object* v___x_7532_; 
v___x_7532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7532_, 0, v_b_7521_);
return v___x_7532_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1___boxed(lean_object* v_as_7533_, lean_object* v_i_7534_, lean_object* v_stop_7535_, lean_object* v_b_7536_){
_start:
{
size_t v_i_boxed_7537_; size_t v_stop_boxed_7538_; lean_object* v_res_7539_; 
v_i_boxed_7537_ = lean_unbox_usize(v_i_7534_);
lean_dec(v_i_7534_);
v_stop_boxed_7538_ = lean_unbox_usize(v_stop_7535_);
lean_dec(v_stop_7535_);
v_res_7539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1(v_as_7533_, v_i_boxed_7537_, v_stop_boxed_7538_, v_b_7536_);
lean_dec_ref(v_as_7533_);
return v_res_7539_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder___redArg(lean_object* v_libs_7546_, lean_object* v_a_7547_){
_start:
{
lean_object* v_snd_7550_; lean_object* v___y_7553_; lean_object* v___x_7577_; lean_object* v___x_7578_; lean_object* v___x_7579_; uint8_t v___x_7580_; 
v___x_7577_ = lean_unsigned_to_nat(0u);
v___x_7578_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v___x_7579_ = lean_array_get_size(v_libs_7546_);
v___x_7580_ = lean_nat_dec_lt(v___x_7577_, v___x_7579_);
if (v___x_7580_ == 0)
{
v_snd_7550_ = v___x_7578_;
goto v___jp_7549_;
}
else
{
lean_object* v___x_7581_; uint8_t v___x_7582_; 
v___x_7581_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__2));
v___x_7582_ = lean_nat_dec_le(v___x_7579_, v___x_7579_);
if (v___x_7582_ == 0)
{
if (v___x_7580_ == 0)
{
v_snd_7550_ = v___x_7578_;
goto v___jp_7549_;
}
else
{
size_t v___x_7583_; size_t v___x_7584_; lean_object* v___x_7585_; 
v___x_7583_ = ((size_t)0ULL);
v___x_7584_ = lean_usize_of_nat(v___x_7579_);
v___x_7585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1(v_libs_7546_, v___x_7583_, v___x_7584_, v___x_7581_);
v___y_7553_ = v___x_7585_;
goto v___jp_7552_;
}
}
else
{
size_t v___x_7586_; size_t v___x_7587_; lean_object* v___x_7588_; 
v___x_7586_ = ((size_t)0ULL);
v___x_7587_ = lean_usize_of_nat(v___x_7579_);
v___x_7588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkLinkOrder_spec__1(v_libs_7546_, v___x_7586_, v___x_7587_, v___x_7581_);
v___y_7553_ = v___x_7588_;
goto v___jp_7552_;
}
}
v___jp_7549_:
{
lean_object* v___x_7551_; 
v___x_7551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7551_, 0, v_snd_7550_);
lean_ctor_set(v___x_7551_, 1, v_a_7547_);
return v___x_7551_;
}
v___jp_7552_:
{
if (lean_obj_tag(v___y_7553_) == 0)
{
lean_object* v_a_7554_; lean_object* v_log_7555_; uint8_t v_action_7556_; uint8_t v_wantsRebuild_7557_; lean_object* v_trace_7558_; lean_object* v_buildTime_7559_; lean_object* v___x_7561_; uint8_t v_isShared_7562_; uint8_t v_isSharedCheck_7574_; 
v_a_7554_ = lean_ctor_get(v___y_7553_, 0);
lean_inc(v_a_7554_);
lean_dec_ref_known(v___y_7553_, 1);
v_log_7555_ = lean_ctor_get(v_a_7547_, 0);
v_action_7556_ = lean_ctor_get_uint8(v_a_7547_, sizeof(void*)*3);
v_wantsRebuild_7557_ = lean_ctor_get_uint8(v_a_7547_, sizeof(void*)*3 + 1);
v_trace_7558_ = lean_ctor_get(v_a_7547_, 1);
v_buildTime_7559_ = lean_ctor_get(v_a_7547_, 2);
v_isSharedCheck_7574_ = !lean_is_exclusive(v_a_7547_);
if (v_isSharedCheck_7574_ == 0)
{
v___x_7561_ = v_a_7547_;
v_isShared_7562_ = v_isSharedCheck_7574_;
goto v_resetjp_7560_;
}
else
{
lean_inc(v_buildTime_7559_);
lean_inc(v_trace_7558_);
lean_inc(v_log_7555_);
lean_dec(v_a_7547_);
v___x_7561_ = lean_box(0);
v_isShared_7562_ = v_isSharedCheck_7574_;
goto v_resetjp_7560_;
}
v_resetjp_7560_:
{
lean_object* v___x_7563_; lean_object* v___x_7564_; lean_object* v___x_7565_; uint8_t v___x_7566_; lean_object* v___x_7567_; lean_object* v___x_7568_; lean_object* v___x_7569_; lean_object* v___x_7571_; 
v___x_7563_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__0));
v___x_7564_ = l_Lake_formatCycle___at___00Lake_mkLinkOrder_spec__0(v_a_7554_);
v___x_7565_ = lean_string_append(v___x_7563_, v___x_7564_);
lean_dec_ref(v___x_7564_);
v___x_7566_ = 3;
v___x_7567_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_7567_, 0, v___x_7565_);
lean_ctor_set_uint8(v___x_7567_, sizeof(void*)*1, v___x_7566_);
v___x_7568_ = lean_array_get_size(v_log_7555_);
v___x_7569_ = lean_array_push(v_log_7555_, v___x_7567_);
if (v_isShared_7562_ == 0)
{
lean_ctor_set(v___x_7561_, 0, v___x_7569_);
v___x_7571_ = v___x_7561_;
goto v_reusejp_7570_;
}
else
{
lean_object* v_reuseFailAlloc_7573_; 
v_reuseFailAlloc_7573_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7573_, 0, v___x_7569_);
lean_ctor_set(v_reuseFailAlloc_7573_, 1, v_trace_7558_);
lean_ctor_set(v_reuseFailAlloc_7573_, 2, v_buildTime_7559_);
lean_ctor_set_uint8(v_reuseFailAlloc_7573_, sizeof(void*)*3, v_action_7556_);
lean_ctor_set_uint8(v_reuseFailAlloc_7573_, sizeof(void*)*3 + 1, v_wantsRebuild_7557_);
v___x_7571_ = v_reuseFailAlloc_7573_;
goto v_reusejp_7570_;
}
v_reusejp_7570_:
{
lean_object* v___x_7572_; 
v___x_7572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7572_, 0, v___x_7568_);
lean_ctor_set(v___x_7572_, 1, v___x_7571_);
return v___x_7572_;
}
}
}
else
{
lean_object* v_a_7575_; lean_object* v_snd_7576_; 
v_a_7575_ = lean_ctor_get(v___y_7553_, 0);
lean_inc(v_a_7575_);
lean_dec_ref_known(v___y_7553_, 1);
v_snd_7576_ = lean_ctor_get(v_a_7575_, 1);
lean_inc(v_snd_7576_);
lean_dec(v_a_7575_);
v_snd_7550_ = v_snd_7576_;
goto v___jp_7549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder___redArg___boxed(lean_object* v_libs_7589_, lean_object* v_a_7590_, lean_object* v_a_7591_){
_start:
{
lean_object* v_res_7592_; 
v_res_7592_ = l_Lake_mkLinkOrder___redArg(v_libs_7589_, v_a_7590_);
lean_dec_ref(v_libs_7589_);
return v_res_7592_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder(lean_object* v_libs_7593_, lean_object* v_a_7594_, lean_object* v_a_7595_, lean_object* v_a_7596_, lean_object* v_a_7597_, lean_object* v_a_7598_, lean_object* v_a_7599_){
_start:
{
lean_object* v___x_7601_; 
v___x_7601_ = l_Lake_mkLinkOrder___redArg(v_libs_7593_, v_a_7599_);
return v___x_7601_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkOrder___boxed(lean_object* v_libs_7602_, lean_object* v_a_7603_, lean_object* v_a_7604_, lean_object* v_a_7605_, lean_object* v_a_7606_, lean_object* v_a_7607_, lean_object* v_a_7608_, lean_object* v_a_7609_){
_start:
{
lean_object* v_res_7610_; 
v_res_7610_ = l_Lake_mkLinkOrder(v_libs_7602_, v_a_7603_, v_a_7604_, v_a_7605_, v_a_7606_, v_a_7607_, v_a_7608_);
lean_dec_ref(v_a_7607_);
lean_dec(v_a_7606_);
lean_dec(v_a_7605_);
lean_dec(v_a_7604_);
lean_dec_ref(v_a_7603_);
lean_dec_ref(v_libs_7602_);
return v_res_7610_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs___redArg(lean_object* v_objs_7611_, lean_object* v_libs_7612_, uint8_t v_linkDeps_7613_, lean_object* v_a_7614_){
_start:
{
lean_object* v_libs_7617_; lean_object* v___y_7618_; 
if (v_linkDeps_7613_ == 0)
{
lean_object* v___x_7621_; 
v___x_7621_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7617_ = v___x_7621_;
v___y_7618_ = v_a_7614_;
goto v___jp_7616_;
}
else
{
lean_object* v___x_7622_; 
v___x_7622_ = l_Lake_mkLinkOrder___redArg(v_libs_7612_, v_a_7614_);
if (lean_obj_tag(v___x_7622_) == 0)
{
lean_object* v_a_7623_; lean_object* v_a_7624_; 
v_a_7623_ = lean_ctor_get(v___x_7622_, 0);
lean_inc(v_a_7623_);
v_a_7624_ = lean_ctor_get(v___x_7622_, 1);
lean_inc(v_a_7624_);
lean_dec_ref_known(v___x_7622_, 2);
v_libs_7617_ = v_a_7623_;
v___y_7618_ = v_a_7624_;
goto v___jp_7616_;
}
else
{
lean_object* v_a_7625_; lean_object* v_a_7626_; lean_object* v___x_7628_; uint8_t v_isShared_7629_; uint8_t v_isSharedCheck_7633_; 
v_a_7625_ = lean_ctor_get(v___x_7622_, 0);
v_a_7626_ = lean_ctor_get(v___x_7622_, 1);
v_isSharedCheck_7633_ = !lean_is_exclusive(v___x_7622_);
if (v_isSharedCheck_7633_ == 0)
{
v___x_7628_ = v___x_7622_;
v_isShared_7629_ = v_isSharedCheck_7633_;
goto v_resetjp_7627_;
}
else
{
lean_inc(v_a_7626_);
lean_inc(v_a_7625_);
lean_dec(v___x_7622_);
v___x_7628_ = lean_box(0);
v_isShared_7629_ = v_isSharedCheck_7633_;
goto v_resetjp_7627_;
}
v_resetjp_7627_:
{
lean_object* v___x_7631_; 
if (v_isShared_7629_ == 0)
{
v___x_7631_ = v___x_7628_;
goto v_reusejp_7630_;
}
else
{
lean_object* v_reuseFailAlloc_7632_; 
v_reuseFailAlloc_7632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7632_, 0, v_a_7625_);
lean_ctor_set(v_reuseFailAlloc_7632_, 1, v_a_7626_);
v___x_7631_ = v_reuseFailAlloc_7632_;
goto v_reusejp_7630_;
}
v_reusejp_7630_:
{
return v___x_7631_;
}
}
}
}
v___jp_7616_:
{
lean_object* v___x_7619_; lean_object* v___x_7620_; 
v___x_7619_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7611_, v_libs_7617_);
lean_dec_ref(v_libs_7617_);
v___x_7620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7620_, 0, v___x_7619_);
lean_ctor_set(v___x_7620_, 1, v___y_7618_);
return v___x_7620_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs___redArg___boxed(lean_object* v_objs_7634_, lean_object* v_libs_7635_, lean_object* v_linkDeps_7636_, lean_object* v_a_7637_, lean_object* v_a_7638_){
_start:
{
uint8_t v_linkDeps_boxed_7639_; lean_object* v_res_7640_; 
v_linkDeps_boxed_7639_ = lean_unbox(v_linkDeps_7636_);
v_res_7640_ = l_Lake_mkLinkArgs___redArg(v_objs_7634_, v_libs_7635_, v_linkDeps_boxed_7639_, v_a_7637_);
lean_dec_ref(v_libs_7635_);
lean_dec_ref(v_objs_7634_);
return v_res_7640_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs(lean_object* v_objs_7641_, lean_object* v_libs_7642_, uint8_t v_linkDeps_7643_, lean_object* v_a_7644_, lean_object* v_a_7645_, lean_object* v_a_7646_, lean_object* v_a_7647_, lean_object* v_a_7648_, lean_object* v_a_7649_){
_start:
{
lean_object* v_libs_7652_; lean_object* v___y_7653_; 
if (v_linkDeps_7643_ == 0)
{
lean_object* v___x_7656_; 
v___x_7656_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7652_ = v___x_7656_;
v___y_7653_ = v_a_7649_;
goto v___jp_7651_;
}
else
{
lean_object* v___x_7657_; 
v___x_7657_ = l_Lake_mkLinkOrder___redArg(v_libs_7642_, v_a_7649_);
if (lean_obj_tag(v___x_7657_) == 0)
{
lean_object* v_a_7658_; lean_object* v_a_7659_; 
v_a_7658_ = lean_ctor_get(v___x_7657_, 0);
lean_inc(v_a_7658_);
v_a_7659_ = lean_ctor_get(v___x_7657_, 1);
lean_inc(v_a_7659_);
lean_dec_ref_known(v___x_7657_, 2);
v_libs_7652_ = v_a_7658_;
v___y_7653_ = v_a_7659_;
goto v___jp_7651_;
}
else
{
lean_object* v_a_7660_; lean_object* v_a_7661_; lean_object* v___x_7663_; uint8_t v_isShared_7664_; uint8_t v_isSharedCheck_7668_; 
v_a_7660_ = lean_ctor_get(v___x_7657_, 0);
v_a_7661_ = lean_ctor_get(v___x_7657_, 1);
v_isSharedCheck_7668_ = !lean_is_exclusive(v___x_7657_);
if (v_isSharedCheck_7668_ == 0)
{
v___x_7663_ = v___x_7657_;
v_isShared_7664_ = v_isSharedCheck_7668_;
goto v_resetjp_7662_;
}
else
{
lean_inc(v_a_7661_);
lean_inc(v_a_7660_);
lean_dec(v___x_7657_);
v___x_7663_ = lean_box(0);
v_isShared_7664_ = v_isSharedCheck_7668_;
goto v_resetjp_7662_;
}
v_resetjp_7662_:
{
lean_object* v___x_7666_; 
if (v_isShared_7664_ == 0)
{
v___x_7666_ = v___x_7663_;
goto v_reusejp_7665_;
}
else
{
lean_object* v_reuseFailAlloc_7667_; 
v_reuseFailAlloc_7667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7667_, 0, v_a_7660_);
lean_ctor_set(v_reuseFailAlloc_7667_, 1, v_a_7661_);
v___x_7666_ = v_reuseFailAlloc_7667_;
goto v_reusejp_7665_;
}
v_reusejp_7665_:
{
return v___x_7666_;
}
}
}
}
v___jp_7651_:
{
lean_object* v___x_7654_; lean_object* v___x_7655_; 
v___x_7654_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7641_, v_libs_7652_);
lean_dec_ref(v_libs_7652_);
v___x_7655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7655_, 0, v___x_7654_);
lean_ctor_set(v___x_7655_, 1, v___y_7653_);
return v___x_7655_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkLinkArgs___boxed(lean_object* v_objs_7669_, lean_object* v_libs_7670_, lean_object* v_linkDeps_7671_, lean_object* v_a_7672_, lean_object* v_a_7673_, lean_object* v_a_7674_, lean_object* v_a_7675_, lean_object* v_a_7676_, lean_object* v_a_7677_, lean_object* v_a_7678_){
_start:
{
uint8_t v_linkDeps_boxed_7679_; lean_object* v_res_7680_; 
v_linkDeps_boxed_7679_ = lean_unbox(v_linkDeps_7671_);
v_res_7680_ = l_Lake_mkLinkArgs(v_objs_7669_, v_libs_7670_, v_linkDeps_boxed_7679_, v_a_7672_, v_a_7673_, v_a_7674_, v_a_7675_, v_a_7676_, v_a_7677_);
lean_dec_ref(v_a_7676_);
lean_dec(v_a_7675_);
lean_dec(v_a_7674_);
lean_dec(v_a_7673_);
lean_dec_ref(v_a_7672_);
lean_dec_ref(v_libs_7670_);
lean_dec_ref(v_objs_7669_);
return v_res_7680_;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0(void){
_start:
{
lean_object* v___x_7681_; lean_object* v___x_7682_; lean_object* v___x_7683_; lean_object* v___x_7684_; 
v___x_7681_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1));
v___x_7682_ = lean_unsigned_to_nat(2u);
v___x_7683_ = lean_mk_empty_array_with_capacity(v___x_7682_);
v___x_7684_ = lean_array_push(v___x_7683_, v___x_7681_);
return v___x_7684_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg(lean_object* v_objs_7685_, lean_object* v_libs_7686_, lean_object* v_args_7687_, uint8_t v_linkDeps_7688_, uint8_t v_sharedLean_7689_, lean_object* v_a_7690_, lean_object* v_a_7691_){
_start:
{
lean_object* v_toContext_7693_; lean_object* v_lakeEnv_7694_; lean_object* v_lean_7695_; lean_object* v_libs_7697_; lean_object* v___y_7698_; 
v_toContext_7693_ = lean_ctor_get(v_a_7690_, 1);
v_lakeEnv_7694_ = lean_ctor_get(v_toContext_7693_, 0);
v_lean_7695_ = lean_ctor_get(v_lakeEnv_7694_, 1);
if (v_linkDeps_7688_ == 0)
{
lean_object* v___x_7708_; 
v___x_7708_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7697_ = v___x_7708_;
v___y_7698_ = v_a_7691_;
goto v___jp_7696_;
}
else
{
lean_object* v___x_7709_; 
v___x_7709_ = l_Lake_mkLinkOrder___redArg(v_libs_7686_, v_a_7691_);
if (lean_obj_tag(v___x_7709_) == 0)
{
lean_object* v_a_7710_; lean_object* v_a_7711_; 
v_a_7710_ = lean_ctor_get(v___x_7709_, 0);
lean_inc(v_a_7710_);
v_a_7711_ = lean_ctor_get(v___x_7709_, 1);
lean_inc(v_a_7711_);
lean_dec_ref_known(v___x_7709_, 2);
v_libs_7697_ = v_a_7710_;
v___y_7698_ = v_a_7711_;
goto v___jp_7696_;
}
else
{
lean_object* v_a_7712_; lean_object* v_a_7713_; lean_object* v___x_7715_; uint8_t v_isShared_7716_; uint8_t v_isSharedCheck_7720_; 
v_a_7712_ = lean_ctor_get(v___x_7709_, 0);
v_a_7713_ = lean_ctor_get(v___x_7709_, 1);
v_isSharedCheck_7720_ = !lean_is_exclusive(v___x_7709_);
if (v_isSharedCheck_7720_ == 0)
{
v___x_7715_ = v___x_7709_;
v_isShared_7716_ = v_isSharedCheck_7720_;
goto v_resetjp_7714_;
}
else
{
lean_inc(v_a_7713_);
lean_inc(v_a_7712_);
lean_dec(v___x_7709_);
v___x_7715_ = lean_box(0);
v_isShared_7716_ = v_isSharedCheck_7720_;
goto v_resetjp_7714_;
}
v_resetjp_7714_:
{
lean_object* v___x_7718_; 
if (v_isShared_7716_ == 0)
{
v___x_7718_ = v___x_7715_;
goto v_reusejp_7717_;
}
else
{
lean_object* v_reuseFailAlloc_7719_; 
v_reuseFailAlloc_7719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7719_, 0, v_a_7712_);
lean_ctor_set(v_reuseFailAlloc_7719_, 1, v_a_7713_);
v___x_7718_ = v_reuseFailAlloc_7719_;
goto v_reusejp_7717_;
}
v_reusejp_7717_:
{
return v___x_7718_;
}
}
}
}
v___jp_7696_:
{
lean_object* v_leanLibDir_7699_; lean_object* v___x_7700_; lean_object* v___x_7701_; lean_object* v___x_7702_; lean_object* v___x_7703_; lean_object* v___x_7704_; lean_object* v___x_7705_; lean_object* v___x_7706_; lean_object* v___x_7707_; 
v_leanLibDir_7699_ = lean_ctor_get(v_lean_7695_, 3);
v___x_7700_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7685_, v_libs_7697_);
lean_dec_ref(v_libs_7697_);
v___x_7701_ = l_Array_append___redArg(v___x_7700_, v_args_7687_);
v___x_7702_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0);
lean_inc_ref(v_leanLibDir_7699_);
v___x_7703_ = lean_array_push(v___x_7702_, v_leanLibDir_7699_);
v___x_7704_ = l_Array_append___redArg(v___x_7701_, v___x_7703_);
lean_dec_ref(v___x_7703_);
v___x_7705_ = l_Lake_LeanInstall_ccLinkFlags(v_sharedLean_7689_, v_lean_7695_);
v___x_7706_ = l_Array_append___redArg(v___x_7704_, v___x_7705_);
lean_dec_ref(v___x_7705_);
v___x_7707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7707_, 0, v___x_7706_);
lean_ctor_set(v___x_7707_, 1, v___y_7698_);
return v___x_7707_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___boxed(lean_object* v_objs_7721_, lean_object* v_libs_7722_, lean_object* v_args_7723_, lean_object* v_linkDeps_7724_, lean_object* v_sharedLean_7725_, lean_object* v_a_7726_, lean_object* v_a_7727_, lean_object* v_a_7728_){
_start:
{
uint8_t v_linkDeps_boxed_7729_; uint8_t v_sharedLean_boxed_7730_; lean_object* v_res_7731_; 
v_linkDeps_boxed_7729_ = lean_unbox(v_linkDeps_7724_);
v_sharedLean_boxed_7730_ = lean_unbox(v_sharedLean_7725_);
v_res_7731_ = l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg(v_objs_7721_, v_libs_7722_, v_args_7723_, v_linkDeps_boxed_7729_, v_sharedLean_boxed_7730_, v_a_7726_, v_a_7727_);
lean_dec_ref(v_a_7726_);
lean_dec_ref(v_args_7723_);
lean_dec_ref(v_libs_7722_);
lean_dec_ref(v_objs_7721_);
return v_res_7731_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs(lean_object* v_objs_7732_, lean_object* v_libs_7733_, lean_object* v_args_7734_, uint8_t v_linkDeps_7735_, uint8_t v_sharedLean_7736_, lean_object* v_a_7737_, lean_object* v_a_7738_, lean_object* v_a_7739_, lean_object* v_a_7740_, lean_object* v_a_7741_, lean_object* v_a_7742_){
_start:
{
lean_object* v_toContext_7744_; lean_object* v_lakeEnv_7745_; lean_object* v_lean_7746_; lean_object* v_libs_7748_; lean_object* v___y_7749_; 
v_toContext_7744_ = lean_ctor_get(v_a_7741_, 1);
v_lakeEnv_7745_ = lean_ctor_get(v_toContext_7744_, 0);
v_lean_7746_ = lean_ctor_get(v_lakeEnv_7745_, 1);
if (v_linkDeps_7735_ == 0)
{
lean_object* v___x_7761_; 
v___x_7761_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7748_ = v___x_7761_;
v___y_7749_ = v_a_7742_;
goto v___jp_7747_;
}
else
{
lean_object* v___x_7762_; 
v___x_7762_ = l_Lake_mkLinkOrder___redArg(v_libs_7733_, v_a_7742_);
if (lean_obj_tag(v___x_7762_) == 0)
{
lean_object* v_a_7763_; lean_object* v_a_7764_; 
v_a_7763_ = lean_ctor_get(v___x_7762_, 0);
lean_inc(v_a_7763_);
v_a_7764_ = lean_ctor_get(v___x_7762_, 1);
lean_inc(v_a_7764_);
lean_dec_ref_known(v___x_7762_, 2);
v_libs_7748_ = v_a_7763_;
v___y_7749_ = v_a_7764_;
goto v___jp_7747_;
}
else
{
lean_object* v_a_7765_; lean_object* v_a_7766_; lean_object* v___x_7768_; uint8_t v_isShared_7769_; uint8_t v_isSharedCheck_7773_; 
v_a_7765_ = lean_ctor_get(v___x_7762_, 0);
v_a_7766_ = lean_ctor_get(v___x_7762_, 1);
v_isSharedCheck_7773_ = !lean_is_exclusive(v___x_7762_);
if (v_isSharedCheck_7773_ == 0)
{
v___x_7768_ = v___x_7762_;
v_isShared_7769_ = v_isSharedCheck_7773_;
goto v_resetjp_7767_;
}
else
{
lean_inc(v_a_7766_);
lean_inc(v_a_7765_);
lean_dec(v___x_7762_);
v___x_7768_ = lean_box(0);
v_isShared_7769_ = v_isSharedCheck_7773_;
goto v_resetjp_7767_;
}
v_resetjp_7767_:
{
lean_object* v___x_7771_; 
if (v_isShared_7769_ == 0)
{
v___x_7771_ = v___x_7768_;
goto v_reusejp_7770_;
}
else
{
lean_object* v_reuseFailAlloc_7772_; 
v_reuseFailAlloc_7772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7772_, 0, v_a_7765_);
lean_ctor_set(v_reuseFailAlloc_7772_, 1, v_a_7766_);
v___x_7771_ = v_reuseFailAlloc_7772_;
goto v_reusejp_7770_;
}
v_reusejp_7770_:
{
return v___x_7771_;
}
}
}
}
v___jp_7747_:
{
lean_object* v_leanLibDir_7750_; lean_object* v___x_7751_; lean_object* v___x_7752_; lean_object* v___x_7753_; lean_object* v___x_7754_; lean_object* v___x_7755_; lean_object* v___x_7756_; lean_object* v___x_7757_; lean_object* v___x_7758_; lean_object* v___x_7759_; lean_object* v___x_7760_; 
v_leanLibDir_7750_ = lean_ctor_get(v_lean_7746_, 3);
v___x_7751_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_objs_7732_, v_libs_7748_);
lean_dec_ref(v_libs_7748_);
v___x_7752_ = l_Array_append___redArg(v___x_7751_, v_args_7734_);
v___x_7753_ = lean_unsigned_to_nat(2u);
v___x_7754_ = lean_mk_empty_array_with_capacity(v___x_7753_);
lean_dec_ref(v___x_7754_);
v___x_7755_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0);
lean_inc_ref(v_leanLibDir_7750_);
v___x_7756_ = lean_array_push(v___x_7755_, v_leanLibDir_7750_);
v___x_7757_ = l_Array_append___redArg(v___x_7752_, v___x_7756_);
lean_dec_ref(v___x_7756_);
v___x_7758_ = l_Lake_LeanInstall_ccLinkFlags(v_sharedLean_7736_, v_lean_7746_);
v___x_7759_ = l_Array_append___redArg(v___x_7757_, v___x_7758_);
lean_dec_ref(v___x_7758_);
v___x_7760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7760_, 0, v___x_7759_);
lean_ctor_set(v___x_7760_, 1, v___y_7749_);
return v___x_7760_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___boxed(lean_object* v_objs_7774_, lean_object* v_libs_7775_, lean_object* v_args_7776_, lean_object* v_linkDeps_7777_, lean_object* v_sharedLean_7778_, lean_object* v_a_7779_, lean_object* v_a_7780_, lean_object* v_a_7781_, lean_object* v_a_7782_, lean_object* v_a_7783_, lean_object* v_a_7784_, lean_object* v_a_7785_){
_start:
{
uint8_t v_linkDeps_boxed_7786_; uint8_t v_sharedLean_boxed_7787_; lean_object* v_res_7788_; 
v_linkDeps_boxed_7786_ = lean_unbox(v_linkDeps_7777_);
v_sharedLean_boxed_7787_ = lean_unbox(v_sharedLean_7778_);
v_res_7788_ = l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs(v_objs_7774_, v_libs_7775_, v_args_7776_, v_linkDeps_boxed_7786_, v_sharedLean_boxed_7787_, v_a_7779_, v_a_7780_, v_a_7781_, v_a_7782_, v_a_7783_, v_a_7784_);
lean_dec_ref(v_a_7783_);
lean_dec(v_a_7782_);
lean_dec(v_a_7781_);
lean_dec(v_a_7780_);
lean_dec_ref(v_a_7779_);
lean_dec_ref(v_args_7776_);
lean_dec_ref(v_libs_7775_);
lean_dec_ref(v_objs_7774_);
return v_res_7788_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync___lam__0(lean_object* v_linkObjs_7789_, lean_object* v_args_7790_, lean_object* v_libFile_7791_, lean_object* v_linker_7792_, lean_object* v___y_7793_, uint8_t v_linkDeps_7794_, lean_object* v_linkLibs_7795_, lean_object* v___y_7796_, lean_object* v___y_7797_, lean_object* v___y_7798_, lean_object* v___y_7799_, lean_object* v___y_7800_, lean_object* v___y_7801_){
_start:
{
lean_object* v_libs_7804_; lean_object* v___y_7805_; 
if (v_linkDeps_7794_ == 0)
{
lean_object* v___x_7842_; 
v___x_7842_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_7804_ = v___x_7842_;
v___y_7805_ = v___y_7801_;
goto v___jp_7803_;
}
else
{
lean_object* v___x_7843_; 
v___x_7843_ = l_Lake_mkLinkOrder___redArg(v_linkLibs_7795_, v___y_7801_);
if (lean_obj_tag(v___x_7843_) == 0)
{
lean_object* v_a_7844_; lean_object* v_a_7845_; 
v_a_7844_ = lean_ctor_get(v___x_7843_, 0);
lean_inc(v_a_7844_);
v_a_7845_ = lean_ctor_get(v___x_7843_, 1);
lean_inc(v_a_7845_);
lean_dec_ref_known(v___x_7843_, 2);
v_libs_7804_ = v_a_7844_;
v___y_7805_ = v_a_7845_;
goto v___jp_7803_;
}
else
{
lean_object* v_a_7846_; lean_object* v_a_7847_; lean_object* v___x_7849_; uint8_t v_isShared_7850_; uint8_t v_isSharedCheck_7854_; 
lean_dec(v___y_7793_);
lean_dec_ref(v_linker_7792_);
lean_dec_ref(v_libFile_7791_);
v_a_7846_ = lean_ctor_get(v___x_7843_, 0);
v_a_7847_ = lean_ctor_get(v___x_7843_, 1);
v_isSharedCheck_7854_ = !lean_is_exclusive(v___x_7843_);
if (v_isSharedCheck_7854_ == 0)
{
v___x_7849_ = v___x_7843_;
v_isShared_7850_ = v_isSharedCheck_7854_;
goto v_resetjp_7848_;
}
else
{
lean_inc(v_a_7847_);
lean_inc(v_a_7846_);
lean_dec(v___x_7843_);
v___x_7849_ = lean_box(0);
v_isShared_7850_ = v_isSharedCheck_7854_;
goto v_resetjp_7848_;
}
v_resetjp_7848_:
{
lean_object* v___x_7852_; 
if (v_isShared_7850_ == 0)
{
v___x_7852_ = v___x_7849_;
goto v_reusejp_7851_;
}
else
{
lean_object* v_reuseFailAlloc_7853_; 
v_reuseFailAlloc_7853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7853_, 0, v_a_7846_);
lean_ctor_set(v_reuseFailAlloc_7853_, 1, v_a_7847_);
v___x_7852_ = v_reuseFailAlloc_7853_;
goto v_reusejp_7851_;
}
v_reusejp_7851_:
{
return v___x_7852_;
}
}
}
}
v___jp_7803_:
{
lean_object* v_log_7806_; uint8_t v_action_7807_; uint8_t v_wantsRebuild_7808_; lean_object* v_trace_7809_; lean_object* v_buildTime_7810_; lean_object* v___x_7812_; uint8_t v_isShared_7813_; uint8_t v_isSharedCheck_7841_; 
v_log_7806_ = lean_ctor_get(v___y_7805_, 0);
v_action_7807_ = lean_ctor_get_uint8(v___y_7805_, sizeof(void*)*3);
v_wantsRebuild_7808_ = lean_ctor_get_uint8(v___y_7805_, sizeof(void*)*3 + 1);
v_trace_7809_ = lean_ctor_get(v___y_7805_, 1);
v_buildTime_7810_ = lean_ctor_get(v___y_7805_, 2);
v_isSharedCheck_7841_ = !lean_is_exclusive(v___y_7805_);
if (v_isSharedCheck_7841_ == 0)
{
v___x_7812_ = v___y_7805_;
v_isShared_7813_ = v_isSharedCheck_7841_;
goto v_resetjp_7811_;
}
else
{
lean_inc(v_buildTime_7810_);
lean_inc(v_trace_7809_);
lean_inc(v_log_7806_);
lean_dec(v___y_7805_);
v___x_7812_ = lean_box(0);
v_isShared_7813_ = v_isSharedCheck_7841_;
goto v_resetjp_7811_;
}
v_resetjp_7811_:
{
lean_object* v___x_7814_; lean_object* v___x_7815_; lean_object* v___x_7816_; 
v___x_7814_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_linkObjs_7789_, v_libs_7804_);
lean_dec_ref(v_libs_7804_);
v___x_7815_ = l_Array_append___redArg(v___x_7814_, v_args_7790_);
v___x_7816_ = l_Lake_compileSharedLib(v_libFile_7791_, v___x_7815_, v_linker_7792_, v___y_7793_, v_log_7806_);
lean_dec_ref(v___x_7815_);
if (lean_obj_tag(v___x_7816_) == 0)
{
lean_object* v_a_7817_; lean_object* v_a_7818_; lean_object* v___x_7820_; uint8_t v_isShared_7821_; uint8_t v_isSharedCheck_7828_; 
v_a_7817_ = lean_ctor_get(v___x_7816_, 0);
v_a_7818_ = lean_ctor_get(v___x_7816_, 1);
v_isSharedCheck_7828_ = !lean_is_exclusive(v___x_7816_);
if (v_isSharedCheck_7828_ == 0)
{
v___x_7820_ = v___x_7816_;
v_isShared_7821_ = v_isSharedCheck_7828_;
goto v_resetjp_7819_;
}
else
{
lean_inc(v_a_7818_);
lean_inc(v_a_7817_);
lean_dec(v___x_7816_);
v___x_7820_ = lean_box(0);
v_isShared_7821_ = v_isSharedCheck_7828_;
goto v_resetjp_7819_;
}
v_resetjp_7819_:
{
lean_object* v___x_7823_; 
if (v_isShared_7813_ == 0)
{
lean_ctor_set(v___x_7812_, 0, v_a_7818_);
v___x_7823_ = v___x_7812_;
goto v_reusejp_7822_;
}
else
{
lean_object* v_reuseFailAlloc_7827_; 
v_reuseFailAlloc_7827_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7827_, 0, v_a_7818_);
lean_ctor_set(v_reuseFailAlloc_7827_, 1, v_trace_7809_);
lean_ctor_set(v_reuseFailAlloc_7827_, 2, v_buildTime_7810_);
lean_ctor_set_uint8(v_reuseFailAlloc_7827_, sizeof(void*)*3, v_action_7807_);
lean_ctor_set_uint8(v_reuseFailAlloc_7827_, sizeof(void*)*3 + 1, v_wantsRebuild_7808_);
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
v_reuseFailAlloc_7826_ = lean_alloc_ctor(0, 2, 0);
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
else
{
lean_object* v_a_7829_; lean_object* v_a_7830_; lean_object* v___x_7832_; uint8_t v_isShared_7833_; uint8_t v_isSharedCheck_7840_; 
v_a_7829_ = lean_ctor_get(v___x_7816_, 0);
v_a_7830_ = lean_ctor_get(v___x_7816_, 1);
v_isSharedCheck_7840_ = !lean_is_exclusive(v___x_7816_);
if (v_isSharedCheck_7840_ == 0)
{
v___x_7832_ = v___x_7816_;
v_isShared_7833_ = v_isSharedCheck_7840_;
goto v_resetjp_7831_;
}
else
{
lean_inc(v_a_7830_);
lean_inc(v_a_7829_);
lean_dec(v___x_7816_);
v___x_7832_ = lean_box(0);
v_isShared_7833_ = v_isSharedCheck_7840_;
goto v_resetjp_7831_;
}
v_resetjp_7831_:
{
lean_object* v___x_7835_; 
if (v_isShared_7813_ == 0)
{
lean_ctor_set(v___x_7812_, 0, v_a_7830_);
v___x_7835_ = v___x_7812_;
goto v_reusejp_7834_;
}
else
{
lean_object* v_reuseFailAlloc_7839_; 
v_reuseFailAlloc_7839_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7839_, 0, v_a_7830_);
lean_ctor_set(v_reuseFailAlloc_7839_, 1, v_trace_7809_);
lean_ctor_set(v_reuseFailAlloc_7839_, 2, v_buildTime_7810_);
lean_ctor_set_uint8(v_reuseFailAlloc_7839_, sizeof(void*)*3, v_action_7807_);
lean_ctor_set_uint8(v_reuseFailAlloc_7839_, sizeof(void*)*3 + 1, v_wantsRebuild_7808_);
v___x_7835_ = v_reuseFailAlloc_7839_;
goto v_reusejp_7834_;
}
v_reusejp_7834_:
{
lean_object* v___x_7837_; 
if (v_isShared_7833_ == 0)
{
lean_ctor_set(v___x_7832_, 1, v___x_7835_);
v___x_7837_ = v___x_7832_;
goto v_reusejp_7836_;
}
else
{
lean_object* v_reuseFailAlloc_7838_; 
v_reuseFailAlloc_7838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7838_, 0, v_a_7829_);
lean_ctor_set(v_reuseFailAlloc_7838_, 1, v___x_7835_);
v___x_7837_ = v_reuseFailAlloc_7838_;
goto v_reusejp_7836_;
}
v_reusejp_7836_:
{
return v___x_7837_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync___lam__0___boxed(lean_object* v_linkObjs_7855_, lean_object* v_args_7856_, lean_object* v_libFile_7857_, lean_object* v_linker_7858_, lean_object* v___y_7859_, lean_object* v_linkDeps_7860_, lean_object* v_linkLibs_7861_, lean_object* v___y_7862_, lean_object* v___y_7863_, lean_object* v___y_7864_, lean_object* v___y_7865_, lean_object* v___y_7866_, lean_object* v___y_7867_, lean_object* v___y_7868_){
_start:
{
uint8_t v_linkDeps_boxed_7869_; lean_object* v_res_7870_; 
v_linkDeps_boxed_7869_ = lean_unbox(v_linkDeps_7860_);
v_res_7870_ = l_Lake_buildSharedLibSync___lam__0(v_linkObjs_7855_, v_args_7856_, v_libFile_7857_, v_linker_7858_, v___y_7859_, v_linkDeps_boxed_7869_, v_linkLibs_7861_, v___y_7862_, v___y_7863_, v___y_7864_, v___y_7865_, v___y_7866_, v___y_7867_);
lean_dec_ref(v___y_7866_);
lean_dec(v___y_7865_);
lean_dec(v___y_7864_);
lean_dec(v___y_7863_);
lean_dec_ref(v___y_7862_);
lean_dec_ref(v_linkLibs_7861_);
lean_dec_ref(v_args_7856_);
lean_dec_ref(v_linkObjs_7855_);
return v_res_7870_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync(lean_object* v_libName_7872_, lean_object* v_libFile_7873_, lean_object* v_linkObjs_7874_, lean_object* v_linkLibs_7875_, lean_object* v_args_7876_, lean_object* v_linker_7877_, uint8_t v_plugin_7878_, uint8_t v_linkDeps_7879_, lean_object* v_macosxDeploymentTarget_x3f_7880_, lean_object* v_a_7881_, lean_object* v_a_7882_, lean_object* v_a_7883_, lean_object* v_a_7884_, lean_object* v_a_7885_, lean_object* v_a_7886_){
_start:
{
lean_object* v___y_7889_; lean_object* v___y_7890_; lean_object* v___y_7891_; lean_object* v___y_7892_; lean_object* v___y_7893_; lean_object* v___y_7894_; lean_object* v___y_7895_; lean_object* v_log_7921_; uint8_t v_action_7922_; uint8_t v_wantsRebuild_7923_; lean_object* v_trace_7924_; lean_object* v_buildTime_7925_; lean_object* v___x_7927_; uint8_t v_isShared_7928_; uint8_t v_isSharedCheck_7955_; 
v_log_7921_ = lean_ctor_get(v_a_7886_, 0);
v_action_7922_ = lean_ctor_get_uint8(v_a_7886_, sizeof(void*)*3);
v_wantsRebuild_7923_ = lean_ctor_get_uint8(v_a_7886_, sizeof(void*)*3 + 1);
v_trace_7924_ = lean_ctor_get(v_a_7886_, 1);
v_buildTime_7925_ = lean_ctor_get(v_a_7886_, 2);
v_isSharedCheck_7955_ = !lean_is_exclusive(v_a_7886_);
if (v_isSharedCheck_7955_ == 0)
{
v___x_7927_ = v_a_7886_;
v_isShared_7928_ = v_isSharedCheck_7955_;
goto v_resetjp_7926_;
}
else
{
lean_inc(v_buildTime_7925_);
lean_inc(v_trace_7924_);
lean_inc(v_log_7921_);
lean_dec(v_a_7886_);
v___x_7927_ = lean_box(0);
v_isShared_7928_ = v_isSharedCheck_7955_;
goto v_resetjp_7926_;
}
v___jp_7888_:
{
uint8_t v___x_7896_; lean_object* v___x_7897_; uint8_t v___x_7898_; lean_object* v___x_7899_; 
v___x_7896_ = 0;
v___x_7897_ = l_Lake_sharedLibExt;
v___x_7898_ = 1;
v___x_7899_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_7873_, v___y_7889_, v___x_7896_, v___x_7897_, v___x_7898_, v___x_7896_, v___x_7896_, v___y_7890_, v___y_7891_, v___y_7892_, v___y_7893_, v___y_7894_, v___y_7895_);
if (lean_obj_tag(v___x_7899_) == 0)
{
lean_object* v_a_7900_; lean_object* v_a_7901_; lean_object* v___x_7903_; uint8_t v_isShared_7904_; uint8_t v_isSharedCheck_7911_; 
v_a_7900_ = lean_ctor_get(v___x_7899_, 0);
v_a_7901_ = lean_ctor_get(v___x_7899_, 1);
v_isSharedCheck_7911_ = !lean_is_exclusive(v___x_7899_);
if (v_isSharedCheck_7911_ == 0)
{
v___x_7903_ = v___x_7899_;
v_isShared_7904_ = v_isSharedCheck_7911_;
goto v_resetjp_7902_;
}
else
{
lean_inc(v_a_7901_);
lean_inc(v_a_7900_);
lean_dec(v___x_7899_);
v___x_7903_ = lean_box(0);
v_isShared_7904_ = v_isSharedCheck_7911_;
goto v_resetjp_7902_;
}
v_resetjp_7902_:
{
lean_object* v_path_7905_; lean_object* v___x_7906_; lean_object* v___x_7907_; lean_object* v___x_7909_; 
v_path_7905_ = lean_ctor_get(v_a_7900_, 1);
lean_inc_ref(v_path_7905_);
lean_dec(v_a_7900_);
v___x_7906_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v___x_7907_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_7907_, 0, v_path_7905_);
lean_ctor_set(v___x_7907_, 1, v_libName_7872_);
lean_ctor_set(v___x_7907_, 2, v_linkLibs_7875_);
lean_ctor_set(v___x_7907_, 3, v___x_7906_);
lean_ctor_set_uint8(v___x_7907_, sizeof(void*)*4, v_plugin_7878_);
if (v_isShared_7904_ == 0)
{
lean_ctor_set(v___x_7903_, 0, v___x_7907_);
v___x_7909_ = v___x_7903_;
goto v_reusejp_7908_;
}
else
{
lean_object* v_reuseFailAlloc_7910_; 
v_reuseFailAlloc_7910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7910_, 0, v___x_7907_);
lean_ctor_set(v_reuseFailAlloc_7910_, 1, v_a_7901_);
v___x_7909_ = v_reuseFailAlloc_7910_;
goto v_reusejp_7908_;
}
v_reusejp_7908_:
{
return v___x_7909_;
}
}
}
else
{
lean_object* v_a_7912_; lean_object* v_a_7913_; lean_object* v___x_7915_; uint8_t v_isShared_7916_; uint8_t v_isSharedCheck_7920_; 
lean_dec_ref(v_linkLibs_7875_);
lean_dec_ref(v_libName_7872_);
v_a_7912_ = lean_ctor_get(v___x_7899_, 0);
v_a_7913_ = lean_ctor_get(v___x_7899_, 1);
v_isSharedCheck_7920_ = !lean_is_exclusive(v___x_7899_);
if (v_isSharedCheck_7920_ == 0)
{
v___x_7915_ = v___x_7899_;
v_isShared_7916_ = v_isSharedCheck_7920_;
goto v_resetjp_7914_;
}
else
{
lean_inc(v_a_7913_);
lean_inc(v_a_7912_);
lean_dec(v___x_7899_);
v___x_7915_ = lean_box(0);
v_isShared_7916_ = v_isSharedCheck_7920_;
goto v_resetjp_7914_;
}
v_resetjp_7914_:
{
lean_object* v___x_7918_; 
if (v_isShared_7916_ == 0)
{
v___x_7918_ = v___x_7915_;
goto v_reusejp_7917_;
}
else
{
lean_object* v_reuseFailAlloc_7919_; 
v_reuseFailAlloc_7919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7919_, 0, v_a_7912_);
lean_ctor_set(v_reuseFailAlloc_7919_, 1, v_a_7913_);
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
v_resetjp_7926_:
{
lean_object* v___x_7929_; lean_object* v___x_7930_; lean_object* v___x_7932_; 
v___x_7929_ = l_Lake_platformTrace;
v___x_7930_ = l_Lake_BuildTrace_mix(v_trace_7924_, v___x_7929_);
lean_inc(v_buildTime_7925_);
lean_inc_ref(v___x_7930_);
lean_inc_ref(v_log_7921_);
if (v_isShared_7928_ == 0)
{
lean_ctor_set(v___x_7927_, 1, v___x_7930_);
v___x_7932_ = v___x_7927_;
goto v_reusejp_7931_;
}
else
{
lean_object* v_reuseFailAlloc_7954_; 
v_reuseFailAlloc_7954_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_7954_, 0, v_log_7921_);
lean_ctor_set(v_reuseFailAlloc_7954_, 1, v___x_7930_);
lean_ctor_set(v_reuseFailAlloc_7954_, 2, v_buildTime_7925_);
lean_ctor_set_uint8(v_reuseFailAlloc_7954_, sizeof(void*)*3, v_action_7922_);
lean_ctor_set_uint8(v_reuseFailAlloc_7954_, sizeof(void*)*3 + 1, v_wantsRebuild_7923_);
v___x_7932_ = v_reuseFailAlloc_7954_;
goto v_reusejp_7931_;
}
v_reusejp_7931_:
{
lean_object* v___y_7934_; lean_object* v_val_7935_; 
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_7880_) == 0)
{
lean_object* v_toBuildConfig_7948_; lean_object* v_macosxDeploymentTarget_x3f_7949_; lean_object* v___x_7950_; lean_object* v___f_7951_; 
v_toBuildConfig_7948_ = lean_ctor_get(v_a_7885_, 0);
v_macosxDeploymentTarget_x3f_7949_ = lean_ctor_get(v_toBuildConfig_7948_, 3);
v___x_7950_ = lean_box(v_linkDeps_7879_);
lean_inc_ref(v_linkLibs_7875_);
lean_inc(v_macosxDeploymentTarget_x3f_7949_);
lean_inc_ref(v_linker_7877_);
lean_inc_ref(v_libFile_7873_);
lean_inc_ref(v_args_7876_);
lean_inc_ref(v_linkObjs_7874_);
v___f_7951_ = lean_alloc_closure((void*)(l_Lake_buildSharedLibSync___lam__0___boxed), 14, 7);
lean_closure_set(v___f_7951_, 0, v_linkObjs_7874_);
lean_closure_set(v___f_7951_, 1, v_args_7876_);
lean_closure_set(v___f_7951_, 2, v_libFile_7873_);
lean_closure_set(v___f_7951_, 3, v_linker_7877_);
lean_closure_set(v___f_7951_, 4, v_macosxDeploymentTarget_x3f_7949_);
lean_closure_set(v___f_7951_, 5, v___x_7950_);
lean_closure_set(v___f_7951_, 6, v_linkLibs_7875_);
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_7949_) == 1)
{
lean_object* v_val_7952_; 
lean_dec_ref(v___f_7951_);
lean_dec_ref(v___x_7932_);
v_val_7952_ = lean_ctor_get(v_macosxDeploymentTarget_x3f_7949_, 0);
lean_inc(v_val_7952_);
lean_inc_ref(v_macosxDeploymentTarget_x3f_7949_);
v___y_7934_ = v_macosxDeploymentTarget_x3f_7949_;
v_val_7935_ = v_val_7952_;
goto v___jp_7933_;
}
else
{
lean_dec_ref(v___x_7930_);
lean_dec(v_buildTime_7925_);
lean_dec_ref(v_log_7921_);
lean_dec_ref(v_linker_7877_);
lean_dec_ref(v_args_7876_);
lean_dec_ref(v_linkObjs_7874_);
v___y_7889_ = v___f_7951_;
v___y_7890_ = v_a_7881_;
v___y_7891_ = v_a_7882_;
v___y_7892_ = v_a_7883_;
v___y_7893_ = v_a_7884_;
v___y_7894_ = v_a_7885_;
v___y_7895_ = v___x_7932_;
goto v___jp_7888_;
}
}
else
{
lean_object* v_val_7953_; 
lean_dec_ref(v___x_7932_);
v_val_7953_ = lean_ctor_get(v_macosxDeploymentTarget_x3f_7880_, 0);
lean_inc(v_val_7953_);
v___y_7934_ = v_macosxDeploymentTarget_x3f_7880_;
v_val_7935_ = v_val_7953_;
goto v___jp_7933_;
}
v___jp_7933_:
{
lean_object* v___x_7936_; lean_object* v___f_7937_; uint64_t v___x_7938_; uint64_t v___x_7939_; uint64_t v___x_7940_; lean_object* v___x_7941_; lean_object* v___x_7942_; lean_object* v___x_7943_; lean_object* v___x_7944_; lean_object* v___x_7945_; lean_object* v___x_7946_; lean_object* v___x_7947_; 
v___x_7936_ = lean_box(v_linkDeps_7879_);
lean_inc_ref(v_linkLibs_7875_);
lean_inc_ref(v_libFile_7873_);
v___f_7937_ = lean_alloc_closure((void*)(l_Lake_buildSharedLibSync___lam__0___boxed), 14, 7);
lean_closure_set(v___f_7937_, 0, v_linkObjs_7874_);
lean_closure_set(v___f_7937_, 1, v_args_7876_);
lean_closure_set(v___f_7937_, 2, v_libFile_7873_);
lean_closure_set(v___f_7937_, 3, v_linker_7877_);
lean_closure_set(v___f_7937_, 4, v___y_7934_);
lean_closure_set(v___f_7937_, 5, v___x_7936_);
lean_closure_set(v___f_7937_, 6, v_linkLibs_7875_);
v___x_7938_ = l_Lake_Hash_nil;
v___x_7939_ = lean_string_hash(v_val_7935_);
v___x_7940_ = lean_uint64_mix_hash(v___x_7938_, v___x_7939_);
v___x_7941_ = ((lean_object*)(l_Lake_buildSharedLibSync___closed__0));
v___x_7942_ = lean_string_append(v___x_7941_, v_val_7935_);
lean_dec_ref(v_val_7935_);
v___x_7943_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_7944_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_7945_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_7945_, 0, v___x_7942_);
lean_ctor_set(v___x_7945_, 1, v___x_7943_);
lean_ctor_set(v___x_7945_, 2, v___x_7944_);
lean_ctor_set_uint64(v___x_7945_, sizeof(void*)*3, v___x_7940_);
v___x_7946_ = l_Lake_BuildTrace_mix(v___x_7930_, v___x_7945_);
v___x_7947_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_7947_, 0, v_log_7921_);
lean_ctor_set(v___x_7947_, 1, v___x_7946_);
lean_ctor_set(v___x_7947_, 2, v_buildTime_7925_);
lean_ctor_set_uint8(v___x_7947_, sizeof(void*)*3, v_action_7922_);
lean_ctor_set_uint8(v___x_7947_, sizeof(void*)*3 + 1, v_wantsRebuild_7923_);
v___y_7889_ = v___f_7937_;
v___y_7890_ = v_a_7881_;
v___y_7891_ = v_a_7882_;
v___y_7892_ = v_a_7883_;
v___y_7893_ = v_a_7884_;
v___y_7894_ = v_a_7885_;
v___y_7895_ = v___x_7947_;
goto v___jp_7888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLibSync___boxed(lean_object* v_libName_7956_, lean_object* v_libFile_7957_, lean_object* v_linkObjs_7958_, lean_object* v_linkLibs_7959_, lean_object* v_args_7960_, lean_object* v_linker_7961_, lean_object* v_plugin_7962_, lean_object* v_linkDeps_7963_, lean_object* v_macosxDeploymentTarget_x3f_7964_, lean_object* v_a_7965_, lean_object* v_a_7966_, lean_object* v_a_7967_, lean_object* v_a_7968_, lean_object* v_a_7969_, lean_object* v_a_7970_, lean_object* v_a_7971_){
_start:
{
uint8_t v_plugin_boxed_7972_; uint8_t v_linkDeps_boxed_7973_; lean_object* v_res_7974_; 
v_plugin_boxed_7972_ = lean_unbox(v_plugin_7962_);
v_linkDeps_boxed_7973_ = lean_unbox(v_linkDeps_7963_);
v_res_7974_ = l_Lake_buildSharedLibSync(v_libName_7956_, v_libFile_7957_, v_linkObjs_7958_, v_linkLibs_7959_, v_args_7960_, v_linker_7961_, v_plugin_boxed_7972_, v_linkDeps_boxed_7973_, v_macosxDeploymentTarget_x3f_7964_, v_a_7965_, v_a_7966_, v_a_7967_, v_a_7968_, v_a_7969_, v_a_7970_);
lean_dec_ref(v_a_7969_);
lean_dec(v_a_7968_);
lean_dec(v_a_7967_);
lean_dec(v_a_7966_);
return v_res_7974_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0(lean_object* v_extraDepTrace_7975_, lean_object* v_traceArgs_7976_, lean_object* v_weakArgs_7977_, lean_object* v_libName_7978_, lean_object* v_libFile_7979_, lean_object* v_objs_7980_, lean_object* v_linker_7981_, uint8_t v_plugin_7982_, uint8_t v_linkDeps_7983_, lean_object* v_macosxDeploymentTarget_x3f_7984_, lean_object* v_libs_7985_, lean_object* v___y_7986_, lean_object* v___y_7987_, lean_object* v___y_7988_, lean_object* v___y_7989_, lean_object* v___y_7990_, lean_object* v___y_7991_){
_start:
{
lean_object* v___x_7993_; 
lean_inc_ref(v___y_7990_);
lean_inc(v___y_7989_);
lean_inc(v___y_7988_);
lean_inc(v___y_7987_);
lean_inc_ref(v___y_7986_);
v___x_7993_ = lean_apply_7(v_extraDepTrace_7975_, v___y_7986_, v___y_7987_, v___y_7988_, v___y_7989_, v___y_7990_, v___y_7991_, lean_box(0));
if (lean_obj_tag(v___x_7993_) == 0)
{
lean_object* v_a_7994_; lean_object* v_a_7995_; lean_object* v_log_7996_; uint8_t v_action_7997_; uint8_t v_wantsRebuild_7998_; lean_object* v_trace_7999_; lean_object* v_buildTime_8000_; lean_object* v___x_8002_; uint8_t v_isShared_8003_; uint8_t v_isSharedCheck_8029_; 
v_a_7994_ = lean_ctor_get(v___x_7993_, 1);
lean_inc(v_a_7994_);
v_a_7995_ = lean_ctor_get(v___x_7993_, 0);
lean_inc(v_a_7995_);
lean_dec_ref_known(v___x_7993_, 2);
v_log_7996_ = lean_ctor_get(v_a_7994_, 0);
v_action_7997_ = lean_ctor_get_uint8(v_a_7994_, sizeof(void*)*3);
v_wantsRebuild_7998_ = lean_ctor_get_uint8(v_a_7994_, sizeof(void*)*3 + 1);
v_trace_7999_ = lean_ctor_get(v_a_7994_, 1);
v_buildTime_8000_ = lean_ctor_get(v_a_7994_, 2);
v_isSharedCheck_8029_ = !lean_is_exclusive(v_a_7994_);
if (v_isSharedCheck_8029_ == 0)
{
v___x_8002_ = v_a_7994_;
v_isShared_8003_ = v_isSharedCheck_8029_;
goto v_resetjp_8001_;
}
else
{
lean_inc(v_buildTime_8000_);
lean_inc(v_trace_7999_);
lean_inc(v_log_7996_);
lean_dec(v_a_7994_);
v___x_8002_ = lean_box(0);
v_isShared_8003_ = v_isSharedCheck_8029_;
goto v_resetjp_8001_;
}
v_resetjp_8001_:
{
lean_object* v___x_8004_; uint64_t v___y_8006_; uint64_t v___x_8022_; lean_object* v___x_8023_; lean_object* v___x_8024_; uint8_t v___x_8025_; 
v___x_8004_ = l_Lake_BuildTrace_mix(v_trace_7999_, v_a_7995_);
v___x_8022_ = l_Lake_Hash_nil;
v___x_8023_ = lean_unsigned_to_nat(0u);
v___x_8024_ = lean_array_get_size(v_traceArgs_7976_);
v___x_8025_ = lean_nat_dec_lt(v___x_8023_, v___x_8024_);
if (v___x_8025_ == 0)
{
v___y_8006_ = v___x_8022_;
goto v___jp_8005_;
}
else
{
size_t v___x_8026_; size_t v___x_8027_; uint64_t v___x_8028_; 
v___x_8026_ = ((size_t)0ULL);
v___x_8027_ = lean_usize_of_nat(v___x_8024_);
v___x_8028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Internal_buildLeanO_spec__1(v_traceArgs_7976_, v___x_8026_, v___x_8027_, v___x_8022_);
v___y_8006_ = v___x_8028_;
goto v___jp_8005_;
}
v___jp_8005_:
{
lean_object* v___x_8007_; lean_object* v___x_8008_; lean_object* v___x_8009_; lean_object* v___x_8010_; lean_object* v___x_8011_; lean_object* v___x_8012_; lean_object* v___x_8013_; lean_object* v___x_8014_; lean_object* v___x_8015_; lean_object* v___x_8016_; lean_object* v___x_8018_; 
v___x_8007_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_8008_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_7976_);
v___x_8009_ = lean_array_to_list(v_traceArgs_7976_);
v___x_8010_ = l_List_toString___at___00Lake_Internal_buildLeanO_spec__0(v___x_8009_);
lean_dec(v___x_8009_);
v___x_8011_ = lean_string_append(v___x_8008_, v___x_8010_);
lean_dec_ref(v___x_8010_);
v___x_8012_ = lean_string_append(v___x_8007_, v___x_8011_);
lean_dec_ref(v___x_8011_);
v___x_8013_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_8014_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_8015_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_8015_, 0, v___x_8012_);
lean_ctor_set(v___x_8015_, 1, v___x_8013_);
lean_ctor_set(v___x_8015_, 2, v___x_8014_);
lean_ctor_set_uint64(v___x_8015_, sizeof(void*)*3, v___y_8006_);
v___x_8016_ = l_Lake_BuildTrace_mix(v___x_8004_, v___x_8015_);
if (v_isShared_8003_ == 0)
{
lean_ctor_set(v___x_8002_, 1, v___x_8016_);
v___x_8018_ = v___x_8002_;
goto v_reusejp_8017_;
}
else
{
lean_object* v_reuseFailAlloc_8021_; 
v_reuseFailAlloc_8021_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8021_, 0, v_log_7996_);
lean_ctor_set(v_reuseFailAlloc_8021_, 1, v___x_8016_);
lean_ctor_set(v_reuseFailAlloc_8021_, 2, v_buildTime_8000_);
lean_ctor_set_uint8(v_reuseFailAlloc_8021_, sizeof(void*)*3, v_action_7997_);
lean_ctor_set_uint8(v_reuseFailAlloc_8021_, sizeof(void*)*3 + 1, v_wantsRebuild_7998_);
v___x_8018_ = v_reuseFailAlloc_8021_;
goto v_reusejp_8017_;
}
v_reusejp_8017_:
{
lean_object* v___x_8019_; lean_object* v___x_8020_; 
v___x_8019_ = l_Array_append___redArg(v_weakArgs_7977_, v_traceArgs_7976_);
lean_dec_ref(v_traceArgs_7976_);
v___x_8020_ = l_Lake_buildSharedLibSync(v_libName_7978_, v_libFile_7979_, v_objs_7980_, v_libs_7985_, v___x_8019_, v_linker_7981_, v_plugin_7982_, v_linkDeps_7983_, v_macosxDeploymentTarget_x3f_7984_, v___y_7986_, v___y_7987_, v___y_7988_, v___y_7989_, v___y_7990_, v___x_8018_);
return v___x_8020_;
}
}
}
}
else
{
lean_object* v_a_8030_; lean_object* v_a_8031_; lean_object* v___x_8033_; uint8_t v_isShared_8034_; uint8_t v_isSharedCheck_8038_; 
lean_dec_ref(v___y_7986_);
lean_dec_ref(v_libs_7985_);
lean_dec(v_macosxDeploymentTarget_x3f_7984_);
lean_dec_ref(v_linker_7981_);
lean_dec_ref(v_objs_7980_);
lean_dec_ref(v_libFile_7979_);
lean_dec_ref(v_libName_7978_);
lean_dec_ref(v_weakArgs_7977_);
lean_dec_ref(v_traceArgs_7976_);
v_a_8030_ = lean_ctor_get(v___x_7993_, 0);
v_a_8031_ = lean_ctor_get(v___x_7993_, 1);
v_isSharedCheck_8038_ = !lean_is_exclusive(v___x_7993_);
if (v_isSharedCheck_8038_ == 0)
{
v___x_8033_ = v___x_7993_;
v_isShared_8034_ = v_isSharedCheck_8038_;
goto v_resetjp_8032_;
}
else
{
lean_inc(v_a_8031_);
lean_inc(v_a_8030_);
lean_dec(v___x_7993_);
v___x_8033_ = lean_box(0);
v_isShared_8034_ = v_isSharedCheck_8038_;
goto v_resetjp_8032_;
}
v_resetjp_8032_:
{
lean_object* v___x_8036_; 
if (v_isShared_8034_ == 0)
{
v___x_8036_ = v___x_8033_;
goto v_reusejp_8035_;
}
else
{
lean_object* v_reuseFailAlloc_8037_; 
v_reuseFailAlloc_8037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8037_, 0, v_a_8030_);
lean_ctor_set(v_reuseFailAlloc_8037_, 1, v_a_8031_);
v___x_8036_ = v_reuseFailAlloc_8037_;
goto v_reusejp_8035_;
}
v_reusejp_8035_:
{
return v___x_8036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object** _args){
lean_object* v_extraDepTrace_8039_ = _args[0];
lean_object* v_traceArgs_8040_ = _args[1];
lean_object* v_weakArgs_8041_ = _args[2];
lean_object* v_libName_8042_ = _args[3];
lean_object* v_libFile_8043_ = _args[4];
lean_object* v_objs_8044_ = _args[5];
lean_object* v_linker_8045_ = _args[6];
lean_object* v_plugin_8046_ = _args[7];
lean_object* v_linkDeps_8047_ = _args[8];
lean_object* v_macosxDeploymentTarget_x3f_8048_ = _args[9];
lean_object* v_libs_8049_ = _args[10];
lean_object* v___y_8050_ = _args[11];
lean_object* v___y_8051_ = _args[12];
lean_object* v___y_8052_ = _args[13];
lean_object* v___y_8053_ = _args[14];
lean_object* v___y_8054_ = _args[15];
lean_object* v___y_8055_ = _args[16];
lean_object* v___y_8056_ = _args[17];
_start:
{
uint8_t v_plugin_boxed_8057_; uint8_t v_linkDeps_boxed_8058_; lean_object* v_res_8059_; 
v_plugin_boxed_8057_ = lean_unbox(v_plugin_8046_);
v_linkDeps_boxed_8058_ = lean_unbox(v_linkDeps_8047_);
v_res_8059_ = l_Lake_buildSharedLib___lam__0(v_extraDepTrace_8039_, v_traceArgs_8040_, v_weakArgs_8041_, v_libName_8042_, v_libFile_8043_, v_objs_8044_, v_linker_8045_, v_plugin_boxed_8057_, v_linkDeps_boxed_8058_, v_macosxDeploymentTarget_x3f_8048_, v_libs_8049_, v___y_8050_, v___y_8051_, v___y_8052_, v___y_8053_, v___y_8054_, v___y_8055_);
lean_dec_ref(v___y_8054_);
lean_dec(v___y_8053_);
lean_dec(v___y_8052_);
lean_dec(v___y_8051_);
return v_res_8059_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1(lean_object* v_extraDepTrace_8061_, lean_object* v_traceArgs_8062_, lean_object* v_weakArgs_8063_, lean_object* v_libName_8064_, lean_object* v_libFile_8065_, lean_object* v_linker_8066_, uint8_t v_plugin_8067_, uint8_t v_linkDeps_8068_, lean_object* v_macosxDeploymentTarget_x3f_8069_, lean_object* v_linkLibs_8070_, lean_object* v___x_8071_, lean_object* v_objs_8072_, lean_object* v___y_8073_, lean_object* v___y_8074_, lean_object* v___y_8075_, lean_object* v___y_8076_, lean_object* v___y_8077_, lean_object* v___y_8078_){
_start:
{
lean_object* v_trace_8080_; lean_object* v___x_8081_; lean_object* v___x_8082_; lean_object* v___f_8083_; lean_object* v___x_8084_; lean_object* v___x_8085_; lean_object* v___x_8086_; uint8_t v___x_8087_; lean_object* v___x_8088_; lean_object* v___x_8089_; 
v_trace_8080_ = lean_ctor_get(v___y_8078_, 1);
v___x_8081_ = lean_box(v_plugin_8067_);
v___x_8082_ = lean_box(v_linkDeps_8068_);
v___f_8083_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__0___boxed), 18, 10);
lean_closure_set(v___f_8083_, 0, v_extraDepTrace_8061_);
lean_closure_set(v___f_8083_, 1, v_traceArgs_8062_);
lean_closure_set(v___f_8083_, 2, v_weakArgs_8063_);
lean_closure_set(v___f_8083_, 3, v_libName_8064_);
lean_closure_set(v___f_8083_, 4, v_libFile_8065_);
lean_closure_set(v___f_8083_, 5, v_objs_8072_);
lean_closure_set(v___f_8083_, 6, v_linker_8066_);
lean_closure_set(v___f_8083_, 7, v___x_8081_);
lean_closure_set(v___f_8083_, 8, v___x_8082_);
lean_closure_set(v___f_8083_, 9, v_macosxDeploymentTarget_x3f_8069_);
v___x_8084_ = ((lean_object*)(l_Lake_buildSharedLib___lam__1___closed__0));
v___x_8085_ = l_Lake_Job_collectArray___redArg(v_linkLibs_8070_, v___x_8084_);
v___x_8086_ = lean_unsigned_to_nat(0u);
v___x_8087_ = 0;
v___x_8088_ = l_Lake_Job_mapM___redArg(v___x_8071_, v___x_8085_, v___f_8083_, v___x_8086_, v___x_8087_, v___y_8073_, v___y_8074_, v___y_8075_, v___y_8076_, v___y_8077_, v_trace_8080_);
v___x_8089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8089_, 0, v___x_8088_);
lean_ctor_set(v___x_8089_, 1, v___y_8078_);
return v___x_8089_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1___boxed(lean_object** _args){
lean_object* v_extraDepTrace_8090_ = _args[0];
lean_object* v_traceArgs_8091_ = _args[1];
lean_object* v_weakArgs_8092_ = _args[2];
lean_object* v_libName_8093_ = _args[3];
lean_object* v_libFile_8094_ = _args[4];
lean_object* v_linker_8095_ = _args[5];
lean_object* v_plugin_8096_ = _args[6];
lean_object* v_linkDeps_8097_ = _args[7];
lean_object* v_macosxDeploymentTarget_x3f_8098_ = _args[8];
lean_object* v_linkLibs_8099_ = _args[9];
lean_object* v___x_8100_ = _args[10];
lean_object* v_objs_8101_ = _args[11];
lean_object* v___y_8102_ = _args[12];
lean_object* v___y_8103_ = _args[13];
lean_object* v___y_8104_ = _args[14];
lean_object* v___y_8105_ = _args[15];
lean_object* v___y_8106_ = _args[16];
lean_object* v___y_8107_ = _args[17];
lean_object* v___y_8108_ = _args[18];
_start:
{
uint8_t v_plugin_boxed_8109_; uint8_t v_linkDeps_boxed_8110_; lean_object* v_res_8111_; 
v_plugin_boxed_8109_ = lean_unbox(v_plugin_8096_);
v_linkDeps_boxed_8110_ = lean_unbox(v_linkDeps_8097_);
v_res_8111_ = l_Lake_buildSharedLib___lam__1(v_extraDepTrace_8090_, v_traceArgs_8091_, v_weakArgs_8092_, v_libName_8093_, v_libFile_8094_, v_linker_8095_, v_plugin_boxed_8109_, v_linkDeps_boxed_8110_, v_macosxDeploymentTarget_x3f_8098_, v_linkLibs_8099_, v___x_8100_, v_objs_8101_, v___y_8102_, v___y_8103_, v___y_8104_, v___y_8105_, v___y_8106_, v___y_8107_);
lean_dec_ref(v___y_8106_);
lean_dec(v___y_8105_);
lean_dec(v___y_8104_);
lean_dec(v___y_8103_);
lean_dec_ref(v_linkLibs_8099_);
return v_res_8111_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib(lean_object* v_libName_8113_, lean_object* v_libFile_8114_, lean_object* v_linkObjs_8115_, lean_object* v_linkLibs_8116_, lean_object* v_weakArgs_8117_, lean_object* v_traceArgs_8118_, lean_object* v_linker_8119_, lean_object* v_extraDepTrace_8120_, uint8_t v_plugin_8121_, uint8_t v_linkDeps_8122_, lean_object* v_macosxDeploymentTarget_x3f_8123_, lean_object* v_a_8124_, lean_object* v_a_8125_, lean_object* v_a_8126_, lean_object* v_a_8127_, lean_object* v_a_8128_, lean_object* v_a_8129_){
_start:
{
lean_object* v___x_8131_; lean_object* v___x_8132_; lean_object* v___x_8133_; lean_object* v___f_8134_; lean_object* v___x_8135_; lean_object* v___x_8136_; lean_object* v___x_8137_; uint8_t v___x_8138_; lean_object* v___x_8139_; 
v___x_8131_ = l_Lake_instDataKindDynlib;
v___x_8132_ = lean_box(v_plugin_8121_);
v___x_8133_ = lean_box(v_linkDeps_8122_);
v___f_8134_ = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__1___boxed), 19, 11);
lean_closure_set(v___f_8134_, 0, v_extraDepTrace_8120_);
lean_closure_set(v___f_8134_, 1, v_traceArgs_8118_);
lean_closure_set(v___f_8134_, 2, v_weakArgs_8117_);
lean_closure_set(v___f_8134_, 3, v_libName_8113_);
lean_closure_set(v___f_8134_, 4, v_libFile_8114_);
lean_closure_set(v___f_8134_, 5, v_linker_8119_);
lean_closure_set(v___f_8134_, 6, v___x_8132_);
lean_closure_set(v___f_8134_, 7, v___x_8133_);
lean_closure_set(v___f_8134_, 8, v_macosxDeploymentTarget_x3f_8123_);
lean_closure_set(v___f_8134_, 9, v_linkLibs_8116_);
lean_closure_set(v___f_8134_, 10, v___x_8131_);
v___x_8135_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8136_ = l_Lake_Job_collectArray___redArg(v_linkObjs_8115_, v___x_8135_);
v___x_8137_ = lean_unsigned_to_nat(0u);
v___x_8138_ = 1;
v___x_8139_ = l_Lake_Job_bindM___redArg(v___x_8131_, v___x_8136_, v___f_8134_, v___x_8137_, v___x_8138_, v_a_8124_, v_a_8125_, v_a_8126_, v_a_8127_, v_a_8128_, v_a_8129_);
return v___x_8139_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___boxed(lean_object** _args){
lean_object* v_libName_8140_ = _args[0];
lean_object* v_libFile_8141_ = _args[1];
lean_object* v_linkObjs_8142_ = _args[2];
lean_object* v_linkLibs_8143_ = _args[3];
lean_object* v_weakArgs_8144_ = _args[4];
lean_object* v_traceArgs_8145_ = _args[5];
lean_object* v_linker_8146_ = _args[6];
lean_object* v_extraDepTrace_8147_ = _args[7];
lean_object* v_plugin_8148_ = _args[8];
lean_object* v_linkDeps_8149_ = _args[9];
lean_object* v_macosxDeploymentTarget_x3f_8150_ = _args[10];
lean_object* v_a_8151_ = _args[11];
lean_object* v_a_8152_ = _args[12];
lean_object* v_a_8153_ = _args[13];
lean_object* v_a_8154_ = _args[14];
lean_object* v_a_8155_ = _args[15];
lean_object* v_a_8156_ = _args[16];
lean_object* v_a_8157_ = _args[17];
_start:
{
uint8_t v_plugin_boxed_8158_; uint8_t v_linkDeps_boxed_8159_; lean_object* v_res_8160_; 
v_plugin_boxed_8158_ = lean_unbox(v_plugin_8148_);
v_linkDeps_boxed_8159_ = lean_unbox(v_linkDeps_8149_);
v_res_8160_ = l_Lake_buildSharedLib(v_libName_8140_, v_libFile_8141_, v_linkObjs_8142_, v_linkLibs_8143_, v_weakArgs_8144_, v_traceArgs_8145_, v_linker_8146_, v_extraDepTrace_8147_, v_plugin_boxed_8158_, v_linkDeps_boxed_8159_, v_macosxDeploymentTarget_x3f_8150_, v_a_8151_, v_a_8152_, v_a_8153_, v_a_8154_, v_a_8155_, v_a_8156_);
lean_dec_ref(v_a_8156_);
lean_dec_ref(v_a_8155_);
lean_dec(v_a_8154_);
lean_dec(v_a_8153_);
lean_dec(v_a_8152_);
lean_dec_ref(v_linkObjs_8142_);
return v_res_8160_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync___lam__0(lean_object* v_linkObjs_8161_, lean_object* v_args_8162_, uint8_t v___x_8163_, lean_object* v_libFile_8164_, lean_object* v_macosxDeploymentTarget_x3f_8165_, uint8_t v_linkDeps_8166_, lean_object* v_linkLibs_8167_, lean_object* v___y_8168_, lean_object* v___y_8169_, lean_object* v___y_8170_, lean_object* v___y_8171_, lean_object* v___y_8172_, lean_object* v___y_8173_){
_start:
{
lean_object* v_toContext_8175_; lean_object* v_lakeEnv_8176_; lean_object* v_lean_8177_; lean_object* v_libs_8179_; lean_object* v___y_8180_; 
v_toContext_8175_ = lean_ctor_get(v___y_8172_, 1);
v_lakeEnv_8176_ = lean_ctor_get(v_toContext_8175_, 0);
v_lean_8177_ = lean_ctor_get(v_lakeEnv_8176_, 1);
if (v_linkDeps_8166_ == 0)
{
lean_object* v___x_8226_; 
v___x_8226_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v_libs_8179_ = v___x_8226_;
v___y_8180_ = v___y_8173_;
goto v___jp_8178_;
}
else
{
lean_object* v___x_8227_; 
v___x_8227_ = l_Lake_mkLinkOrder___redArg(v_linkLibs_8167_, v___y_8173_);
if (lean_obj_tag(v___x_8227_) == 0)
{
lean_object* v_a_8228_; lean_object* v_a_8229_; 
v_a_8228_ = lean_ctor_get(v___x_8227_, 0);
lean_inc(v_a_8228_);
v_a_8229_ = lean_ctor_get(v___x_8227_, 1);
lean_inc(v_a_8229_);
lean_dec_ref_known(v___x_8227_, 2);
v_libs_8179_ = v_a_8228_;
v___y_8180_ = v_a_8229_;
goto v___jp_8178_;
}
else
{
lean_object* v_a_8230_; lean_object* v_a_8231_; lean_object* v___x_8233_; uint8_t v_isShared_8234_; uint8_t v_isSharedCheck_8238_; 
lean_dec(v_macosxDeploymentTarget_x3f_8165_);
lean_dec_ref(v_libFile_8164_);
v_a_8230_ = lean_ctor_get(v___x_8227_, 0);
v_a_8231_ = lean_ctor_get(v___x_8227_, 1);
v_isSharedCheck_8238_ = !lean_is_exclusive(v___x_8227_);
if (v_isSharedCheck_8238_ == 0)
{
v___x_8233_ = v___x_8227_;
v_isShared_8234_ = v_isSharedCheck_8238_;
goto v_resetjp_8232_;
}
else
{
lean_inc(v_a_8231_);
lean_inc(v_a_8230_);
lean_dec(v___x_8227_);
v___x_8233_ = lean_box(0);
v_isShared_8234_ = v_isSharedCheck_8238_;
goto v_resetjp_8232_;
}
v_resetjp_8232_:
{
lean_object* v___x_8236_; 
if (v_isShared_8234_ == 0)
{
v___x_8236_ = v___x_8233_;
goto v_reusejp_8235_;
}
else
{
lean_object* v_reuseFailAlloc_8237_; 
v_reuseFailAlloc_8237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8237_, 0, v_a_8230_);
lean_ctor_set(v_reuseFailAlloc_8237_, 1, v_a_8231_);
v___x_8236_ = v_reuseFailAlloc_8237_;
goto v_reusejp_8235_;
}
v_reusejp_8235_:
{
return v___x_8236_;
}
}
}
}
v___jp_8178_:
{
lean_object* v_leanLibDir_8181_; lean_object* v_cc_8182_; lean_object* v_log_8183_; uint8_t v_action_8184_; uint8_t v_wantsRebuild_8185_; lean_object* v_trace_8186_; lean_object* v_buildTime_8187_; lean_object* v___x_8189_; uint8_t v_isShared_8190_; uint8_t v_isSharedCheck_8225_; 
v_leanLibDir_8181_ = lean_ctor_get(v_lean_8177_, 3);
v_cc_8182_ = lean_ctor_get(v_lean_8177_, 14);
v_log_8183_ = lean_ctor_get(v___y_8180_, 0);
v_action_8184_ = lean_ctor_get_uint8(v___y_8180_, sizeof(void*)*3);
v_wantsRebuild_8185_ = lean_ctor_get_uint8(v___y_8180_, sizeof(void*)*3 + 1);
v_trace_8186_ = lean_ctor_get(v___y_8180_, 1);
v_buildTime_8187_ = lean_ctor_get(v___y_8180_, 2);
v_isSharedCheck_8225_ = !lean_is_exclusive(v___y_8180_);
if (v_isSharedCheck_8225_ == 0)
{
v___x_8189_ = v___y_8180_;
v_isShared_8190_ = v_isSharedCheck_8225_;
goto v_resetjp_8188_;
}
else
{
lean_inc(v_buildTime_8187_);
lean_inc(v_trace_8186_);
lean_inc(v_log_8183_);
lean_dec(v___y_8180_);
v___x_8189_ = lean_box(0);
v_isShared_8190_ = v_isSharedCheck_8225_;
goto v_resetjp_8188_;
}
v_resetjp_8188_:
{
lean_object* v___x_8191_; lean_object* v___x_8192_; lean_object* v___x_8193_; lean_object* v___x_8194_; lean_object* v___x_8195_; lean_object* v___x_8196_; lean_object* v___x_8197_; lean_object* v___x_8198_; lean_object* v___x_8199_; lean_object* v___x_8200_; 
v___x_8191_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_linkObjs_8161_, v_libs_8179_);
lean_dec_ref(v_libs_8179_);
v___x_8192_ = l_Array_append___redArg(v___x_8191_, v_args_8162_);
v___x_8193_ = lean_unsigned_to_nat(2u);
v___x_8194_ = lean_mk_empty_array_with_capacity(v___x_8193_);
lean_dec_ref(v___x_8194_);
v___x_8195_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0);
lean_inc_ref(v_leanLibDir_8181_);
v___x_8196_ = lean_array_push(v___x_8195_, v_leanLibDir_8181_);
v___x_8197_ = l_Array_append___redArg(v___x_8192_, v___x_8196_);
lean_dec_ref(v___x_8196_);
v___x_8198_ = l_Lake_LeanInstall_ccLinkFlags(v___x_8163_, v_lean_8177_);
v___x_8199_ = l_Array_append___redArg(v___x_8197_, v___x_8198_);
lean_dec_ref(v___x_8198_);
lean_inc_ref(v_cc_8182_);
v___x_8200_ = l_Lake_compileSharedLib(v_libFile_8164_, v___x_8199_, v_cc_8182_, v_macosxDeploymentTarget_x3f_8165_, v_log_8183_);
lean_dec_ref(v___x_8199_);
if (lean_obj_tag(v___x_8200_) == 0)
{
lean_object* v_a_8201_; lean_object* v_a_8202_; lean_object* v___x_8204_; uint8_t v_isShared_8205_; uint8_t v_isSharedCheck_8212_; 
v_a_8201_ = lean_ctor_get(v___x_8200_, 0);
v_a_8202_ = lean_ctor_get(v___x_8200_, 1);
v_isSharedCheck_8212_ = !lean_is_exclusive(v___x_8200_);
if (v_isSharedCheck_8212_ == 0)
{
v___x_8204_ = v___x_8200_;
v_isShared_8205_ = v_isSharedCheck_8212_;
goto v_resetjp_8203_;
}
else
{
lean_inc(v_a_8202_);
lean_inc(v_a_8201_);
lean_dec(v___x_8200_);
v___x_8204_ = lean_box(0);
v_isShared_8205_ = v_isSharedCheck_8212_;
goto v_resetjp_8203_;
}
v_resetjp_8203_:
{
lean_object* v___x_8207_; 
if (v_isShared_8190_ == 0)
{
lean_ctor_set(v___x_8189_, 0, v_a_8202_);
v___x_8207_ = v___x_8189_;
goto v_reusejp_8206_;
}
else
{
lean_object* v_reuseFailAlloc_8211_; 
v_reuseFailAlloc_8211_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8211_, 0, v_a_8202_);
lean_ctor_set(v_reuseFailAlloc_8211_, 1, v_trace_8186_);
lean_ctor_set(v_reuseFailAlloc_8211_, 2, v_buildTime_8187_);
lean_ctor_set_uint8(v_reuseFailAlloc_8211_, sizeof(void*)*3, v_action_8184_);
lean_ctor_set_uint8(v_reuseFailAlloc_8211_, sizeof(void*)*3 + 1, v_wantsRebuild_8185_);
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
v_reuseFailAlloc_8210_ = lean_alloc_ctor(0, 2, 0);
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
else
{
lean_object* v_a_8213_; lean_object* v_a_8214_; lean_object* v___x_8216_; uint8_t v_isShared_8217_; uint8_t v_isSharedCheck_8224_; 
v_a_8213_ = lean_ctor_get(v___x_8200_, 0);
v_a_8214_ = lean_ctor_get(v___x_8200_, 1);
v_isSharedCheck_8224_ = !lean_is_exclusive(v___x_8200_);
if (v_isSharedCheck_8224_ == 0)
{
v___x_8216_ = v___x_8200_;
v_isShared_8217_ = v_isSharedCheck_8224_;
goto v_resetjp_8215_;
}
else
{
lean_inc(v_a_8214_);
lean_inc(v_a_8213_);
lean_dec(v___x_8200_);
v___x_8216_ = lean_box(0);
v_isShared_8217_ = v_isSharedCheck_8224_;
goto v_resetjp_8215_;
}
v_resetjp_8215_:
{
lean_object* v___x_8219_; 
if (v_isShared_8190_ == 0)
{
lean_ctor_set(v___x_8189_, 0, v_a_8214_);
v___x_8219_ = v___x_8189_;
goto v_reusejp_8218_;
}
else
{
lean_object* v_reuseFailAlloc_8223_; 
v_reuseFailAlloc_8223_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8223_, 0, v_a_8214_);
lean_ctor_set(v_reuseFailAlloc_8223_, 1, v_trace_8186_);
lean_ctor_set(v_reuseFailAlloc_8223_, 2, v_buildTime_8187_);
lean_ctor_set_uint8(v_reuseFailAlloc_8223_, sizeof(void*)*3, v_action_8184_);
lean_ctor_set_uint8(v_reuseFailAlloc_8223_, sizeof(void*)*3 + 1, v_wantsRebuild_8185_);
v___x_8219_ = v_reuseFailAlloc_8223_;
goto v_reusejp_8218_;
}
v_reusejp_8218_:
{
lean_object* v___x_8221_; 
if (v_isShared_8217_ == 0)
{
lean_ctor_set(v___x_8216_, 1, v___x_8219_);
v___x_8221_ = v___x_8216_;
goto v_reusejp_8220_;
}
else
{
lean_object* v_reuseFailAlloc_8222_; 
v_reuseFailAlloc_8222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8222_, 0, v_a_8213_);
lean_ctor_set(v_reuseFailAlloc_8222_, 1, v___x_8219_);
v___x_8221_ = v_reuseFailAlloc_8222_;
goto v_reusejp_8220_;
}
v_reusejp_8220_:
{
return v___x_8221_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync___lam__0___boxed(lean_object* v_linkObjs_8239_, lean_object* v_args_8240_, lean_object* v___x_8241_, lean_object* v_libFile_8242_, lean_object* v_macosxDeploymentTarget_x3f_8243_, lean_object* v_linkDeps_8244_, lean_object* v_linkLibs_8245_, lean_object* v___y_8246_, lean_object* v___y_8247_, lean_object* v___y_8248_, lean_object* v___y_8249_, lean_object* v___y_8250_, lean_object* v___y_8251_, lean_object* v___y_8252_){
_start:
{
uint8_t v___x_34592__boxed_8253_; uint8_t v_linkDeps_boxed_8254_; lean_object* v_res_8255_; 
v___x_34592__boxed_8253_ = lean_unbox(v___x_8241_);
v_linkDeps_boxed_8254_ = lean_unbox(v_linkDeps_8244_);
v_res_8255_ = l_Lake_buildLeanSharedLibSync___lam__0(v_linkObjs_8239_, v_args_8240_, v___x_34592__boxed_8253_, v_libFile_8242_, v_macosxDeploymentTarget_x3f_8243_, v_linkDeps_boxed_8254_, v_linkLibs_8245_, v___y_8246_, v___y_8247_, v___y_8248_, v___y_8249_, v___y_8250_, v___y_8251_);
lean_dec_ref(v___y_8250_);
lean_dec(v___y_8249_);
lean_dec(v___y_8248_);
lean_dec(v___y_8247_);
lean_dec_ref(v___y_8246_);
lean_dec_ref(v_linkLibs_8245_);
lean_dec_ref(v_args_8240_);
lean_dec_ref(v_linkObjs_8239_);
return v_res_8255_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync(lean_object* v_libName_8256_, lean_object* v_libFile_8257_, lean_object* v_linkObjs_8258_, lean_object* v_linkLibs_8259_, lean_object* v_args_8260_, uint8_t v_plugin_8261_, uint8_t v_linkDeps_8262_, lean_object* v_macosxDeploymentTarget_x3f_8263_, lean_object* v_a_8264_, lean_object* v_a_8265_, lean_object* v_a_8266_, lean_object* v_a_8267_, lean_object* v_a_8268_, lean_object* v_a_8269_){
_start:
{
lean_object* v_log_8271_; uint8_t v_action_8272_; uint8_t v_wantsRebuild_8273_; lean_object* v_trace_8274_; lean_object* v_buildTime_8275_; lean_object* v___x_8277_; uint8_t v_isShared_8278_; uint8_t v_isSharedCheck_8314_; 
v_log_8271_ = lean_ctor_get(v_a_8269_, 0);
v_action_8272_ = lean_ctor_get_uint8(v_a_8269_, sizeof(void*)*3);
v_wantsRebuild_8273_ = lean_ctor_get_uint8(v_a_8269_, sizeof(void*)*3 + 1);
v_trace_8274_ = lean_ctor_get(v_a_8269_, 1);
v_buildTime_8275_ = lean_ctor_get(v_a_8269_, 2);
v_isSharedCheck_8314_ = !lean_is_exclusive(v_a_8269_);
if (v_isSharedCheck_8314_ == 0)
{
v___x_8277_ = v_a_8269_;
v_isShared_8278_ = v_isSharedCheck_8314_;
goto v_resetjp_8276_;
}
else
{
lean_inc(v_buildTime_8275_);
lean_inc(v_trace_8274_);
lean_inc(v_log_8271_);
lean_dec(v_a_8269_);
v___x_8277_ = lean_box(0);
v_isShared_8278_ = v_isSharedCheck_8314_;
goto v_resetjp_8276_;
}
v_resetjp_8276_:
{
lean_object* v_leanTrace_8279_; lean_object* v___x_8280_; lean_object* v___x_8281_; lean_object* v___x_8282_; lean_object* v___x_8284_; 
v_leanTrace_8279_ = lean_ctor_get(v_a_8268_, 2);
lean_inc_ref(v_leanTrace_8279_);
v___x_8280_ = l_Lake_BuildTrace_mix(v_trace_8274_, v_leanTrace_8279_);
v___x_8281_ = l_Lake_platformTrace;
v___x_8282_ = l_Lake_BuildTrace_mix(v___x_8280_, v___x_8281_);
if (v_isShared_8278_ == 0)
{
lean_ctor_set(v___x_8277_, 1, v___x_8282_);
v___x_8284_ = v___x_8277_;
goto v_reusejp_8283_;
}
else
{
lean_object* v_reuseFailAlloc_8313_; 
v_reuseFailAlloc_8313_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8313_, 0, v_log_8271_);
lean_ctor_set(v_reuseFailAlloc_8313_, 1, v___x_8282_);
lean_ctor_set(v_reuseFailAlloc_8313_, 2, v_buildTime_8275_);
lean_ctor_set_uint8(v_reuseFailAlloc_8313_, sizeof(void*)*3, v_action_8272_);
lean_ctor_set_uint8(v_reuseFailAlloc_8313_, sizeof(void*)*3 + 1, v_wantsRebuild_8273_);
v___x_8284_ = v_reuseFailAlloc_8313_;
goto v_reusejp_8283_;
}
v_reusejp_8283_:
{
uint8_t v___x_8285_; lean_object* v___x_8286_; lean_object* v___x_8287_; lean_object* v___f_8288_; uint8_t v___x_8289_; lean_object* v___x_8290_; lean_object* v___x_8291_; 
v___x_8285_ = 1;
v___x_8286_ = lean_box(v___x_8285_);
v___x_8287_ = lean_box(v_linkDeps_8262_);
lean_inc_ref(v_linkLibs_8259_);
lean_inc_ref(v_libFile_8257_);
v___f_8288_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibSync___lam__0___boxed), 14, 7);
lean_closure_set(v___f_8288_, 0, v_linkObjs_8258_);
lean_closure_set(v___f_8288_, 1, v_args_8260_);
lean_closure_set(v___f_8288_, 2, v___x_8286_);
lean_closure_set(v___f_8288_, 3, v_libFile_8257_);
lean_closure_set(v___f_8288_, 4, v_macosxDeploymentTarget_x3f_8263_);
lean_closure_set(v___f_8288_, 5, v___x_8287_);
lean_closure_set(v___f_8288_, 6, v_linkLibs_8259_);
v___x_8289_ = 0;
v___x_8290_ = l_Lake_sharedLibExt;
v___x_8291_ = l_Lake_buildArtifactUnlessUpToDate(v_libFile_8257_, v___f_8288_, v___x_8289_, v___x_8290_, v___x_8285_, v___x_8289_, v___x_8289_, v_a_8264_, v_a_8265_, v_a_8266_, v_a_8267_, v_a_8268_, v___x_8284_);
if (lean_obj_tag(v___x_8291_) == 0)
{
lean_object* v_a_8292_; lean_object* v_a_8293_; lean_object* v___x_8295_; uint8_t v_isShared_8296_; uint8_t v_isSharedCheck_8303_; 
v_a_8292_ = lean_ctor_get(v___x_8291_, 0);
v_a_8293_ = lean_ctor_get(v___x_8291_, 1);
v_isSharedCheck_8303_ = !lean_is_exclusive(v___x_8291_);
if (v_isSharedCheck_8303_ == 0)
{
v___x_8295_ = v___x_8291_;
v_isShared_8296_ = v_isSharedCheck_8303_;
goto v_resetjp_8294_;
}
else
{
lean_inc(v_a_8293_);
lean_inc(v_a_8292_);
lean_dec(v___x_8291_);
v___x_8295_ = lean_box(0);
v_isShared_8296_ = v_isSharedCheck_8303_;
goto v_resetjp_8294_;
}
v_resetjp_8294_:
{
lean_object* v_path_8297_; lean_object* v___x_8298_; lean_object* v___x_8299_; lean_object* v___x_8301_; 
v_path_8297_ = lean_ctor_get(v_a_8292_, 1);
lean_inc_ref(v_path_8297_);
lean_dec(v_a_8292_);
v___x_8298_ = ((lean_object*)(l_Lake_mkLinkOrder___redArg___closed__1));
v___x_8299_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_8299_, 0, v_path_8297_);
lean_ctor_set(v___x_8299_, 1, v_libName_8256_);
lean_ctor_set(v___x_8299_, 2, v_linkLibs_8259_);
lean_ctor_set(v___x_8299_, 3, v___x_8298_);
lean_ctor_set_uint8(v___x_8299_, sizeof(void*)*4, v_plugin_8261_);
if (v_isShared_8296_ == 0)
{
lean_ctor_set(v___x_8295_, 0, v___x_8299_);
v___x_8301_ = v___x_8295_;
goto v_reusejp_8300_;
}
else
{
lean_object* v_reuseFailAlloc_8302_; 
v_reuseFailAlloc_8302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8302_, 0, v___x_8299_);
lean_ctor_set(v_reuseFailAlloc_8302_, 1, v_a_8293_);
v___x_8301_ = v_reuseFailAlloc_8302_;
goto v_reusejp_8300_;
}
v_reusejp_8300_:
{
return v___x_8301_;
}
}
}
else
{
lean_object* v_a_8304_; lean_object* v_a_8305_; lean_object* v___x_8307_; uint8_t v_isShared_8308_; uint8_t v_isSharedCheck_8312_; 
lean_dec_ref(v_linkLibs_8259_);
lean_dec_ref(v_libName_8256_);
v_a_8304_ = lean_ctor_get(v___x_8291_, 0);
v_a_8305_ = lean_ctor_get(v___x_8291_, 1);
v_isSharedCheck_8312_ = !lean_is_exclusive(v___x_8291_);
if (v_isSharedCheck_8312_ == 0)
{
v___x_8307_ = v___x_8291_;
v_isShared_8308_ = v_isSharedCheck_8312_;
goto v_resetjp_8306_;
}
else
{
lean_inc(v_a_8305_);
lean_inc(v_a_8304_);
lean_dec(v___x_8291_);
v___x_8307_ = lean_box(0);
v_isShared_8308_ = v_isSharedCheck_8312_;
goto v_resetjp_8306_;
}
v_resetjp_8306_:
{
lean_object* v___x_8310_; 
if (v_isShared_8308_ == 0)
{
v___x_8310_ = v___x_8307_;
goto v_reusejp_8309_;
}
else
{
lean_object* v_reuseFailAlloc_8311_; 
v_reuseFailAlloc_8311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8311_, 0, v_a_8304_);
lean_ctor_set(v_reuseFailAlloc_8311_, 1, v_a_8305_);
v___x_8310_ = v_reuseFailAlloc_8311_;
goto v_reusejp_8309_;
}
v_reusejp_8309_:
{
return v___x_8310_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibSync___boxed(lean_object* v_libName_8315_, lean_object* v_libFile_8316_, lean_object* v_linkObjs_8317_, lean_object* v_linkLibs_8318_, lean_object* v_args_8319_, lean_object* v_plugin_8320_, lean_object* v_linkDeps_8321_, lean_object* v_macosxDeploymentTarget_x3f_8322_, lean_object* v_a_8323_, lean_object* v_a_8324_, lean_object* v_a_8325_, lean_object* v_a_8326_, lean_object* v_a_8327_, lean_object* v_a_8328_, lean_object* v_a_8329_){
_start:
{
uint8_t v_plugin_boxed_8330_; uint8_t v_linkDeps_boxed_8331_; lean_object* v_res_8332_; 
v_plugin_boxed_8330_ = lean_unbox(v_plugin_8320_);
v_linkDeps_boxed_8331_ = lean_unbox(v_linkDeps_8321_);
v_res_8332_ = l_Lake_buildLeanSharedLibSync(v_libName_8315_, v_libFile_8316_, v_linkObjs_8317_, v_linkLibs_8318_, v_args_8319_, v_plugin_boxed_8330_, v_linkDeps_boxed_8331_, v_macosxDeploymentTarget_x3f_8322_, v_a_8323_, v_a_8324_, v_a_8325_, v_a_8326_, v_a_8327_, v_a_8328_);
lean_dec_ref(v_a_8327_);
lean_dec(v_a_8326_);
lean_dec(v_a_8325_);
lean_dec(v_a_8324_);
return v_res_8332_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object* v_traceArgs_8333_, lean_object* v_weakArgs_8334_, lean_object* v_libName_8335_, lean_object* v_libFile_8336_, lean_object* v_objs_8337_, uint8_t v_plugin_8338_, uint8_t v_linkDeps_8339_, lean_object* v_macosxDeploymentTarget_x3f_8340_, lean_object* v_libs_8341_, lean_object* v___y_8342_, lean_object* v___y_8343_, lean_object* v___y_8344_, lean_object* v___y_8345_, lean_object* v___y_8346_, lean_object* v___y_8347_){
_start:
{
uint64_t v___y_8350_; uint64_t v___x_8375_; lean_object* v___x_8376_; lean_object* v___x_8377_; uint8_t v___x_8378_; 
v___x_8375_ = l_Lake_Hash_nil;
v___x_8376_ = lean_unsigned_to_nat(0u);
v___x_8377_ = lean_array_get_size(v_traceArgs_8333_);
v___x_8378_ = lean_nat_dec_lt(v___x_8376_, v___x_8377_);
if (v___x_8378_ == 0)
{
v___y_8350_ = v___x_8375_;
goto v___jp_8349_;
}
else
{
size_t v___x_8379_; size_t v___x_8380_; uint64_t v___x_8381_; 
v___x_8379_ = ((size_t)0ULL);
v___x_8380_ = lean_usize_of_nat(v___x_8377_);
v___x_8381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Internal_buildLeanO_spec__1(v_traceArgs_8333_, v___x_8379_, v___x_8380_, v___x_8375_);
v___y_8350_ = v___x_8381_;
goto v___jp_8349_;
}
v___jp_8349_:
{
lean_object* v_log_8351_; uint8_t v_action_8352_; uint8_t v_wantsRebuild_8353_; lean_object* v_trace_8354_; lean_object* v_buildTime_8355_; lean_object* v___x_8357_; uint8_t v_isShared_8358_; uint8_t v_isSharedCheck_8374_; 
v_log_8351_ = lean_ctor_get(v___y_8347_, 0);
v_action_8352_ = lean_ctor_get_uint8(v___y_8347_, sizeof(void*)*3);
v_wantsRebuild_8353_ = lean_ctor_get_uint8(v___y_8347_, sizeof(void*)*3 + 1);
v_trace_8354_ = lean_ctor_get(v___y_8347_, 1);
v_buildTime_8355_ = lean_ctor_get(v___y_8347_, 2);
v_isSharedCheck_8374_ = !lean_is_exclusive(v___y_8347_);
if (v_isSharedCheck_8374_ == 0)
{
v___x_8357_ = v___y_8347_;
v_isShared_8358_ = v_isSharedCheck_8374_;
goto v_resetjp_8356_;
}
else
{
lean_inc(v_buildTime_8355_);
lean_inc(v_trace_8354_);
lean_inc(v_log_8351_);
lean_dec(v___y_8347_);
v___x_8357_ = lean_box(0);
v_isShared_8358_ = v_isSharedCheck_8374_;
goto v_resetjp_8356_;
}
v_resetjp_8356_:
{
lean_object* v___x_8359_; lean_object* v___x_8360_; lean_object* v___x_8361_; lean_object* v___x_8362_; lean_object* v___x_8363_; lean_object* v___x_8364_; lean_object* v___x_8365_; lean_object* v___x_8366_; lean_object* v___x_8367_; lean_object* v___x_8368_; lean_object* v___x_8370_; 
v___x_8359_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_8360_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_8361_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_8333_);
v___x_8362_ = lean_array_to_list(v_traceArgs_8333_);
v___x_8363_ = l_List_toString___at___00Lake_Internal_buildLeanO_spec__0(v___x_8362_);
lean_dec(v___x_8362_);
v___x_8364_ = lean_string_append(v___x_8361_, v___x_8363_);
lean_dec_ref(v___x_8363_);
v___x_8365_ = lean_string_append(v___x_8360_, v___x_8364_);
lean_dec_ref(v___x_8364_);
v___x_8366_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_8367_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_8367_, 0, v___x_8365_);
lean_ctor_set(v___x_8367_, 1, v___x_8359_);
lean_ctor_set(v___x_8367_, 2, v___x_8366_);
lean_ctor_set_uint64(v___x_8367_, sizeof(void*)*3, v___y_8350_);
v___x_8368_ = l_Lake_BuildTrace_mix(v_trace_8354_, v___x_8367_);
if (v_isShared_8358_ == 0)
{
lean_ctor_set(v___x_8357_, 1, v___x_8368_);
v___x_8370_ = v___x_8357_;
goto v_reusejp_8369_;
}
else
{
lean_object* v_reuseFailAlloc_8373_; 
v_reuseFailAlloc_8373_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8373_, 0, v_log_8351_);
lean_ctor_set(v_reuseFailAlloc_8373_, 1, v___x_8368_);
lean_ctor_set(v_reuseFailAlloc_8373_, 2, v_buildTime_8355_);
lean_ctor_set_uint8(v_reuseFailAlloc_8373_, sizeof(void*)*3, v_action_8352_);
lean_ctor_set_uint8(v_reuseFailAlloc_8373_, sizeof(void*)*3 + 1, v_wantsRebuild_8353_);
v___x_8370_ = v_reuseFailAlloc_8373_;
goto v_reusejp_8369_;
}
v_reusejp_8369_:
{
lean_object* v___x_8371_; lean_object* v___x_8372_; 
v___x_8371_ = l_Array_append___redArg(v_weakArgs_8334_, v_traceArgs_8333_);
lean_dec_ref(v_traceArgs_8333_);
v___x_8372_ = l_Lake_buildLeanSharedLibSync(v_libName_8335_, v_libFile_8336_, v_objs_8337_, v_libs_8341_, v___x_8371_, v_plugin_8338_, v_linkDeps_8339_, v_macosxDeploymentTarget_x3f_8340_, v___y_8342_, v___y_8343_, v___y_8344_, v___y_8345_, v___y_8346_, v___x_8370_);
return v___x_8372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object* v_traceArgs_8382_, lean_object* v_weakArgs_8383_, lean_object* v_libName_8384_, lean_object* v_libFile_8385_, lean_object* v_objs_8386_, lean_object* v_plugin_8387_, lean_object* v_linkDeps_8388_, lean_object* v_macosxDeploymentTarget_x3f_8389_, lean_object* v_libs_8390_, lean_object* v___y_8391_, lean_object* v___y_8392_, lean_object* v___y_8393_, lean_object* v___y_8394_, lean_object* v___y_8395_, lean_object* v___y_8396_, lean_object* v___y_8397_){
_start:
{
uint8_t v_plugin_boxed_8398_; uint8_t v_linkDeps_boxed_8399_; lean_object* v_res_8400_; 
v_plugin_boxed_8398_ = lean_unbox(v_plugin_8387_);
v_linkDeps_boxed_8399_ = lean_unbox(v_linkDeps_8388_);
v_res_8400_ = l_Lake_buildLeanSharedLib___lam__0(v_traceArgs_8382_, v_weakArgs_8383_, v_libName_8384_, v_libFile_8385_, v_objs_8386_, v_plugin_boxed_8398_, v_linkDeps_boxed_8399_, v_macosxDeploymentTarget_x3f_8389_, v_libs_8390_, v___y_8391_, v___y_8392_, v___y_8393_, v___y_8394_, v___y_8395_, v___y_8396_);
lean_dec_ref(v___y_8395_);
lean_dec(v___y_8394_);
lean_dec(v___y_8393_);
lean_dec(v___y_8392_);
return v_res_8400_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object* v_traceArgs_8401_, lean_object* v_weakArgs_8402_, lean_object* v_libName_8403_, lean_object* v_libFile_8404_, uint8_t v_plugin_8405_, uint8_t v_linkDeps_8406_, lean_object* v_macosxDeploymentTarget_x3f_8407_, lean_object* v_linkLibs_8408_, lean_object* v___x_8409_, lean_object* v_objs_8410_, lean_object* v___y_8411_, lean_object* v___y_8412_, lean_object* v___y_8413_, lean_object* v___y_8414_, lean_object* v___y_8415_, lean_object* v___y_8416_){
_start:
{
lean_object* v_trace_8418_; lean_object* v___x_8419_; lean_object* v___x_8420_; lean_object* v___f_8421_; lean_object* v___x_8422_; lean_object* v___x_8423_; lean_object* v___x_8424_; uint8_t v___x_8425_; lean_object* v___x_8426_; lean_object* v___x_8427_; 
v_trace_8418_ = lean_ctor_get(v___y_8416_, 1);
v___x_8419_ = lean_box(v_plugin_8405_);
v___x_8420_ = lean_box(v_linkDeps_8406_);
v___f_8421_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__0___boxed), 16, 8);
lean_closure_set(v___f_8421_, 0, v_traceArgs_8401_);
lean_closure_set(v___f_8421_, 1, v_weakArgs_8402_);
lean_closure_set(v___f_8421_, 2, v_libName_8403_);
lean_closure_set(v___f_8421_, 3, v_libFile_8404_);
lean_closure_set(v___f_8421_, 4, v_objs_8410_);
lean_closure_set(v___f_8421_, 5, v___x_8419_);
lean_closure_set(v___f_8421_, 6, v___x_8420_);
lean_closure_set(v___f_8421_, 7, v_macosxDeploymentTarget_x3f_8407_);
v___x_8422_ = ((lean_object*)(l_Lake_buildSharedLib___lam__1___closed__0));
v___x_8423_ = l_Lake_Job_collectArray___redArg(v_linkLibs_8408_, v___x_8422_);
v___x_8424_ = lean_unsigned_to_nat(0u);
v___x_8425_ = 0;
v___x_8426_ = l_Lake_Job_mapM___redArg(v___x_8409_, v___x_8423_, v___f_8421_, v___x_8424_, v___x_8425_, v___y_8411_, v___y_8412_, v___y_8413_, v___y_8414_, v___y_8415_, v_trace_8418_);
v___x_8427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8427_, 0, v___x_8426_);
lean_ctor_set(v___x_8427_, 1, v___y_8416_);
return v___x_8427_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1___boxed(lean_object** _args){
lean_object* v_traceArgs_8428_ = _args[0];
lean_object* v_weakArgs_8429_ = _args[1];
lean_object* v_libName_8430_ = _args[2];
lean_object* v_libFile_8431_ = _args[3];
lean_object* v_plugin_8432_ = _args[4];
lean_object* v_linkDeps_8433_ = _args[5];
lean_object* v_macosxDeploymentTarget_x3f_8434_ = _args[6];
lean_object* v_linkLibs_8435_ = _args[7];
lean_object* v___x_8436_ = _args[8];
lean_object* v_objs_8437_ = _args[9];
lean_object* v___y_8438_ = _args[10];
lean_object* v___y_8439_ = _args[11];
lean_object* v___y_8440_ = _args[12];
lean_object* v___y_8441_ = _args[13];
lean_object* v___y_8442_ = _args[14];
lean_object* v___y_8443_ = _args[15];
lean_object* v___y_8444_ = _args[16];
_start:
{
uint8_t v_plugin_boxed_8445_; uint8_t v_linkDeps_boxed_8446_; lean_object* v_res_8447_; 
v_plugin_boxed_8445_ = lean_unbox(v_plugin_8432_);
v_linkDeps_boxed_8446_ = lean_unbox(v_linkDeps_8433_);
v_res_8447_ = l_Lake_buildLeanSharedLib___lam__1(v_traceArgs_8428_, v_weakArgs_8429_, v_libName_8430_, v_libFile_8431_, v_plugin_boxed_8445_, v_linkDeps_boxed_8446_, v_macosxDeploymentTarget_x3f_8434_, v_linkLibs_8435_, v___x_8436_, v_objs_8437_, v___y_8438_, v___y_8439_, v___y_8440_, v___y_8441_, v___y_8442_, v___y_8443_);
lean_dec_ref(v___y_8442_);
lean_dec(v___y_8441_);
lean_dec(v___y_8440_);
lean_dec(v___y_8439_);
lean_dec_ref(v_linkLibs_8435_);
return v_res_8447_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object* v_libName_8448_, lean_object* v_libFile_8449_, lean_object* v_linkObjs_8450_, lean_object* v_linkLibs_8451_, lean_object* v_weakArgs_8452_, lean_object* v_traceArgs_8453_, uint8_t v_plugin_8454_, uint8_t v_linkDeps_8455_, lean_object* v_macosxDeploymentTarget_x3f_8456_, lean_object* v_a_8457_, lean_object* v_a_8458_, lean_object* v_a_8459_, lean_object* v_a_8460_, lean_object* v_a_8461_, lean_object* v_a_8462_){
_start:
{
lean_object* v___x_8464_; lean_object* v___x_8465_; lean_object* v___x_8466_; lean_object* v___f_8467_; lean_object* v___x_8468_; lean_object* v___x_8469_; lean_object* v___x_8470_; uint8_t v___x_8471_; lean_object* v___x_8472_; 
v___x_8464_ = l_Lake_instDataKindDynlib;
v___x_8465_ = lean_box(v_plugin_8454_);
v___x_8466_ = lean_box(v_linkDeps_8455_);
v___f_8467_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__1___boxed), 17, 9);
lean_closure_set(v___f_8467_, 0, v_traceArgs_8453_);
lean_closure_set(v___f_8467_, 1, v_weakArgs_8452_);
lean_closure_set(v___f_8467_, 2, v_libName_8448_);
lean_closure_set(v___f_8467_, 3, v_libFile_8449_);
lean_closure_set(v___f_8467_, 4, v___x_8465_);
lean_closure_set(v___f_8467_, 5, v___x_8466_);
lean_closure_set(v___f_8467_, 6, v_macosxDeploymentTarget_x3f_8456_);
lean_closure_set(v___f_8467_, 7, v_linkLibs_8451_);
lean_closure_set(v___f_8467_, 8, v___x_8464_);
v___x_8468_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8469_ = l_Lake_Job_collectArray___redArg(v_linkObjs_8450_, v___x_8468_);
v___x_8470_ = lean_unsigned_to_nat(0u);
v___x_8471_ = 1;
v___x_8472_ = l_Lake_Job_bindM___redArg(v___x_8464_, v___x_8469_, v___f_8467_, v___x_8470_, v___x_8471_, v_a_8457_, v_a_8458_, v_a_8459_, v_a_8460_, v_a_8461_, v_a_8462_);
return v___x_8472_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object* v_libName_8473_, lean_object* v_libFile_8474_, lean_object* v_linkObjs_8475_, lean_object* v_linkLibs_8476_, lean_object* v_weakArgs_8477_, lean_object* v_traceArgs_8478_, lean_object* v_plugin_8479_, lean_object* v_linkDeps_8480_, lean_object* v_macosxDeploymentTarget_x3f_8481_, lean_object* v_a_8482_, lean_object* v_a_8483_, lean_object* v_a_8484_, lean_object* v_a_8485_, lean_object* v_a_8486_, lean_object* v_a_8487_, lean_object* v_a_8488_){
_start:
{
uint8_t v_plugin_boxed_8489_; uint8_t v_linkDeps_boxed_8490_; lean_object* v_res_8491_; 
v_plugin_boxed_8489_ = lean_unbox(v_plugin_8479_);
v_linkDeps_boxed_8490_ = lean_unbox(v_linkDeps_8480_);
v_res_8491_ = l_Lake_buildLeanSharedLib(v_libName_8473_, v_libFile_8474_, v_linkObjs_8475_, v_linkLibs_8476_, v_weakArgs_8477_, v_traceArgs_8478_, v_plugin_boxed_8489_, v_linkDeps_boxed_8490_, v_macosxDeploymentTarget_x3f_8481_, v_a_8482_, v_a_8483_, v_a_8484_, v_a_8485_, v_a_8486_, v_a_8487_);
lean_dec_ref(v_a_8487_);
lean_dec_ref(v_a_8486_);
lean_dec(v_a_8485_);
lean_dec(v_a_8484_);
lean_dec(v_a_8483_);
lean_dec_ref(v_linkObjs_8475_);
return v_res_8491_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync___lam__0(lean_object* v_linkLibs_8492_, lean_object* v_linkObjs_8493_, lean_object* v_args_8494_, uint8_t v_sharedLean_8495_, lean_object* v_exeFile_8496_, lean_object* v___y_8497_, lean_object* v___y_8498_, lean_object* v___y_8499_, lean_object* v___y_8500_, lean_object* v___y_8501_, lean_object* v___y_8502_, lean_object* v___y_8503_){
_start:
{
lean_object* v___x_8505_; 
v___x_8505_ = l_Lake_mkLinkOrder___redArg(v_linkLibs_8492_, v___y_8503_);
if (lean_obj_tag(v___x_8505_) == 0)
{
lean_object* v_toContext_8506_; lean_object* v_lakeEnv_8507_; lean_object* v_lean_8508_; lean_object* v_a_8509_; lean_object* v_a_8510_; lean_object* v_leanLibDir_8511_; lean_object* v_cc_8512_; lean_object* v_log_8513_; uint8_t v_action_8514_; uint8_t v_wantsRebuild_8515_; lean_object* v_trace_8516_; lean_object* v_buildTime_8517_; lean_object* v___x_8519_; uint8_t v_isShared_8520_; uint8_t v_isSharedCheck_8555_; 
v_toContext_8506_ = lean_ctor_get(v___y_8502_, 1);
v_lakeEnv_8507_ = lean_ctor_get(v_toContext_8506_, 0);
v_lean_8508_ = lean_ctor_get(v_lakeEnv_8507_, 1);
v_a_8509_ = lean_ctor_get(v___x_8505_, 1);
lean_inc(v_a_8509_);
v_a_8510_ = lean_ctor_get(v___x_8505_, 0);
lean_inc(v_a_8510_);
lean_dec_ref_known(v___x_8505_, 2);
v_leanLibDir_8511_ = lean_ctor_get(v_lean_8508_, 3);
v_cc_8512_ = lean_ctor_get(v_lean_8508_, 14);
v_log_8513_ = lean_ctor_get(v_a_8509_, 0);
v_action_8514_ = lean_ctor_get_uint8(v_a_8509_, sizeof(void*)*3);
v_wantsRebuild_8515_ = lean_ctor_get_uint8(v_a_8509_, sizeof(void*)*3 + 1);
v_trace_8516_ = lean_ctor_get(v_a_8509_, 1);
v_buildTime_8517_ = lean_ctor_get(v_a_8509_, 2);
v_isSharedCheck_8555_ = !lean_is_exclusive(v_a_8509_);
if (v_isSharedCheck_8555_ == 0)
{
v___x_8519_ = v_a_8509_;
v_isShared_8520_ = v_isSharedCheck_8555_;
goto v_resetjp_8518_;
}
else
{
lean_inc(v_buildTime_8517_);
lean_inc(v_trace_8516_);
lean_inc(v_log_8513_);
lean_dec(v_a_8509_);
v___x_8519_ = lean_box(0);
v_isShared_8520_ = v_isSharedCheck_8555_;
goto v_resetjp_8518_;
}
v_resetjp_8518_:
{
lean_object* v___x_8521_; lean_object* v___x_8522_; lean_object* v___x_8523_; lean_object* v___x_8524_; lean_object* v___x_8525_; lean_object* v___x_8526_; lean_object* v___x_8527_; lean_object* v___x_8528_; lean_object* v___x_8529_; lean_object* v___x_8530_; 
v___x_8521_ = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(v_linkObjs_8493_, v_a_8510_);
lean_dec(v_a_8510_);
v___x_8522_ = l_Array_append___redArg(v___x_8521_, v_args_8494_);
v___x_8523_ = lean_unsigned_to_nat(2u);
v___x_8524_ = lean_mk_empty_array_with_capacity(v___x_8523_);
lean_dec_ref(v___x_8524_);
v___x_8525_ = lean_obj_once(&l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0, &l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0_once, _init_l___private_Lake_Build_Common_0__Lake_mkLeanLinkArgs___redArg___closed__0);
lean_inc_ref(v_leanLibDir_8511_);
v___x_8526_ = lean_array_push(v___x_8525_, v_leanLibDir_8511_);
v___x_8527_ = l_Array_append___redArg(v___x_8522_, v___x_8526_);
lean_dec_ref(v___x_8526_);
v___x_8528_ = l_Lake_LeanInstall_ccLinkFlags(v_sharedLean_8495_, v_lean_8508_);
v___x_8529_ = l_Array_append___redArg(v___x_8527_, v___x_8528_);
lean_dec_ref(v___x_8528_);
lean_inc_ref(v_cc_8512_);
v___x_8530_ = l_Lake_compileExe(v_exeFile_8496_, v___x_8529_, v_cc_8512_, v___y_8497_, v_log_8513_);
lean_dec_ref(v___x_8529_);
if (lean_obj_tag(v___x_8530_) == 0)
{
lean_object* v_a_8531_; lean_object* v_a_8532_; lean_object* v___x_8534_; uint8_t v_isShared_8535_; uint8_t v_isSharedCheck_8542_; 
v_a_8531_ = lean_ctor_get(v___x_8530_, 0);
v_a_8532_ = lean_ctor_get(v___x_8530_, 1);
v_isSharedCheck_8542_ = !lean_is_exclusive(v___x_8530_);
if (v_isSharedCheck_8542_ == 0)
{
v___x_8534_ = v___x_8530_;
v_isShared_8535_ = v_isSharedCheck_8542_;
goto v_resetjp_8533_;
}
else
{
lean_inc(v_a_8532_);
lean_inc(v_a_8531_);
lean_dec(v___x_8530_);
v___x_8534_ = lean_box(0);
v_isShared_8535_ = v_isSharedCheck_8542_;
goto v_resetjp_8533_;
}
v_resetjp_8533_:
{
lean_object* v___x_8537_; 
if (v_isShared_8520_ == 0)
{
lean_ctor_set(v___x_8519_, 0, v_a_8532_);
v___x_8537_ = v___x_8519_;
goto v_reusejp_8536_;
}
else
{
lean_object* v_reuseFailAlloc_8541_; 
v_reuseFailAlloc_8541_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8541_, 0, v_a_8532_);
lean_ctor_set(v_reuseFailAlloc_8541_, 1, v_trace_8516_);
lean_ctor_set(v_reuseFailAlloc_8541_, 2, v_buildTime_8517_);
lean_ctor_set_uint8(v_reuseFailAlloc_8541_, sizeof(void*)*3, v_action_8514_);
lean_ctor_set_uint8(v_reuseFailAlloc_8541_, sizeof(void*)*3 + 1, v_wantsRebuild_8515_);
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
v_reuseFailAlloc_8540_ = lean_alloc_ctor(0, 2, 0);
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
else
{
lean_object* v_a_8543_; lean_object* v_a_8544_; lean_object* v___x_8546_; uint8_t v_isShared_8547_; uint8_t v_isSharedCheck_8554_; 
v_a_8543_ = lean_ctor_get(v___x_8530_, 0);
v_a_8544_ = lean_ctor_get(v___x_8530_, 1);
v_isSharedCheck_8554_ = !lean_is_exclusive(v___x_8530_);
if (v_isSharedCheck_8554_ == 0)
{
v___x_8546_ = v___x_8530_;
v_isShared_8547_ = v_isSharedCheck_8554_;
goto v_resetjp_8545_;
}
else
{
lean_inc(v_a_8544_);
lean_inc(v_a_8543_);
lean_dec(v___x_8530_);
v___x_8546_ = lean_box(0);
v_isShared_8547_ = v_isSharedCheck_8554_;
goto v_resetjp_8545_;
}
v_resetjp_8545_:
{
lean_object* v___x_8549_; 
if (v_isShared_8520_ == 0)
{
lean_ctor_set(v___x_8519_, 0, v_a_8544_);
v___x_8549_ = v___x_8519_;
goto v_reusejp_8548_;
}
else
{
lean_object* v_reuseFailAlloc_8553_; 
v_reuseFailAlloc_8553_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8553_, 0, v_a_8544_);
lean_ctor_set(v_reuseFailAlloc_8553_, 1, v_trace_8516_);
lean_ctor_set(v_reuseFailAlloc_8553_, 2, v_buildTime_8517_);
lean_ctor_set_uint8(v_reuseFailAlloc_8553_, sizeof(void*)*3, v_action_8514_);
lean_ctor_set_uint8(v_reuseFailAlloc_8553_, sizeof(void*)*3 + 1, v_wantsRebuild_8515_);
v___x_8549_ = v_reuseFailAlloc_8553_;
goto v_reusejp_8548_;
}
v_reusejp_8548_:
{
lean_object* v___x_8551_; 
if (v_isShared_8547_ == 0)
{
lean_ctor_set(v___x_8546_, 1, v___x_8549_);
v___x_8551_ = v___x_8546_;
goto v_reusejp_8550_;
}
else
{
lean_object* v_reuseFailAlloc_8552_; 
v_reuseFailAlloc_8552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8552_, 0, v_a_8543_);
lean_ctor_set(v_reuseFailAlloc_8552_, 1, v___x_8549_);
v___x_8551_ = v_reuseFailAlloc_8552_;
goto v_reusejp_8550_;
}
v_reusejp_8550_:
{
return v___x_8551_;
}
}
}
}
}
}
else
{
lean_object* v_a_8556_; lean_object* v_a_8557_; lean_object* v___x_8559_; uint8_t v_isShared_8560_; uint8_t v_isSharedCheck_8564_; 
lean_dec(v___y_8497_);
lean_dec_ref(v_exeFile_8496_);
v_a_8556_ = lean_ctor_get(v___x_8505_, 0);
v_a_8557_ = lean_ctor_get(v___x_8505_, 1);
v_isSharedCheck_8564_ = !lean_is_exclusive(v___x_8505_);
if (v_isSharedCheck_8564_ == 0)
{
v___x_8559_ = v___x_8505_;
v_isShared_8560_ = v_isSharedCheck_8564_;
goto v_resetjp_8558_;
}
else
{
lean_inc(v_a_8557_);
lean_inc(v_a_8556_);
lean_dec(v___x_8505_);
v___x_8559_ = lean_box(0);
v_isShared_8560_ = v_isSharedCheck_8564_;
goto v_resetjp_8558_;
}
v_resetjp_8558_:
{
lean_object* v___x_8562_; 
if (v_isShared_8560_ == 0)
{
v___x_8562_ = v___x_8559_;
goto v_reusejp_8561_;
}
else
{
lean_object* v_reuseFailAlloc_8563_; 
v_reuseFailAlloc_8563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8563_, 0, v_a_8556_);
lean_ctor_set(v_reuseFailAlloc_8563_, 1, v_a_8557_);
v___x_8562_ = v_reuseFailAlloc_8563_;
goto v_reusejp_8561_;
}
v_reusejp_8561_:
{
return v___x_8562_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync___lam__0___boxed(lean_object* v_linkLibs_8565_, lean_object* v_linkObjs_8566_, lean_object* v_args_8567_, lean_object* v_sharedLean_8568_, lean_object* v_exeFile_8569_, lean_object* v___y_8570_, lean_object* v___y_8571_, lean_object* v___y_8572_, lean_object* v___y_8573_, lean_object* v___y_8574_, lean_object* v___y_8575_, lean_object* v___y_8576_, lean_object* v___y_8577_){
_start:
{
uint8_t v_sharedLean_boxed_8578_; lean_object* v_res_8579_; 
v_sharedLean_boxed_8578_ = lean_unbox(v_sharedLean_8568_);
v_res_8579_ = l_Lake_buildLeanExeSync___lam__0(v_linkLibs_8565_, v_linkObjs_8566_, v_args_8567_, v_sharedLean_boxed_8578_, v_exeFile_8569_, v___y_8570_, v___y_8571_, v___y_8572_, v___y_8573_, v___y_8574_, v___y_8575_, v___y_8576_);
lean_dec_ref(v___y_8575_);
lean_dec(v___y_8574_);
lean_dec(v___y_8573_);
lean_dec(v___y_8572_);
lean_dec_ref(v___y_8571_);
lean_dec_ref(v_args_8567_);
lean_dec_ref(v_linkObjs_8566_);
lean_dec_ref(v_linkLibs_8565_);
return v_res_8579_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync(lean_object* v_exeFile_8580_, lean_object* v_linkObjs_8581_, lean_object* v_linkLibs_8582_, lean_object* v_args_8583_, uint8_t v_sharedLean_8584_, lean_object* v_macosxDeploymentTarget_x3f_8585_, lean_object* v_a_8586_, lean_object* v_a_8587_, lean_object* v_a_8588_, lean_object* v_a_8589_, lean_object* v_a_8590_, lean_object* v_a_8591_){
_start:
{
lean_object* v___y_8594_; lean_object* v___y_8595_; lean_object* v___y_8596_; lean_object* v___y_8597_; lean_object* v___y_8598_; lean_object* v___y_8599_; lean_object* v___y_8600_; lean_object* v_log_8624_; uint8_t v_action_8625_; uint8_t v_wantsRebuild_8626_; lean_object* v_trace_8627_; lean_object* v_buildTime_8628_; lean_object* v___x_8630_; uint8_t v_isShared_8631_; uint8_t v_isSharedCheck_8660_; 
v_log_8624_ = lean_ctor_get(v_a_8591_, 0);
v_action_8625_ = lean_ctor_get_uint8(v_a_8591_, sizeof(void*)*3);
v_wantsRebuild_8626_ = lean_ctor_get_uint8(v_a_8591_, sizeof(void*)*3 + 1);
v_trace_8627_ = lean_ctor_get(v_a_8591_, 1);
v_buildTime_8628_ = lean_ctor_get(v_a_8591_, 2);
v_isSharedCheck_8660_ = !lean_is_exclusive(v_a_8591_);
if (v_isSharedCheck_8660_ == 0)
{
v___x_8630_ = v_a_8591_;
v_isShared_8631_ = v_isSharedCheck_8660_;
goto v_resetjp_8629_;
}
else
{
lean_inc(v_buildTime_8628_);
lean_inc(v_trace_8627_);
lean_inc(v_log_8624_);
lean_dec(v_a_8591_);
v___x_8630_ = lean_box(0);
v_isShared_8631_ = v_isSharedCheck_8660_;
goto v_resetjp_8629_;
}
v___jp_8593_:
{
uint8_t v___x_8601_; uint8_t v___x_8602_; lean_object* v___x_8603_; lean_object* v___x_8604_; 
v___x_8601_ = 1;
v___x_8602_ = 0;
v___x_8603_ = l_System_FilePath_exeExtension;
v___x_8604_ = l_Lake_buildArtifactUnlessUpToDate(v_exeFile_8580_, v___y_8594_, v___x_8602_, v___x_8603_, v___x_8601_, v___x_8601_, v___x_8602_, v___y_8595_, v___y_8596_, v___y_8597_, v___y_8598_, v___y_8599_, v___y_8600_);
if (lean_obj_tag(v___x_8604_) == 0)
{
lean_object* v_a_8605_; lean_object* v_a_8606_; lean_object* v___x_8608_; uint8_t v_isShared_8609_; uint8_t v_isSharedCheck_8614_; 
v_a_8605_ = lean_ctor_get(v___x_8604_, 0);
v_a_8606_ = lean_ctor_get(v___x_8604_, 1);
v_isSharedCheck_8614_ = !lean_is_exclusive(v___x_8604_);
if (v_isSharedCheck_8614_ == 0)
{
v___x_8608_ = v___x_8604_;
v_isShared_8609_ = v_isSharedCheck_8614_;
goto v_resetjp_8607_;
}
else
{
lean_inc(v_a_8606_);
lean_inc(v_a_8605_);
lean_dec(v___x_8604_);
v___x_8608_ = lean_box(0);
v_isShared_8609_ = v_isSharedCheck_8614_;
goto v_resetjp_8607_;
}
v_resetjp_8607_:
{
lean_object* v_path_8610_; lean_object* v___x_8612_; 
v_path_8610_ = lean_ctor_get(v_a_8605_, 1);
lean_inc_ref(v_path_8610_);
lean_dec(v_a_8605_);
if (v_isShared_8609_ == 0)
{
lean_ctor_set(v___x_8608_, 0, v_path_8610_);
v___x_8612_ = v___x_8608_;
goto v_reusejp_8611_;
}
else
{
lean_object* v_reuseFailAlloc_8613_; 
v_reuseFailAlloc_8613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8613_, 0, v_path_8610_);
lean_ctor_set(v_reuseFailAlloc_8613_, 1, v_a_8606_);
v___x_8612_ = v_reuseFailAlloc_8613_;
goto v_reusejp_8611_;
}
v_reusejp_8611_:
{
return v___x_8612_;
}
}
}
else
{
lean_object* v_a_8615_; lean_object* v_a_8616_; lean_object* v___x_8618_; uint8_t v_isShared_8619_; uint8_t v_isSharedCheck_8623_; 
v_a_8615_ = lean_ctor_get(v___x_8604_, 0);
v_a_8616_ = lean_ctor_get(v___x_8604_, 1);
v_isSharedCheck_8623_ = !lean_is_exclusive(v___x_8604_);
if (v_isSharedCheck_8623_ == 0)
{
v___x_8618_ = v___x_8604_;
v_isShared_8619_ = v_isSharedCheck_8623_;
goto v_resetjp_8617_;
}
else
{
lean_inc(v_a_8616_);
lean_inc(v_a_8615_);
lean_dec(v___x_8604_);
v___x_8618_ = lean_box(0);
v_isShared_8619_ = v_isSharedCheck_8623_;
goto v_resetjp_8617_;
}
v_resetjp_8617_:
{
lean_object* v___x_8621_; 
if (v_isShared_8619_ == 0)
{
v___x_8621_ = v___x_8618_;
goto v_reusejp_8620_;
}
else
{
lean_object* v_reuseFailAlloc_8622_; 
v_reuseFailAlloc_8622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_8622_, 0, v_a_8615_);
lean_ctor_set(v_reuseFailAlloc_8622_, 1, v_a_8616_);
v___x_8621_ = v_reuseFailAlloc_8622_;
goto v_reusejp_8620_;
}
v_reusejp_8620_:
{
return v___x_8621_;
}
}
}
}
v_resetjp_8629_:
{
lean_object* v_toBuildConfig_8632_; lean_object* v_leanTrace_8633_; lean_object* v___x_8634_; lean_object* v___x_8635_; lean_object* v___x_8636_; lean_object* v___x_8638_; 
v_toBuildConfig_8632_ = lean_ctor_get(v_a_8590_, 0);
v_leanTrace_8633_ = lean_ctor_get(v_a_8590_, 2);
lean_inc_ref(v_leanTrace_8633_);
v___x_8634_ = l_Lake_BuildTrace_mix(v_trace_8627_, v_leanTrace_8633_);
v___x_8635_ = l_Lake_platformTrace;
v___x_8636_ = l_Lake_BuildTrace_mix(v___x_8634_, v___x_8635_);
lean_inc(v_buildTime_8628_);
lean_inc_ref(v___x_8636_);
lean_inc_ref(v_log_8624_);
if (v_isShared_8631_ == 0)
{
lean_ctor_set(v___x_8630_, 1, v___x_8636_);
v___x_8638_ = v___x_8630_;
goto v_reusejp_8637_;
}
else
{
lean_object* v_reuseFailAlloc_8659_; 
v_reuseFailAlloc_8659_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8659_, 0, v_log_8624_);
lean_ctor_set(v_reuseFailAlloc_8659_, 1, v___x_8636_);
lean_ctor_set(v_reuseFailAlloc_8659_, 2, v_buildTime_8628_);
lean_ctor_set_uint8(v_reuseFailAlloc_8659_, sizeof(void*)*3, v_action_8625_);
lean_ctor_set_uint8(v_reuseFailAlloc_8659_, sizeof(void*)*3 + 1, v_wantsRebuild_8626_);
v___x_8638_ = v_reuseFailAlloc_8659_;
goto v_reusejp_8637_;
}
v_reusejp_8637_:
{
lean_object* v___y_8640_; lean_object* v_val_8641_; 
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_8585_) == 0)
{
lean_object* v_macosxDeploymentTarget_x3f_8654_; lean_object* v___x_8655_; lean_object* v___f_8656_; 
v_macosxDeploymentTarget_x3f_8654_ = lean_ctor_get(v_toBuildConfig_8632_, 3);
v___x_8655_ = lean_box(v_sharedLean_8584_);
lean_inc(v_macosxDeploymentTarget_x3f_8654_);
lean_inc_ref(v_exeFile_8580_);
lean_inc_ref(v_args_8583_);
lean_inc_ref(v_linkObjs_8581_);
lean_inc_ref(v_linkLibs_8582_);
v___f_8656_ = lean_alloc_closure((void*)(l_Lake_buildLeanExeSync___lam__0___boxed), 13, 6);
lean_closure_set(v___f_8656_, 0, v_linkLibs_8582_);
lean_closure_set(v___f_8656_, 1, v_linkObjs_8581_);
lean_closure_set(v___f_8656_, 2, v_args_8583_);
lean_closure_set(v___f_8656_, 3, v___x_8655_);
lean_closure_set(v___f_8656_, 4, v_exeFile_8580_);
lean_closure_set(v___f_8656_, 5, v_macosxDeploymentTarget_x3f_8654_);
if (lean_obj_tag(v_macosxDeploymentTarget_x3f_8654_) == 1)
{
lean_object* v_val_8657_; 
lean_dec_ref(v___f_8656_);
lean_dec_ref(v___x_8638_);
v_val_8657_ = lean_ctor_get(v_macosxDeploymentTarget_x3f_8654_, 0);
lean_inc(v_val_8657_);
lean_inc_ref(v_macosxDeploymentTarget_x3f_8654_);
v___y_8640_ = v_macosxDeploymentTarget_x3f_8654_;
v_val_8641_ = v_val_8657_;
goto v___jp_8639_;
}
else
{
lean_dec_ref(v___x_8636_);
lean_dec(v_buildTime_8628_);
lean_dec_ref(v_log_8624_);
lean_dec_ref(v_args_8583_);
lean_dec_ref(v_linkLibs_8582_);
lean_dec_ref(v_linkObjs_8581_);
v___y_8594_ = v___f_8656_;
v___y_8595_ = v_a_8586_;
v___y_8596_ = v_a_8587_;
v___y_8597_ = v_a_8588_;
v___y_8598_ = v_a_8589_;
v___y_8599_ = v_a_8590_;
v___y_8600_ = v___x_8638_;
goto v___jp_8593_;
}
}
else
{
lean_object* v_val_8658_; 
lean_dec_ref(v___x_8638_);
v_val_8658_ = lean_ctor_get(v_macosxDeploymentTarget_x3f_8585_, 0);
lean_inc(v_val_8658_);
v___y_8640_ = v_macosxDeploymentTarget_x3f_8585_;
v_val_8641_ = v_val_8658_;
goto v___jp_8639_;
}
v___jp_8639_:
{
lean_object* v___x_8642_; lean_object* v___f_8643_; uint64_t v___x_8644_; uint64_t v___x_8645_; uint64_t v___x_8646_; lean_object* v___x_8647_; lean_object* v___x_8648_; lean_object* v___x_8649_; lean_object* v___x_8650_; lean_object* v___x_8651_; lean_object* v___x_8652_; lean_object* v___x_8653_; 
v___x_8642_ = lean_box(v_sharedLean_8584_);
lean_inc_ref(v_exeFile_8580_);
v___f_8643_ = lean_alloc_closure((void*)(l_Lake_buildLeanExeSync___lam__0___boxed), 13, 6);
lean_closure_set(v___f_8643_, 0, v_linkLibs_8582_);
lean_closure_set(v___f_8643_, 1, v_linkObjs_8581_);
lean_closure_set(v___f_8643_, 2, v_args_8583_);
lean_closure_set(v___f_8643_, 3, v___x_8642_);
lean_closure_set(v___f_8643_, 4, v_exeFile_8580_);
lean_closure_set(v___f_8643_, 5, v___y_8640_);
v___x_8644_ = l_Lake_Hash_nil;
v___x_8645_ = lean_string_hash(v_val_8641_);
v___x_8646_ = lean_uint64_mix_hash(v___x_8644_, v___x_8645_);
v___x_8647_ = ((lean_object*)(l_Lake_buildSharedLibSync___closed__0));
v___x_8648_ = lean_string_append(v___x_8647_, v_val_8641_);
lean_dec_ref(v_val_8641_);
v___x_8649_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_8650_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_8651_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_8651_, 0, v___x_8648_);
lean_ctor_set(v___x_8651_, 1, v___x_8649_);
lean_ctor_set(v___x_8651_, 2, v___x_8650_);
lean_ctor_set_uint64(v___x_8651_, sizeof(void*)*3, v___x_8646_);
v___x_8652_ = l_Lake_BuildTrace_mix(v___x_8636_, v___x_8651_);
v___x_8653_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_8653_, 0, v_log_8624_);
lean_ctor_set(v___x_8653_, 1, v___x_8652_);
lean_ctor_set(v___x_8653_, 2, v_buildTime_8628_);
lean_ctor_set_uint8(v___x_8653_, sizeof(void*)*3, v_action_8625_);
lean_ctor_set_uint8(v___x_8653_, sizeof(void*)*3 + 1, v_wantsRebuild_8626_);
v___y_8594_ = v___f_8643_;
v___y_8595_ = v_a_8586_;
v___y_8596_ = v_a_8587_;
v___y_8597_ = v_a_8588_;
v___y_8598_ = v_a_8589_;
v___y_8599_ = v_a_8590_;
v___y_8600_ = v___x_8653_;
goto v___jp_8593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExeSync___boxed(lean_object* v_exeFile_8661_, lean_object* v_linkObjs_8662_, lean_object* v_linkLibs_8663_, lean_object* v_args_8664_, lean_object* v_sharedLean_8665_, lean_object* v_macosxDeploymentTarget_x3f_8666_, lean_object* v_a_8667_, lean_object* v_a_8668_, lean_object* v_a_8669_, lean_object* v_a_8670_, lean_object* v_a_8671_, lean_object* v_a_8672_, lean_object* v_a_8673_){
_start:
{
uint8_t v_sharedLean_boxed_8674_; lean_object* v_res_8675_; 
v_sharedLean_boxed_8674_ = lean_unbox(v_sharedLean_8665_);
v_res_8675_ = l_Lake_buildLeanExeSync(v_exeFile_8661_, v_linkObjs_8662_, v_linkLibs_8663_, v_args_8664_, v_sharedLean_boxed_8674_, v_macosxDeploymentTarget_x3f_8666_, v_a_8667_, v_a_8668_, v_a_8669_, v_a_8670_, v_a_8671_, v_a_8672_);
lean_dec_ref(v_a_8671_);
lean_dec(v_a_8670_);
lean_dec(v_a_8669_);
lean_dec(v_a_8668_);
return v_res_8675_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0(lean_object* v_traceArgs_8676_, lean_object* v_weakArgs_8677_, lean_object* v_exeFile_8678_, lean_object* v_objs_8679_, uint8_t v_sharedLean_8680_, lean_object* v_macosxDeploymentTarget_x3f_8681_, lean_object* v_libs_8682_, lean_object* v___y_8683_, lean_object* v___y_8684_, lean_object* v___y_8685_, lean_object* v___y_8686_, lean_object* v___y_8687_, lean_object* v___y_8688_){
_start:
{
uint64_t v___y_8691_; uint64_t v___x_8716_; lean_object* v___x_8717_; lean_object* v___x_8718_; uint8_t v___x_8719_; 
v___x_8716_ = l_Lake_Hash_nil;
v___x_8717_ = lean_unsigned_to_nat(0u);
v___x_8718_ = lean_array_get_size(v_traceArgs_8676_);
v___x_8719_ = lean_nat_dec_lt(v___x_8717_, v___x_8718_);
if (v___x_8719_ == 0)
{
v___y_8691_ = v___x_8716_;
goto v___jp_8690_;
}
else
{
size_t v___x_8720_; size_t v___x_8721_; uint64_t v___x_8722_; 
v___x_8720_ = ((size_t)0ULL);
v___x_8721_ = lean_usize_of_nat(v___x_8718_);
v___x_8722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Internal_buildLeanO_spec__1(v_traceArgs_8676_, v___x_8720_, v___x_8721_, v___x_8716_);
v___y_8691_ = v___x_8722_;
goto v___jp_8690_;
}
v___jp_8690_:
{
lean_object* v_log_8692_; uint8_t v_action_8693_; uint8_t v_wantsRebuild_8694_; lean_object* v_trace_8695_; lean_object* v_buildTime_8696_; lean_object* v___x_8698_; uint8_t v_isShared_8699_; uint8_t v_isSharedCheck_8715_; 
v_log_8692_ = lean_ctor_get(v___y_8688_, 0);
v_action_8693_ = lean_ctor_get_uint8(v___y_8688_, sizeof(void*)*3);
v_wantsRebuild_8694_ = lean_ctor_get_uint8(v___y_8688_, sizeof(void*)*3 + 1);
v_trace_8695_ = lean_ctor_get(v___y_8688_, 1);
v_buildTime_8696_ = lean_ctor_get(v___y_8688_, 2);
v_isSharedCheck_8715_ = !lean_is_exclusive(v___y_8688_);
if (v_isSharedCheck_8715_ == 0)
{
v___x_8698_ = v___y_8688_;
v_isShared_8699_ = v_isSharedCheck_8715_;
goto v_resetjp_8697_;
}
else
{
lean_inc(v_buildTime_8696_);
lean_inc(v_trace_8695_);
lean_inc(v_log_8692_);
lean_dec(v___y_8688_);
v___x_8698_ = lean_box(0);
v_isShared_8699_ = v_isSharedCheck_8715_;
goto v_resetjp_8697_;
}
v_resetjp_8697_:
{
lean_object* v___x_8700_; lean_object* v___x_8701_; lean_object* v___x_8702_; lean_object* v___x_8703_; lean_object* v___x_8704_; lean_object* v___x_8705_; lean_object* v___x_8706_; lean_object* v___x_8707_; lean_object* v___x_8708_; lean_object* v___x_8709_; lean_object* v___x_8711_; 
v___x_8700_ = ((lean_object*)(l_Lake_platformTrace___closed__2));
v___x_8701_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__0));
v___x_8702_ = ((lean_object*)(l_Lake_buildO___lam__2___closed__1));
lean_inc_ref(v_traceArgs_8676_);
v___x_8703_ = lean_array_to_list(v_traceArgs_8676_);
v___x_8704_ = l_List_toString___at___00Lake_Internal_buildLeanO_spec__0(v___x_8703_);
lean_dec(v___x_8703_);
v___x_8705_ = lean_string_append(v___x_8702_, v___x_8704_);
lean_dec_ref(v___x_8704_);
v___x_8706_ = lean_string_append(v___x_8701_, v___x_8705_);
lean_dec_ref(v___x_8705_);
v___x_8707_ = lean_obj_once(&l_Lake_platformTrace___closed__4, &l_Lake_platformTrace___closed__4_once, _init_l_Lake_platformTrace___closed__4);
v___x_8708_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_8708_, 0, v___x_8706_);
lean_ctor_set(v___x_8708_, 1, v___x_8700_);
lean_ctor_set(v___x_8708_, 2, v___x_8707_);
lean_ctor_set_uint64(v___x_8708_, sizeof(void*)*3, v___y_8691_);
v___x_8709_ = l_Lake_BuildTrace_mix(v_trace_8695_, v___x_8708_);
if (v_isShared_8699_ == 0)
{
lean_ctor_set(v___x_8698_, 1, v___x_8709_);
v___x_8711_ = v___x_8698_;
goto v_reusejp_8710_;
}
else
{
lean_object* v_reuseFailAlloc_8714_; 
v_reuseFailAlloc_8714_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_8714_, 0, v_log_8692_);
lean_ctor_set(v_reuseFailAlloc_8714_, 1, v___x_8709_);
lean_ctor_set(v_reuseFailAlloc_8714_, 2, v_buildTime_8696_);
lean_ctor_set_uint8(v_reuseFailAlloc_8714_, sizeof(void*)*3, v_action_8693_);
lean_ctor_set_uint8(v_reuseFailAlloc_8714_, sizeof(void*)*3 + 1, v_wantsRebuild_8694_);
v___x_8711_ = v_reuseFailAlloc_8714_;
goto v_reusejp_8710_;
}
v_reusejp_8710_:
{
lean_object* v___x_8712_; lean_object* v___x_8713_; 
v___x_8712_ = l_Array_append___redArg(v_weakArgs_8677_, v_traceArgs_8676_);
lean_dec_ref(v_traceArgs_8676_);
v___x_8713_ = l_Lake_buildLeanExeSync(v_exeFile_8678_, v_objs_8679_, v_libs_8682_, v___x_8712_, v_sharedLean_8680_, v_macosxDeploymentTarget_x3f_8681_, v___y_8683_, v___y_8684_, v___y_8685_, v___y_8686_, v___y_8687_, v___x_8711_);
return v___x_8713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object* v_traceArgs_8723_, lean_object* v_weakArgs_8724_, lean_object* v_exeFile_8725_, lean_object* v_objs_8726_, lean_object* v_sharedLean_8727_, lean_object* v_macosxDeploymentTarget_x3f_8728_, lean_object* v_libs_8729_, lean_object* v___y_8730_, lean_object* v___y_8731_, lean_object* v___y_8732_, lean_object* v___y_8733_, lean_object* v___y_8734_, lean_object* v___y_8735_, lean_object* v___y_8736_){
_start:
{
uint8_t v_sharedLean_boxed_8737_; lean_object* v_res_8738_; 
v_sharedLean_boxed_8737_ = lean_unbox(v_sharedLean_8727_);
v_res_8738_ = l_Lake_buildLeanExe___lam__0(v_traceArgs_8723_, v_weakArgs_8724_, v_exeFile_8725_, v_objs_8726_, v_sharedLean_boxed_8737_, v_macosxDeploymentTarget_x3f_8728_, v_libs_8729_, v___y_8730_, v___y_8731_, v___y_8732_, v___y_8733_, v___y_8734_, v___y_8735_);
lean_dec_ref(v___y_8734_);
lean_dec(v___y_8733_);
lean_dec(v___y_8732_);
lean_dec(v___y_8731_);
return v_res_8738_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object* v_traceArgs_8739_, lean_object* v_weakArgs_8740_, lean_object* v_exeFile_8741_, uint8_t v_sharedLean_8742_, lean_object* v_macosxDeploymentTarget_x3f_8743_, lean_object* v_linkLibs_8744_, lean_object* v___x_8745_, lean_object* v_objs_8746_, lean_object* v___y_8747_, lean_object* v___y_8748_, lean_object* v___y_8749_, lean_object* v___y_8750_, lean_object* v___y_8751_, lean_object* v___y_8752_){
_start:
{
lean_object* v_trace_8754_; lean_object* v___x_8755_; lean_object* v___f_8756_; lean_object* v___x_8757_; lean_object* v___x_8758_; lean_object* v___x_8759_; uint8_t v___x_8760_; lean_object* v___x_8761_; lean_object* v___x_8762_; 
v_trace_8754_ = lean_ctor_get(v___y_8752_, 1);
v___x_8755_ = lean_box(v_sharedLean_8742_);
v___f_8756_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__0___boxed), 14, 6);
lean_closure_set(v___f_8756_, 0, v_traceArgs_8739_);
lean_closure_set(v___f_8756_, 1, v_weakArgs_8740_);
lean_closure_set(v___f_8756_, 2, v_exeFile_8741_);
lean_closure_set(v___f_8756_, 3, v_objs_8746_);
lean_closure_set(v___f_8756_, 4, v___x_8755_);
lean_closure_set(v___f_8756_, 5, v_macosxDeploymentTarget_x3f_8743_);
v___x_8757_ = ((lean_object*)(l_Lake_buildSharedLib___lam__1___closed__0));
v___x_8758_ = l_Lake_Job_collectArray___redArg(v_linkLibs_8744_, v___x_8757_);
v___x_8759_ = lean_unsigned_to_nat(0u);
v___x_8760_ = 0;
v___x_8761_ = l_Lake_Job_mapM___redArg(v___x_8745_, v___x_8758_, v___f_8756_, v___x_8759_, v___x_8760_, v___y_8747_, v___y_8748_, v___y_8749_, v___y_8750_, v___y_8751_, v_trace_8754_);
v___x_8762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8762_, 0, v___x_8761_);
lean_ctor_set(v___x_8762_, 1, v___y_8752_);
return v___x_8762_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object* v_traceArgs_8763_, lean_object* v_weakArgs_8764_, lean_object* v_exeFile_8765_, lean_object* v_sharedLean_8766_, lean_object* v_macosxDeploymentTarget_x3f_8767_, lean_object* v_linkLibs_8768_, lean_object* v___x_8769_, lean_object* v_objs_8770_, lean_object* v___y_8771_, lean_object* v___y_8772_, lean_object* v___y_8773_, lean_object* v___y_8774_, lean_object* v___y_8775_, lean_object* v___y_8776_, lean_object* v___y_8777_){
_start:
{
uint8_t v_sharedLean_boxed_8778_; lean_object* v_res_8779_; 
v_sharedLean_boxed_8778_ = lean_unbox(v_sharedLean_8766_);
v_res_8779_ = l_Lake_buildLeanExe___lam__1(v_traceArgs_8763_, v_weakArgs_8764_, v_exeFile_8765_, v_sharedLean_boxed_8778_, v_macosxDeploymentTarget_x3f_8767_, v_linkLibs_8768_, v___x_8769_, v_objs_8770_, v___y_8771_, v___y_8772_, v___y_8773_, v___y_8774_, v___y_8775_, v___y_8776_);
lean_dec_ref(v___y_8775_);
lean_dec(v___y_8774_);
lean_dec(v___y_8773_);
lean_dec(v___y_8772_);
lean_dec_ref(v_linkLibs_8768_);
return v_res_8779_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object* v_exeFile_8780_, lean_object* v_linkObjs_8781_, lean_object* v_linkLibs_8782_, lean_object* v_weakArgs_8783_, lean_object* v_traceArgs_8784_, uint8_t v_sharedLean_8785_, lean_object* v_macosxDeploymentTarget_x3f_8786_, lean_object* v_a_8787_, lean_object* v_a_8788_, lean_object* v_a_8789_, lean_object* v_a_8790_, lean_object* v_a_8791_, lean_object* v_a_8792_){
_start:
{
lean_object* v___x_8794_; lean_object* v___x_8795_; lean_object* v___f_8796_; lean_object* v___x_8797_; lean_object* v___x_8798_; lean_object* v___x_8799_; uint8_t v___x_8800_; lean_object* v___x_8801_; 
v___x_8794_ = l_Lake_instDataKindFilePath;
v___x_8795_ = lean_box(v_sharedLean_8785_);
v___f_8796_ = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__1___boxed), 15, 7);
lean_closure_set(v___f_8796_, 0, v_traceArgs_8784_);
lean_closure_set(v___f_8796_, 1, v_weakArgs_8783_);
lean_closure_set(v___f_8796_, 2, v_exeFile_8780_);
lean_closure_set(v___f_8796_, 3, v___x_8795_);
lean_closure_set(v___f_8796_, 4, v_macosxDeploymentTarget_x3f_8786_);
lean_closure_set(v___f_8796_, 5, v_linkLibs_8782_);
lean_closure_set(v___f_8796_, 6, v___x_8794_);
v___x_8797_ = ((lean_object*)(l_Lake_buildSharedLib___closed__0));
v___x_8798_ = l_Lake_Job_collectArray___redArg(v_linkObjs_8781_, v___x_8797_);
v___x_8799_ = lean_unsigned_to_nat(0u);
v___x_8800_ = 1;
v___x_8801_ = l_Lake_Job_bindM___redArg(v___x_8794_, v___x_8798_, v___f_8796_, v___x_8799_, v___x_8800_, v_a_8787_, v_a_8788_, v_a_8789_, v_a_8790_, v_a_8791_, v_a_8792_);
return v___x_8801_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object* v_exeFile_8802_, lean_object* v_linkObjs_8803_, lean_object* v_linkLibs_8804_, lean_object* v_weakArgs_8805_, lean_object* v_traceArgs_8806_, lean_object* v_sharedLean_8807_, lean_object* v_macosxDeploymentTarget_x3f_8808_, lean_object* v_a_8809_, lean_object* v_a_8810_, lean_object* v_a_8811_, lean_object* v_a_8812_, lean_object* v_a_8813_, lean_object* v_a_8814_, lean_object* v_a_8815_){
_start:
{
uint8_t v_sharedLean_boxed_8816_; lean_object* v_res_8817_; 
v_sharedLean_boxed_8816_ = lean_unbox(v_sharedLean_8807_);
v_res_8817_ = l_Lake_buildLeanExe(v_exeFile_8802_, v_linkObjs_8803_, v_linkLibs_8804_, v_weakArgs_8805_, v_traceArgs_8806_, v_sharedLean_boxed_8816_, v_macosxDeploymentTarget_x3f_8808_, v_a_8809_, v_a_8810_, v_a_8811_, v_a_8812_, v_a_8813_, v_a_8814_);
lean_dec_ref(v_a_8814_);
lean_dec_ref(v_a_8813_);
lean_dec(v_a_8812_);
lean_dec(v_a_8811_);
lean_dec(v_a_8810_);
lean_dec_ref(v_linkObjs_8803_);
return v_res_8817_;
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
